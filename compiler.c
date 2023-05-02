#include <stdio.h>
#include <stdlib.h>
#include "common.h"
#include "compiler.h"
#include "scanner.h"

#ifdef DEBUG_PRINT_CODE
#include "debug.h"
#endif

typedef struct
{
    Token current;
    Token previous;
    bool hadError;
    bool panicMode;
} Parser;

typedef enum
{
    PREC_NONE,
    PREC_ASSIGNMENT,
    PREC_OR,
    PREC_AND,
    PREC_EQUALITY,
    PREC_COMPARISON,
    PREC_TERM,
    PREC_FACTOR,
    PREC_UNARY,
    PREC_CALL,
    PREC_PRIMARY
} Precedence;

typedef void (*ParseFn)();

typedef struct
{
    ParseFn prefix;
    ParseFn infix;
    Precedence precedence;
} ParseRule;

Parser parser;
Chunk *compilingChunk;
static Chunk *currentChunk()
{
    return compilingChunk;
}

static void errorAt(Token *token, const char *message)
{
    if (parser.panicMode)
        return;
    parser.panicMode = true;
    fprintf(stderr, "[line %d] Error", token->line);
    if (token->type == TOKEN_EOF)
    {
        fprintf(stderr, " at end");
    }
    else if (token->type == TOKEN_ERROR)
    {
        // Nothing.
    }
    else
    {
        fprintf(stderr, " at '%.*s'", token->length, token->start);
    }
    fprintf(stderr, ": %s\n", message);
    parser.hadError = true;
}

static void errorAtCurrent(const char *message)
{
    errorAt(&parser.current, message);
}

static void error(const char *message)
{
    errorAt(&parser.previous, message);
}

static void advance()
{
    parser.previous = parser.current;
    for (;;)
    {
        parser.current = scanToken();
        if (parser.current.type != TOKEN_ERROR)
            break;
        errorAtCurrent(parser.current.start);
    }
}

static void consume(TokenType type, const char *message)
{
    if (parser.current.type == type)
    {
        advance();
        return;
    }
    errorAtCurrent(message);
}

static void emitByte(uint8_t byte)
{
    writeChunk(currentChunk(), byte, parser.previous.line);
}

static void emitBytes(uint8_t byte1, uint8_t byte2)
{
    emitByte(byte1);
    emitByte(byte2);
}

static void emitReturn()
{
    emitByte(OP_RETURN);
}

static void endCompiler()
{
    emitReturn();
#ifdef DEBUG_PRINT_CODE
    if (!parser.hadError)
    {
        disassembleChunk(currentChunk(), "code");
    }
#endif
}

static void expression();
static ParseRule *getRule(TokenType type);
static void parsePrecedence(Precedence precedence);

static void binary()
{
    // Remember the operator.
    TokenType operatorType = parser.previous.type;
    // Compile the right operand.
    ParseRule *rule = getRule(operatorType);
    parsePrecedence((Precedence)(rule->precedence + 1));
    switch (operatorType)
    {
    case TOKEN_PLUS:
        emitByte(OP_ADD);
        break;
    case TOKEN_MINUS:
        emitByte(OP_SUBTRACT);
        break;
    case TOKEN_STAR:
        emitByte(OP_MULTIPLY);
        break;
    case TOKEN_SLASH:
        emitByte(OP_DIVIDE);
        break;
    default:
        return; // Unreachable.
    }
}

static void grouping()
{
    expression();
    consume(TOKEN_RIGHT_PAREN, "Expect ')' after expression.");
}

static uint8_t makeConstant(Value value)
{
    int constant = addConstant(currentChunk(), value);
    if (constant > UINT8_MAX)
    {
        error("Too many constants in one chunk.");
        return 0;
    }
    return (uint8_t)constant;
}

static void emitConstant(Value value)
{
    emitBytes(OP_CONSTANT, makeConstant(value));
}

static void number()
{
    double value = strtod(parser.previous.start, NULL);
    emitConstant(value);
}

static void unary()
{
    TokenType operatorType = parser.previous.type;
    // Compile the operand.
    parsePrecedence(PREC_UNARY);
    // Emit the operator instruction.
    switch (operatorType)
    {
    case TOKEN_MINUS:
        emitByte(OP_NEGATE);
        break;
    default:
        return; // Unreachable.
    }
}

ParseRule rules[] = {
    /* Compiling Expressions rules < Calls and Functions infix-left-paren
      [TOKEN_LEFT_PAREN]    = {grouping, NULL,   PREC_NONE},
    */
    //> Calls and Functions infix-left-paren
    [TOKEN_LEFT_PAREN] = {grouping, NULL, PREC_CALL},
    //< Calls and Functions infix-left-paren
    [TOKEN_RIGHT_PAREN] = {NULL, NULL, PREC_NONE},
    [TOKEN_LEFT_BRACE] = {NULL, NULL, PREC_NONE}, // [big]
    [TOKEN_RIGHT_BRACE] = {NULL, NULL, PREC_NONE},
    [TOKEN_COMMA] = {NULL, NULL, PREC_NONE},
    /* Compiling Expressions rules < Classes and Instances table-dot
      [TOKEN_DOT]           = {NULL,     NULL,   PREC_NONE},
    */
    //> Classes and Instances table-dot
    [TOKEN_DOT] = {NULL, NULL, PREC_CALL},
    //< Classes and Instances table-dot
    [TOKEN_MINUS] = {unary, binary, PREC_TERM},
    [TOKEN_PLUS] = {NULL, binary, PREC_TERM},
    [TOKEN_SEMICOLON] = {NULL, NULL, PREC_NONE},
    [TOKEN_SLASH] = {NULL, binary, PREC_FACTOR},
    [TOKEN_STAR] = {NULL, binary, PREC_FACTOR},
    /* Compiling Expressions rules < Types of Values table-not
      [TOKEN_BANG]          = {NULL,     NULL,   PREC_NONE},
    */
    //> Types of Values table-not
    [TOKEN_BANG] = {unary, NULL, PREC_NONE},
    //< Types of Values table-not
    /* Compiling Expressions rules < Types of Values table-equal
      [TOKEN_BANG_EQUAL]    = {NULL,     NULL,   PREC_NONE},
    */
    //> Types of Values table-equal
    [TOKEN_BANG_EQUAL] = {NULL, binary, PREC_EQUALITY},
    //< Types of Values table-equal
    [TOKEN_EQUAL] = {NULL, NULL, PREC_NONE},
    /* Compiling Expressions rules < Types of Values table-comparisons
      [TOKEN_EQUAL_EQUAL]   = {NULL,     NULL,   PREC_NONE},
      [TOKEN_GREATER]       = {NULL,     NULL,   PREC_NONE},
      [TOKEN_GREATER_EQUAL] = {NULL,     NULL,   PREC_NONE},
      [TOKEN_LESS]          = {NULL,     NULL,   PREC_NONE},
      [TOKEN_LESS_EQUAL]    = {NULL,     NULL,   PREC_NONE},
    */
    //> Types of Values table-comparisons
    [TOKEN_EQUAL_EQUAL] = {NULL, binary, PREC_EQUALITY},
    [TOKEN_GREATER] = {NULL, binary, PREC_COMPARISON},
    [TOKEN_GREATER_EQUAL] = {NULL, binary, PREC_COMPARISON},
    [TOKEN_LESS] = {NULL, binary, PREC_COMPARISON},
    [TOKEN_LESS_EQUAL] = {NULL, binary, PREC_COMPARISON},
    //< Types of Values table-comparisons
    /* Compiling Expressions rules < Global Variables table-identifier
      [TOKEN_IDENTIFIER]    = {NULL,     NULL,   PREC_NONE},
    */
    //> Global Variables table-identifier
    [TOKEN_IDENTIFIER] = {NULL, NULL, PREC_NONE},
    //< Global Variables table-identifier
    /* Compiling Expressions rules < Strings table-string
      [TOKEN_STRING]        = {NULL,     NULL,   PREC_NONE},
    */
    //> Strings table-string
    [TOKEN_STRING] = {NULL, NULL, PREC_NONE},
    //< Strings table-string
    [TOKEN_NUMBER] = {number, NULL, PREC_NONE},
    /* Compiling Expressions rules < Jumping Back and Forth table-and
      [TOKEN_AND]           = {NULL,     NULL,   PREC_NONE},
    */
    //> Jumping Back and Forth table-and
    [TOKEN_AND] = {NULL, NULL, PREC_AND},
    //< Jumping Back and Forth table-and
    [TOKEN_CLASS] = {NULL, NULL, PREC_NONE},
    [TOKEN_ELSE] = {NULL, NULL, PREC_NONE},
    /* Compiling Expressions rules < Types of Values table-false
      [TOKEN_FALSE]         = {NULL,     NULL,   PREC_NONE},
    */
    //> Types of Values table-false
    [TOKEN_FALSE] = {NULL, NULL, PREC_NONE},
    //< Types of Values table-false
    [TOKEN_FOR] = {NULL, NULL, PREC_NONE},
    [TOKEN_FUN] = {NULL, NULL, PREC_NONE},
    [TOKEN_IF] = {NULL, NULL, PREC_NONE},
    /* Compiling Expressions rules < Types of Values table-nil
      [TOKEN_NIL]           = {NULL,     NULL,   PREC_NONE},
    */
    //> Types of Values table-nil
    [TOKEN_NIL] = {NULL, NULL, PREC_NONE},
    //< Types of Values table-nil
    /* Compiling Expressions rules < Jumping Back and Forth table-or
      [TOKEN_OR]            = {NULL,     NULL,   PREC_NONE},
    */
    //> Jumping Back and Forth table-or
    [TOKEN_OR] = {NULL, NULL, PREC_OR},
    //< Jumping Back and Forth table-or
    [TOKEN_PRINT] = {NULL, NULL, PREC_NONE},
    [TOKEN_RETURN] = {NULL, NULL, PREC_NONE},
    /* Compiling Expressions rules < Superclasses table-super
      [TOKEN_SUPER]         = {NULL,     NULL,   PREC_NONE},
    */
    //> Superclasses table-super
    [TOKEN_SUPER] = {NULL, NULL, PREC_NONE},
    //< Superclasses table-super
    /* Compiling Expressions rules < Methods and Initializers table-this
      [TOKEN_THIS]          = {NULL,     NULL,   PREC_NONE},
    */
    //> Methods and Initializers table-this
    [TOKEN_THIS] = {NULL, NULL, PREC_NONE},
    //< Methods and Initializers table-this
    /* Compiling Expressions rules < Types of Values table-true
      [TOKEN_TRUE]          = {NULL,     NULL,   PREC_NONE},
    */
    //> Types of Values table-true
    [TOKEN_TRUE] = {NULL, NULL, PREC_NONE},
    //< Types of Values table-true
    [TOKEN_VAR] = {NULL, NULL, PREC_NONE},
    [TOKEN_WHILE] = {NULL, NULL, PREC_NONE},
    [TOKEN_ERROR] = {NULL, NULL, PREC_NONE},
    [TOKEN_EOF] = {NULL, NULL, PREC_NONE},
};

static void parsePrecedence(Precedence precedence)
{
    advance();
    ParseFn prefixRule = getRule(parser.previous.type)->prefix;
    if (prefixRule == NULL)
    {
        error("Expect expression.");
        return;
    }
    prefixRule();

    while (precedence <= getRule(parser.current.type)->precedence)
    {
        advance();
        ParseFn infixRule = getRule(parser.previous.type)->infix;
        infixRule();
    }
}

static ParseRule *getRule(TokenType type)
{
    return &rules[type];
}

static void expression()
{
    parsePrecedence(PREC_ASSIGNMENT);
}

bool compile(const char *source, Chunk *chunk)
{
    initScanner(source);
    compilingChunk = chunk;

    parser.hadError = false;
    parser.panicMode = false;

    advance();
    expression();
    consume(TOKEN_EOF, "Expect end of expression.");
    endCompiler();
    return !parser.hadError;
}
