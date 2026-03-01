// Kea tree-sitter external scanner.
//
// Emits INDENT, DEDENT, NEWLINE, DOC_START, and DOC_BODY tokens based
// on an indentation stack.  Mirrors the layout logic in the Kea
// compiler's lexer (crates/kea-syntax/src/lexer.rs  apply_layout()).
//
// Key invariants:
//   - indent_stack is never empty (always has at least the base level 0)
//   - blank lines (only whitespace) never produce tokens
//   - inside brackets, no layout tokens are emitted
//   - EOF pops all remaining indent levels
//
// Doc blocks are split into two tokens:
//   - DOC_START: the "doc" keyword (3 chars)
//   - DOC_BODY:  optional inline text + indented body lines
// This allows the grammar to highlight "doc" as a keyword and the
// body as documentation.  The external scanner is called before extras
// processing, so DOC_BODY sees raw input right after "doc".

#include "tree_sitter/parser.h"

#include <stdbool.h>
#include <stdint.h>
#include <string.h>

// Token types — must match the order in grammar.js externals array.
enum TokenType {
    INDENT,
    DEDENT,
    NEWLINE,
    DOC_START,
    DOC_BODY,
};

// Scanner limits.
#define MAX_INDENT_DEPTH 128

typedef struct {
    uint16_t indent_stack[MAX_INDENT_DEPTH];
    uint8_t  stack_len;       // number of entries in indent_stack
    uint8_t  queued_dedents;  // pending DEDENT tokens to emit
    uint8_t  bracket_depth;   // nesting depth of (), [], {}
} Scanner;

// ── Lifecycle ───────────────────────────────────────────────────

void *tree_sitter_kea_external_scanner_create(void) {
    Scanner *s = calloc(1, sizeof(Scanner));
    s->indent_stack[0] = 0;
    s->stack_len = 1;
    return s;
}

void tree_sitter_kea_external_scanner_destroy(void *payload) {
    free(payload);
}

unsigned tree_sitter_kea_external_scanner_serialize(void *payload, char *buffer) {
    Scanner *s = (Scanner *)payload;
    unsigned i = 0;
    buffer[i++] = (char)s->stack_len;
    buffer[i++] = (char)s->queued_dedents;
    buffer[i++] = (char)s->bracket_depth;
    for (uint8_t j = 0; j < s->stack_len && i + 1 < TREE_SITTER_SERIALIZATION_BUFFER_SIZE; j++) {
        buffer[i++] = (char)(s->indent_stack[j] & 0xFF);
        buffer[i++] = (char)(s->indent_stack[j] >> 8);
    }
    return i;
}

void tree_sitter_kea_external_scanner_deserialize(void *payload, const char *buffer, unsigned length) {
    Scanner *s = (Scanner *)payload;
    if (length == 0) {
        s->indent_stack[0] = 0;
        s->stack_len = 1;
        s->queued_dedents = 0;
        s->bracket_depth = 0;
        return;
    }
    unsigned i = 0;
    s->stack_len = (uint8_t)buffer[i++];
    s->queued_dedents = (uint8_t)buffer[i++];
    s->bracket_depth = (uint8_t)buffer[i++];
    if (s->stack_len > MAX_INDENT_DEPTH) s->stack_len = MAX_INDENT_DEPTH;
    for (uint8_t j = 0; j < s->stack_len && i + 1 < length; j++) {
        s->indent_stack[j] = (uint8_t)buffer[i] | ((uint8_t)buffer[i + 1] << 8);
        i += 2;
    }
    if (s->stack_len == 0) {
        s->indent_stack[0] = 0;
        s->stack_len = 1;
    }
}

// ── Helpers ─────────────────────────────────────────────────────

static inline uint16_t stack_top(Scanner *s) {
    return s->indent_stack[s->stack_len - 1];
}

static inline void stack_push(Scanner *s, uint16_t val) {
    if (s->stack_len < MAX_INDENT_DEPTH) {
        s->indent_stack[s->stack_len++] = val;
    }
}

static inline void stack_pop(Scanner *s) {
    if (s->stack_len > 1) {
        s->stack_len--;
    }
}

static inline bool is_space_or_tab(int32_t c) {
    return c == ' ' || c == '\t';
}

static inline bool is_doc_start(int32_t c) {
    return c == 'd';
}

// ── Doc start scanner ──────────────────────────────────────────

// Scan just the "doc" keyword (3 chars).
static bool scan_doc_start(Scanner *s, TSLexer *lexer) {
    if (lexer->lookahead != 'd') return false;
    lexer->advance(lexer, false);
    if (lexer->lookahead != 'o') return false;
    lexer->advance(lexer, false);
    if (lexer->lookahead != 'c') return false;
    lexer->advance(lexer, false);

    int32_t after = lexer->lookahead;
    if (after != ' ' && after != '\t' && after != '\n' && after != '\r' && !lexer->eof(lexer)) {
        return false;
    }

    lexer->mark_end(lexer);
    lexer->result_symbol = DOC_START;
    return true;
}

// ── Doc body scanner ───────────────────────────────────────────

// Scan the doc body: optional inline text + indented body lines.
// Called right after DOC_START ("doc") was consumed.
//
// doc_col is the column where the "doc" keyword started (stack_top).
// Body lines must be indented strictly MORE than doc_col.
static bool scan_doc_body(Scanner *s, TSLexer *lexer, uint32_t doc_col) {
    bool has_content = false;

    // Inline text: if lookahead is space/tab, consume rest of line.
    if (lexer->lookahead == ' ' || lexer->lookahead == '\t') {
        while (lexer->lookahead != '\n' && lexer->lookahead != '\r' && !lexer->eof(lexer)) {
            lexer->advance(lexer, false);
        }
        lexer->mark_end(lexer);
        has_content = true;
    }

    // Try to consume indented body lines.
    for (;;) {
        if (lexer->lookahead != '\n' && lexer->lookahead != '\r') break;

        // Consume the newline speculatively.
        if (lexer->lookahead == '\r') lexer->advance(lexer, false);
        if (lexer->lookahead == '\n') lexer->advance(lexer, false);

        bool found_content = false;
        for (;;) {
            uint32_t line_indent = 0;
            while (is_space_or_tab(lexer->lookahead)) {
                line_indent++;
                lexer->advance(lexer, false);
            }

            if (lexer->eof(lexer)) break;

            if (lexer->lookahead == '\n' || lexer->lookahead == '\r') {
                // Blank line — consume and continue looking.
                if (lexer->lookahead == '\r') lexer->advance(lexer, false);
                if (lexer->lookahead == '\n') lexer->advance(lexer, false);
                continue;
            }

            if (line_indent > doc_col) {
                // Indented more than "doc" keyword — part of body.
                while (lexer->lookahead != '\n' && lexer->lookahead != '\r' && !lexer->eof(lexer)) {
                    lexer->advance(lexer, false);
                }
                lexer->mark_end(lexer);
                has_content = true;
                found_content = true;
                break;
            } else {
                break;
            }
        }

        if (!found_content) break;
    }

    if (has_content) {
        lexer->result_symbol = DOC_BODY;
        return true;
    }
    return false;
}

// ── Main scan function ──────────────────────────────────────────

bool tree_sitter_kea_external_scanner_scan(void *payload, TSLexer *lexer,
                                           const bool *valid_symbols) {
    Scanner *s = (Scanner *)payload;

    // --- Phase 0: Emit queued DEDENTs ---
    if (s->queued_dedents > 0 && valid_symbols[DEDENT]) {
        s->queued_dedents--;
        lexer->result_symbol = DEDENT;
        return true;
    }

    // --- Phase 0.5: Error recovery guard ---
    // If ALL external symbols are valid, the parser is in error recovery.
    if (valid_symbols[INDENT] && valid_symbols[DEDENT] &&
        valid_symbols[NEWLINE] && valid_symbols[DOC_START] && valid_symbols[DOC_BODY]) {
        return false;
    }

    // --- Phase 0.6: Doc body scan ---
    // Called right after DOC_START was consumed.  We check DOC_BODY
    // first because the external scanner runs before extras processing,
    // so we can see the raw newlines/spaces after "doc".  If we fall
    // through to Phase 2, those characters get consumed as whitespace.
    if (valid_symbols[DOC_BODY]) {
        // The doc keyword started at the current indent level.
        if (scan_doc_body(s, lexer, stack_top(s))) {
            return true;
        }
        // No body content — fall through.  The parser will skip the
        // optional($.doc_body) and try the next alternative.
    }

    // At EOF, only emit DEDENT or NEWLINE — never try DOC_START.
    if (lexer->eof(lexer) &&
        !valid_symbols[INDENT] && !valid_symbols[DEDENT] && !valid_symbols[NEWLINE]) {
        return false;
    }

    // --- Phase 2: Look for a newline ---
    bool found_newline = false;

    while (lexer->lookahead == ' ' || lexer->lookahead == '\t') {
        lexer->advance(lexer, true);
    }

    if (lexer->lookahead == '\n' || lexer->lookahead == '\r') {
        found_newline = true;
        while (lexer->lookahead == '\n' || lexer->lookahead == '\r' ||
               lexer->lookahead == ' ' || lexer->lookahead == '\t') {
            if (lexer->lookahead == '\n' || lexer->lookahead == '\r') {
                lexer->advance(lexer, true);
            } else {
                lexer->advance(lexer, true);
            }
        }
    }

    // --- Phase 3: At EOF, emit remaining layout tokens ---
    if (lexer->eof(lexer)) {
        if (valid_symbols[DEDENT] && s->stack_len > 1) {
            stack_pop(s);
            lexer->result_symbol = DEDENT;
            return true;
        }
        if (found_newline && valid_symbols[NEWLINE]) {
            lexer->result_symbol = NEWLINE;
            return true;
        }
        return false;
    }

    // --- Phase 4: If no newline found, try DOC_START at start of file ---
    if (!found_newline) {
        if (valid_symbols[DOC_START] && is_doc_start(lexer->lookahead)) {
            uint32_t col = lexer->get_column(lexer);
            if (col == stack_top(s)) {
                return scan_doc_start(s, lexer);
            }
        }
        return false;
    }

    // --- Phase 5: We crossed a newline.  Measure indent of next line ---
    uint32_t indent = lexer->get_column(lexer);

    // --- Phase 6: Emit layout token based on indent comparison ---
    uint16_t current = stack_top(s);

    if (indent > current) {
        if (valid_symbols[INDENT]) {
            stack_push(s, (uint16_t)indent);
            lexer->result_symbol = INDENT;
            return true;
        }
        if (valid_symbols[DOC_START] && is_doc_start(lexer->lookahead)) {
            return scan_doc_start(s, lexer);
        }
        return false;
    }

    if (indent < current) {
        if (valid_symbols[DEDENT]) {
            stack_pop(s);
            while (s->stack_len > 1 && indent < stack_top(s)) {
                stack_pop(s);
                s->queued_dedents++;
            }
            lexer->result_symbol = DEDENT;
            return true;
        }
        return false;
    }

    // indent == current
    if (valid_symbols[DOC_START] && is_doc_start(lexer->lookahead)) {
        return scan_doc_start(s, lexer);
    }

    if (valid_symbols[NEWLINE]) {
        lexer->result_symbol = NEWLINE;
        return true;
    }

    return false;
}
