// Kea tree-sitter external scanner.
//
// Emits INDENT, DEDENT, NEWLINE, and DOC_BLOCK tokens based on an
// indentation stack.  Mirrors the layout logic in the Kea compiler's
// lexer (crates/kea-syntax/src/lexer.rs  apply_layout()).
//
// Key invariants:
//   - indent_stack is never empty (always has at least the base level 0)
//   - blank lines (only whitespace) never produce tokens
//   - inside brackets, no layout tokens are emitted
//   - EOF pops all remaining indent levels

#include "tree_sitter/parser.h"

#include <stdbool.h>
#include <stdint.h>
#include <string.h>

// Token types — must match the order in grammar.js externals array.
enum TokenType {
    INDENT,
    DEDENT,
    NEWLINE,
    DOC_BLOCK,
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

// Check if a character could start "doc" keyword.
static inline bool is_doc_start(int32_t c) {
    return c == 'd';
}

// ── Doc block scanner ───────────────────────────────────────────

// Scan a doc block: `doc` keyword + optional inline text + indented body.
// Returns true if a DOC_BLOCK token was emitted.
//
// The doc_col parameter is the column where `doc` starts.  Body lines must
// be indented strictly MORE than doc_col to be included.  A line at the same
// indent (or less) ends the doc block — this is how `fn` declarations after
// a doc block inside an effect/trait/struct body are not swallowed.
static bool scan_doc_block(Scanner *s, TSLexer *lexer, uint32_t doc_col) {
    // We're positioned at 'd' — verify "doc" followed by space/newline/EOF.
    // We must not consume characters unless we commit to the token.

    // Check 'd'
    if (lexer->lookahead != 'd') return false;
    lexer->advance(lexer, false);
    // Check 'o'
    if (lexer->lookahead != 'o') return false;
    lexer->advance(lexer, false);
    // Check 'c'
    if (lexer->lookahead != 'c') return false;
    lexer->advance(lexer, false);

    // "doc" must be followed by space, tab, newline, or EOF — not an identifier char.
    int32_t after = lexer->lookahead;
    if (after != ' ' && after != '\t' && after != '\n' && after != '\r' && !lexer->eof(lexer)) {
        // It's an identifier like "document" — not a doc block.
        return false;
    }

    // We have "doc" — now consume the rest.
    lexer->mark_end(lexer);  // Mark end after "doc" as fallback.

    // Inline text: consume rest of line if there's content.
    if (after == ' ' || after == '\t') {
        // Consume space + rest of line.
        while (lexer->lookahead != '\n' && lexer->lookahead != '\r' && !lexer->eof(lexer)) {
            lexer->advance(lexer, false);
        }
        lexer->mark_end(lexer);
    }

    // Now try to consume indented body lines (block form).
    // Body lines must be indented MORE than doc_col.
    // Blank lines within the body are allowed.
    for (;;) {
        // Peek ahead: consume newlines and blank lines, looking for
        // an indented content line.
        if (lexer->lookahead != '\n' && lexer->lookahead != '\r') break;

        // Consume the newline.
        if (lexer->lookahead == '\r') lexer->advance(lexer, false);
        if (lexer->lookahead == '\n') lexer->advance(lexer, false);

        // Skip blank lines (lines with only spaces/tabs).
        bool found_content = false;
        for (;;) {
            // Measure indent on this line.
            uint32_t line_indent = 0;
            while (is_space_or_tab(lexer->lookahead)) {
                line_indent++;
                lexer->advance(lexer, false);
            }

            if (lexer->eof(lexer)) {
                // EOF after whitespace — stop.
                break;
            }

            if (lexer->lookahead == '\n' || lexer->lookahead == '\r') {
                // Blank line — consume and continue looking.
                if (lexer->lookahead == '\r') lexer->advance(lexer, false);
                if (lexer->lookahead == '\n') lexer->advance(lexer, false);
                continue;
            }

            if (line_indent > doc_col) {
                // Indented more than the doc keyword — part of doc body.
                // Consume rest of line.
                while (lexer->lookahead != '\n' && lexer->lookahead != '\r' && !lexer->eof(lexer)) {
                    lexer->advance(lexer, false);
                }
                lexer->mark_end(lexer);
                found_content = true;
                break;
            } else {
                // At same indent or less — end of doc block.
                break;
            }
        }

        if (!found_content) break;
    }

    lexer->result_symbol = DOC_BLOCK;
    return true;
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
    // Don't interfere.
    if (valid_symbols[INDENT] && valid_symbols[DEDENT] &&
        valid_symbols[NEWLINE] && valid_symbols[DOC_BLOCK]) {
        return false;
    }

    // At EOF, only emit DEDENT or NEWLINE — never try DOC_BLOCK.
    // This prevents the scanner from consuming whitespace at EOF when only
    // DOC_BLOCK is valid, which would prevent the parser from reaching
    // the state where DEDENT is valid.
    if (lexer->eof(lexer) &&
        !valid_symbols[INDENT] && !valid_symbols[DEDENT] && !valid_symbols[NEWLINE]) {
        return false;
    }

    // --- Phase 1: Track brackets ---
    // Peek at the current character to update bracket depth.
    // We don't consume anything here — let the main parser handle brackets.
    // But we need to know if we're inside brackets to suppress layout.
    //
    // Actually, bracket tracking in tree-sitter external scanners works
    // differently from the compiler: we can't peek at the next *token*.
    // Instead, we rely on the grammar: inside (), [], {}, the parser
    // won't have INDENT/DEDENT/NEWLINE in valid_symbols because those
    // rules aren't in the bracket-delimited grammar positions.
    //
    // So we don't need explicit bracket tracking — the valid_symbols
    // array already handles it.

    // --- Phase 2: Look for a newline ---
    // Skip spaces/tabs (horizontal whitespace) first.
    // We need to find if we're at a line boundary.

    bool found_newline = false;

    // If the very first character is a newline, we're at a line boundary.
    // Consume all whitespace until we find content, tracking indentation.

    // Consume horizontal whitespace before checking for newline.
    while (lexer->lookahead == ' ' || lexer->lookahead == '\t') {
        lexer->advance(lexer, true);  // skip = true (whitespace)
    }

    // Check for newline.
    if (lexer->lookahead == '\n' || lexer->lookahead == '\r') {
        found_newline = true;

        // Consume the newline and any subsequent blank lines.
        while (lexer->lookahead == '\n' || lexer->lookahead == '\r' ||
               lexer->lookahead == ' ' || lexer->lookahead == '\t') {
            if (lexer->lookahead == '\n' || lexer->lookahead == '\r') {
                lexer->advance(lexer, true);
            } else {
                // Could be indentation of a content line, or trailing
                // whitespace on a blank line.  We need to peek ahead.
                // Consume spaces, then check if next is newline/EOF.
                lexer->advance(lexer, true);
            }
        }
    }

    // --- Phase 3: At EOF, emit remaining layout tokens ---
    if (lexer->eof(lexer)) {
        // Emit DEDENT if valid and we have pending indent levels.
        if (valid_symbols[DEDENT] && s->stack_len > 1) {
            stack_pop(s);
            lexer->result_symbol = DEDENT;
            return true;
        }
        // Emit NEWLINE at EOF to close the last statement.
        // This lets repeat1(seq(decl, optional(newline))) finish its
        // iteration so the parser can then request DEDENT.
        if (found_newline && valid_symbols[NEWLINE]) {
            lexer->result_symbol = NEWLINE;
            return true;
        }
        return false;
    }

    // --- Phase 4: If no newline found, try DOC_BLOCK at start of file ---
    if (!found_newline) {
        // We might be at the very start of the file (column 0).
        // Check for doc block.
        if (valid_symbols[DOC_BLOCK] && is_doc_start(lexer->lookahead)) {
            uint32_t col = lexer->get_column(lexer);
            // Doc blocks only start at column 0 or at the current indent level.
            if (col == stack_top(s)) {
                return scan_doc_block(s, lexer, col);
            }
        }
        return false;
    }

    // --- Phase 5: We crossed a newline.  Measure indent of next line ---
    uint32_t indent = lexer->get_column(lexer);

    // --- Phase 6: Emit layout token based on indent comparison ---
    // INDENT/DEDENT must be emitted BEFORE doc blocks.  A doc block
    // at increased indent is inside a new block — the INDENT must come
    // first so the parser can open the block.
    uint16_t current = stack_top(s);

    if (indent > current) {
        if (valid_symbols[INDENT]) {
            stack_push(s, (uint16_t)indent);
            lexer->result_symbol = INDENT;
            return true;
        }
        // If INDENT not valid but DOC_BLOCK is, try doc block.
        if (valid_symbols[DOC_BLOCK] && is_doc_start(lexer->lookahead)) {
            return scan_doc_block(s, lexer, indent);
        }
        return false;
    }

    if (indent < current) {
        if (valid_symbols[DEDENT]) {
            // Pop levels until we match.
            stack_pop(s);
            // Queue additional dedents if needed.
            while (s->stack_len > 1 && indent < stack_top(s)) {
                stack_pop(s);
                s->queued_dedents++;
            }
            lexer->result_symbol = DEDENT;
            return true;
        }
        return false;
    }

    // indent == current — check for doc block before NEWLINE.
    // Doc blocks at the current indent level document the next
    // declaration at this level.
    if (valid_symbols[DOC_BLOCK] && is_doc_start(lexer->lookahead)) {
        return scan_doc_block(s, lexer, indent);
    }

    if (valid_symbols[NEWLINE]) {
        lexer->result_symbol = NEWLINE;
        return true;
    }

    return false;
}
