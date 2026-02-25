# Brief: Lexer and Indentation-Sensitive Parser

**Status:** active
**Priority:** v1-critical
**Depends on:** bootstrap-infra
**Blocks:** 0b-type-system-core, 0c-effect-handlers, everything downstream

## Motivation

Kea uses indentation-sensitive syntax (KERNEL §2, §10). Rill uses
braces. The parser architecture (recursive descent + Pratt for
expressions) transfers from rill-syntax, but block handling needs
a full rewrite for INDENT/DEDENT token emission. The lexer needs
rewriting for Kea's keywords and tokens.

This is the first crate with real code. Everything depends on it.

## What transfers from Rill

**rill-syntax** (11,901 LOC):
- `lexer.rs` (1,587 LOC): Hand-written lexer with trivia tracking.
  The tokenization architecture transfers. Keywords, operators, and
  block delimiters are rewritten. Trivia handling (whitespace tracking
  for comments) is useful but must be extended for significant
  whitespace.
- `parser.rs` (9,686 LOC): Recursive descent + Pratt precedence.
  The Pratt expression parser for operators transfers largely intact.
  Statement/declaration parsing is rewritten — no braces, blocks
  delimited by indentation. The function/struct/enum parsing logic
  informs structure but can't be copied verbatim.
- `token.rs` (202 LOC): Token kind definitions. Rewritten for Kea's
  keyword set (KERNEL Appendix A: 30 reserved words) and operator set
  (KERNEL Appendix B).
- `chunks.rs` (412 LOC): Source splitter for script files. May not
  be needed for Kea (one file = one module).

**rill-ast** (1,766 LOC):
- Span type and visitor patterns transfer directly.
- AST node types rewritten for Kea syntax: struct blocks with
  inherent methods, effect declarations, handler expressions,
  `resume`, labeled/positional params, `$` receiver placement,
  `::` qualified dispatch.

## What's new (not in Rill)

1. **Indentation lexer.** INDENT/DEDENT token emission using a
   level stack. Reference implementations: Python's `tokenize.py`,
   Haskell's layout rule, Lean 4's whitespace-sensitive parsing.

   The approach: lexer emits INDENT, DEDENT, and NEWLINE tokens
   by tracking an indentation stack. When a line's indentation
   exceeds the current level, emit INDENT. When it decreases,
   emit one or more DEDENT tokens to match.

   Key decisions:
   - Tabs vs spaces: **spaces only** (tabs are a compile error).
     Mixing is too error-prone.
   - Indent width: **2 spaces, globally mandated.** The KERNEL
     examples all use 2. Mandating a single width eliminates an
     entire class of confusing edge cases (Python allows "any
     consistent width" and it's a constant source of pain).
   - Continuation lines: `.method()` on a new line at deeper
     indent is a continuation, not a new statement. The parser
     handles this (if the line starts with `.`, it's a method
     chain continuation).

2. **Kea-specific syntax nodes:**
   - `effect` declarations (KERNEL §5.2)
   - `handle` / `resume` expressions (KERNEL §5.6, §5.7)
   - `catch` sugar (KERNEL §5.8)
   - `fail` sugar (KERNEL §5.8)
   - Labeled parameters: `fn f(_ x: Int, label: String)` (KERNEL §10.2)
   - `$` receiver placement in method args (KERNEL §9.3)
   - `::` qualified dispatch (KERNEL §9.2)
   - `~` functional update (KERNEL §2.3)
   - `#{ }` anonymous record literals (KERNEL §2.5)
   - `borrow` parameter convention (KERNEL §10.2.1)
   - `@annotation` syntax (KERNEL §14)
   - `--|` doc comments (KERNEL §1.7)
   - `Type as Trait` blocks (KERNEL §6.2)
   - Nested struct/enum/type definitions (KERNEL §2.9)
   - `where` clauses (KERNEL §6.3, §7.6, §8.3)
   - GADT constructor return types (KERNEL §3.3)

3. **Multi-line handling:**
   - Method chains: `expr\n  .method()` — the leading `.` signals
     continuation.
   - Function arguments: open paren allows continuation until close.
   - List/record literals: `[` and `#{` allow continuation.
   - `if`/`match`/`for`/`handle` bodies: indented blocks.

## Implementation Plan

### Step 1: kea-ast crate

Create `crates/kea-ast/` with:
- `Span` type (from rill-ast)
- AST node definitions for all Kea syntax forms
- Visitor trait (from rill-ast pattern)

Don't try to be exhaustive on the first pass. Start with what the
parser needs for basic programs: literals, let bindings, function
calls, struct definitions, basic pattern matching. Effect and
handler nodes can be stubs that we flesh out in 0c.

### Step 2: kea-syntax crate — lexer

Create `crates/kea-syntax/` with:
- Token definitions (Kea keywords, operators, INDENT/DEDENT/NEWLINE)
- Indentation-sensitive lexer
- Trivia handling (comments, whitespace before tokens)

Test strategy: snapshot tests (insta) of token streams for
representative Kea source. Key cases:
- Basic indentation (struct with fields and methods)
- Nested indentation (nested structs, match arms)
- Continuation lines (method chains, multi-line args)
- Dedent across multiple levels
- Error recovery: inconsistent indentation, tabs

### Step 3: kea-syntax crate — parser

Extend `crates/kea-syntax/` with:
- Recursive descent parser for declarations and statements
- Pratt precedence parser for expressions (from rill-syntax)
- Struct-everything: struct blocks, inherent methods, nested types
- Pattern matching (KERNEL §4.2)
- Labeled/positional arguments
- Type annotation parsing (including effect arrows `-[e]>`)

Test strategy: snapshot tests of AST output. One test per syntax
form from the KERNEL. Error recovery tests: what happens with
missing indentation, unexpected dedent, etc.

### Step 4: kea-diag crate

Create `crates/kea-diag/` with:
- Copy rill-diag (341 LOC) nearly verbatim
- Rename rill → kea
- Keep diagnostic categories, severity levels, source location
- This is the simplest crate — get it done first as a warm-up

(Step 4 is listed last but can be done first since it's trivial
and other crates depend on it.)

## Testing

- Lexer: snapshot tests of token streams for ~20 representative
  Kea source fragments. Cover every token in Appendix B.
- Parser: snapshot tests of AST for ~30 representative programs.
  Cover every syntax form in the KERNEL.
- Error recovery: snapshot tests of diagnostics for ~10 malformed
  inputs. Error messages are a feature (KERNEL ethos).
- Property tests: randomly generated indentation patterns should
  either lex correctly or produce a coherent error.

## Definition of Done

- `cargo test -p kea-ast -p kea-syntax -p kea-diag` passes
- Can parse the Kea source fragments in the KERNEL spec
- Indentation handling works for the patterns in KERNEL §2, §10
- Error messages for parse failures include source location and
  are human-readable
- `mise run check` passes (clippy clean)

## Open Questions

- Should we support significant whitespace in the REPL differently
  from files? (Probably yes — see REPL.md §15 on indentation
  handling. But we can defer REPL-specific parsing.)
- How do we handle blank lines inside indented blocks? (Proposal:
  blank lines don't change indentation state. A blank line followed
  by a line at the original indent level emits DEDENT.)

## Progress
- 2026-02-25: Bootstrapped `kea-ast`, `kea-diag`, and `kea-syntax` from Rill; added `lex_layout` with INDENT/DEDENT emission, `--|` doc comments, and layout lexer tests. (commit `6456af5`)
- **Next:** Parser layout migration for declaration/expr blocks (accept `INDENT/DEDENT` alongside `{ ... }`).
