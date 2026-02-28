# Brief: Syntax Migration — Rill to KERNEL Kea

**Status:** ready
**Priority:** v1-critical
**Depends on:** 0a-lexer-parser (done)
**Blocks:** stdlib-bootstrap, 0f, 0g (all code written must use KERNEL syntax)

## Motivation

The parser was cannibalized from Rill and still uses several Rill-era syntax
constructs that diverge from the KERNEL specification. This causes agents
writing Kea code to produce incorrect syntax (Rill's `record`, `{ ..base }`,
`#(a, b)`) because the parser/evaluator accepts it. The spec is the source
of truth — the parser must match.

## Migration Items

### 1. `record` → `struct` (KERNEL §2)

**Rill:** `record Foo` / `record Bar { field: Type }`
**Kea:** `struct Foo` with indentation-delimited fields

- Lexer: add `struct` keyword, keep `record` as deprecated/error with
  helpful message ("did you mean `struct`?")
- Parser: `struct_def` replaces `record_def`
- AST: rename `RecordDef` → `StructDef` (or alias)
- All downstream: update pattern matches

### 2. Functional update: `{ ..base, field }` → `base~{ field }` (KERNEL §2.3)

**Rill:** `Name { ..base, field: value }` or `{ ..base, field: value }`
**Kea:** `base~{ field: value }`

- Lexer: add `Tilde` token for `~`
- Parser: parse `expr ~ { field: value, ... }` as functional update
- Remove `DotDot` spread in struct literal context
- AST: `FunctionalUpdate { base: Expr, fields: Vec<(Name, Expr)> }`

### 3. Tuple syntax: `#(a, b)` → `(a, b)` (KERNEL §1.5)

**Rill:** `#(a, b, c)` (Gleam-style hash-paren tuples)
**Kea:** `(a, b, c)` — parentheses are tuples when they contain commas

- Parser: `(expr)` is grouping, `(expr, expr, ...)` is a tuple
- Remove `#(` token/parsing path
- Tuple patterns: `(a, b)` not `#(a, b)`
- Single-element parens `(expr)` remain grouping, NOT a 1-tuple

### 4. Map literals: `%{ key => value }` (KERNEL §1.5.1)

**Status:** Parser already has `%{ key => value }` — this is correct per KERNEL.
No migration needed. Verify it works end-to-end and is tested.

### 5. Anonymous records: `#{ field: value }` (KERNEL §2.5)

**Status:** Parser already has `#{ field: value }` — this is correct per KERNEL.
No migration needed.

### 6. Struct literal syntax alignment

**Rill:** `Name { field: value }` with braces
**Kea (current):** Same — KERNEL §2 shows `Point { x: 1.0, y: 2.0 }`

This is correct. Struct literals use braces. The indentation-sensitive
syntax applies to struct *definitions* (the `struct` block), not to
struct *literal expressions*.

## What NOT to change

- `[a, b, c]` list literals — correct per KERNEL
- `#{ field: value }` anonymous records — correct per KERNEL
- `%{ key => value }` map literals — correct per KERNEL
- `{ f1: p1, f2: p2 }` destructuring patterns — correct per KERNEL
- `Name { field: value }` struct construction — correct per KERNEL

## Implementation Order

1. Add `Tilde` token to lexer, add `struct` keyword
2. Migrate `record` → `struct` in parser + AST
3. Migrate functional update to `~` syntax
4. Migrate tuple syntax from `#()` to `()`
5. Update all `.kea` test files and stdlib
6. Update evaluator/typechecker/codegen for AST changes
7. Run `mise run check-full`

## Testing

- All existing parser snapshot tests updated
- Functional update: `p~{ x: 3.0 }` parses correctly
- Tuple: `(1, 2)` is tuple, `(1)` is grouping, `()` is unit
- Old syntax (`record`, `#()`, `{ ..base }`) produces clear error
  messages pointing to the new syntax
- `mise run check-full` passes

## Definition of Done

- Parser accepts only KERNEL syntax for struct/tuple/update
- Old Rill syntax produces helpful deprecation errors
- All stdlib and test `.kea` files use KERNEL syntax
- No agent can accidentally write Rill syntax and have it accepted
