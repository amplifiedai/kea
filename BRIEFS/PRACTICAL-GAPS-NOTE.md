# Agent Note: Practical Language Gaps

Read `BRIEFS/in-progress/practical-language-gaps.md` for the full brief.
This note tells you what to do and in what order.

## Priority

**Gaps 7 and 8 block 0g. Fix them first.**

## Gap 7: Mutual Recursion (BLOCKER)

Records and sum types are registered in separate sequential passes in
`crates/kea/src/compiler.rs` (lines ~1230-1270). Record field types
are validated *during* registration, before sum types exist. Any
struct referencing a sum type (or a struct defined later) fails:

```
struct Wrapper
  inner: HirExpr    -- ERROR: unknown type `HirExpr`

type HirExpr = | Lit(Int) | Wrapped(Wrapper)
```

**Fix:** Two-pass approach:
1. First pass: collect all type *names* (records + sum types +
   aliases) without validating field types. Just register that
   `Wrapper` and `HirExpr` exist.
2. Second pass: validate all field types, resolve references,
   check for cycles.

This is the standard Haskell/OCaml approach. The function-level
code already does this (functions are registered before bodies are
checked). Apply the same pattern to type definitions.

**Test:** Write a .kea file with mutually recursive struct/enum:
```kea
struct MatchArm
  body: HirExpr
  tag: Int

type HirExpr = | Lit(Int) | Match(HirExpr, MatchArm)

fn depth(e: HirExpr) -> Int
  case e
    Lit(_) -> 0
    Match(inner, _) -> 1 + depth(inner)

fn main() -> Int
  let arm = MatchArm { body: Lit(1), tag: 0 }
  depth(Match(Lit(5), arm))
```
Verify: `kea run` returns 1. Both JIT and AOT paths.

## Gap 8: `enum` Keyword (BLOCKER)

The parser uses Rill's `type Name = | A | B(Int)` syntax. The KERNEL
specifies `enum Name` with indented variants. Change the parser.

**Specifically:**
1. Add `Enum` to `TokenKind` in the lexer (`crates/kea-syntax/src/lexer.rs`).
   Add `"enum"` to keyword recognition.
2. In the parser, add an `enum_def` method that:
   - Consumes `enum` keyword (already consumed at call site)
   - Parses name + optional type parameters
   - Parses indented block of variants (one per line)
   - Each variant: `Name` or `Name(fields)` or `Name(fields) : ReturnType`
   - Optional `|` prefix per variant (allowed but not required)
3. The `enum_def` produces the same `TypeDef` AST node as the current
   `type_def` method — no downstream changes needed.
4. **Remove** the `type = |` sum type syntax entirely. `type` stays
   for aliases only (`type Handler = Request -> Response`).
   Do NOT keep it as a deprecated alias.
5. Update all test strings and `.kea` files that use `type = |`.
6. Update snapshot tests.

**Syntax:**
```kea
enum Option A
  Some(A)
  None

enum Ordering
  Less
  Equal
  Greater

enum Expr T
  IntLit(Int)                        : Expr Int
  BoolLit(Bool)                      : Expr Bool
  If(Expr Bool, Expr T, Expr T)      : Expr T
```

**Test:** Parse an enum, construct values, pattern match. Verify
both simple enums and parameterised enums work. GADT return type
annotations parse correctly.

## After Gaps 7+8

The remaining gaps are important but not blocking other phases:

- **Gap 1 (layout intrinsics):** Implement `size_of`/`align_of` as
  compiler intrinsics. Needed for Vector/HAMT in 0f.
- **Gap 3 (string ops):** Add intrinsic-backed string operations
  (slice, starts_with, contains, split, trim, index_of, to_int).
  Only 3 of 25 needed ops exist. Self-hosting blocker.
- **Gap 2 (numeric inference):** Bidirectional propagation of expected
  type to integer literals. Ergonomic, not blocking.
- **Gap 5 (tuple-case):** MIR optimization pass. Low priority.
- **Gap 4 (early exit):** No action — by design.

## Validation

After gaps 7 and 8:
```
mise run check-full
PKG=kea-syntax mise run test-pkg
PKG=kea mise run test-pkg
```

Mutual recursion test passes with `kea run`. Enum syntax parses
and produces correct `TypeDef` AST nodes. All existing tests pass
(existing `type = |` tests will need updating to `enum` syntax).
