# Brief: Type as Trait Syntax Migration

**Status:** done
**Priority:** v1
**Depends on:** 0a-parser
**Blocks:** none

## What

Change trait implementation syntax from Rill's `impl Trait for Type` to
Kea's `Type as Trait` (KERNEL §6.2).

## Why

The KERNEL spec says `Type as Trait`. The parser currently uses Rill's
`impl Trait for Type`. Kea's syntax is better:

- Subject-first: "Int as Eq" — the type is the subject, the trait is
  the role. Matches how you think about it.
- Consistent with Kea's left-to-right style (case, handle — concrete
  first, abstraction second).
- No `impl` keyword needed — `as` is the only keyword.
- Parameterised traits read naturally: `ConfigError as From FileError`.

## KERNEL Syntax Reference

```kea
-- Simple impl
Point as Show
  fn show(_ self: Point) -> String
    "({self.x}, {self.y})"

-- Conditional impl
Tree A as Show where A: Show
  fn show(_ self: Tree A) -> String
    case self
      Leaf(v) -> "Leaf({v.show()})"
      Branch(l, r) -> "Branch({l.show()}, {r.show()})"

-- Parameterised trait
ConfigError as From FileError
  fn from(_ value: FileError) -> ConfigError
    ConfigError.IoError(value)
```

`Self` is always the type on the left of `as`.

## Changes

### 1. Parser (`crates/kea-syntax/src/parser.rs`)

The `impl_block` method (line 1172) currently:
1. Consumes `impl` keyword (already consumed before entering)
2. Expects `UpperIdent` (trait name)
3. Expects `for` keyword
4. Expects `UpperIdent` (type name)
5. Parses optional type params and where clause
6. Parses method body

Change to `Type as Trait` parsing. Two entry points:

**(a) From top-level declaration parsing:** When the parser sees an
`UpperIdent` at declaration level, it currently handles struct/enum/
effect/trait. Add: if the next token after `UpperIdent` is `as` (or
the next token after optional type params is `as`), parse as a trait
impl block.

```
-- Simple: starts with UpperIdent, next is `as`
Int as Eq
  ...

-- Parameterised type: starts with UpperIdent, then type args, then `as`
Tree A as Show where A: Show
  ...

-- Parameterised trait: UpperIdent `as` UpperIdent UpperIdent
ConfigError as From FileError
  ...
```

**(b) The `impl` keyword:** Either remove `impl` from the keyword list
entirely, or keep it as a deprecated alias that emits a warning pointing
to `Type as Trait` syntax. Removing is cleaner.

The parsing logic becomes:
1. Parse type name (already have it as the leading `UpperIdent`)
2. Parse optional type parameters: `Tree A` or `List(a)`
3. Expect `as` keyword
4. Parse trait name
5. Parse optional trait type parameters: `From FileError`
6. Parse optional `where` clause
7. Parse indented method block

### 2. AST (`crates/kea-ast/src/lib.rs`)

The `ImplBlock` struct (line 874) stays mostly the same. Consider
swapping field order to put `type_name` before `trait_name` to match
source order, but this is cosmetic.

No functional AST changes needed — the struct already has both fields.

### 3. Compiler desugaring (`crates/kea/src/compiler.rs`)

The impl block desugaring (line 1079) works on AST `ImplBlock` nodes
and doesn't care about surface syntax. No changes needed here.

### 4. Type checker (`crates/kea-infer/src/typeck.rs`)

`register_trait_impl` (line 3110) works on `ImplBlock` AST — no
syntax dependency. No changes needed.

### 5. Tests

Update all test strings that use `impl Trait for Type`:
- `crates/kea/src/main.rs:2837` — `impl Inc for Int` → `Int as Inc`
- `crates/kea/src/main.rs:2851` — two `impl Inc for` → `Int as Inc`, `Float as Inc`
- `crates/kea/src/main.rs:659` — `impl Tinc for Int` → `Int as Tinc`
- Search for all `"impl "` in test strings across the codebase

### 6. Stdlib

Update all `.kea` files in `stdlib/` that should use impl blocks.
Currently they use bare functions (a separate bug — they should be
using impl blocks regardless of syntax).

Fix both: use `Type as Trait` syntax with proper impl blocks.

```kea
-- stdlib/eq.kea: BEFORE (wrong — bare functions)
fn eq(x: Int, y: Int) -> Bool
  x == y

-- stdlib/eq.kea: AFTER
Int as Eq
  fn eq(x: Int, y: Int) -> Bool
    x == y

String as Eq
  fn eq(x: String, y: String) -> Bool
    x == y

Bool as Eq
  fn eq(x: Bool, y: Bool) -> Bool
    x == y
```

Same pattern for `show.kea`, `ord.kea`, and any other trait impls.

### 7. Error messages

Update error messages that reference the old syntax:
- `parser.rs:1179` — `"expected 'for' in impl header"` → remove
- Any diagnostic that mentions `impl Trait for Type`

### 8. Documentation

- `docs/spec/KERNEL.md` — already uses `Type as Trait` ✓
- Any other docs referencing `impl` syntax

## Validation

```bash
mise run check-full
mise run test
```

All existing trait impl tests must pass with new syntax. The orphan
rule, coherence checking, UMS dispatch — all work on AST `ImplBlock`
nodes, so they're syntax-agnostic.

## Progress
- 2026-02-28 15:22: Canonical `Type as Trait` parser path landed, legacy `impl Trait for Type` retained as compatibility alias, and parser tests updated.
- 2026-02-28 15:32: Snapshot corpus and CLI fixture strings migrated to canonical syntax; `PKG=kea-syntax mise run test-pkg`, `PKG=kea mise run test-pkg`, and `mise run check` all passed.
- 2026-02-28 15:48: Finalized brief/note status and cleaned Kea-facing docs/brief references to prefer `Type as Trait`.

## What NOT to do

- Don't change the AST `ImplBlock` struct name or shape — it's fine.
- Don't change trait resolution, coherence, or orphan rule logic.
- Don't add runtime dispatch — that's a 0g concern.
- Don't try to parse `impl` as a general keyword for anything else.
  Just remove it or alias it with a deprecation warning.
