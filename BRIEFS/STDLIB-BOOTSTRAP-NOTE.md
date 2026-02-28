# Agent Note: Stdlib Bootstrap Next Steps

Read `BRIEFS/in-progress/stdlib-bootstrap.md` for the full brief.
This note tells you what to do and in what order.

## Priority

**Fix the three Tier 0 blockers first, then expand Tier 1.**

## Blocker 1: Generic List (HIGHEST PRIORITY)

`List` is currently monomorphic. Attempting `type List a = Nil | Cons(a, List a)`
fails because the typechecker treats parametric `List a` as the Rill-era
builtin list shape (`[]`, `[_, .._]`), making `Nil`/`Cons` arms unreachable
and emitting non-exhaustive errors.

**Root cause:** Rill had a built-in list type with special syntax. That
special-casing is still in the typechecker/exhaustiveness checker. Kea's
`List` is a user-defined enum — the builtin list handling must be removed.

**Fix:** Find and remove the Rill-era builtin list special-casing in
`crates/kea-infer/src/typeck.rs` (and possibly exhaustiveness checking).
`List` should be treated as any other user-defined enum with type
parameters. Search for `[]`, `[_`, list-related pattern matching
special cases, and any `Type::List` or `Type::Cons` variants.

**Test:** After fixing, this should work:
```kea
enum List A
  Nil
  Cons(A, List A)

fn length(xs: List Int) -> Int
  case xs
    Nil -> 0
    Cons(_, rest) -> 1 + length(rest)

fn main() -> Int
  length(Cons(1, Cons(2, Cons(3, Nil))))
```
Verify: `kea run` returns 3.

## Blocker 2: Trait Method Return Types

`Ord.compare` can't return `Ordering` because trait method registration
fails with "unknown return type" when the return type references an
imported module type.

**Root cause:** Trait method type validation happens before module types
are fully resolved. The trait registration pass doesn't see types from
other stdlib modules.

**Fix:** In `crates/kea/src/compiler.rs`, ensure trait method return
types are resolved against the full type environment (including imported
module types), not just the local scope. This is likely the same kind
of ordering issue that Gap 7 (mutual recursion) fixed for struct/enum
— trait methods need to see all registered types.

**Test:**
```kea
enum Ordering
  Less
  Equal
  Greater

trait Ord A
  fn compare(a: A, b: A) -> Ordering

fn main() -> Int
  0
```
Verify: compiles without error.

## Blocker 3: Prelude Re-export Collisions

Prelude re-exports fail with `DuplicateDefinition("map")` because
`Option.map`, `Result.map`, and `List.map` all export `map` and the
import flattening treats them as collisions.

**Root cause:** The module resolver flattens all exports from re-exported
modules into the same namespace. When multiple modules export the same
function name, it collides.

**Fix:** Module-qualified re-exports should not collide. `Option.map`
and `List.map` are different functions in different namespaces. The
prelude should re-export the *modules* (so `Option`, `Result`, `List`
are in scope), not flatten their contents. Users write `List.map(xs, f)`,
not bare `map(xs, f)`.

Alternatively, if the prelude re-exports specific symbols, it should
use qualified names and only re-export the *types* and *constructors*
(Some, None, Ok, Err, Cons, Nil) — not the methods. Methods are
accessed via UMS (`xs.map(f)`) or module-qualified (`List.map(xs, f)`).

**Test:** A program with `use Prelude` (or implicit prelude) that uses
`Option.map`, `Result.map`, and `List.map` without explicit `use`
statements for each module should compile.

## After Blockers: Tier 1 Expansion

The effect runtime (0e) is done. These stdlib modules should exist
as `.kea` files with Kea-written handlers:

### `stdlib/state.kea`
```kea
effect State S
  fn get() -> S
  fn put(s: S) -> Unit

fn with_state(init: S, @with f: () -[State S, e]> T) -[e]> (T, S)
  -- handle State.get/put using Unique cell
```
The handler implementation already works in the runtime. Wrap it as
a Kea module. Note: `@with` annotation isn't implemented yet — just
write the function with a callback last param for now. `@with` is
tracked in `BRIEFS/todo/with-syntax.md`.

### `stdlib/log.kea`
```kea
effect Log
  fn debug(msg: String) -> Unit
  fn info(msg: String) -> Unit
  fn warn(msg: String) -> Unit
  fn error(msg: String) -> Unit

fn with_stdout_logger(@with f: () -[Log, e]> T) -[IO, e]> T
  -- handle Log.* by printing to stdout

fn with_collected_logs(@with f: () -[Log, e]> T) -[e]> (T, List String)
  -- handle Log.* by collecting into a list (for tests)
```

### `stdlib/reader.kea`
```kea
effect Reader R
  fn ask() -> R

fn with_reader(env: R, @with f: () -[Reader R, e]> T) -[e]> T
  -- handle Reader.ask by returning env
```

### Test each module
For each new stdlib module, add an execute-path regression test in
`crates/kea/src/main_tests.rs` following the existing pattern:
`compile_and_execute_real_stdlib_{module}_exit_code`.

## Validation

After each slice:
```
mise run check
PKG=kea mise run test-pkg
```

After all blockers + Tier 1:
```
mise run check-full
```

## What NOT to do

- Don't attempt Tier 2 (Vector, Map, Set) — blocked on 0f Ptr/@unsafe.
- Don't attempt Tier 3 (@derive, Foldable, Iterator) — blocked on 0g.
- Don't ship placeholder implementations that return wrong values.
  If something can't be implemented correctly, leave it out and
  document why.
- Don't fight the prelude collision by renaming functions. Fix the
  module resolver instead.
