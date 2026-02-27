# Brief: Incremental Stdlib Bootstrap

**Status:** ready
**Priority:** v1-critical
**Depends on:** 0d1-module-system (needs multi-file compilation)
**Blocks:** Phase 1 (self-hosting requires working stdlib)
**Also read before implementing:**
- [0d1-module-system](0d1-module-system.md) — module loading, prelude, intrinsics
- [KERNEL §1-2](../../docs/spec/KERNEL.md) — primitive types, collection types, structs
- [KERNEL §5](../../docs/spec/KERNEL.md) — effects, Fail, catch, ?
- [KERNEL Appendix C](../../docs/spec/KERNEL.md) — prelude traits
- [COMPILER-AS-DATA](../../docs/COMPILER-AS-DATA.md) — why stdlib in Kea matters for self-hosting

## Motivation

The stdlib is not a late phase. It grows alongside the compiler.
Each phase that adds compilation capabilities delivers the stdlib
code those capabilities unlock. By the time Phase 1 (self-hosting)
starts, the stdlib is 3000+ lines of battle-tested Kea code —
written by the bootstrap compiler, validated against real use.

Writing the stdlib in Kea from day one serves three purposes:

1. **Integration test.** The stdlib is the most thorough test of
   the language. If `List.map` doesn't compile, the type system
   has a bug. If `IO.read_file` doesn't link, the effect system
   has a gap. Every stdlib module is a test of the phase that
   enables it.

2. **No throwaway work.** The `List` you write in Phase 0d is the
   `List` that exists at self-hosting. There's no "builtin List"
   that gets replaced later. The code improves — linked list
   becomes contiguous array in 0f — but it's always Kea code.

3. **Self-hosting velocity.** When Phase 1 starts, the compiler's
   dependencies (collections, IO, error handling, traits) already
   exist. Self-hosting is "rewrite the compiler in Kea" — not
   "rewrite the compiler AND write a stdlib."

## Stdlib Tiers

### Tier 0: Pure (lands with 0d1)

Everything compiled with `->` or `-[Fail]>`. No effects beyond
Fail (which compiles as Result-passing). Core traits defined with
manual impls.

```
stdlib/
  prelude.kea      -- Option, Result, Bool extensions, Unit
  list.kea         -- List (struct wrapping Option (A, List A))
  string.kea       -- String operations via @intrinsic
  int.kea          -- Int: abs, min, max, clamp
  float.kea        -- Float: abs, floor, ceil, round
  order.kea        -- Ordering enum, comparison utilities
  eq.kea           -- Eq trait + manual impls for primitives
  ord.kea          -- Ord trait (manual, no supertrait yet)
  show.kea         -- Show trait + manual impls for primitives
```

**~500-800 lines.** Enough for non-trivial pure programs.

**What this exercises:** Enums, structs, pattern matching, closures,
higher-order functions, recursion, generics, basic trait dispatch,
the module system itself.

**List is a linked list, struct wrapping `Option (A, List A)`.**
No `Cons`/`Nil` — use the existing `Option` type for the empty case.
Empty list is `List None`, cons is `List Some(x, xs)`. UMS hangs
methods on the struct. Pattern matching goes through Option.

```kea
record List A
  head: Option (A, List A)
```

It's O(n) for indexing but sufficient for bootstrap. `List` is the
permanent name for linked list — it does NOT get renamed or replaced.
Tier 2 adds `Vector` as a separate type for array-backed collections.

**String operations use @intrinsic.** `String.length`,
`String.concat`, `String.slice` call Rust-provided runtime
functions. The Kea signatures provide the type; the runtime
provides the implementation.

**Traits have manual impls only.** `@derive` doesn't exist yet
(lands in Tier 3). Every `impl Eq for MyType` is written by hand.
This is acceptable for a small stdlib.

### Tier 1: Effects (lands with 0e)

Effect declarations, handlers, and IO operations. Stdlib modules
that perform effects.

```
stdlib/
  io.kea           -- IO effect: stdout, stderr, read_file, write_file
  state.kea        -- State effect + with_state handler
  log.kea          -- Log effect + stdout/collect handlers
  reader.kea       -- Reader effect + with_reader handler
  test.kea         -- assert (Fail-based), basic test utilities
```

**~300-500 additional lines.**

**IO wraps intrinsics.** `IO.stdout` is a Kea function with
`-[IO]>` in its signature that calls `@intrinsic("__kea_io_stdout")`.
The effect annotation is Kea; the syscall is Rust.

**State/Log/Reader handlers are pure Kea.** `with_state` is a
handler written in Kea that intercepts `State.get`/`State.put`.
This is the first real validation that handler compilation works.

**Test utilities use Fail.** `assert` is `fn assert(cond: Bool)
-[Fail AssertionError]> Unit`. The test runner handles the Fail
effect.

### Tier 2: Performance (lands with 0f)

Data structures that need Ptr, @unsafe, Unique, and fixed-width
integers. These replace the Tier 0 linked-list implementations.

```
stdlib/
  vector.kea       -- Contiguous-memory array (Unique + Ptr)
  map.kea          -- HAMT Map (Ptr-based nodes, @unsafe internals)
  set.kea          -- HAMT Set
  bytes.kea        -- Bytes (Ptr UInt8 + length)
  buffer.kea       -- Mutable buffer (Unique Buffer)
```

**~800-1200 additional lines.**

**Vector is a separate type, not a List replacement.** `List`
remains the linked list permanently — it's the correct name for
a linked list, and Kea is a functional language where linked lists
are idiomatic for recursive processing. `Vector` is the array-backed
collection for when you need O(1) indexing and cache-friendly
iteration. Backed by contiguous memory via `Ptr` and `@unsafe`.
`Unique` ensures single-ownership for in-place mutations. Users
choose explicitly: `List` for recursive/cons patterns, `Vector`
for performance-sensitive sequential access.

**HAMT Map/Set.** Hash Array Mapped Tries per KERNEL §1.2.
Internal nodes use `Ptr` and `@unsafe` for the trie structure.
External API is pure. This is the production Map.

**Writing these IS the test for 0f.** If HAMT can't be written
with Ptr + @unsafe, the memory model has a gap.

### Tier 3: Abstractions (lands with 0g)

Trait hierarchies, @derive, and the abstractions that make the
stdlib ergonomic. Also absorbs what was previously 0h Checkpoint 1.

```
stdlib/
  foldable.kea     -- Foldable trait + associated Item type
  iterator.kea     -- Iterator trait + lazy iteration
  derive/show.kea  -- @derive(Show) recipe
  derive/eq.kea    -- @derive(Eq) recipe
  derive/ord.kea   -- @derive(Ord) recipe
  codec.kea        -- Encode/Decode traits
  json.kea         -- JSON via Encode/Decode
  sorted_map.kea   -- SortedMap (Ord supertrait constraint)
  sorted_set.kea   -- SortedSet
  format.kea       -- String formatting, pretty-printing
```

**~800-1000 additional lines.**

**@derive lands here.** Moved from 0h. Tightly coupled to the
trait system and associated types from 0g. @derive(Show, Eq, Ord)
for structs and enums.

**Supertraits enable Ord : Eq.** The Tier 0 Ord trait was
standalone. Now it properly requires Eq.

**This tier completes the self-hosting stdlib.** After Tier 3,
the compiler has: collections (Map, Vector, Set), IO (file
read/write, stdout), error handling (Fail, catch, Result),
traits (Show, Eq, Ord, Foldable, Iterator), serialization
(JSON via Encode/Decode), and formatting. Enough to write a
compiler.

## Intrinsics

Stdlib functions that bottom out in runtime operations use
`@intrinsic`:

```kea
struct String
  @intrinsic("__kea_string_length")
  fn length(self: String) -> Int

  @intrinsic("__kea_string_concat")
  fn concat(self: String, other: String) -> String
```

Codegen recognizes `@intrinsic` and emits a call to the named
runtime function instead of compiling a Kea body. The runtime
functions are Rust code linked into the JIT/AOT module.

**Intrinsic sets by tier:**

| Tier | Intrinsics |
|------|-----------|
| 0 | String ops, alloc/free, print (debug) |
| 1 | IO syscalls (read/write/stdout/stderr), clock |
| 2 | Ptr ops (read/write/alloc/free/offset) |
| 3 | None (pure Kea, builds on Tier 0-2 intrinsics) |

## Stdlib-as-test principle

Every tier is a test of the phase that enables it:

| Tier | Tests |
|------|-------|
| 0 | Enums, pattern matching, closures, recursion, generics, trait dispatch, module system |
| 1 | Effect declarations, handler compilation, evidence passing, IO runtime |
| 2 | Unique T, move checking, Ptr/@unsafe, refcounting, reuse analysis |
| 3 | GADTs, associated types, supertraits, @derive recipes |

If the stdlib compiles and its tests pass, the phase works.

## Definition of Done (per tier)

**Tier 0:** Option, Result, List, String, Int, Float, Eq, Ord,
Show exist as `.kea` files. A user program can `use List` and
call `List.map`. At least 20 tests exercising stdlib functions.

**Tier 1:** IO, State, Log, Reader exist with working handlers.
A program can read a file, process it with State, and write
output. At least 10 handler tests.

**Tier 2:** Vector and HAMT Map replace linked-list for production
use. Benchmark comparison: HAMT Map within 5x of Rust HashMap for
10K-entry lookup.

**Tier 3:** @derive(Show, Eq, Ord) works on structs and enums.
Foldable/Iterator enable `list.fold(0, |a, b| -> a + b)`. JSON
round-trips through Encode/Decode. Stdlib is sufficient for
compiler self-hosting.

## Open Questions

- Should Tier 0 List be `type List A = Cons(A, List A) | Nil`
  (classic algebraic) or a struct wrapping a recursive enum?
  Struct gives a namespace for methods via UMS. (Proposal: struct
  wrapping the enum, methods on the struct.)
- When Tier 2 Vector lands, does it replace the `List` name or
  coexist as `Vector`? (Proposal: coexist. `List` stays as the
  linked list, `Vector` is the array. Users choose based on
  access pattern. The prelude exports both.)
- Should the stdlib directory structure be flat (`stdlib/list.kea`)
  or nested (`stdlib/collections/list.kea`)? (Proposal: flat for
  Tier 0-1, introduce nesting in Tier 2-3 as the stdlib grows.)
