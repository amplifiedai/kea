# Brief: Practical Language Gaps for Self-Hosting

**Status:** ready
**Priority:** v1-critical
**Depends on:** 0f (memory model), 0g (advanced types)
**Blocks:** Phase 1 (self-hosting)

## Motivation

Kea aims to be the first *practical* algebraic effect language — competing
with Rust, Go, OCaml, and Nim, not just with research languages. The
KERNEL spec and current implementation plan are sound for the type system
and effect system. This brief identifies gaps in the *low-level
ergonomics* that would create a false ceiling when writing real programs:
a compiler, a web server, a database, or a game engine.

These gaps don't require fundamental design changes. They're missing
library functions, type inference features, and ergonomic patterns that
fall out of what's already specified. Most are small. All are necessary
for self-hosting.

## Gap 1: Layout Intrinsics (`size_of`, `align_of`)

**Status:** Spec'd in KERNEL §17.4 (added 2026-02-28)

You can't write a generic `Vector(T)` or arena allocator without knowing
the size and alignment of `T`. These are compile-time constants — safe
to expose, trivial to implement via Cranelift's `type_size` / `type_align`.

```kea
fn size_of() -> Int     -- size in bytes of type T
fn align_of() -> Int    -- alignment in bytes of type T
```

**Implementation:** Add as compiler intrinsics in 0f alongside Ptr ops.
Monomorphization resolves `T` before codegen, so the size is always
known. Emit as Cranelift `iconst` with the resolved size.

**Landing:** 0f (needed for Vector, HAMT)

## Gap 2: Bidirectional Numeric Literal Inference

**Status:** Spec'd in KERNEL §1.1.1 (added 2026-02-28)

Currently all integer literals are `Int`. Writing `let x: Int32 = 42`
should infer `42` as `Int32` without requiring `Int32.from(42)`.

```kea
let x: Int32 = 42          -- 42 infers as Int32
let y = [1u8, 2u8, 3u8]    -- suffix syntax NOT needed if context available
write(fd, buf, 1024)        -- 1024 infers as UInt64 from parameter type
```

**Implementation:** During type checking, when an integer literal has
an expected type that is a fixed-width integer, check that the literal
value fits and assign the expected type. Already how bidirectional
checking works for other constructs.

**Landing:** 0f Step 6 (already doing numeric infrastructure)

## Gap 3: String/Bytes Core Operations

**Status:** Partially implemented (String.length, String.concat via intrinsic)

For self-hosting, the compiler needs to manipulate source text efficiently.
Minimum viable String/Bytes surface:

```
String:
  .length() -> Int
  .concat(other) -> String           -- already intrinsic
  .slice(from, to) -> String         -- byte-indexed, panics on non-UTF8 boundary
  .chars() -> List Char              -- until Iterator lands
  .bytes() -> Bytes
  .starts_with(prefix) -> Bool
  .ends_with(suffix) -> Bool
  .contains(needle) -> Bool
  .index_of(needle) -> Option Int
  .split(sep) -> List String
  .trim() -> String
  .to_int() -> Result(Int, String)   -- parse integer
  .to_float() -> Result(Float, String)

Bytes:
  .length() -> Int
  .get(index) -> UInt8               -- panics on out-of-bounds
  .slice(from, to) -> Bytes
  .as_ptr() -> Ptr UInt8             -- @unsafe for FFI boundary
  .from_string(s) -> Bytes
  .to_string() -> Result(String, String)  -- UTF-8 validation
```

All of these are intrinsic-backed (Rust runtime functions). The Kea
signatures provide the types; the runtime provides the implementation.

**Landing:** Tier 0 (String basics) + Tier 2 (Bytes, as_ptr)

## Gap 4: Early Exit / Break Ergonomics

**Status:** Design question — no spec change needed yet

The pure-functional model means no `break`, `continue`, or `return`.
Early exit from loops uses `Fail`:

```kea
-- "find first match" via Fail
let found = catch
  for item in items
    if item.matches(query)
      fail item
  fail NotFound
```

This works but reads wrong — `fail` connotes error, not success. Two
possible improvements (not mutually exclusive):

**Option A: `Break` effect (stdlib, no language change)**
```kea
effect Break T
  fn break(value: T) -> Never

fn find_first(items: List A, pred: fn(A) -> Bool) -[Fail NotFound]> A
  let result = catch
    for item in items
      if pred(item)
        Break.break(item)
    fail NotFound
  result
```

This is really just `Fail` with a different name. The question is
whether the ergonomic win of `Break.break(x)` over `fail x` justifies
a separate effect. Probably not — `Fail` is the mechanism, naming is
the user's choice via type aliases.

**Option B: Just use `.find()` / `.fold()` / explicit recursion**

```kea
let found = items.find(|item| -> item.matches(query))
```

Most "early exit" patterns are already covered by iterator methods.
The cases that aren't are handled by `Fail`. The unfamiliar feeling
of `fail` for non-error early exit is a one-time learning curve, not
a real expressiveness gap.

**Recommendation:** Don't add `break`/`continue`/`return`. Lean into
`.find()`, `.fold()`, and `Fail`. If stdlib code reveals real pain
points, revisit — but the hypothesis is that iterator methods cover
95% of cases and `Fail` covers the rest.

**Landing:** Revisit during Tier 3 stdlib writing. No action now.

## Gap 5: Tuple-Case Optimization

**Status:** Implementation detail, no spec change

`case (a, b)` constructs a tuple on the heap, then immediately
destructures it. The compiler should recognize this pattern and
destructure on the stack with no allocation.

```kea
case (direction, speed)
  (North, Fast) -> ...
  (South, _) -> ...
```

**Implementation:** MIR pass that detects `case` on a tuple literal
and eliminates the allocation, lowering to cascaded branches.

**Landing:** 0g (optimization pass, not urgent)

## Gap 6: IO Decomposition in Runtime

**Status:** Spec'd in KERNEL §5.2 (updated 2026-02-28)

KERNEL now specifies `IO`, `Clock`, `Net`, `Rand` as separate
capability effects. The runtime needs to provide separate handler
registration for each. Already implemented in 0e for IO; Clock/Net/Rand
need the same treatment.

**Landing:** Already in progress (0e done for IO, stdlib-bootstrap
covers the rest)

## Non-Gaps (Things That Look Like Problems But Aren't)

**Mutable local variables:** No `let mut`. Use `.fold()` for
accumulators, `State` effect for complex stateful loops, `Unique`
for in-place mutation of large structures. The verbosity tax of
`.fold()` over `let mut i = 0; i += 1` is real but acceptable —
OCaml and Haskell prove this works at scale. Adding `let mut` would
complicate the memory model and break the "all values are immutable"
guarantee that enables reuse analysis.

**No HKTs:** Effects replace monadic composition. Collection traits
work on concrete types. The `fn map(c: F Int) where F: Functor`
pattern doesn't exist, but the Elixir-style `impl Foldable for List`
pattern covers real use cases. If self-hosting reveals genuine pain
from missing HKTs, it can be added later — but the prediction is that
effects remove 90% of the motivation.

**No inline assembly / SIMD:** Not needed for self-hosting. If Kea
eventually targets game engines or numerical computing, SIMD can land
via `@extern` FFI or a future `@simd` annotation. Not a v1 concern.

## Definition of Done

- [ ] `size_of` / `align_of` intrinsics implemented and used by Vector
- [ ] Bidirectional numeric literal inference passes type checker tests
- [ ] String/Bytes operations sufficient for source text manipulation
- [ ] `IO`/`Clock`/`Net`/`Rand` all have separate runtime handlers
- [ ] Self-hosting compiler can read source, tokenize, parse, infer,
      and emit code — exercising all of the above
