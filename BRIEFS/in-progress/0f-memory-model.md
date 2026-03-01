# Brief: Memory Model

**Status:** active
**Priority:** v1-critical
**Depends on:** 0d-codegen-pure (steps 1-6), 0e-runtime-effects (step 7 only: Unique + effects)
**Blocks:** Phase 1
**Also read before implementing:**
- [performance-backend-strategy](../design/performance-backend-strategy.md) — Reuse analysis is a MIR pass. Layout stability (declaration order = memory order) governs @unboxed. ABI manifest must include Unique/borrow metadata.
- [testing](testing.md) — Allocation counters for reuse analysis verification. Benchmark harness gates.
- [effects-platform-vision](../design/effects-platform-vision.md) — Unique + Alloc effect = zero-overhead arena path. Unique + Send = safe actor message passing.

## Motivation

Kea's memory model (KERNEL §12) combines reference counting with
copy-on-write, Unique types for guaranteed single ownership, and
arena allocation via effects. This is what lets Kea be a high-level
language with predictable performance: no GC pauses, deterministic
deallocation, and opt-in zero-overhead paths for hot code.

0d gives us basic refcounting and CoW. This brief adds the
sophistication: Unique T, borrow convention, reuse analysis,
unsafe/Ptr, @unboxed, and the interaction between uniqueness
and effects.

## What transfers from Rill

**Nothing directly.** Rill uses tree-walking evaluation with
Rust's own memory management. It has no refcounting, no Unique
types, no borrow convention.

**Conceptual reference:**
- Austral language: linear types, similar to Kea's Unique
- Clean language: uniqueness typing for in-place updates
- Perceus (Reinking et al. 2021): reference counting with
  reuse analysis, used by Koka
- Lean 4: reference counting with reuse analysis

## What's new

### 1. Unique T (KERNEL §12.6)

`Unique T` guarantees single ownership at compile time. The
compiler enforces:
- Move semantics: using a `Unique T` value moves it
- Subsequent references to a moved binding are compile errors
- Functions taking `Unique T` consume it — caller can't use
  it after the call
- `freeze`: drops uniqueness, value becomes refcounted
- `try_claim`: runtime check, wraps in Unique if refcount is 1

Implementation: a move-checking pass over the MIR or HIR.
Track which bindings are live/moved. Flag use-after-move as
compile errors. Similar to Rust's borrow checker but simpler —
no lifetimes, no mutable borrows, just move/not-moved.

### 2. Borrow convention (KERNEL §10.2.1)

`borrow` parameters grant temporary read-only access without
consuming ownership:

```kea
fn length(borrow self: Unique Buffer) -> Int
  self.len
```

The callee may read but not store, return, or capture the
borrowed reference. Implementation: track that borrow params
cannot escape the function scope. Verify at call sites that
the value isn't consumed.

Key rules:
- borrow callee can call other borrow functions
- borrow callee cannot pass to a consuming function
- borrow callee cannot capture in a closure
- Multiple borrows of different values in same call are OK
- borrow on non-Unique values is an optimisation hint (skip
  refcount increment). **Safety condition:** this is sound only
  when the borrow's no-escape guarantee holds — the callee cannot
  store, return, or capture the reference, so no alias can outlive
  the call. The existing borrow escape checks (step 2) are
  sufficient; no additional analysis needed beyond what Unique
  borrows already require.

### 3. Reuse analysis (KERNEL §12.5)

Static analysis to prove a value's refcount is 1 at a given
point, enabling:
- Unconditional in-place mutation for functional update (~)
- Memory reuse: deallocation + reallocation fused
- Drop-before-last-use: insert drop before consuming operation
  to ensure refcount reaches 1

This is a MIR optimisation pass. It doesn't require Unique —
it works on regular refcounted values when the analysis can
prove single ownership. Perceus (Koka) and Lean 4 both do this.

**Critical design constraint: reuse analysis is a PURE OPTIMISATION.**
Programs must be correct without it. Reuse makes them faster, not
different. If we make reuse analysis load-bearing (correctness
depends on it firing), we end up with Rust-like "fighting the
borrow checker" complexity. Keep it as a transparent optimisation
that the programmer never needs to think about.

### 4. Unsafe and Ptr T (KERNEL §17.2, §17.3)

- `@unsafe` functions can use raw pointer operations
- `unsafe` blocks in safe code mark the trust boundary
- `Ptr T`: raw unmanaged pointer, only dereferenceable in
  unsafe context
- Operations: read, write, offset, cast, null, alloc, free

Implementation: the compiler tracks unsafe context. Ptr
operations outside unsafe context are compile errors. This is
a scope-based check, not a type system extension.

**Managed memory invariants:**
- `Ptr T` must NOT point into refcounted heap objects. RC'd
  values can be moved/freed by the runtime at any time. A Ptr
  into RC'd memory is a dangling pointer waiting to happen.
- `Ptr T` may point into: stack allocations, `@unboxed` values,
  foreign-allocated memory, or arena-allocated memory (within
  the arena's lifetime).
- No "pinning" mechanism in v1. If you need a stable address for
  an RC'd value, `freeze` it and use the safe API, or copy the
  data into foreign-allocated memory via unsafe.
- `free` on a Ptr that was not allocated via `alloc` is undefined
  behavior (same as C). The unsafe boundary is the trust boundary.

### 5. @unboxed types (KERNEL §12.8)

`@unboxed` structs are always stack-allocated, passed by value,
no heap indirection, no refcounting:

```kea
@unboxed
struct Vec3
  x: Float32
  y: Float32
  z: Float32
```

Restrictions: all fields must be primitives or other @unboxed
types. No recursion, no heap pointers.

Implementation: at codegen, @unboxed types map directly to
Cranelift value types or struct types with known flat layout.
No retain/release generated.

### 6. Unique + effects interaction (KERNEL §12.6)

This is the tricky part. The rules depend on handler classification
from 0e (tail-resumptive vs non-tail vs zero-resume):

**Handler boundary rules:**
- **Tail-resumptive handlers** (inlined, no continuation capture):
  Unique values flow through freely. The handler runs synchronously
  in the same scope — no capture, no suspension.
- **Non-tail handlers** (continuation captured): Unique values in
  the continuation's captured environment are MOVED into the
  continuation. The caller loses ownership. Use-after-resume is a
  compile error. If resume is called, the Unique value moves back
  to the handler body — but only once (at-most-once resume).
- **Zero-resume handlers** (Fail-style): Unique values in the
  aborted continuation are dropped. No ownership questions.

**Actor messages:**
- `Unique T` sent as actor message: move semantics. Sender loses
  ownership. KERNEL §12.6 says "sending moves the value."
- `borrow` reference in actor message: compile error. Borrows are
  synchronous-scope-only. KERNEL §12.6 is explicit about this.

**Arena interaction:**
- `Unique T` + `Alloc` effect: unique arena-allocated values get
  both zero refcount checks (Unique) and bump allocation (Alloc).
  This is the strongest performance path. Arena-allocated Unique
  values must not escape the arena's handler scope — the move
  checker enforces this at handler boundaries.

## Implementation Plan

### Step 1: Move checking pass

Add a pass (on HIR or MIR) that tracks Unique bindings:
- Mark bindings as live when bound
- Mark as moved when used in consuming position
- Error on use-after-move
- Handle control flow: both branches of if must agree on
  move state (either both move or neither moves)
- Handle pattern matching: each arm independently

This is similar to Rust's move analysis but without borrows
and lifetimes (those are Kea's borrow convention, which is
simpler — just "doesn't escape the call").

### Step 2: Borrow checking

Extend the move checker:
- borrow parameters: verify the value isn't consumed during
  the call
- borrow references: verify they don't escape (not stored,
  not returned, not captured in closures)
- Multiple borrows: OK as long as they're different values

### Step 3: Reuse analysis and memory optimisation pipeline

This step has multiple sub-passes that build on each other. The agent
has already landed 3a and parts of 3b. The remaining sub-steps are
where the real performance wins come from.

#### Step 3a: Release scheduling and churn elimination (DONE)

- `schedule_trailing_releases_after_last_use` — move block-exit
  releases to each value's last in-block use position
- `elide_adjacent_retain_release_pairs` — remove trivial and
  non-interfering retain/release churn windows
- Linear alias ownership transfer — `let t = s` skips retain
  when `s` is linear-local and dead after the alias

#### Step 3b: Auto borrow inference (Lean 4 style)

**This is the single highest-impact optimisation.** Lean reports
it eliminates the majority of inc/dec operations.

Heuristic: if a function parameter is only *projected* (fields
read, passed to other borrowed positions) and never stored,
returned, or captured, it is automatically borrowed. No user
annotation needed.

Implementation:
- Add an inference pass over typed HIR/MIR that classifies each
  parameter as "borrowed" or "owned" based on its usage within
  the function body
- A parameter is auto-borrowed when:
  - It is never returned or stored in a data structure
  - It is never captured in a closure
  - It is never passed to a consuming (non-borrow) parameter
    of another function
  - It is only used for field projection, method calls on
    borrow params, or passed to other auto-borrow positions
- Layer this on the existing `BorrowParamMap` infrastructure:
  infer the map automatically for functions where the user
  didn't annotate, then let explicit `borrow` override
- Callers skip retain/release for auto-borrowed arguments
- This is a **pure optimisation** — programs are correct without
  it, auto-borrow just eliminates redundant RC operations

**Impact:** Massive. Most function parameters in functional code
are read-only. Lean's experience shows this is the #1 optimisation.
**Effort:** Medium. The borrow machinery exists; need an inference pass.

#### Step 3c: Drop specialization

Instead of a generic recursive drop function, generate specialised
drop code per type. When dropping a `Cons(head, tail)`, inline the
uniqueness check: if unique, extract children, drop them, free the
cell; if shared, just decrement.

Implementation:
- For each heap-allocated type, generate a type-specific drop
  function during codegen
- The drop function pattern-matches on the type's structure:
  check refcount, if unique → extract fields, recursively drop
  heap-typed fields, free the cell; if shared → decrement only
- This avoids function-call overhead and lets the optimiser see
  through drops — critical for reuse analysis to work well

**Impact:** Moderate standalone, but *enables* reuse tokens and TRMC.
**Effort:** Low-medium. It's code generation, not analysis.

#### Step 3d: Reuse tokens (Perceus FBIP)

The missing half of reuse analysis. When you pattern-match on
`Cons(head, tail)` and construct a new `Cons(f(head), mapped_tail)`,
the old cons cell's memory should be reused directly for the new
one. Zero allocator calls.

This is the FBIP (Functional But In-Place) paradigm from Perceus
(Reinking et al. 2021). Tree maps, list maps, any recursive traversal
that preserves structure — all become zero-allocation when the input
is unique.

Implementation:
- MIR pass that pairs `Release` sites with `Alloc` sites of the
  same layout (same size and alignment)
- Emit a `ReuseToken` instruction: instead of freeing the old cell,
  stash the pointer as a reuse token
- At the `Alloc` site, check: if reuse token available, use it
  (just overwrite fields); otherwise allocate fresh
- The runtime check is: `if (token != null) { reuse } else { alloc }`
- With drop specialisation (3c), the compiler can see that the
  pattern match drops the scrutinee's cell, and the constructor
  allocates one of the same layout → fuse them
- Combined with Unique T: when the input is provably unique,
  skip the runtime check entirely — unconditional reuse

**Impact:** Huge for recursive data structure code. 1.8-4.3x
speedup measured in Koka.
**Effort:** Medium. Needs a MIR pass pairing releases with allocs.

#### Step 3e: TRMC — Tail Recursion Modulo Context (Leijen, POPL 2023)

Consider:
```kea
fn map(_ xs: List A, _ f: A -> B) -> List B
  case xs
    [] -> []
    [h, ..t] -> [f(h), ..map(t, f)]
```

This isn't tail-recursive — it constructs `Cons` around the recursive
call. TRMC transforms it to: allocate the Cons cell with a hole for
the tail, then loop, filling in the hole on each iteration. Combined
with reuse tokens (3d), `map` becomes a zero-allocation in-place loop
when the input list is unique.

Implementation:
- MIR transformation pass that detects "tail call under constructor"
  patterns: `Constructor(args..., recursive_call)`
- Transform to: allocate constructor with uninitialised tail field,
  loop with hole-filling
- The hole is a `Ptr` to the uninitialised field — this is safe
  because the partially-constructed value is not yet visible
- Interacts with effect handlers: Leijen's POPL 2023 paper proves
  soundness under non-linear control flow. Kea's at-most-once
  resume constraint makes this simpler than general delimited
  continuations

**Impact:** Critical for idiomatic functional patterns (map, filter,
flatMap, any structure-preserving traversal).
**Effort:** Medium-high. Requires a MIR transformation pass.

#### Step 3f: FIP verification (`@fip` annotation)

Statically verify that a function over Unique values is fully
in-place: zero allocation, zero deallocation, constant stack.
Based on Koka's FP² work (Lorenzen et al., ICFP 2023).

```kea
@fip
fn splay_insert(_ t: Unique Tree, _ k: Int) -> Unique Tree
  -- compiler verifies: every input consumed exactly once,
  -- every allocation reuses a dead input's memory
```

Implementation:
- `@fip` annotation triggers a linear-fragment verification on MIR
- Check: every Unique input is consumed exactly once
- Check: every allocation has a matching reuse token from a dead input
- Check: no net allocations or deallocations
- If verification fails, emit a clear error explaining which
  allocation couldn't be paired with a reuse
- Can also infer `@fip` automatically for Unique-only functions
  (diagnostic, not annotation — "this function is FIP")

**Impact:** Gives users a *guarantee*, not just a hope, that their
code is zero-alloc. Splay trees, finger trees, merge sort, quicksort
— all verified FIP in Koka.
**Effort:** Medium. The check is a linear-fragment verification on MIR.

**Sequencing:** 3a → 3b → 3c → 3d → 3e → 3f. Each sub-step builds
on the previous. 3a is done. 3b (auto borrow) is the next highest
priority — it's the biggest single win. 3c (drop specialisation)
enables 3d (reuse tokens). 3e (TRMC) and 3f (FIP) are the cutting-edge
tier but proven sound in Koka/Lean.

### Step 4: Unsafe infrastructure

- Track unsafe context in the compiler
- Ptr T operations: implement in codegen as raw pointer
  operations in Cranelift
- @unsafe annotation: mark functions, verify callers use
  unsafe blocks
- Keep it simple: the goal is FFI support, not a rich unsafe
  sublanguage

### Step 5: @unboxed types

- Compiler recognises @unboxed annotation
- Verify all fields are value types
- Codegen: flat layout, value semantics, no retain/release
- Type checker: @unboxed types can't have trait impls that
  require heap allocation. **PROVISIONAL** — this constraint may
  be too strict (e.g., Show on @unboxed should be fine since it
  allocates a String, not modifying the @unboxed value). Revisit
  when trait impls land. Do not hard-code this restriction into
  the type system; implement as a lint/warning initially.

### Step 6: Fixed-width integers, bitwise ops, and numeric extensions

- Int8, Int16, Int32, Int64, UInt8-64, Float32 (KERNEL §1.1.1)
- Bitwise methods (KERNEL §1.1.2): bit_and, bit_or, bit_xor,
  bit_not, shift_left, shift_right, shift_right_unsigned
- Wrapping arithmetic (KERNEL §1.1.3): wrapping_add, wrapping_sub,
  wrapping_mul — needed for hash functions and checksums. Default
  arithmetic traps on overflow in debug builds.
- Bit counting (KERNEL §1.1.4): popcount, leading_zeros,
  trailing_zeros — map to Cranelift popcnt/clz/ctz. Needed for
  HAMT index calculation.
- Hex/binary/octal literal prefixes (KERNEL §1.5): 0xFF, 0b1010,
  0o77 — requires lexer extension. Underscore separators (1_000_000).
- Widening conversions implicit, narrowing explicit
- Codegen: direct Cranelift integer types
- **Bidirectional numeric literal inference** (KERNEL §1.1.1):
  `let x: Int32 = 42` infers `42` as `Int32`. When an integer
  literal appears in a context with a known expected fixed-width
  type (let annotation, function argument, return position), the
  literal should infer as that type. Out-of-range = compile error.
  Without context, default to `Int`. See [practical-language-gaps](../todo/practical-language-gaps.md) Gap 2.
- **Layout intrinsics** (KERNEL §17.4): `size_of` and `align_of`
  as compiler intrinsics that return compile-time constants for
  any sized type. Safe (not @unsafe). Required for Vector, HAMT,
  and arena allocators in Tier 2 stdlib. Emit as Cranelift `iconst`
  with monomorphized size. See [practical-language-gaps](../todo/practical-language-gaps.md) Gap 1.

### Step 7: Unique + effects interaction (needs 0e)

This is the 0e-dependent step. After handler compilation lands:
- Verify Unique values can cross handler boundaries when the
  handler doesn't capture them
- Verify Unique values move correctly in actor message sends
- Verify borrow references are rejected in actor messages
- Verify Unique + Alloc arena path compiles to bump + no-refcount
- Escape checks at handler/Send/Spawn/borrow boundaries

**Parallelism note:** Steps 1-3 are sequential (borrow extends
move checking; reuse needs move info; auto borrow inference extends
borrow; drop specialisation enables reuse tokens; TRMC and FIP
build on reuse tokens). Steps 4-6 are independent of 1-3 and of
each other. Step 7 is blocked on 0e.

## Testing

- Move checking: use-after-move is compile error. Linear use
  works. Branch analysis correct.
- Borrow: borrow params can read, can't escape. Multiple
  borrows OK.
- Auto borrow inference: verify parameters inferred as borrowed
  have zero retain/release. Verify storing/returning a param
  prevents auto-borrow.
- Drop specialisation: per-type drop functions generated, no
  generic recursive drop calls
- Reuse tokens: verify in-place mutation happens when expected
  (measure allocation count in test). `map` on a unique list
  should have zero net allocations.
- TRMC: `map`, `filter` on lists compile to loops, not recursive
  calls. Stack depth constant regardless of list length.
- FIP: `@fip` annotation on splay insert/delete verifies. Removing
  `@fip` from a function that allocates produces clear error.
- Unique + CoW: functional update on Unique value is always
  in-place (no conditional check needed)
- Unsafe: Ptr operations work in unsafe context, rejected
  outside
- @unboxed: value semantics, no heap allocation
- Fixed-width: bitwise ops produce correct results, narrowing
  conversions checked, wrapping arithmetic wraps correctly,
  popcount/clz/ctz match hardware instructions
- Numeric literals: hex (0xFF), binary (0b1010), octal (0o77)
  lex and compile correctly. Underscore separators ignored.

## Definition of Done

- Unique T values enforce move semantics at compile time
- borrow parameters prevent escaping and consuming
- Auto borrow inference eliminates majority of RC ops on read-only params
- Reuse tokens pair drops with allocs for zero-allocation recursive traversals
- Drop specialisation generates per-type drop code
- TRMC transforms structure-preserving recursion into loops
- `@fip` verifies zero-alloc guarantee on Unique functions
- unsafe blocks and @unsafe functions work
- Ptr T operations work for FFI
- @unboxed types compile to flat value-type layout
- Unique + effects interaction works (step 7, after 0e)
- Fixed-width integers and bitwise operations work
- `mise run check` passes

## Optimization Contract

Memory classes with benchmark gates. These are type-driven — the
compiler reads types and picks the optimal memory strategy.

| Class | Strategy | Benchmark gate |
|-------|---------|----------------|
| **Unique T** | No refcount ops, unconditional in-place mutation | Zero overhead vs raw pointer mutation |
| **Auto-borrowed** (inferred read-only params) | No retain/release at call site | Zero RC ops for projected-only params |
| **Reuse-hit** (refcount==1 proven by analysis) | Elide retain/release, in-place mutation | Within 10% of Unique for linear-use patterns |
| **Reuse-token** (drop+alloc same layout fused) | Zero allocator calls for structure-preserving recursion | Zero net allocations for `map` on unique list |
| **TRMC** (tail call under constructor) | Loop instead of recursive call + stack frame | Constant stack for `map`/`filter`/`flatMap` |
| **@fip verified** | Statically proven zero-alloc | Compiler-verified, not benchmarked |
| **@unboxed** | Flat value-type layout, passed in registers, no heap | Zero overhead vs C struct by-value |
| **Refcounted** (general case) | Atomic or non-atomic refcount (effect-directed per 0d) | Baseline — this is the default |

Precision notes:
1. **Unique + Alloc** (arena-allocated unique values) is the fastest
   path: bump allocation + no refcount + deterministic deallocation.
   But this only holds with explicit no-escape/no-alias guarantees.
   Unique values crossing handler/Send/Spawn/borrow boundaries
   must have escape checks. The move checker (step 1) enforces this.
2. **Reuse analysis is a pure optimisation** — correctness must not
   depend on it firing. Test with allocation counters: assert
   allocation count *with* reuse analysis, verify it's lower than
   *without*.

## Type-System-Driven Memory Optimizations

Effects and types structurally prove properties about memory that
other languages discover heuristically (or can't discover at all).
These optimizations are free riders on the effect system — programmers
declare effects for functionality, the compiler harvests them for
memory performance.

### Guaranteed in v0

These require no speculative analysis. They follow directly from
the type/effect signatures and existing compiler passes.

**1. Pure callee retain elision.**
A pure function (`->`) cannot store its arguments — no side effects
means no hidden storage paths. The compiler can skip caller-side
retain/release on arguments to pure callees when the argument
cannot escape except via the return value. Condition: the callee's
signature is `->` (no effects) and no `unsafe` blocks exist in the
callee body. This generalizes the `borrow` optimization to all
pure functions without annotation.

**2. Effect-directed refcount atomicity.**
Values that never cross a thread boundary (no `Send` effect in
scope) use non-atomic refcount operations. Condition: no `Send`
or `Spawn` in the function's effect row, AND no FFI calls that
could share the reference with foreign threads. The FFI boundary
must be audited — `extern "C"` calls that take a managed reference
are conservatively treated as thread-escaping unless annotated
`@thread_local`.

**3. Unique functional update chain.**
Chained functional updates (`x ~ {a: 1} ~ {b: 2} ~ {c: 3}`) in
a pure scope: after the first update creates a new value, subsequent
updates operate on a value with provably RC==1 (just created, pure
scope, no aliasing possible). The compiler can skip the runtime
RC==1 check for all updates after the first.

**4. Fail-only = pure for memory.**
Functions whose only effect is `Fail E` have the same memory
properties as pure functions — `Fail` is an early return, not a
storage operation. All pure-callee optimizations apply to
fail-only callees.

### Conditional (requires proof pass, lands with reuse analysis)

These require a MIR analysis pass but the analysis is sound because
effects provide the necessary invariants.

**5. Handler-scoped region inference.**
A `handle` block creates a scope with a known lifetime. Values
allocated inside the handler scope that don't appear in the
handler's return type provably don't escape. Condition: the handler
is non-escaping (tail-resumptive or zero-resume — NOT non-tail
handlers where continuations are captured and may be stored). For
qualifying handlers, all intermediate allocations can use region/
arena allocation with bulk deallocation at handler exit.

**6. Pure-scope escape analysis.**
Values created inside a pure function body that aren't returned
are provably scope-local. The compiler can stack-allocate them.
This is stronger than traditional escape analysis because purity
is a type-level guarantee, not a heuristic. Requires: a pass that
tracks value flow within pure function bodies and identifies
non-escaping allocations.

**7. Effect-narrowed CoW elimination.**
Functional update on a value in a pure scope where the value was
created in the same scope: the compiler can prove RC==1 without
runtime checks (no aliasing path exists in pure code). This
extends optimization #3 beyond chained updates to any functional
update on a locally-created value in a pure context.

### Phase 2+ research

These are structurally sound but require significant implementation
investment. Keep as research targets, not commitments.

**8. Automatic arena promotion.**
The compiler detects allocation-heavy pure scopes and automatically
inserts `Alloc` handlers with arena allocation. Correctness
invariant: values escaping the arena boundary must be deep-copied.
The effect system guarantees the boundary is well-defined (handler
scope), but automatic insertion requires heuristics for when it's
profitable. Requires: cost model for arena vs individual allocation.

**9. Handler allocation fusion.**
Consecutive handler blocks for the same effect type could share
an allocation arena. The compiler knows the scope boundaries
precisely from handler nesting. Requires: analysis that consecutive
handlers don't have escaping references between them.

**10. `with`-scope optimizations.**
The `with` syntax (KERNEL §10.6) desugars to nested closures, but
the flat preamble pattern (`with A; with B; with C; body`) gives
the compiler a recognizable structure for several optimizations:

- **Scope-bounded lifetimes:** `with conn <- Db.with_connection(config)`
  guarantees `conn` is dead after the block. The handler owns
  cleanup. This is exactly the information drop scheduling and
  reuse analysis need — the resource provably doesn't escape.
- **Unique propagation through handlers:** When a `with` handler
  creates a `Unique` resource and passes it to the callback via
  binding form, the compiler knows there's exactly one owner with
  a bounded scope. No RC needed within the block.
- **Stacked handler churn fusion:** Contiguous `with` handlers
  that retain/release on entry/exit are candidates for fusion.
  The compiler can see the full handler stack is contiguous and
  elide intermediate retains across handler boundaries.
- **Arena scope recognition:** `with_arena` is a `with` pattern —
  the `with` scope boundary is exactly where bulk deallocation
  happens. Recognizing the `with` preamble lets the compiler
  identify arena-eligible scopes without special-casing.

Note: the desugared form (nested closures) already gives the
compiler the same information in principle. The optimization
value is that `with` makes the pattern more recognizable and
common — worth targeting specifically in MIR passes.

**10. Dead allocation elimination.**
If a pure function's return value is unused, the entire call and
all its internal allocations can be eliminated. Effects make this
safe: pure means no observable side effects. Requires: standard
dead code elimination extended with effect-awareness (only safe
for pure or fail-only functions).

## Stdlib Tier 2: Performance

When 0f lands, the stdlib gains data structures that need Ptr, @unsafe,
Unique, and fixed-width integers. These replace the Tier 0 linked-list
implementations. See [stdlib-bootstrap](stdlib-bootstrap.md).

```
stdlib/
  vector.kea       -- Contiguous-memory array (Unique + Ptr)
  map.kea          -- HAMT Map (Ptr-based nodes, @unsafe internals)
  set.kea          -- HAMT Set
  bytes.kea        -- Bytes (Ptr UInt8 + length)
  buffer.kea       -- Mutable buffer (Unique Buffer)
```

**~800-1200 lines.** Writing these IS the test for 0f. If HAMT can't
be written with Ptr + @unsafe, the memory model has a gap. Benchmark
gate: HAMT Map within 5x of Rust HashMap for 10K-entry lookup.

## Open Questions

- How precise should the move checker be in the first pass?
  (Proposal: start with per-binding tracking, no flow-sensitive
  analysis within expressions. If `x` is moved in any branch,
  it's moved. Refine later if too conservative.)
- Should reuse analysis be a required correctness pass or a
  pure optimisation? (Proposal: pure optimisation. Programs
  must be correct without it. Reuse just makes them faster.)
- How do we test that reuse analysis actually fires? (Proposal:
  allocation counters in test runtime. Assert "this program
  allocates N times" and verify reuse reduces it.)

## Lean Formalization Priority

From ROADMAP.md:
- **Uniqueness typing soundness** — must not have holes. Unique
  values crossing handler boundaries is the tricky case.
- **Unique/effect interaction** — prove that effects don't
  violate uniqueness invariants.
- **Arena escape analysis** — highest-risk bet. If there's a
  soundness hole, major redesign needed.

These are the formalizations most likely to find false theorems.
Start them as soon as the design stabilizes from prototyping.

## Progress
- 2026-02-28 00:31: Step 6 kickoff landed in `kea-syntax` lexer: numeric literal parsing now supports base-prefixed integers (`0x`, `0b`, `0o`) and underscore separators for decimal integers/floats. Added lexer regressions for valid prefixed/underscored forms and invalid forms (`0x`, `1__0`). Verified with `PKG=kea-syntax mise run test-pkg` and `mise run check`.
- 2026-02-28 00:33: Completed parse + execute-path coverage for the new literal forms. Added parser regressions (`parse_prefixed_int`, `parse_underscored_int`, `parse_underscored_float`) and CLI execute-path regressions proving compiled programs evaluate prefixed and underscored integers end-to-end (`compile_and_execute_prefixed_integer_literals_exit_code`, `compile_and_execute_underscored_numeric_literals_exit_code`). Verified with `PKG=kea-syntax mise run test-pkg`, `PKG=kea mise run test-pkg`, and `mise run check`.
- 2026-02-28 00:36: Landed Step 6 wrapping arithmetic method surface end-to-end for `Int`: `wrapping_add`, `wrapping_sub`, `wrapping_mul` now register in infer builtin methods (`Kea.Int`), lower to dedicated MIR ops, and compile through codegen. Added execute-path CLI regressions (`compile_and_execute_wrapping_add_method_exit_code`, `compile_and_execute_wrapping_sub_method_exit_code`, `compile_and_execute_wrapping_mul_method_exit_code`) and validated touched crates with `PKG=kea-mir/kea-codegen/kea/kea-infer mise run test-pkg` plus `mise run check`.
- 2026-02-28 00:38: Landed Step 6 integer bit-count methods end-to-end for `Int`: `popcount`, `leading_zeros`, and `trailing_zeros` now register in infer builtin methods, lower to MIR unary ops, and compile to Cranelift `popcnt/clz/ctz`. Added MIR regression (`lower_hir_module_lowers_popcount_method_call_to_mir_unary_op`) plus execute-path CLI regressions (`compile_and_execute_popcount_method_exit_code`, `compile_and_execute_leading_zeros_method_exit_code`, `compile_and_execute_trailing_zeros_method_exit_code`). Verified with `PKG=kea-mir/kea-codegen/kea/kea-infer mise run test-pkg` and `mise run check`.
- 2026-02-28 00:42: Tightened Step 6 fixed-width diagnostics in `kea-infer`: precision range checks now evaluate constant integer expressions (unary/binary arithmetic) under expected `IntN/UIntN` annotations, so expression-result overflow and negative-to-unsigned errors surface at typecheck time (not just raw literal overflow). Added regressions `infer_precision_let_annotation_rejects_out_of_range_int_expression_result` and `infer_precision_let_annotation_rejects_negative_expression_for_unsigned_int`. Verified with `PKG=kea-infer mise run test-pkg` and `mise run check`.
- 2026-02-28 00:46: Implemented Step 6 mixed-width integer coercion rules in `kea-infer` arithmetic inference: implicit widening now computes result type across precision ints (`Int8 + Int16 -> Int16`, `UInt8 + UInt16 -> UInt16`), and mixed signed/unsigned arithmetic widens to `Int` in v0. Added regressions `infer_arithmetic_widens_signed_precision_ints`, `infer_arithmetic_widens_unsigned_precision_ints`, and `infer_arithmetic_mixed_signed_unsigned_defaults_to_int`. Verified with `PKG=kea-infer mise run test-pkg` and `mise run check`.
- 2026-02-28 00:50: Wired Step 6 fixed-width execute-path bootstrap coverage: codegen now accepts `Type::IntN`/`Type::FloatN` in scalar lowering (`clif_type`) via the existing scalar ABI, and CLI execute-path regressions now cover mixed-width typed arithmetic programs (`Int8 + Int16`, `UInt8 + UInt16`, `Int8 + UInt8`) without coercion hacks in source. Extended JIT main dispatch to accept any integer logical return (not just `Int`) so typed-width mains execute directly and normalize to process exit codes. Verified with `PKG=kea-codegen mise run test-pkg`, `PKG=kea-infer mise run test-pkg`, `PKG=kea mise run test-pkg`, and `mise run check`.
- 2026-02-28 07:22: Replaced the scalar-ABI fallback with width-accurate fixed-width codegen lowering in `kea-codegen`: `clif_type` now maps `Int8..Int64`/`UInt8..UInt64` to matching Cranelift integer widths and `Float32` to `f32` (`Float16` remains bootstrap-mapped to `f32`). Local call lowering now coerces arguments against callee runtime signatures (not source arg metadata), return lowering coerces to function runtime return type, fail-result payload stores are type-directed, and JIT `main` entrypoint decoding now reads `IntN/UIntN` payloads with width/signedness-aware decoding in both direct and fail-result ABI paths. Added regressions `clif_type_maps_precision_int_widths`, `clif_type_maps_precision_float_widths`, `compile_and_execute_int8_main_exit_code`, `compile_and_execute_uint16_main_exit_code`, and `compile_and_execute_int8_call_arg_coercion_exit_code`. Verified with `PKG=kea-codegen mise run test-pkg`, `PKG=kea mise run test-pkg`, and `mise run check`.
- 2026-02-28 08:13: Landed explicit narrowing conversion surface for fixed-width ints: `Int8..UInt64.try_from(Int)` now registers as builtin module functions in `kea-infer`, call-site constant overflows emit precise diagnostics, and MIR lowers `*.try_from` to checked bounds branches that construct `Option` (`Some` on in-range, `None` otherwise) on the compiled path. Added MIR regression `lower_hir_module_lowers_fixed_width_try_from_to_checked_option_path` plus execute-path CLI regressions (`compile_and_execute_int8_try_from_some_exit_code`, `compile_and_execute_int8_try_from_none_exit_code`, `compile_and_execute_uint8_try_from_negative_none_exit_code`, `compile_rejects_const_try_from_overflow`). Verified with `PKG=kea-infer mise run test-pkg`, `PKG=kea-mir mise run test-pkg`, `PKG=kea mise run test-pkg`, and `mise run check`.
- 2026-02-28 08:20: Closed the remaining Step 6 narrowing edge cases for `*.try_from`: type checking now rejects non-integer inputs with a dedicated diagnostic while still allowing integer-width arguments at call sites, MIR adds signed/unsigned widening ops before bounds checks for fixed-width integer inputs, and lowering now tolerates `Dynamic`-typed integer carriers emitted at some resolved callsites. Added MIR regression `lower_hir_module_widens_signed_fixed_width_input_before_try_from_checks` and CLI regressions `compile_and_execute_int8_try_from_fixed_width_input_exit_code` plus `compile_rejects_try_from_non_integer_input`. Verified with `PKG=kea-infer mise run test-pkg`, `PKG=kea-mir mise run test-pkg`, `PKG=kea mise run test-pkg`, and `mise run check`.
- 2026-02-28 08:28: Landed Step 1 move-checking skeleton as a typed-HIR ownership pass (`check_unique_moves`) wired into `compile_module`, project module loading, and MCP `process_module_in_env` paths. The pass seeds `Unique`-typed bindings from function params/let bindings, marks them moved on use, reports use-after-move, and enforces branch move-state agreement across `if` branches. Added end-to-end CLI regressions `compile_rejects_unique_use_after_move` and `compile_rejects_unique_branch_move_mismatch`. Verified with `PKG=kea-hir mise run test-pkg`, `PKG=kea mise run test-pkg`, and `mise run check`.
- 2026-02-28 08:33: Extended Step 1 ownership checking to the remaining early hotspots: `HirExprKind::Raw` now traverses AST fallback forms with case-arm branch-state merge logic, and lambda analysis now treats captured outer `Unique` bindings as moves at closure creation. Added CLI regression `compile_rejects_unique_capture_then_reuse` to lock the capture path. Verified with `PKG=kea-hir mise run test-pkg`, `PKG=kea mise run test-pkg`, and `mise run check`.
- 2026-02-28 08:47: Started Step 2 borrow-checking constraints on top of Step 1: borrow parameters are now recognized via `borrow` parameter convention (`Param::is_borrowed`), signature labels no longer treat `borrow` as a call label, and move checking now threads borrow-parameter position maps into HIR/AST call traversal so borrowed argument positions are read-only (no caller move). Added borrowed-binding state to move checker: attempting to consume a borrowed `Unique` binding emits an explicit diagnostic. Added execute-path regressions `compile_and_execute_borrow_param_does_not_consume_caller_unique` and `compile_rejects_consuming_borrow_parameter_in_callee`. Verified with `PKG=kea-hir mise run test-pkg`, `PKG=kea mise run test-pkg`, and `mise run check`.
- 2026-02-28 08:57: Completed the next Step 2 borrow slice across syntax + compiler plumbing: `borrow` is now tokenized as a first-class keyword (`TokenKind::Borrow`) and parsed into dedicated AST parameter label state (`ParamLabel::Borrow`) instead of the prior label-name convention. Borrow metadata collection now includes module-qualified function aliases (`Module.fn`) and project typechecking seeds each module’s move-check pass with a qualified borrow map from all loaded modules, so qualified cross-module calls preserve borrow argument read-only behavior. Added execute-path regressions `compile_rejects_returning_borrow_parameter`, `compile_rejects_capturing_borrow_parameter`, and `compile_and_execute_qualified_borrow_call_does_not_consume_unique`, plus parser regression `parse_borrow_parameter_declaration`. Verified with `PKG=kea-syntax mise run test-pkg`, `PKG=kea mise run test-pkg`, and `mise run check`.
- 2026-02-28 09:01: Began Step 3 reuse-analysis scaffolding in MIR with a conservative post-lowering pass that re-schedules trailing block-exit `Release` instructions to each value’s last in-block use position (`schedule_trailing_releases_after_last_use`). The pass is optimization-only, keeps definitions/liveness ordering intact, and avoids moving releases for values without local defs. Added MIR regression `lower_hir_module_schedules_block_exit_releases_after_last_use` and re-ran downstream execute-path coverage to confirm no runtime/codegen regressions. Verified with `PKG=kea-mir mise run test-pkg`, `PKG=kea mise run test-pkg`, and `mise run check`.
- 2026-02-28 09:06: Extended Step 3 with initial churn fusion in MIR: added `elide_adjacent_retain_release_pairs` as a conservative pass after release scheduling, removing only trivial adjacent `Retain(v); Release(v)` pairs. Added MIR regression `elide_adjacent_retain_release_pairs_removes_trivial_churn` and updated heap-alias lowering coverage to assert the post-pass invariant (no adjacent retain/release churn) via `lower_hir_module_avoids_adjacent_retain_release_churn_for_heap_alias_binding`. Verified with `PKG=kea-mir mise run test-pkg`, `PKG=kea mise run test-pkg`, and `mise run check`.
- 2026-02-28 09:08: Expanded Step 3 churn fusion to short nop-separated windows: `elide_adjacent_retain_release_pairs` now also removes `Retain(v)` / `Release(v)` pairs separated only by `Nop` instructions, preserving surrounding instruction order while dropping dead RC churn. Added MIR regression `elide_adjacent_retain_release_pairs_removes_nop_separated_churn`. Verified with `PKG=kea-mir mise run test-pkg` and `mise run check`.
- 2026-02-28 09:09: Generalized Step 3 churn fusion from nop-only to non-interfering windows: `elide_adjacent_retain_release_pairs` now removes `Retain(v)` / `Release(v)` pairs when intervening instructions neither read nor redefine `v` (e.g., unrelated const/setup work), while stopping at any `v` use/definition. Added MIR regression `elide_adjacent_retain_release_pairs_removes_non_interfering_window_churn`. Revalidated downstream compiled-path behavior with `PKG=kea mise run test-pkg` after MIR changes. Verified with `PKG=kea-mir mise run test-pkg`, `PKG=kea mise run test-pkg`, and `mise run check`.
- 2026-02-28 09:11: Added allocation-count-focused coverage for Step 3 churn fusion in CLI compile stats: new regression `compile_elides_heap_alias_retain_release_churn_in_stats` compiles a heap-alias program and asserts fused behavior (`retain_count == 0` while keeping `release_count > 0`) to ensure churn reduction is measurable at the pass-stats layer, not just MIR snapshots. Verified with `PKG=kea mise run test-pkg` and `mise run check`.
- 2026-02-28 09:18: Closed the first linear-use-driven Step 3 candidate in MIR lowering with scope-safe alias ownership transfer: heap alias lets (`let t = s`) now avoid retain/release churn only when the source binding is linear-local to the current block and not referenced later, while aliases of outer-scope bindings still retain to keep lifetimes sound. Added regressions `lower_hir_module_transfers_linear_local_heap_alias_without_retain` and `lower_hir_module_keeps_outer_heap_binding_alive_across_inner_alias_block`. Verified with `PKG=kea-mir mise run test-pkg`, `PKG=kea mise run test-pkg`, and `mise run check`.
- 2026-02-28 09:23: Extended Step 3 stats coverage from single-alias to chain-alias kernels: added CLI regression `compile_elides_linear_heap_alias_chain_retain_churn_in_stats` using a heap record alias chain (`b0 -> b1 -> b2 -> b3`) and asserting `retain_count == 0` with runtime semantic parity (`exit_code == 1`). This locks in that linear ownership transfer scales beyond one alias edge and remains observable-safe on compiled path. Verified with `PKG=kea mise run test-pkg` and `mise run check`.
- 2026-02-28 09:31: Extended Step 3 linear-use ownership transfer from var-alias lets to record-update bases in MIR lowering. `RecordUpdate` now skips pre-claim `Retain` only when the base binding is linear-local to the current block, not referenced later, and not referenced by update field expressions; otherwise it conservatively keeps retain behavior. Added MIR regressions `lower_hir_module_transfers_linear_local_record_update_base_without_retain` and `lower_hir_module_keeps_retain_when_record_update_fields_read_base_binding`, plus updated safety plumbing tests remain green. Verified with `PKG=kea-mir mise run test-pkg`, `PKG=kea mise run test-pkg`, and `mise run check`.
- 2026-02-28 09:36: Added benchmark harness coverage for Step 3 alias-transfer paths in `kea-bench`: new divan benches `lower_linear_heap_alias_chain_to_mir` and `compile_linear_heap_alias_chain_hir_jit`, backed by `build_linear_heap_alias_chain_hir_module(levels)`. This makes alias-churn optimization effects observable in benchmark artifacts (Stage A/Stage B regression workflows) instead of only unit/integration tests. Verified with `cargo test -p kea-bench --benches --no-run` and `mise run check`.
- 2026-02-28: **Step 3 expanded** with five new sub-steps (3b-3f) based on Lean 4 / Koka / Perceus research. See the updated Step 3 section above for full details. Priority order: 3b (auto borrow inference) → 3c (drop specialisation) → 3d (reuse tokens) → 3e (TRMC) → 3f (FIP verification). These are where the real performance wins come from — the current churn elimination is necessary but not sufficient.
- 2026-02-28 14:04: Landed Step 3b auto-borrow inference as a fixpoint pass over typed HIR (`infer_auto_borrow_param_positions`) layered on top of explicit `borrow` annotations. The compiler now infers additional borrow positions for `Unique` parameters when move-check simulation proves non-consuming usage, and threads inferred positions through single-module, project, and MCP compilation paths before move checking. Added local + cross-module execute-path regressions (`compile_and_execute_auto_borrow_inferred_param_does_not_consume_caller_unique`, `compile_and_execute_qualified_auto_borrow_inferred_call_does_not_consume_unique`) and a guard regression proving consuming params are not inferred as borrowed (`compile_rejects_auto_borrow_inference_for_consuming_parameter`). Verified with `PKG=kea-hir mise run test-pkg`, `PKG=kea mise run test-pkg`, and `mise run check`.
- 2026-02-28 14:13: Landed Step 3c drop-specialization scaffolding in `kea-codegen`: codegen now declares/defines per-layout drop functions for records and sums (`__kea_drop_record__*`, `__kea_drop_sum__*`), converts release lowering to typed dispatch (`Release` uses inferred MIR value types to call type-specific drop functions when available), and extends layout planning to retain nominal field payload types (including per-variant sum payload types). Added immediate-tag guards for mixed/unit sum carriers and projection retains for known heap payloads to keep compiled-path behavior stable while typed drops are enabled. Added regressions for layout type capture (`field_types`, `variant_field_types`) and value-type inference (`infer_mir_value_types_resolves_dynamic_sum_payload_from_layout`). Verified with `PKG=kea-codegen mise run test-pkg`, `mise run check`, and `mise run check-full`.
- 2026-02-28 14:31: Landed first Step 3d reuse slice for record layouts: MIR now fuses adjacent same-layout `Release` + `RecordInit` into `RecordInitReuse` when the source layout is reuse-safe, and codegen lowers `RecordInitReuse` with a unique-fast-path (overwrite in place) plus fallback path (typed release + fresh alloc). Added MIR regressions (`fuse_release_alloc_same_layout_rewrites_to_record_init_reuse`, `fuse_release_alloc_same_layout_skips_managed_record_layouts`) and a codegen execute-path regression (`cranelift_backend_executes_record_init_reuse_and_field_load`). Verified with `PKG=kea-mir mise run test-pkg`, `PKG=kea-codegen mise run test-pkg`, `PKG=kea mise run test-pkg`, and `mise run check`.
- 2026-02-28 14:33: Added Step 3d observability hook in `kea-codegen` pass stats: `FunctionPassStats` now tracks `reuse_count` (currently `RecordInitReuse` hits), with regression coverage (`collect_pass_stats_counts_record_reuse_ops`) and updated baseline expectations (`collect_pass_stats_counts_effect_ops`). This makes reuse-hit tracking available to benchmark/CI reporting without relying only on alloc/release deltas. Verified with `PKG=kea-codegen mise run test-pkg` and `mise run check`.
- 2026-02-28 14:35: Extended Step 3d MIR fusion to non-adjacent same-block pairings under a conservative safety window: `Release` can now fuse with a later `RecordInit` when intervening instructions neither read/redefine the released value nor cross a memory-op barrier. Added regressions `fuse_release_alloc_same_layout_rewrites_non_adjacent_non_interfering_init` and `fuse_release_alloc_same_layout_stops_when_released_value_is_read_before_alloc` to lock the widened and blocked paths. Verified with `PKG=kea-mir mise run test-pkg`, `PKG=kea mise run test-pkg`, and `mise run check`.
- 2026-02-28 14:42: Extended Step 3d reuse fusion beyond records: MIR now fuses eligible same-layout `Release` + `SumInit` into `SumInitReuse` for payload-only unmanaged sum layouts, with mixed/unit sums explicitly excluded. Codegen now lowers `SumInitReuse` through the same unique-fast-path + fallback-release/alloc pattern as records, and pass stats count both record and sum reuse hits under `reuse_count`. Added MIR regressions (`fuse_release_alloc_same_layout_rewrites_sum_init_to_sum_init_reuse`, `fuse_release_alloc_same_layout_skips_sum_reuse_for_unit_mixed_layouts`) and codegen execute-path regression (`cranelift_backend_executes_sum_init_reuse_and_tag_load`). Verified with `PKG=kea-mir mise run test-pkg`, `PKG=kea-codegen mise run test-pkg`, `PKG=kea mise run test-pkg`, and `mise run check`.
- 2026-02-28 14:45: Wired `reuse_count` into benchmark artifacts: added `kea-bench` utility binary (`reuse_metrics`) that compiles canonical record/sum reuse kernels and emits reuse/alloc/release totals as JSON, and integrated it into `scripts/bench-export.sh` so each benchmark export now writes `reuse.metrics.json` beside timing summaries. Verified by running `./scripts/cargo-agent.sh run -p kea-bench --bin reuse_metrics -- /tmp/reuse.metrics.json`, `mise run check`, and `cargo test -p kea-bench --benches --no-run`.
- 2026-02-28 14:54: Extended Step 3d fusion across simple block boundaries: MIR now rewrites predecessor-tail `Release(v)` + single-predecessor jump-target init (`RecordInit`/`SumInit`) into `RecordInitReuse`/`SumInitReuse` when the released value is forwarded through the jump argument to a successor block parameter and reuse eligibility constraints hold. Added regressions `fuse_release_alloc_cross_block_jump_rewrites_successor_init_to_reuse` and `fuse_release_alloc_cross_block_jump_skips_multi_predecessor_successor`. Verified with `PKG=kea-mir mise run test-pkg` and `mise run check`.
- 2026-02-28 14:56: Generalized Step 3d cross-block reuse to branch-join style successor blocks: jump-target rewrites now permit multi-predecessor joins when every incoming jump forwards the same reused parameter position and each predecessor ends with `Release` of that incoming value. Added positive/negative regressions (`fuse_release_alloc_cross_block_jump_rewrites_join_when_all_predecessors_release`, `fuse_release_alloc_cross_block_jump_skips_when_any_predecessor_lacks_release`) while preserving the earlier single-predecessor rewrite coverage. Verified with `PKG=kea-mir mise run test-pkg` and `mise run check`.
- 2026-02-28 14:58: Widened cross-block Step 3d matching to tolerate trailing `Nop` instructions after predecessor releases: cross-block fusion now treats `Release` as valid when it is the last non-nop instruction before a jump, while still rejecting non-nop work after release. Added regressions `fuse_release_alloc_cross_block_jump_rewrites_with_trailing_nops_after_release` and `fuse_release_alloc_cross_block_jump_skips_when_non_nop_follows_release`. Verified with `PKG=kea-mir mise run test-pkg` and `mise run check`.
- 2026-02-28 15:03: Completed explicit `ReuseToken` feasibility instrumentation for Step 3d without changing runtime ABI: `kea-codegen` pass stats now expose `reuse_token_candidate_count` by CFG reachability (remaining `Release` sites with reachable unfused same-layout `RecordInit`/`SumInit`, including loop/join paths), with value-layout inference seeded from allocs, block params, move-like ops, and jump argument flow. Added regression `collect_pass_stats_counts_reuse_token_candidates`, and extended benchmark artifact JSON (`reuse.metrics.json`) to include per-kernel + total `reuse_token_candidate_count` alongside reuse/alloc/release. Verified with `PKG=kea-codegen mise run test-pkg`, `mise run check`, and `./scripts/cargo-agent.sh run -p kea-bench --bin reuse_metrics -- /tmp/reuse.metrics.json`.
- 2026-02-28 15:11: Landed first explicit Step 3d MIR token flow implementation: added `ReuseToken` producer op plus token-consuming alloc ops (`RecordInitFromToken`, `SumInitFromToken`) in MIR and wired Cranelift lowering with reuse-fast-path (`token != null`) and alloc fallback. `ReuseToken` now materializes token-or-null by uniqueness test (unique keeps pointer as token, shared path performs typed release + null token). Extended pass stats with `reuse_token_produced_count`/`reuse_token_consumed_count`, updated value-type/layout propagation for token-flow instructions, and added regressions (`collect_pass_stats_counts_reuse_token_flow_ops`, `cranelift_backend_executes_record_init_from_token_and_field_load`). Verified with `PKG=kea-mir mise run test-pkg`, `PKG=kea-codegen mise run test-pkg`, and `mise run check`.
- 2026-02-28 15:19: Extended Step 3d token-flow emission with conservative loop/back-edge support: added `emit_reuse_tokens_for_loop_backedge_joins` to rewrite all-release back-edge joins (including self-backedge predecessors on non-entry loop headers) into `ReuseToken` + `RecordInitFromToken`/`SumInitFromToken` flow, covering cases intentionally skipped by mixed-predecessor tokenization. Added MIR regression `emit_reuse_tokens_for_loop_backedge_join_rewrites_all_releasing_predecessors`. In parallel, extended benchmark artifact export (`reuse_metrics`) with `reuse_token_produced_count`, `reuse_token_consumed_count`, and `reuse_token_consumed_pct` so candidate→consumed conversion can be trended per kernel and in totals. Verified with `mise run check`, `PKG=kea-mir mise run test-pkg`, and `cargo test -p kea-bench --benches --no-run`.
- 2026-02-28 15:22: Refined Step 3d conversion telemetry semantics in `reuse_metrics`: replaced naive `consumed / remaining_candidates` with coverage (`consumed / (consumed + remaining_candidates)`), and added a tail-recursive source kernel (`loop_backedge_rotate`) to keep loop/back-edge paths in the exported metrics corpus as reuse-token work evolves. Current source-kernel coverage remains 0%, which now serves as an explicit baseline for upcoming source-level token-hit expansion. Verified with `mise run check`, `cargo test -p kea-bench --benches --no-run`, and `./scripts/cargo-agent.sh run -p kea-bench --bin reuse_metrics -- /tmp/reuse.metrics.json`.
- 2026-02-28 15:31: Expanded source-level Step 3d benchmark corpus in `reuse_metrics` with additional real-language kernels (`recursive_churn`, `mixed_join_unit`, `loop_mixed_unit_walk`) to probe join/loop token-flow shapes through the full frontend pipeline. Baseline remains `reuse_token_consumed_count == 0` across current source kernels (while MIR-level token regressions are green), which narrows the remaining gap to frontend/lowering shape coverage rather than token runtime/codegen plumbing. Verified with `mise run check`, `cargo test -p kea-bench --benches --no-run`, and `./scripts/cargo-agent.sh run -p kea-bench --bin reuse_metrics -- /tmp/reuse.metrics.json`.
- 2026-02-28 18:39: Closed the Step 3d source-kernel conversion gap and pinned the first CI floor. MIR pass ordering now runs `emit_reuse_tokens_for_trailing_release_alloc` before release scheduling, allowing source kernels to preserve trailing-release tokenization opportunities; `reuse_metrics` now reports non-zero consumed coverage at source level (`record_build` and `sum_build` each emit+consume one token, totals `reuse_token_consumed_count=2`). Added `scripts/bench-reuse-floor-check.sh` plus baseline floors (`benchmarks/baselines/reuse-token-floors*.csv`) and wired both Stage B benchmark workflows to enforce/publish reuse-token floor summaries. Verified with `PKG=kea-mir mise run test-pkg`, `cargo test -p kea-bench --benches --no-run`, `./scripts/cargo-agent.sh run -p kea-bench --bin reuse_metrics -- /tmp/reuse.metrics.try6.json`, `./scripts/bench-reuse-floor-check.sh /tmp/reuse.metrics.try6.json benchmarks/baselines/reuse-token-floors.csv /tmp/reuse-floor-check.try6`, and `mise run check`.
- 2026-02-28 18:47: Started Step 3e instrumentation lane: `FunctionPassStats` now tracks `trmc_candidate_count`, with candidate detection covering constructor-wrapped self recursion in direct return and simple jump-through-return-join shapes. Added codegen regression `collect_pass_stats_counts_trmc_candidates` and expanded `reuse_metrics` with a source kernel (`trmc_chain`) plus per-kernel/total TRMC candidate telemetry (`trmc_candidate_count`) so candidate prevalence is now visible in benchmark artifacts (`totals.trmc_candidate_count=1` on current corpus). Verified with `PKG=kea-codegen mise run test-pkg`, `./scripts/cargo-agent.sh run -p kea-bench --bin reuse_metrics -- /tmp/reuse.metrics.try10.json`, `./scripts/bench-reuse-floor-check.sh /tmp/reuse.metrics.try10.json benchmarks/baselines/reuse-token-floors.csv /tmp/reuse-floor-check.try10`, and `mise run check`.
- 2026-02-28 19:08: Landed the first Step 3e rewrite slice in MIR: `rewrite_trmc_descending_sum_chain` now recognizes descending self-recursive sum constructors of the form `if n <= 0 then Base else Variant(n, self(n - 1))` (including join-return shape) and rewrites to an explicit loop (`i`/`acc` block params) with no recursive `Call` in the constructor path. Added MIR regression `rewrite_trmc_descending_sum_chain_rewrites_recursive_constructor_call`. In telemetry, `trmc_chain` now drops from `trmc_candidate_count=1` to `0` in `reuse_metrics`, confirming rewrite application on source lowering. Verified with `PKG=kea-mir mise run test-pkg`, `PKG=kea mise run test-pkg`, `cargo test -p kea-bench --benches --no-run`, `./scripts/cargo-agent.sh run -p kea-bench --bin reuse_metrics -- /tmp/reuse.metrics.try12.json`, and `mise run check`.
- 2026-03-01 23:44: Extended Step 3e TRMC rewrite coverage for constructor-field contexts in MIR: `rewrite_trmc_descending_sum_chain` now remaps supported pre-call field-expression values (`Const`/`Unary`/`Binary`) into the loop step block, so constructor payloads derived from the recursive index are preserved instead of requiring direct `Variant(n, self(...))` fields only. Added regression `rewrite_trmc_descending_sum_chain_preserves_pre_call_constructor_fields` alongside existing call-elision coverage. Verified with `PKG=kea-mir mise run test-pkg` and `mise run check`.
- 2026-03-01 23:51: Landed a Step 3c drop-specialisation follow-up in `kea-codegen`: record and sum drop functions now release managed child fields before freeing the parent allocation. Record drops iterate typed fields from layout metadata and call typed drop dispatch for managed children; sum drops now load tags, dispatch variant-specific managed payload release, and then free. This closes the previous shallow-free behavior where nested managed fields were not dropped. Verified with `PKG=kea-codegen mise run test-pkg` and `mise run check`.
- **Next:** Complete the remaining deep-recursive Step 3c follow-up (iterative/self-recursive sum teardown path for very large chains) and continue Step 3e generalization beyond current descending-int patterns.
