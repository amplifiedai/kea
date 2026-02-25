# Brief: Memory Model

**Status:** design
**Priority:** v1-critical
**Depends on:** 0e-runtime-effects (needs working effect compilation)
**Blocks:** 0g-advanced-types, Phase 1

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
  refcount increment)

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

This is the tricky part. Key questions:
- Can a `Unique T` value cross a handler boundary? (Yes — if
  the handler doesn't capture it. The handler body runs in the
  same scope.)
- Can a `Unique T` be sent as an actor message? (Yes — it's
  a move. KERNEL §12.6 says "sending moves the value.")
- Can a `borrow` reference appear in an actor message? (No —
  borrows are synchronous. KERNEL §12.6 says compile error.)
- `Unique T` + `Alloc` effect: unique arena-allocated values
  get both zero refcount checks (Unique) and bump allocation
  (Alloc). This is the strongest performance path.

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

### Step 3: Reuse analysis (basic)

MIR optimisation pass:
- Identify values that are consumed (pattern matched, passed
  to consuming function) and never referenced again
- Insert drop-before-last-use to enable refcount to reach 1
- Identify allocation + deallocation pairs of same-sized values
  and fuse them (reuse token)

Start with obvious cases: linear use of a value (bound once,
used once, consumed). Extend to more complex patterns later.

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
  require heap allocation (this constraint may be too strict —
  revisit)

### Step 6: Fixed-width integers and bitwise ops

- Int8, Int16, Int32, Int64, UInt8-64, Float32 (KERNEL §1.1.1)
- Bitwise methods (KERNEL §1.1.2): bit_and, bit_or, bit_xor,
  bit_not, shift_left, shift_right, shift_right_unsigned
- Widening conversions implicit, narrowing explicit
- Codegen: direct Cranelift integer types

## Testing

- Move checking: use-after-move is compile error. Linear use
  works. Branch analysis correct.
- Borrow: borrow params can read, can't escape. Multiple
  borrows OK.
- Reuse analysis: verify in-place mutation happens when
  expected (measure allocation count in test, not just
  correctness)
- Unique + CoW: functional update on Unique value is always
  in-place (no conditional check needed)
- Unsafe: Ptr operations work in unsafe context, rejected
  outside
- @unboxed: value semantics, no heap allocation
- Fixed-width: bitwise ops produce correct results, narrowing
  conversions checked

## Definition of Done

- Unique T values enforce move semantics at compile time
- borrow parameters prevent escaping and consuming
- Basic reuse analysis elides some retain/release pairs
- unsafe blocks and @unsafe functions work
- Ptr T operations work for FFI
- @unboxed types compile to flat value-type layout
- Fixed-width integers and bitwise operations work
- `mise run check` passes

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
