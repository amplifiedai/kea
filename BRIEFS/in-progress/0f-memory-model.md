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

### Step 7: Unique + effects interaction (needs 0e)

This is the 0e-dependent step. After handler compilation lands:
- Verify Unique values can cross handler boundaries when the
  handler doesn't capture them
- Verify Unique values move correctly in actor message sends
- Verify borrow references are rejected in actor messages
- Verify Unique + Alloc arena path compiles to bump + no-refcount
- Escape checks at handler/Send/Spawn/borrow boundaries

**Parallelism note:** Steps 1-3 are sequential (borrow extends
move checking; reuse needs move info). Steps 4-6 are independent
of 1-3 and of each other. Step 7 is blocked on 0e.

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
  conversions checked, wrapping arithmetic wraps correctly,
  popcount/clz/ctz match hardware instructions
- Numeric literals: hex (0xFF), binary (0b1010), octal (0o77)
  lex and compile correctly. Underscore separators ignored.

## Definition of Done

- Unique T values enforce move semantics at compile time
- borrow parameters prevent escaping and consuming
- Basic reuse analysis elides some retain/release pairs
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
| **Reuse-hit** (refcount==1 proven by analysis) | Elide retain/release, in-place mutation | Within 10% of Unique for linear-use patterns |
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
- **Next:** finish Step 2 escape hardening for non-call escape forms (notably explicit actor/send/handler boundary borrow escape diagnostics) and then begin Step 3 reuse-analysis scaffolding on MIR.
