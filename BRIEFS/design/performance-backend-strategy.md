# Brief: Performance and Backend Strategy

**Status:** design
**Priority:** v1-critical
**Depends on:** 0d-codegen-pure, 0e-runtime-effects, 0f-memory-model
**Blocks:** credible performance claims, backend roadmap decisions, self-hosting compiler UX targets

## Motivation

Kea's value proposition includes reliability, predictable behavior,
and strong tooling. That only lands if performance is:

1. competitive enough for real workloads,
2. predictable enough for production operations,
3. measurable enough to steer architecture decisions.

This brief defines concrete performance targets and, critically,
the IR/backend design constraints needed now so a future Kea-native
backend is viable without a rewrite.

## Ground Truth

Near-term Kea uses Cranelift for speed of compilation and bootstrap.
Long-term, we may add:

- an optional LLVM release backend, and/or
- a Kea-native backend once self-hosted.

The long-term upside is real only if MIR/effect/ownership semantics
are represented explicitly and backend-neutrally now.

## Performance Targets (Directional, by phase)

These are engineering targets, not marketing copy:

1. **0d (pure subset):** establish stable baseline and variance.
2. **0e (handlers):** capability effects + tail-resumptive handlers
   should be close to direct-call baselines on representative cases.
3. **0f (memory model):** measurable reduction in retain/release and
   allocation count from uniqueness/reuse passes.
4. **Self-hosting (Phase 1):** edit-compile-run loop should be fast
   enough that compiler development is not bottlenecked by toolchain.

Absolute "faster than X" claims are deferred until benchmark suite
and CI gates are stable.

## Material Design Requirements (Do This Now)

### 1) Backend-neutral MIR contract

Define MIR as the stable boundary between type/effect semantics and
machine lowering.

MIR must encode:
- explicit control flow and data flow,
- explicit effect operations (capability vs handler-dispatch forms),
- explicit ownership operations (retain/release/move/borrow markers),
- value categories (unboxed value, pointer-managed aggregate, etc.),
- deterministic layout metadata references.

No backend should need to infer language semantics from opaque calls.

### 2) Ownership/effect-aware lowerable ops

Do not hide key semantics inside generic function calls.
Represent as MIR ops/intrinsics:

- `retain`, `release`, `try_claim`, `freeze`,
- functional update fast/slow paths,
- effect operation invocation class:
  - capability direct-call candidate,
  - handler-dispatch candidate,
  - fail/zero-resume candidate.

This is what enables backend-specific optimization later.

### 3) Calling convention manifest

Define a language-level calling convention manifest independent of
Cranelift internals:

- parameter classes (value/ref/evidence),
- return style (single/multi/result-form),
- effect evidence placement strategy,
- async/actor message ABI shapes.

Backends should implement this manifest, not ad-hoc conventions.

### 4) Layout and ABI side tables

Maintain explicit, queryable layout tables for structs/enums/tuples:
- size/alignment,
- field offsets,
- tag encoding,
- ABI passing mode.

Future backends consume the same layout metadata.

**Layout stability rule:** Field reordering for alignment/cache
optimization is opt-in only (`@packed`, `@reorder`, or similar).
Default struct layout preserves declaration order. Rationale:

- FFI interop (`extern "C"` structs) requires stable, predictable
  layout. Global reordering would break C ABI compatibility.
- `@unboxed` types used in FFI must have deterministic field
  offsets that match C struct layout.
- Serialization/deserialization assumes stable field order unless
  the format is self-describing.
- Debug tooling needs predictable layout for memory inspection.

The compiler MAY reorder fields internally for non-FFI, non-
`@unboxed` structs when an explicit annotation opts in. But the
default is: declaration order = memory order. This is the same
rule Rust uses (`repr(Rust)` is unspecified but `repr(C)` is
stable) — except Kea defaults to the stable side.

### 5) Pass pipeline observability

Each pass should emit machine-readable stats:
- instruction counts by op class,
- retain/release counts before/after optimization,
- allocations and CoW branch counts,
- handler classification counts (tail/non-tail/zero-resume),
- compile-time spent per pass.

Without this, performance work becomes guesswork.

### 6) Backend interface trait

Define a narrow backend interface now:
- input: validated MIR + layout tables + target config,
- output: object code / executable image + diagnostics + stats.

Cranelift is one implementation of this interface, not the interface.

## Benchmark Suite (Required)

Create a benchmark corpus with fixed inputs and harness automation:

1. Pure numeric loops
2. String/collection transforms
3. Effect-heavy pipelines (IO + Fail + Log-like handlers)
4. Actor/message throughput + mailbox pressure
5. Compiler-like workloads (AST/type inference style allocations)

Track:
- throughput,
- latency percentiles,
- allocation and retain/release counts,
- compile-time.

### Actor Benchmark Targets (0e+)

Actor performance must be benchmarked against Go and Erlang
baselines, not claimed narratively. Targets are directional —
exact thresholds set after initial measurement.

| Metric | Measure | Compare against |
|--------|---------|-----------------|
| Message throughput | msgs/sec, 2 actors ping-pong | Go channels, Erlang `!` |
| Message latency | p50/p99 single message RTT | Go channels, Erlang `!` |
| Actor spawn cost | time + memory per actor creation | Go goroutine, Erlang spawn |
| Memory per actor | bytes, idle actor with minimal state | Go goroutine (~2KB), Erlang (~300B) |
| Actor count ceiling | max actors before OOM/degradation | Go (~100K), Erlang (~1M) |
| Throughput scaling | msgs/sec vs core count | Linear is target |

Expected positioning: Kea actors will be heavier than Erlang
processes (~KB range, not ~300B) but faster per-message (native
code, zero-copy immutable sharing, non-atomic RC for single-
threaded actors). Closer to Go goroutines in weight, closer to
Erlang in programming model.

These benchmarks land in 0e when the actor runtime exists. They
feed into the benchmark regression suite alongside the 0d pure
baselines.

## Roadmap Placement

1. **0d:** establish MIR contract + backend interface + initial benches.
2. **0e:** handler performance classification + direct-call fast paths.
3. **0f:** ownership/reuse optimization counters and gates.
4. **Phase 1:** self-host compiler perf gates.
5. **Phase 2-3:** optional LLVM release backend evaluation; optional
   Kea-native backend spike on one architecture.

## Decision Framework: LLVM vs Kea-native backend

Use measured criteria:

1. Runtime performance gain from LLVM on target workloads.
2. Build/install complexity and maintenance cost.
3. Time-to-value versus deep Kea-native optimizations on MIR ops.

Do not commit to a backend transition based on anecdotal microbenchmarks.

## Testing and Gates

CI gates should include:

1. No >N% regression on benchmark medians (per class).
2. No >N% regression in compile-time for self-host/compiler workloads.
3. Retain/release and allocation counters trend non-regressive on
   ownership-sensitive benchmarks.

Thresholds should begin permissive and tighten as measurements stabilize.

## Non-Goals (v0-v1)

- Beating Rust/C universally.
- Multi-architecture native backend from day one.
- Heroic whole-program optimization before semantics are stable.

## Open Questions

- Should we keep Cranelift for `kea run` and use LLVM or native backend
  for `kea build --release`?
- Which architecture should be first for a native backend spike
  (arm64 vs x86_64)?
- How much handler/evidence metadata should survive into late lowering
  for optimization without bloating compile-time?
