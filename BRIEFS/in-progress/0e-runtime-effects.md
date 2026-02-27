# Brief: Runtime Effects

**Status:** active
**Priority:** v1-critical
**Depends on:** 0d1-module-system (needs module system for stdlib imports)
**Blocks:** 0f-memory-model (step 7), Phase 1
**Also read before implementing:**
- [performance-backend-strategy](../design/performance-backend-strategy.md) — Effect ops must be classified MIR ops (capability-direct, handler-dispatch, zero-resume). Handler inlining benchmark gate (within 2x of parameter-passing). Actor benchmark targets.
- [testing](testing.md) — Effect-heavy pipeline benchmark is a 0e deliverable. CI regression gates on 0d baselines.

## Motivation

This is the highest-risk phase. We have effect declarations,
handler typing, and Fail sugar from 0c. We have Cranelift codegen
for pure programs from 0d. Now we need effects to actually *work*
at runtime — handler compilation, the IO runtime, and arena
allocation.

The handler compilation strategy determines Kea's performance
ceiling for effectful code. Getting this wrong means effectful
code is slow, which means effects become a tax rather than an
organizing principle. The whole vision depends on effects being
cheap enough that people use them everywhere.

## The Core Decision: Handler Compilation Strategy

**Decision: Evidence passing.** The three-way prototype (evidence
vs CPS vs setjmp/longjmp) from the original brief was the right
framing, but Koka's production experience and our MIR scaffolding
both point to evidence passing as the clear winner. CPS causes
code bloat and destroys natural stack structure. setjmp/longjmp
is platform-specific and only wins for non-tail-resumptive handlers
— which Kea's at-most-once resumption makes rare. Evidence passing
is simple, composable, and optimisable.

**Koka reference:** Leijen's "Type Directed Compilation of
Row-Typed Algebraic Effects" (2017). Evidence is a vector of
handler frames threaded through effectful calls.

The key insight is that **most handlers don't need the full
machinery**. The tiered strategy below exploits this:

### Tier 1: Zero-resume (Fail) — Result-passing

`Fail.fail(e)` compiles to `return Err(e)`. `catch` compiles to
match on Result. `?` compiles to branch-on-error. No continuations,
no evidence, no stack manipulation. Just control flow.

Coverage: every program with error handling (~100% of real code).

### Tier 2: Tail-resumptive + statically known — inlined evidence

~80%+ of real handlers: State.get, State.put, Log.log, Reader.ask.
The handler body runs, then `resume` is the last expression. These
compile as direct function calls with the handler body inlined at
each operation site. No closure allocation, no indirect call, no
evidence lookup.

```
-- Source:
handle computation()
  State.get() -> resume current_state
  State.put(s) ->
    current_state = s
    resume ()

-- After inlining: State.get() → read local, State.put(s) → write local
-- Identical codegen to manually threading state as a parameter
```

Coverage: State, Log, Reader, Writer, Emit, and most user effects.

### Tier 3: Tail-resumptive + dynamically dispatched — evidence vtable

When the handler is not statically known (effect-polymorphic code,
handler passed through a function boundary), evidence is a vtable-like
struct threaded as a hidden parameter. Each effect operation becomes
an indirect call through the evidence struct.

```
-- Conceptually:
fn computation(ev_state: &StateEvidence<Int>) -> Int
  ev_state.get()           -- indirect call
  ev_state.put(new_val)    -- indirect call
```

Coverage: higher-order effectful functions, library abstractions.

### Tier 4: Non-tail-resumptive — one-shot continuations

The rare case where `resume` appears in non-tail position. Because
Kea enforces at-most-once resumption (KERNEL §5.7), the continuation
is a **one-shot closure** — no stack copying needed. The continuation
captures the stack frame from the operation site to the handler.

Implementation: `setjmp` at handler install, `longjmp` at perform,
`resume` calls the saved continuation exactly once using the
original stack.

Coverage: exotic handlers (coroutine-style yield, backtracking with
commit). Rare enough to defer until Tiers 1-3 are solid.

### Coverage estimate

| Tier | Mechanism | Real-world coverage |
|------|-----------|-------------------|
| 1 | Result-passing | ~100% (Fail) |
| 2 | Inlined evidence | ~80% of remaining handlers |
| 3 | Evidence vtable | ~15% of remaining handlers |
| 4 | One-shot continuation | ~5% of remaining handlers |

Tiers 1+2 cover ~95%+ of actual handler usage. Tier 3 covers
the polymorphic case. Tier 4 can ship later without blocking
real programs.

## What transfers from Rill / what 0d built

**rill-codegen** (cannibalised in 0d): Cranelift function
compilation, ISA config, JIT + AOT pipelines. No direct handler
transfer (rill has no effects).

**rill-eval** (structural reference): The evaluator's stdlib
provides behavioral reference for IO operations.

**MIR scaffolding from 0d (already landed):**
The MIR already has the effect IR nodes we need:
- `MirInst::EffectOp { class, effect, operation, args, result }`
  — classified as `Direct`, `Dispatch`, or `ZeroResume`
- `MirInst::HandlerEnter { effect }` / `HandlerExit { effect }`
  — handler scope markers
- `MirInst::Resume { value }` — resume instruction
- `MirEffectOpClass` enum with `is_handler_op()` helper
- Codegen stats tracking: `effect_op_direct_count`,
  `effect_op_dispatch_count`, `effect_op_zero_resume_count`,
  `handler_enter_count`, `handler_exit_count`, `resume_count`
- Fail/ZeroResume path partially wired (codegen validates
  `ZeroResume` class on Fail operations)
- Non-effect MIR ops (`EffectOp`, `HandlerEnter`, `HandlerExit`,
  `Resume`) currently return `UnsupportedMir` in codegen — these
  are the stubs 0e fills in.

**This means 0e starts from a working MIR representation, not
from scratch.** The job is wiring codegen for each tier, not
designing the IR.

## Entry Gate: IO Granularity Decision

Before implementation begins, decide and lock the standard effect
surface granularity. The [effects-platform-vision](../design/effects-platform-vision.md)
argues IO must be decomposed into separate capability effects:

| Effect | Scope |
|--------|-------|
| `IO` | File read/write, stdout/stderr |
| `Net` | Network connections, HTTP, DNS |
| `Clock` | System time, monotonic clock |
| `Rand` | Random number generation |

This decision affects handler compilation, the runtime effect set,
and every downstream brief. It must be explicit — not drift in
during implementation.

**Decision: Option A — decomposed from day one.** IO + Net + Clock +
Rand are separate effects from Step 2 onward. The handler compilation
machinery gets tested against multiple concrete effects from the start,
and the platform vision's policy-as-code capabilities depend on this
split. No "monolithic then decompose" path — that just means re-testing
every handler path against 4 separate effects later.

## Implementation Plan

Steps are ordered by tier — each tier is independently shippable
and covers a wider slice of real programs. The agent implementing
0e should ship each step end-to-end (MIR lowering → codegen →
test) before moving to the next.

### Step 1: Fail / ZeroResume end-to-end (Tier 1)

Complete the partially-wired Fail path in codegen. The MIR already
classifies `Fail.fail(e)` as `EffectOp { class: ZeroResume }`.
Wire it through to Cranelift:

- `Fail.fail(e)` → early return with error tag (Result-passing)
- `catch expr` → branch on return tag, extract Ok/Err
- `?` → branch-on-error, propagate Err or unwrap Ok
- `MirInst::HandlerEnter/Exit { effect: "Fail" }` → no-op
  (Fail doesn't install runtime handler frames)

**Milestone:** First Kea program with error handling compiles
and runs natively. This is the "hello world with errors" moment.

Test: `fn main() -> Result(Int, String) = catch(|| -> ...)`
produces correct Ok/Err values.

### Step 2: Capability-direct effects (Tier 1)

Capability-direct effects have no user-defined handlers — their
handler IS the runtime. No evidence passing, no dispatch.
`MirEffectOpClass::Direct` maps to direct function calls into
thin runtime shims.

Implement all four capability effects as separate `Direct` effects:

**IO** (file/console):
- `IO.stdout(msg)` → `libc::write(1, ...)`
- `IO.stderr(msg)` → `libc::write(2, ...)`
- `IO.read_file(path)` → `libc::read` wrapper
- `IO.write_file(path, data)` → `libc::write` wrapper

**Net** (network):
- `Net.connect(addr)` → socket connect wrapper
- `Net.listen(addr)` → socket bind/listen wrapper
- `Net.send(conn, data)` → socket send wrapper
- `Net.recv(conn, size)` → socket recv wrapper

**Clock** (time):
- `Clock.now()` → `clock_gettime(CLOCK_REALTIME)`
- `Clock.monotonic()` → `clock_gettime(CLOCK_MONOTONIC)`

**Rand** (randomness):
- `Rand.int(lo, hi)` → arc4random/getrandom wrapper
- `Rand.float()` → [0,1) uniform via getrandom
- `Rand.bytes(n)` → getrandom wrapper

The runtime installs capability handlers around `main()`. Unhandled
effects at the main boundary (other than capability effects and Fail)
are a compile error (already enforced by 0c). Programs declare exactly
the capabilities they need: `fn main() -[IO, Net]> Unit`.

Stdlib layout: `io.kea`, `net.kea`, `clock.kea`, `rand.kea` — four
files, each with their own effect declaration and `Direct` operations.

**Milestone:** `kea run hello.kea` prints "Hello, world!" to
stdout. First effectful compiled program.

### Step 3: Evidence passing for tail-resumptive handlers (Tier 2)

The core handler compilation. Implement evidence passing for
user-defined effects, starting with the State effect:

```kea
effect State S
  fn get() -> S
  fn put(_ new_state: S) -> Unit

fn count_to(_ n: Int) -[State Int]> Int
  let i = State.get()
  if i >= n
    i
  else
    State.put(i + 1)
    count_to(n)
```

Evidence representation:
- Each effect gets an evidence struct (one closure per operation)
- `HandlerEnter` creates the evidence struct from handler clauses
- Effectful functions receive evidence as hidden parameters
- `EffectOp { class: Dispatch }` calls through evidence

Handler clause classification (at MIR lowering time):
- **Tail-resumptive:** `resume` is the last expression → compile
  handler body as a direct function, `resume` = return value
- **Zero-resume:** no `resume` → compile as early return (Step 1)
- **Non-tail-resumptive:** `resume` in non-tail position → error
  for now ("non-tail-resumptive handlers not yet supported"),
  implement in Step 7

**Benchmark immediately:** `with_state(0, || -> count_to(1_000_000))`
vs equivalent pure parameter-passing code. Target: < 10x overhead
for the unoptimized evidence path.

### Step 4: Handler inlining / devirtualization (Tier 2 optimized)

When a handler is statically known and tail-resumptive, inline
the handler body at each operation site:

```kea
-- before inlining:
handle computation()
  State.get() -> resume current_state
  State.put(s) ->
    current_state = s
    resume ()

-- after inlining: State.get() becomes "read local"
-- State.put(s) becomes "write to local"
-- no evidence struct, no indirect call, no closure allocation
```

This is a MIR optimization pass:
1. Identify `HandlerEnter`/`HandlerExit` pairs where the handler
   is visible (not passed through a function boundary)
2. For each `EffectOp { class: Dispatch }` in the handler scope,
   replace with the inlined handler body
3. Eliminate the evidence struct entirely

**Benchmark gate:** State effect tight loop with inlined handler
must be within 2x of equivalent parameter-passing code. Stretch
goal: within 1.2x.

**Pass stats:** report handlers inlined vs dispatched, per function.
This is how we know the optimization is firing.

This is an explicit 0e deliverable, not a stretch goal. If handler
dispatch is measurably slower than function calls for the common
case, the programming model doesn't work.

### Step 5: Handler nesting and scoping

Multiple handlers compose correctly:

```kea
handle
  handle computation()
    State.get() -> resume current_state
    State.put(s) -> ...
  Log.log(level, msg) ->
    IO.stdout("[{level}] {msg}")
    resume ()
```

Inner handler shadows outer for the same effect. Evidence passing
handles this naturally — the innermost `HandlerEnter` for an
effect provides the evidence, outer evidence is shadowed.

Test matrix:
- Nested handlers for different effects
- Inner handler shadows outer for same effect
- Handler body performs a different effect (handler adds effects)
- Handler body re-performs the handled effect (goes to outer handler)

### Step 6: ~~IO decomposition~~ — ABSORBED INTO STEP 2

IO decomposition is no longer a separate step. IO/Net/Clock/Rand
are separate effects from Step 2 onward (see Entry Gate decision).
The stdlib layout is `io.kea`, `net.kea`, `clock.kea`, `rand.kea` —
four files, each with their own effect declaration and Direct-compilation
operations. The 0d1 intrinsic set needs `__kea_clock_now`,
`__kea_clock_monotonic`, `__kea_rand_int`, `__kea_rand_float`,
`__kea_rand_bytes`, `__kea_net_connect`, `__kea_net_listen`,
`__kea_net_send`, `__kea_net_recv` alongside the existing IO intrinsics.

### Step 7: `then` clause on handle expressions

The `then` clause (KERNEL §5.14) runs when the handled body completes
normally. `catch` already desugars to a handler with a `then` clause
(landed in 0d), but the general form is needed for handlers that
transform the body's return value:

```kea
handle computation()
  State.get() -> resume current_state
  State.put(s) ->
    current_state = s
    resume ()
then result ->
  (result, current_state)
```

This is the general form of what `catch` already does. Implementation
is incremental on top of the existing handler frame work — the `then`
body runs after `HandlerExit` with the body's return value bound.

**Interaction with evidence passing:** The evidence struct contains
one closure per operation. The `then` clause is a completion callback
that transforms the handler's return value. In the evidence
representation, `then` is a separate field — not an operation closure.
When `HandlerExit` fires, the runtime checks for a `then` callback
in the handler frame: if present, apply it to the body's return value
before returning to the handler's caller. If absent, return the body's
value directly (the `catch` desugaring from 0d is the special case
where `then` wraps in `Ok`). The implementing agent should design
the evidence struct with a `then: Option<Closure>` field from the
start, even though Steps 1-5 don't use it — retrofitting it later
means revisiting every handler frame layout.

**In scope for 0e.** Without `then`, you can't write handlers that
return accumulated state alongside the computation result (the State
handler above needs it to return the final state).

### Step 8: Non-tail-resumptive handlers (Tier 4) — DEFERRABLE

One-shot continuations for the rare case where `resume` is in
non-tail position. Because Kea enforces at-most-once resumption,
the continuation is one-shot — no stack copying.

Implementation: `setjmp` at handler install, `longjmp` at perform,
`resume` calls the saved continuation using the original stack.

**This step can ship after 0f.** Tiers 1-3 cover 95%+ of real
handler usage. Non-tail-resumptive handlers are exotic (coroutine
yield, backtracking with commit). Emit a clear error message
("non-tail-resumptive handlers not yet supported") until this
lands.

### Step 9: Arena allocation (Alloc effect) — DEFERRED to post-0f

The `Alloc` effect (KERNEL §5.9, §12.7). Deferred until the
memory model (0f) clarifies Unique type interactions. For now,
`Alloc` is a no-op effect that type-checks but doesn't change
allocation behavior.

## Testing

**Per-tier tests (each step ships with tests):**

Tier 1 (Fail/IO):
- `Fail.fail(e)` produces correct Err value at runtime
- `catch` converts effectful code to Result
- `?` propagates errors, unwraps Ok
- Nested `catch` blocks compose correctly
- `IO.stdout("hello")` produces output
- `IO.read_file` / `IO.write_file` round-trip
- Unhandled non-IO effect at main → compile error (0c, verify)

Tier 2 (tail-resumptive handlers):
- State get/put: counter accumulation produces correct value
- Log handler: collects log entries into a list
- Reader handler: provides read-only context
- Handler body effects correctly added to outer scope
- Resume value correctly returned to operation call site
- Handler with multiple operations: all operations handled

Tier 2 optimized (inlining):
- Same behavioral tests as Tier 2 (inlining must be transparent)
- Benchmark: State tight loop within 2x of parameter passing
- Pass stats: verify inlining fires for statically-known handlers

Handler composition:
- Nested handlers for different effects
- Inner handler shadows outer for same effect
- Handler body re-performs handled effect (goes to outer handler)
- Three-deep nesting: State inside Log inside IO

**Microbenchmarks (added to kea-bench):**
- `state_count_to_1M`: State effect tight loop
- `state_count_to_1M_manual`: equivalent pure parameter-passing
- `fail_propagation_depth_N`: Fail through N call frames
- `io_stdout_throughput`: IO.stdout in tight loop

## Definition of Done

**Core (must ship):**
- Fail/ZeroResume compiles end-to-end (Result-passing)
- IO works (stdout, stderr, file read/write)
- `kea run hello.kea` prints output — first effectful compiled program
- User-defined tail-resumptive handlers compile via evidence passing
- Handler inlining fires for statically-known tail-resumptive handlers
- Handler nesting and scoping work correctly
- Non-tail-resumptive handlers produce a clear "not yet supported" error

**Performance gates:**
- State effect tight loop with inlined handler: within 2x of
  parameter-passing equivalent (stretch: 1.2x)
- Fail/catch overhead: within 1.5x of hand-written Result code
- IO.stdout: within 2x of direct libc write

**Infrastructure:**
- Benchmark suite extended: effect-heavy pipeline added to 0d's
  baseline harness
- CI regression gates enabled on 0d baselines (no >N% regression
  on existing benchmarks, thresholds start permissive)
- Pass stats report: handlers inlined vs dispatched, per function
- `mise run check-full` passes

## Decisions

- **Refcount atomicity: scope model, non-atomic only in 0e.**
  Non-atomic refcounts by default. The current function's effect set
  determines atomicity of new allocations — no concurrency effects
  (Send, Spawn, Par) means non-atomic. Since 0e doesn't include
  actors, **0e wires the non-atomic path only.** Everything is
  non-atomic until actors land (post-0f), at which point the atomic
  path and promotion at Send.tell / Spawn.spawn / Par.map boundaries
  are added. No point building the atomic branch before the effects
  that trigger it exist. Values crossing thread boundaries are promoted
  to atomic at the Send.tell / Spawn.spawn / Par.map boundary.

  Scope model (not infection model): atomicity is determined by
  the current function's effect set, not the provenance of input
  values. A pure function processing actor-received data allocates
  non-atomic intermediaries. Existing atomic refcounts on inputs
  remain atomic (can't downgrade), but new allocations are
  non-atomic. This means mixed atomic/non-atomic values in the
  same data structure — handled by a per-value flag that determines
  `add` vs `lock xadd` on retain/release. The flag overhead is
  trivial (one bit per allocation header).

  This matters because single-threaded code (most code) should
  pay zero atomic overhead. The effect system gives the compiler
  the information to make this decision per-function, for free.

- **Lazy runtime activation.** No thread pool or scheduler spins
  up unless the program's effect set includes Send, Spawn, or Par.
  A program with only `-[IO]>` runs on the main thread like a C
  program. The runtime exists but is dormant until concurrency
  effects are used. Specified in KERNEL §20 (pending).

- **Effect signatures are scheduling hints, not policy truth.**
  The effect row tells the scheduler a function's *capability
  class* (CPU-bound pure, IO-bound, concurrent). The scheduler
  may use this as a hint for thread pool assignment or priority.
  But dynamic behavior can differ from static signatures — a
  function with `-[IO]>` might do one syscall then spend 99%
  of its time computing. The scheduler must observe actual
  behavior (wall time, yield frequency) and adapt. Effect hints
  bootstrap scheduling decisions; runtime telemetry corrects
  them. Never treat the effect signature as ground truth for
  scheduling policy.

- **Par effect for data parallelism.** Separate from actor
  concurrency. Par.map requires a pure callback (`-> B`). The
  compiler verifies safety via the effect signature, codegen
  decides strategy (chunk size, thread count, work-stealing).
  Distinct from Enum.concurrent_map which uses actors for
  IO-bound work. Based on Rill's Par design.

- **Backpressure is a mailbox property, not an effect handler.**
  `Send.tell` is a direct runtime call (§5.15 capability effect).
  Backpressure is configured at spawn time via mailbox type:
  `Bounded N` (block/error when full), `Unbounded`, `Dropping N`
  (drop oldest). The receiver owns its mailbox policy — the sender
  doesn't know or care. This keeps `Send` as a cheap direct call
  and avoids compositionality problems where backpressure behavior
  depends on handler scope rather than target actor. Full mailbox
  surfaces as a `Fail` to the sender via normal error handling.

- **Capability effects (Send, IO, Spawn) compile to direct
  runtime calls when not intercepted.** In production, these
  compile per §5.15 — no continuation capture, no evidence
  lookup, no closure allocation. User handlers for capability
  effects are legal and type-check normally, enabling test
  mocks (e.g., intercepting IO to test file operations without
  touching the filesystem). The direct-call path is a codegen
  optimisation: when no user handler is installed for a
  capability effect, the compiler emits a direct runtime call.
  When a handler is installed (testing), it goes through the
  normal handler machinery. This preserves the zero-cost
  production guarantee while keeping effects compositional
  for testing. Backpressure, rate limiting, and circuit breaking
  remain runtime/mailbox/library concerns, not handler
  composition.

## Backend Portability Constraint

Effect operations are already represented as classified MIR ops
(landed in 0d). The MIR encodes:
- Operation class: `MirEffectOpClass::Direct` / `Dispatch` / `ZeroResume`
- Handler scope: `HandlerEnter` / `HandlerExit` markers
- Resume: `MirInst::Resume { value }`
- Codegen stats tracking per class

**Extend for 0e:** Add handler classification metadata to MIR:
- `MirHandlerClass::TailResumptive` / `NonTailResumptive` / `ZeroResume`
  (computed at MIR lowering from AST handler clause analysis)
- Evidence parameter slots: abstract (not Cranelift ABI-specific)
- Inlining eligibility flag: statically-known + tail-resumptive

The Cranelift backend lowers these classified ops. A future backend
could use a different strategy for the same MIR.
See [performance-backend-strategy](performance-backend-strategy.md).

## Stdlib Tier 1: Effects

When 0e lands, the stdlib grows with effect-using modules. These are
written in Kea and compiled by the bootstrap compiler — see
[stdlib-bootstrap](stdlib-bootstrap.md) for the full plan.

```
stdlib/
  io.kea           -- IO effect: stdout, stderr, read_file, write_file
  state.kea        -- State effect + with_state handler
  log.kea          -- Log effect + stdout/collect handlers
  reader.kea       -- Reader effect + with_reader handler
  test.kea         -- assert (Fail-based), basic test utilities
```

**~300-500 lines.** IO wraps `@intrinsic` runtime functions. State,
Log, and Reader handlers are pure Kea — the first real validation
that handler compilation works end-to-end.

**Net scope for 0e:** 0e ships raw TCP primitives only (`Net.connect`,
`Net.send`, `Net.recv`, `Net.listen`). The HTTP client (`http.kea`)
is listed as Tier 1 in the stdlib brief and is pure Kea code that
wraps Net operations — someone needs to write it, but it's a stdlib
deliverable that lands alongside 0e, not a 0e implementation step.
The 0e agent's job is to make the Net intrinsics work; the HTTP
client is a separate task that exercises them.

## Open Questions

*(None remaining — see Resolved Questions.)*

## Resolved Questions

- **Tail-resumptive handlers:** Yes, support specially (Step 2.5
  above). This is the single most important performance
  optimisation. ~80%+ of handlers are tail-resumptive in practice.

- **Handler inlining for statically known handlers:** Yes, as a
  follow-on optimisation after the basic handler compilation works.
  When `with_state(0, || -> body)` is visible, inline the State
  operations directly. This is a natural extension of evidence
  passing — if the evidence is a compile-time constant, inline it.

- **Capability effects interceptability:** Capability effects (IO,
  Send, Spawn) are ordinary effect labels in the type system.
  Handlers for them type-check normally (enabling test mocks).
  Direct-call compilation is a codegen optimisation, not a type
  system restriction. See Decisions section above.

- **Capability effect dual-path compilation (IMPORTANT):** The
  compiler must decide per-callsite whether a capability effect
  operation (e.g., `IO.read_file`) goes through the direct runtime
  call or through a user handler. The decision rule: at MIR lowering
  time, check whether there is a `HandlerEnter` for this effect in
  the current scope. If yes → `EffectOp { class: Dispatch }` (route
  through handler evidence). If no → `EffectOp { class: Direct }`
  (direct runtime call). This is a **codegen correctness** decision,
  not just a performance optimization. When a user writes
  `handle f() with IO.read_file(path) -> resume fake_data`, all IO
  operations inside `f()` must go through the handler. IO operations
  outside that handler scope must still be direct. The scoping of
  this decision is critical — get it wrong and test mocks don't
  work or production code pays handler overhead unnecessarily.

- **Cranelift calling convention interaction:** Evidence passing
  adds hidden parameters to effectful functions. Cranelift handles
  this naturally — evidence structs are pointer-sized arguments in
  the standard calling convention. No ABI changes needed. For the
  inlined case, evidence parameters are eliminated entirely by
  the MIR optimization pass before Cranelift sees the code.

- **Handler compilation strategy:** Evidence passing (see "Core
  Decision" section). The three-way prototype is unnecessary —
  Koka's production experience validates evidence passing, and
  Kea's at-most-once resumption makes CPS/setjmp advantages
  negligible. Ship evidence passing, optimize with inlining.

- **`@with` annotation deferred to 0h.** The `@with` annotation
  (KERNEL §10.6) marks handler-shaped functions for implicit handler
  installation at call sites. This is sugar, not plumbing — it changes
  how the function is called, not how it's compiled. Stdlib Tier 1
  handlers use explicit `handle`/`with` blocks. `@with` lands with
  the rest of the annotation system in 0h.

- **Handler composition uses nested `handle` blocks, not `with`
  syntax.** `with` is not special syntax — it is (or will be) a
  stdlib function. In 0e, the only mechanism for composing multiple
  handlers is nested `handle` blocks. The implementing agent should
  NOT add `with` as a language keyword or special form. Ergonomic
  handler composition (via a `Par` stdlib module or similar) depends
  on the `Eff` kind from 0g for proper typing.

- **`then` clause in scope for 0e.** The `then` clause on `handle`
  expressions (KERNEL §5.14) is the general form of the `catch`
  desugaring already landed in 0d. Needed for handlers that transform
  the body's return value (e.g., State handler returning final state
  alongside result). See Step 7.

## Progress

- 2026-02-27 19:08: Activated 0e brief and started runtime-effects implementation lane. First compiled-path scaffolding landed in `kea-codegen`: `MirInst::HandlerEnter/HandlerExit` lower as explicit no-op instructions (preserve scope markers in MIR without tripping pure-lowering unsupported errors), while `MirInst::Resume` now fails with a precise non-tail-resumptive unsupported diagnostic.
- 2026-02-27 19:10: Added codegen regression coverage for the new behavior:
  `cranelift_backend_allows_handler_scope_markers_as_noop` and
  `cranelift_backend_reports_non_tail_resume_not_supported`. Targeted package checks are green for `kea-codegen`.
- 2026-02-27 19:17: Expanded Tier-1 capability-direct IO coverage with `IO.stderr` end-to-end support. MIR now lowers `IO.stderr(...)` calls to `MirEffectOpClass::Direct`; Cranelift lowering handles direct `IO.stderr` via `strlen + write(fd=2, ...)`; and tests now cover MIR lowering, codegen compile-path support, JIT run-path success, and AOT stderr output capture.
- 2026-02-27 19:28: Restored compiled-path usability of `?` fail sugar by removing hard dependency on unresolved `From.from` desugaring in the parser. `expr?` now propagates `Err(e)` via direct `fail e` desugar in bootstrap mode. Added execute-path regressions for both `?` fail propagation and ok passthrough under `catch`.
- 2026-02-27 19:42: Fixed module/effect propagation for imported effect modules (real fix, no wrappers): effect operations declared in a source module are now also registered under that module path for qualified resolution (`use IO` now enables `IO.stdout` / `IO.stderr` in importing modules). Added real `stdlib/io.kea` effect module and execute-path integration test `compile_and_execute_real_stdlib_io_module_exit_code`.
- 2026-02-27 18:35: Added direct `Clock.now` capability lowering end-to-end on the compiled path. MIR now lowers `Clock.now()` to `MirEffectOpClass::Direct` with an Int result, codegen imports and lowers through libc `time(NULL)`, and coverage includes MIR lowering, codegen compile-path support, and execute-path CLI regression (`compile_and_execute_clock_now_direct_effect_exit_code`).
- 2026-02-27 18:39: Extended direct `Clock` capability coverage with `Clock.monotonic()` on the compiled path. MIR now lowers both `Clock.now` and `Clock.monotonic` as direct effect ops; codegen lowers both via imported libc `time`; and tests now cover MIR lowering, codegen compile-path checks, inline source execution, plus real-stdlib import execution via new `stdlib/clock.kea`.
- **Next:** continue Step 2 capability-direct expansion by adding `Rand` and `Net` operation lowering paths (with stdlib effect modules and execute-path integration tests) while keeping wrappers out of stdlib effect modules.
