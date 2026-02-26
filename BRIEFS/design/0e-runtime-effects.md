# Brief: Runtime Effects

**Status:** design
**Priority:** v1-critical
**Depends on:** 0d-codegen-pure (needs working codegen pipeline)
**Blocks:** 0f-memory-model, 0g-advanced-types, Phase 1

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

Three options (ROADMAP §0e). Must prototype and benchmark before
committing.

### Option 1: Evidence Passing

Handlers compiled as closures passed through the call stack.
Each effect operation looks up its handler via an evidence
parameter threaded through function calls.

```
-- Conceptually: every effectful function gets an extra
-- "evidence" parameter containing handler implementations
fn process(order, evidence_log, evidence_tx, evidence_fail) -> ...
```

**Pros:** Simple to implement. Low overhead for simple handlers.
Well-understood (Koka uses this for many cases). Handlers are
just function calls — no stack manipulation.

**Cons:** Every effectful function call passes extra arguments.
Polymorphic effect variables (`e`) become dynamically dispatched
via vtable-like evidence records. Deep call stacks accumulate
evidence parameters.

**Koka reference:** Leijen's "Type Directed Compilation of
Row-Typed Algebraic Effects" (2017). Evidence is represented as
a vector of handler frames.

### Option 2: CPS Transform

Effectful code is CPS-transformed at compile time. Handlers
receive the continuation (the rest of the computation).

```
-- Conceptually: effect operations pass a continuation
fn process_cps(order, k_log, k_tx, k_fail) -> ...
```

**Pros:** Clean semantics. Resume is just calling the
continuation. Zero-resumption (Fail) is just not calling it.
No runtime stack manipulation.

**Cons:** Code bloat — CPS transform can significantly increase
code size. Loss of natural stack structure makes debugging harder.
Every function boundary becomes a continuation allocation.

### Option 3: Segmented Stacks / setjmp-longjmp

Handlers install frames on the stack. Effect operations jump
to the handler frame, optionally capturing the intervening
stack for resumption.

```
-- Conceptually: handlers save stack state, operations longjmp
install_handler(Log, handler_fn)
  ...body...
-- Log.log() longjmps to handler, handler can resume
```

**Pros:** Potentially fastest for the common case (handler
is nearby on the stack). Natural stack structure preserved.
Familiar to C programmers (setjmp/longjmp).

**Cons:** Platform-specific. Harder to implement correctly.
Capturing stack for resumption requires copying or segmenting.
At-most-once resumption simplifies this (no need to copy for
multi-shot), but it's still the most complex option.

### Recommendation

Prototype all three on a microbenchmark: a tight loop performing
a `State` effect (get/put). Measure:
- Handler installation cost
- Effect operation cost (common path)
- Evidence/continuation passing overhead on deep call stacks
- Code size impact

**Likely winner:** Evidence passing for the common case (simple
effects, shallow stacks), with potential optimisation to inline
handler bodies for known-static handlers. Koka's experience
suggests this is practical. Start with evidence passing, measure,
optimise.

## What transfers from Rill

**rill-codegen** (already cannibalised in 0d):
- Cranelift function compilation extends to handle evidence
  parameters or CPS-transformed code
- No direct transfer for handler compilation (rill has no effects)

**rill-eval** (structural reference):
- The evaluator's stdlib provides behavioral reference for IO
  operations (file IO, stdout, clock, network)
- Actor runtime patterns inform how Send/Spawn could work
  (conceptual reference only — Kea actors are library-level)

## Implementation Plan

### Step 1: Prototype handler strategies

Three minimal prototypes, each implementing the State effect:

```kea
effect State S
  fn get() -> S
  fn put(_ new_state: S) -> ()

fn count_to(_ n: Int) -[State Int]> Int
  let i = State.get()
  if i >= n
    i
  else
    State.put(i + 1)
    count_to(n)
```

Benchmark: `with_state(0, || -> count_to(1_000_000))`

Measure execution time, code size, and implementation complexity.
Pick the winner.

### Step 2: IO runtime handler

The `IO` effect is special — its handler is the runtime itself.
Implement:
- `IO.stdout(msg)` → write to stdout
- `IO.read_file(path)` → read file bytes
- `IO.write_file(path, data)` → write file
- `IO.clock_now()` → system timestamp

The IO handler is installed by the runtime around `Main.main()`.
Any unhandled effects at the main boundary (other than IO) are
a compile error (already enforced by 0c).

### Step 2.5: Tail-resumptive handler optimisation

Most handlers call `resume` as the last thing in the handler
body: `Log.log` logs and resumes, `State.get` reads state and
resumes, `State.put` writes state and resumes. These are
**tail-resumptive** handlers.

A tail-resumptive handler doesn't need continuation capture. It
can compile as a direct call: perform the handler body, then
return the resume value — no stack manipulation, no closure
allocation, no evidence lookup on the hot path.

Classify each handler clause at compile time:
- **Tail-resumptive:** `resume` is the last expression. Compile
  as a direct function call. This is the common case (~80%+ of
  handlers in practice).
- **Non-tail-resumptive:** `resume` appears in non-tail position
  (e.g., `let x = resume(); process(x)`). Needs the full handler
  compilation machinery.
- **Zero-resumption:** no `resume` at all (Fail). Compile as
  early return / Result-passing (see Step 3).

Koka optimises tail-resumptive handlers aggressively and this
is the single most important performance optimisation for
making effects cheap. Prioritise getting this right.

### Step 3: Fail compilation (optimised path)

`Fail` is the most common effect. It deserves an optimised
compilation:
- `Fail.fail(e)` can compile to Result-passing (return Err)
  rather than going through the general handler mechanism
- `catch` compiles to a simple match on the Result
- `?` compiles to a branch-on-error

This is a special case: because Fail's handler never resumes,
it's equivalent to Result propagation. We can recognise this
statically and bypass the general handler machinery.

### Step 4: User-defined effect compilation

General handler compilation for arbitrary effects using the
chosen strategy from Step 1. This handles:
- `Log`, `State S`, `Rand`, `Tx`, and any user-defined effect
- Handler installation
- Effect operation dispatch to installed handler
- Resume mechanics (passing value back to operation call site)
- Nested handlers (inner handler shadows outer for same effect)

### Step 5: Arena allocation (Alloc effect)

The `Alloc` effect (KERNEL §5.9, §12.7):
- `with_arena` handler creates a bump allocator
- Inside the handler, all heap allocations go to the arena
- On handler exit: deep-copy the return value to caller's
  allocation context, then free the arena in bulk

This is the riskiest piece. Key concerns:
- How does the compiler know which allocations to redirect?
  (Via the Alloc effect — if Alloc is in the effect set,
  allocations go through the arena)
- Deep-copy at boundary: how do we copy a value that may
  contain pointers into the arena? (Walk the value, copy
  transitively, update pointers)
- Nested arenas: inner arena allocations shouldn't escape to
  outer arena

**Proposal:** Defer arena allocation to after 0f (memory model).
The Unique type interactions need to be clear first. For now,
make `Alloc` a no-op effect that's handled but doesn't change
allocation behavior.

## Testing

- Microbenchmarks: State effect tight loop, measure against
  equivalent pure code
- IO: hello world, file read/write, clock
- Fail: error propagation, catch, `?` operator — verify
  optimised path produces same results as general path
- Handler nesting: multiple handlers compose correctly at runtime
- Handler scoping: inner handler shadows outer for same effect
- Resume: value correctly returned to operation call site
- Zero-resumption: Fail handler doesn't resume, computation aborts

## Definition of Done

- Effectful Kea programs compile and run
- IO works (stdout, file read/write, clock)
- Fail compiles efficiently (Result-passing optimisation)
- User-defined effects work with the chosen compilation strategy
- Handler nesting works
- Performance: State effect overhead < 10x compared to passing
  state as a parameter (stretch goal: < 3x)
- `mise run check` passes

## Decisions

- **Refcount atomicity: scope model.** Non-atomic refcounts by
  default. The current function's effect set determines atomicity
  of new allocations — no concurrency effects (Send, Spawn, Par)
  means non-atomic. Values crossing thread boundaries are promoted
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

- **Capability effects (Send, IO, Spawn) are not interceptable
  by user handlers.** They compile to direct runtime calls per
  §5.15. User handlers compose around user-defined effects (Log,
  State, Tx, etc.), not around capability effects. This preserves
  the performance guarantee and avoids the "middleware changes
  Send semantics" problem. Backpressure, rate limiting, and
  circuit breaking are runtime/mailbox/library concerns, not
  handler composition.

## Open Questions

- Should we support tail-resumptive handlers specially? (A handler
  that calls `resume` as the last thing in its body can avoid
  capturing the continuation. This is a common pattern — Log,
  State get, etc. Koka optimises this aggressively.)
- Can we inline handlers when the handler is statically known?
  (If `with_state(0, || -> body)` is visible, the compiler could
  inline the State operations directly rather than going through
  evidence dispatch.)
- How does the handler compilation interact with Cranelift's
  calling convention? (Evidence passing adds parameters. CPS
  changes return conventions. Need to verify Cranelift can
  handle whichever strategy we pick.)
