# Brief: Handler Compilation Tiers 3-4

**Status:** ready
**Priority:** v1-critical
**Depends on:** 0e-runtime-effects (done)
**Blocks:** Phase 1 (self-hosting requires polymorphic effect passing), 0g (advanced types with effect-parameterised generics)

## Context

The 0e brief defined four handler compilation tiers. Tiers 1-2 shipped and are well-tested. Tiers 3-4 were designed in 0e but never implemented. The MIR has the classification scaffolding (`MirEffectOpClass::Dispatch`) and the codegen has ABI type stubs (`AbiEffectEvidencePlacement`), but no code path actually compiles Dispatch operations or non-tail-resumptive handlers.

### What works today (Tiers 1-2)

- **Tier 1 — Fail/ZeroResume:** Result-passing via early return. `fail`, `?`, `catch` all compile. <1.5x overhead vs hand-written Result.
- **Tier 1.5 — Direct capabilities:** IO/Clock/Rand/Net compile to direct runtime calls. Zero handler overhead.
- **Tier 2 — Tail-resumptive, statically known:** State/Log/Reader handlers compile via **state cells** — heap-allocated cells keyed by `(effect, operation)`. `HandlerEnter`/`HandlerExit` are no-ops. Operation calls become cell loads/stores or callback invocations. Within 1.3x of parameter-passing baseline at 1M iterations.

### What doesn't work (Tiers 3-4)

- **Tier 3 — Dynamically dispatched handlers:** When the handler is not visible at the operation call site (effect-polymorphic code, handler passed through a function boundary), the current approach fails. `EffectOp { class: Dispatch }` triggers `UnsupportedMir` in codegen. There is no evidence struct, no indirect call lowering, no hidden parameter threading.
- **Tier 4 — Non-tail-resumptive:** `Resume` in non-tail position triggers a hard error: "non-tail-resumptive handlers are not yet supported in compiled mode." No `setjmp`/`longjmp` infrastructure exists.

### What this blocks

Any function that takes an effectful callback and needs to forward the caller's handler:

```kea
fn map_with_effect(_ f: A -[State S]> B, _ xs: List A) -[State S]> List B
  -- Can't compile: handler for State must be passed to f
  case xs
    [] -> []
    [x, ...rest] -> [f(x), ...map_with_effect(f, rest)]
```

Also blocks: effect-polymorphic library functions, higher-order effectful combinators, capability effect mocking in tests (KERNEL §5.6), and any non-trivial handler clause body (code after `resume`).

### Capability effect mocking

KERNEL §5.6 specifies that capability effects (IO, Net, Clock, Rand) can be intercepted by user handlers for testing:

```kea
fn with_mock_fs(_ files: Map String Bytes, _ f: () -[IO, e]> T) -[e]> T
  handle f()
    IO.read_file(path) ->
      case files.get(path)
        Some(data) -> resume data
        None -> panic "mock: file not found: {path}"
    IO.write_file(path, data) ->
      resume ()
```

Today, IO operations always compile to direct runtime calls (`MirEffectOpClass::Direct`) regardless of handler scope. For mocking to work, the compiler must detect when a user handler is installed for a capability effect and route operations through the handler (evidence dispatch) instead of the direct runtime path. This is a Tier 3 feature — the mock handler's evidence must be threaded to the computation as a hidden parameter, and operations must dispatch through it instead of calling libc directly.

---

## Tier 3: Evidence Passing for Polymorphic Handlers

### Design

When a handler is **not statically visible** at the operation call site, the compiler threads an **evidence struct** as a hidden parameter through all effectful functions. Each effect gets its own evidence struct containing one function pointer per operation.

This is Koka's evidence-passing approach (Leijen 2017, "Type Directed Compilation of Row-Typed Algebraic Effects").

### Evidence struct layout

For an effect with operations `op1(A) -> B` and `op2(C) -> D`:

```c
struct Effect_Evidence {
    B (*op1)(A, void* env);   // operation function pointer
    void* op1_env;             // closure environment for op1
    D (*op2)(C, void* env);   // operation function pointer
    void* op2_env;             // closure environment for op2
}
```

Each operation is a function pointer + environment pair (a closure). The environment captures the handler's local state (the cell, in Tier 2 terms).

### ABI changes

Effectful functions gain hidden trailing parameters — one evidence pointer per effect in their effect row:

```
// Source: fn compute() -[State Int, Log]> Int
// Compiled signature: fn compute(ev_state: *StateEvidence, ev_log: *LogEvidence) -> Int
```

The evidence parameters are:
- **Invisible** at the source level — the type system tracks effects, not the programmer
- **Ordered** by effect name (alphabetical) for ABI stability
- **Pointer-sized** — one pointer per effect in the function's row

### Operation dispatch

`EffectOp { class: Dispatch, effect: "State", operation: "get" }` compiles to:

```
evidence_param = function_arg[evidence_offset_for_state]
op_fn = evidence_param.get_fn_ptr
op_env = evidence_param.get_env
result = indirect_call(op_fn, args..., op_env)
```

### Handler installation

`HandlerEnter { effect: "State" }` with tail-resumptive clauses:

1. Allocate evidence struct on the stack (or heap if it escapes)
2. Populate function pointers from handler clause bodies
3. Populate environments from captured state (cells)
4. Pass evidence to the handled computation

### Interaction with Tier 2 inlining

Tier 2's state-cell approach is the **inlined form** of Tier 3. When the handler is statically visible, the evidence struct is eliminated entirely — operation calls become direct cell loads/stores (what we already have). Tier 3 is the **general case** that Tier 2 optimises away for the common path.

The implementation should:
1. Lower all user handlers to evidence-passing form first
2. Run an inlining pass that eliminates evidence for statically-known handlers
3. This replaces the current ad-hoc cell lowering with a principled optimisation

However, a pragmatic alternative is to keep Tier 2's cell lowering as-is for the statically-known case and only add evidence passing for the Dispatch case. This avoids rewriting working code.

### Implementation steps

**Step 1: Evidence struct codegen**
- Define `EvidenceStruct` layout per effect (from effect declaration's operation signatures)
- Generate Cranelift struct types for evidence
- Implement evidence allocation (stack or heap)
- Implement evidence field access (load function pointer, load env)

**Step 2: ABI threading**
- Extend `AbiManifest` to track evidence parameters per function
- Add evidence parameters to Cranelift function signatures for effectful functions
- Thread evidence through all call sites (caller passes evidence to callee)
- Handle closures: evidence must be captured or threaded through closure environments

**Step 3: Dispatch lowering**
- `EffectOp { class: Dispatch }` → load fn pointer from evidence → indirect call
- Wire evidence creation at `HandlerEnter` sites
- Wire evidence teardown at `HandlerExit` sites

**Step 4: Capability effect interception**
- When a user handler is installed for a capability effect (IO, Net, Clock, Rand), operations within the handled scope must dispatch through evidence instead of direct runtime calls
- MIR lowering must check whether a capability effect has an active user handler before classifying as `Direct`
- If handler is active: classify as `Dispatch`, thread evidence
- If no handler: classify as `Direct` (zero overhead production path)
- This is the mechanism that enables test mocking per KERNEL §5.6

**Step 5: Testing**
- Effect-polymorphic function that forwards handler to callback
- Nested handlers where inner handler shadows outer for same effect via evidence
- Evidence passing through 3+ function call depth
- Mix of Dispatch and Direct effects in same function
- Capability effect mocking: `handle f() with IO.read_file(path) -> resume "fake"` intercepts IO
- Benchmark: evidence dispatch overhead vs Tier 2 inlined (target: <5x overhead for dispatch path)

---

## Tier 4: Non-Tail-Resumptive Handlers

### Design

When `resume` appears in non-tail position, the handler needs to **capture a continuation** at the operation site and **resume it later** within the clause body. Kea's at-most-once resumption (KERNEL §5.7) means this is a one-shot continuation — no stack copying needed.

```kea
-- Non-tail-resumptive: code after resume
Choose.choose(options) ->
  let picked = resume(options.first())
  transform(picked)    -- runs after the computation resumes
```

### Implementation: setjmp/longjmp

Following the 0e brief's design:

1. **At handler install (`HandlerEnter`):** `setjmp` to save the handler's stack frame
2. **At operation site (`EffectOp`):** `longjmp` to jump to the handler clause body
3. **At `resume` in clause body:** Jump back to the operation site, passing the resume value
4. **After resume returns:** Continue executing the clause body (the non-tail part)

The continuation is the stack segment from the operation call site to the handler frame. Because resumption is at-most-once, this segment is used exactly once — no copying needed.

### Platform considerations

- **POSIX:** `setjmp`/`longjmp` or `sigsetjmp`/`siglongjmp`
- **Windows:** `setjmp`/`longjmp` (MSVC) or structured exception handling
- **Alternative:** Cranelift's stack switching API if available (check Wasmtime's fiber implementation)

### One-shot enforcement

The type system already enforces at-most-once resumption (KERNEL §5.7: `resume` is not first-class, can't be stored/returned/passed). The runtime should additionally null out the continuation pointer after use as a safety net.

### Implementation steps

**Step 1: Continuation representation**
- Define `Continuation` struct: saved stack pointer, saved instruction pointer, resume value slot
- Implement `setjmp`-equivalent at handler install via Cranelift (or C runtime call)
- Implement `longjmp`-equivalent at operation perform

**Step 2: Resume in non-tail position**
- At `resume(value)`: store value in continuation's resume slot, jump back to operation site
- Operation site receives resume value and returns it to the computation
- After operation returns, computation continues normally
- When computation reaches handler scope end, control returns to clause body after `resume`

**Step 3: Testing**
- Basic non-tail-resumptive handler (transform result of resume)
- Choose/backtracking pattern from KERNEL §5.15 example
- Coroutine-style yield handler
- Verify double-resume is statically rejected
- Verify continuation cleanup (no leaks)

---

## Implementation order

1. **Tier 3 first.** It's more impactful (~15% of real handlers, blocks library design) and the ABI work is foundational for Tier 4's evidence threading.
2. **Tier 4 second.** Only ~5% of handlers, but needed for completeness before Phase 1.
3. **Keep Tier 2 cell lowering intact.** Don't rewrite working code. Add evidence passing alongside it for the Dispatch case.

## Testing strategy

### Regression gate

All existing Tier 1-2 tests must continue passing. The state-cell path for statically-known handlers is unchanged.

### New test cases

**Tier 3:**
- `effect_polymorphic_callback_forwards_handler` — function takes effectful callback, handler installed by caller
- `evidence_threading_three_deep` — handler → fn1 → fn2 → operation, evidence passed through chain
- `mixed_dispatch_and_direct_effects` — function with both `State` (dispatch) and `IO` (direct)
- `nested_evidence_inner_shadows_outer` — inner handler provides new evidence for same effect
- `evidence_through_closure` — closure captures evidence from enclosing scope
- `benchmark_evidence_dispatch_vs_cell` — quantify overhead of indirect call vs inline cell
- `capability_mock_io_read_file` — user handler intercepts IO.read_file, returns fake data
- `capability_mock_clock_now` — user handler intercepts Clock.now, returns deterministic value
- `capability_mock_scoped` — IO operations outside handler scope still use direct runtime calls

**Tier 4:**
- `non_tail_resume_transforms_result` — code after `resume` modifies returned value
- `choose_handler_picks_first` — KERNEL §5.15 example
- `coroutine_yield_handler` — yield effect with non-tail resume
- `double_resume_rejected` — verify compile error (already tested)
- `continuation_cleanup_no_leak` — handler exits cleanly after one-shot resume

### Stdlib parity

After Tier 3 lands, verify all stdlib effect modules still compile and their tests pass. No stdlib module currently needs Tier 3 (all handlers are statically known), but this validates no regressions.

## Definition of Done

- [ ] `EffectOp { class: Dispatch }` compiles and runs correctly
- [ ] Evidence structs allocated, populated, and threaded as hidden parameters
- [ ] Effect-polymorphic functions compile (handler passed through function boundary)
- [x] Capability effects (IO/Clock/Rand/Net) interceptable by user handlers for test mocking
- [ ] Non-tail-resumptive handlers compile via continuation capture
- [x] Existing Tier 1-2 tests unchanged and passing
- [ ] New Tier 3-4 test suites passing
- [ ] Benchmark: Tier 3 dispatch overhead <5x vs Tier 2 inlined
- [x] `mise run check-full` passes

## Progress

- 2026-03-01 17:30: Capability effect mocking — DONE (commit c153c7c)
  - Capability effects now participate in per-operation cell dispatch
  - Non-entry-point functions get hidden dispatch params for capability ops
  - Entry-point `main` creates default cells wrapping runtime functions
  - Handler clauses for capability effects use InvokeCallback (not LoadCell/StoreArg)
  - Direct capability call-site guard checks for active handler cells
  - Previously-failing Clock.elapsed_since and Rand mock tests now pass
  - All 1605 tests pass, `mise run check-full` clean
- **Next:** Dispatch codegen hardening (Step 2), then Tier 4 non-tail-resumptive handlers
