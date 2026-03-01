# Brief: Tier 4 — Non-Tail-Resumptive Handlers via One-Shot Continuations

**Status:** ready
**Priority:** v1
**Depends on:** handler-tiers-3-4 (Tier 3 done), 0e-runtime-effects (done)
**Blocks:** Phase 1 (self-hosting needs full handler coverage), Choose/backtracking patterns

## Context

Tier 3 shipped: per-operation cell dispatch, capability mocking, evidence threading through call chains and closures — all working. The remaining gap is **non-tail-resumptive handlers** where `resume` appears in non-tail position:

```kea
Choose.choose(options) ->
  let picked = resume(options.first())
  transform(picked)    -- code after resume
```

Today this is rejected with "must be tail-resumptive for compiled lowering." About ~5% of real-world handlers need this capability, but it's required for completeness before Phase 1.

### Why then-clause desugaring failed

An earlier attempt to desugar non-tail resume into `resume val` + `then` was rejected as semantically unsound. The fundamental issue: `then` applies once when the handled computation finishes, but a non-tail clause body runs **per operation occurrence**. For multi-call computations, the transformation compounds incorrectly. See handler-tiers-3-4.md progress entry for 2026-03-01 23:30.

### What we need

True continuation capture: when an operation is performed, save the computation's execution state, run the handler clause, and when `resume(value)` is called, restore the computation with that value. When the computation eventually finishes, return control to the clause body after resume.

---

## Research Summary

### Koka's three generations

| Generation | Library | Technique | Yield/resume cost |
|------------|---------|-----------|-------------------|
| Gen 1 | libhandler | setjmp/longjmp + **stack copying** | O(stack depth) |
| Gen 2 | libmprompt | **In-place growable stacks** via mmap | O(1) — stack pointer swap |
| Gen 3 | libseff | **Segmented stacks** via coroutines | O(1) — fastest asymptotically |

All three share the critical optimisation: **tail-resumptive handlers bypass continuation machinery entirely** — they compile to direct function calls via the evidence vector. This is what Kea's Tier 2 state cells already achieve.

### Why setjmp/longjmp works for Kea

Kea's at-most-once resumption (KERNEL §5.7) is the key enabler. One-shot continuations mean:

1. The stack segment between operation and handler is used exactly once
2. No stack copying needed — the segment is live for exactly one yield-resume pair
3. `longjmp` back to the operation site is safe because the frames haven't been destroyed
4. `longjmp` from computation completion to the clause body is safe because the handler's frame is still live on the stack (the `setjmp` at the handler install point preserves it)

### Why NOT CPS, mini-stacks, or Cranelift stack_switch

| Approach | Verdict | Reason |
|----------|---------|--------|
| CPS transformation | Overkill | ~1000+ lines MIR rewrite, doubles function variants, conflicts with Cranelift's direct-style strengths |
| Mini-stacks (mmap) | Future option | More complex (200C + 200 Rust), 64-bit only, better for deep stacks we don't need yet |
| Cranelift stack_switch | Not available | Tied to Wasm stack switching proposal internals, not a stable API |
| setjmp/longjmp | **Correct choice** | ~100 C + ~200 Rust, proven technique (libhandler Gen 1), minimal MIR/codegen change |

---

## Design

### The three-jmpbuf protocol

Three jump buffers collaborate to implement the yield-resume-completion cycle:

```
handler_buf  — saved at handler install (setjmp returns 0 on entry, 1 on yield)
perform_buf  — saved at operation call site (setjmp returns 0 on entry, 1 on resume)
resume_buf   — saved in clause body at resume point (setjmp returns 0 on entry, 1 on completion)
```

**Flow:**

```
1. Handler install:
   frame = alloc_handler_frame()
   ret = setjmp(handler_buf)
   if ret == 0:
     // Normal path: run computation with frame threaded
     comp_result = computation(..., frame)
     // Computation finished — signal clause body
     frame.comp_result = comp_result
     longjmp(resume_buf, 1)           ──→ step 7
     unreachable
   else:
     // Yielded from operation ──→ from step 2
     goto step 3

2. Operation performs (in computation):
   frame.op_arg = arg
   ret = setjmp(perform_buf)
   if ret == 0:
     longjmp(handler_buf, 1)           ──→ step 1 else branch
     unreachable
   else:
     // Resumed ──→ from step 5
     return frame.resume_value         ──→ computation continues

3. Handler clause body runs:
   arg = frame.op_arg
   ... pre-resume code ...

4. resume(value) in clause body:
   frame.resume_value = value
   ret = setjmp(resume_buf)
   if ret == 0:
     longjmp(perform_buf, 1)           ──→ step 2 else branch
     unreachable
   else:
     // Computation completed ──→ from step 6
     result = frame.comp_result        ──→ step 7

5. Computation receives resume value, continues...
   ... more operations possible (re-enters step 2) ...
   ... computation finishes normally ...

6. Computation done:
   frame.comp_result = result
   longjmp(resume_buf, 1)              ──→ step 4 else branch

7. Clause body continues after resume:
   ... post-resume code using result ...
   return final_value
```

### Multi-operation re-entrancy

When the computation performs the same operation multiple times, the clause body runs multiple times. Each invocation gets its own `perform_buf` (step 2 saves a fresh one each time). The handler loop is:

```
handler_install:
  ret = setjmp(handler_buf)
  if ret == 0: goto run_computation
  else: goto clause_body

run_computation:
  result = computation(...)
  // computation finished — need to return to latest resume_buf
  longjmp(resume_buf, 1)

clause_body:
  // Run clause body with current op_arg
  ... pre-resume ...
  // resume(value) — saves resume_buf, jumps to perform_buf
  comp_result = resume(value)  // returns after comp finishes OR next yield
  ... post-resume using comp_result ...
```

Wait — there's a subtlety. With multiple operations, the clause body from the FIRST `resume` call needs to receive the result from after the SECOND operation has been handled. The `resume(value)` in the first clause invocation doesn't return until the computation is done (or the next operation yields). If the next operation yields, the handler clause runs again — this is re-entrancy.

For correct semantics with re-entrancy, the handler needs a **stack of resume points** — one per active `resume` call. The computation's "continuation" is the chain of nested clause invocations.

**Simplification for v1:** Kea's type system enforces at-most-once resumption per handler clause invocation. But the same handler clause can be entered multiple times (once per operation occurrence). The C runtime needs to handle this correctly.

The simplest correct implementation: the handler install loops on `setjmp(handler_buf)`, and each clause invocation is a fresh function call. The `resume` inside the clause calls `setjmp(resume_buf)` before jumping back. When the computation finishes (or yields again), it jumps to the most recent `resume_buf`.

### C runtime API

```c
#include <setjmp.h>

typedef struct KeaHandlerFrame {
    jmp_buf handler_buf;    // saved at handler install
    jmp_buf perform_buf;    // saved at operation site
    jmp_buf resume_buf;     // saved at resume point in clause
    int64_t resume_value;   // clause → operation site
    int64_t op_arg;         // operation site → clause
    int64_t comp_result;    // computation → clause (after resume)
    int32_t op_id;          // which operation was performed
    int32_t state;          // 0=init, 1=yielded, 2=resumed, 3=done
} KeaHandlerFrame;

KeaHandlerFrame* __kea_handler_frame_new(void);
void __kea_handler_frame_free(KeaHandlerFrame* frame);

// Returns 0 on initial entry, 1 when an operation yields
int32_t __kea_handler_setjmp(KeaHandlerFrame* frame);

// At operation site: saves continuation, jumps to handler
// Returns resume_value when clause calls resume
int64_t __kea_perform(KeaHandlerFrame* frame, int32_t op_id, int64_t arg);

// In clause body: sends value to operation, gets comp result
int64_t __kea_resume(KeaHandlerFrame* frame, int64_t value);

// When computation finishes: jumps to clause's post-resume code
void __kea_handler_comp_done(KeaHandlerFrame* frame, int64_t result);
```

### MIR changes

No new MIR instructions needed. The non-tail handler lowering emits:

1. A `Call` to `__kea_handler_frame_new` (external)
2. A `Call` to `__kea_handler_setjmp` (external) + conditional branch
3. In the normal branch: lower the handled expression, then `Call` to `__kea_handler_comp_done`
4. In the yielded branch: run the clause body, with `Resume` lowered as `Call` to `__kea_resume`
5. A `Call` to `__kea_handler_frame_free` (external)

At the operation call site (in the computation), when a non-tail handler is active: emit `Call` to `__kea_perform` instead of the normal cell load/callback invoke.

The key MIR lowering change is in `lower_handle_expr`: when the clause body is non-tail-resumptive, don't reject — instead emit the handler frame protocol. The clause body itself is lowered inline in the "yielded" branch of the setjmp conditional.

### Codegen changes

1. Declare `__kea_handler_frame_new`, `__kea_handler_setjmp`, `__kea_perform`, `__kea_resume`, `__kea_handler_comp_done`, `__kea_handler_frame_free` as imported functions
2. Register JIT stubs (Rust implementations using `libc::setjmp`/`libc::longjmp` FFI)
3. `HandlerEnter` for non-tail handlers: emit the setjmp + branch structure
4. `Resume` instruction: emit call to `__kea_resume`
5. Operation calls under non-tail handler scope: emit call to `__kea_perform`

### JIT stub implementation

For JIT mode, the C runtime functions are implemented in Rust:

```rust
// Use libc setjmp/longjmp via FFI
extern "C" {
    fn setjmp(env: *mut libc::jmp_buf) -> libc::c_int;
    fn longjmp(env: *mut libc::jmp_buf, val: libc::c_int) -> !;
}

#[repr(C)]
struct KeaHandlerFrame {
    handler_buf: libc::jmp_buf,
    perform_buf: libc::jmp_buf,
    resume_buf: libc::jmp_buf,
    resume_value: i64,
    op_arg: i64,
    comp_result: i64,
    op_id: i32,
    state: i32,
}

unsafe extern "C" fn kea_handler_frame_new() -> *mut KeaHandlerFrame {
    Box::into_raw(Box::new(KeaHandlerFrame { /* zeroed */ }))
}

unsafe extern "C" fn kea_handler_setjmp(frame: *mut KeaHandlerFrame) -> i32 {
    setjmp(&mut (*frame).handler_buf as *mut _) as i32
}

// ... etc
```

Note: `libc::jmp_buf` may need platform-specific handling. On macOS aarch64, `jmp_buf` is `[c_int; 48]`. On Linux x86_64, it's `[c_long; 8]`. The `libc` crate provides the correct definition.

---

## Implementation Plan

### Step 1: C runtime helpers (~50 LOC)

- Add handler frame functions to `crates/kea/runtime/kea_aot_runtime.c`
- Verify C compilation on macOS (aarch64) and Linux (x86_64)
- Write a standalone C test that exercises the yield/resume/completion cycle

### Step 2: JIT stubs (~80 LOC)

- Add Rust FFI wrappers in `crates/kea-codegen/src/lib.rs`
- Register symbols in `register_jit_runtime_symbols`
- Declare function signatures in `runtime_signature_map`

### Step 3: MIR lowering for non-tail resume (~150 LOC)

- In `lower_handle_expr`: detect non-tail clause body (any body that isn't `Resume { value }`)
- For non-tail clauses: emit handler frame allocation + setjmp + conditional branch
- Normal branch: lower handled expression, call `__kea_handler_comp_done`
- Yielded branch: lower clause body, with `HirExprKind::Resume` lowered as call to `__kea_resume`
- Thread the handler frame pointer to operation call sites

### Step 4: Codegen lowering (~100 LOC)

- Declare imported functions for handler frame operations
- Lower `NonTailYield` to call to `__kea_perform`
- Lower `Resume` (in non-tail context) to call to `__kea_resume`
- Lower `HandlerEnter` for non-tail handlers to setjmp + branch
- Lower `HandlerExit` for non-tail handlers to `__kea_handler_frame_free`

### Step 5: Tests

- `non_tail_resume_transforms_result` — `let x = resume 40; x + 2` → 42
- `non_tail_resume_with_pre_resume_binding` — `let n = f(arg); let x = resume n; x + n`
- `non_tail_resume_multi_operation` — computation calls same op twice
- `choose_handler_picks_first` — KERNEL §5.15 example
- `non_tail_resume_with_nested_handler` — outer non-tail, inner tail
- `double_resume_rejected` — static rejection (already tested)
- `non_tail_handler_cleanup_no_leak` — valgrind/ASAN clean

---

## Risks

### Risk 1: setjmp/longjmp register corruption with Cranelift

**Likelihood:** Low. Cranelift follows platform ABIs, setjmp saves all callee-saved registers.
**Mitigation:** Test with live local variables across yield/resume boundary. Run ASAN.

### Risk 2: Reference count imbalance on non-resumed paths

**Likelihood:** Low (zero-resume non-tail handlers are extremely rare — use Fail for that).
**Mitigation:** Document limitation. For production, add stack maps or cleanup trampolines.

### Risk 3: macOS setjmp signal mask

**Likelihood:** None (Kea doesn't use signals for control flow).
**Mitigation:** Use `_setjmp`/`_longjmp` on macOS (non-signal-saving variants).

### Risk 4: libc::jmp_buf portability

**Likelihood:** Medium (jmp_buf size varies by platform).
**Mitigation:** Use `libc` crate which provides correct platform definitions. Alternatively, implement entirely in C and link as object.

---

## Future upgrade path

1. **Phase 1 (self-hosting):** Keep setjmp/longjmp. Works. Focus on language features.
2. **Phase 2 (production):** Profile non-tail handler perf. If bottleneck:
   - Option A: Mini-stacks via mmap (libmprompt approach) — O(1) yield/resume
   - Option B: Selective CPS at MIR level for hot non-tail handlers
   - Option C: Cranelift `stack_switch` if it becomes a stable API
3. **Phase 3 (LLVM backend):** CPS becomes more attractive with LLVM optimisation passes.

---

## Definition of Done

- [ ] C runtime handler frame functions compile and pass standalone test
- [ ] JIT stubs registered and callable from Cranelift-generated code
- [ ] `lower_handle_expr` accepts non-tail clause bodies
- [ ] Handler frame protocol emitted correctly in MIR
- [ ] Codegen lowers setjmp/longjmp + yield/resume calls
- [ ] All 5+ Tier 4 test cases passing
- [ ] Existing 1614 tests unchanged and passing
- [ ] `mise run check-full` passes
- [ ] ASAN clean on test suite

## References

- Leijen, D. (2017). "Implementing Algebraic Effects in C." APLAS. — setjmp/longjmp technique
- Xie, N. & Leijen, D. (2021). "Generalized Evidence Passing for Effect Handlers." ICFP. — evidence-passing + yield bubbling
- [libmprompt](https://github.com/koka-lang/libmprompt) — Koka's current continuation library
- [libhandler](https://github.com/koka-lang/libhandler) — Koka's Gen 1 library (setjmp/longjmp)
- [libseff](https://dl.acm.org/doi/10.1145/3689798) — Segmented stack approach (OOPSLA 2024)
- KERNEL.md §5.7 (at-most-once resumption), §5.15 (Choose example)
