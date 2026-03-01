# Brief: Callback Stacking for Multi-Yield Non-Tail Handlers

**Status:** design
**Priority:** post-v1
**Depends on:** tier4-continuations (done)
**Blocks:** nothing (Phase 1 self-hosting doesn't need this)

## Context

Tier 4's clause body splitting decomposes `let x = resume val; f(x)` into a
tail-resumptive callback (returns `val`) + post-resume code (`f` applied to the
handle result). This works correctly for **single-operation** computations.

For computations that perform the same handled operation multiple times, the
current approach has a "last invocation wins" limitation: the callback runs once
per operation, but the post-resume code runs only once (after the handle returns).
The post-resume code sees the handle expression's final result, not the per-invocation
results.

### Example of the limitation

```kea
effect Choose
  fn choose(n: Int) -> Int

fn body() -[Choose]> Int
  let a = Choose.choose(10)   -- first invocation
  let b = Choose.choose(20)   -- second invocation
  a + b

fn main() -> Int
  handle body()
    Choose.choose(n) ->
      let picked = resume n    -- runs twice (n=10, n=20)
      picked * 2               -- post-resume: only runs once, sees final result
```

**Current behavior:** callback returns `n` each time (correct). Post-resume runs
once with `result = 30` (10 + 20), produces `60`. But the intended deep-handler
semantics would have each invocation's post-resume transform the computation's
continuation independently.

**Who needs this:** generators, backtracking combinators, coroutine-style yield
handlers, any pattern where the same non-tail operation fires multiple times.

### Why Phase 1 doesn't need this

The self-hosting compiler uses State, Fail, IO, Log — all tail-resumptive.
Non-tail handlers in practice are rare (~5% of handlers), and multi-yield
non-tail handlers are rarer still. The stdlib patterns that would exercise
this (Choose, Generator, Coroutine) are post-v1 features.

---

## Design: LIFO Post-Resume Chain

Instead of running post-resume code once after the handle returns, maintain a
**stack of post-resume closures** — one per operation invocation. When the
computation finishes, unwind the stack, applying each post-resume transform
in LIFO order.

### Data structure

```
PostResumeStack = List (result: Dynamic) -> Dynamic
```

Each entry is a closure that takes the "continuation result" and produces the
transformed result. The stack grows with each operation invocation and unwinds
when the computation completes.

### Protocol

1. **Handler install:** allocate empty post-resume stack (a state cell holding `[]`)
2. **Operation fires (callback runs):** the callback:
   a. Captures any pre-resume bindings
   b. Pushes a post-resume closure onto the stack (closure captures the bindings)
   c. Returns the resume value (tail-resumptive)
3. **Computation finishes:** handle expression returns `raw_result`
4. **Stack unwind:** fold the stack over `raw_result`:
   ```
   final_result = stack.fold_right(raw_result, |transform, acc| transform(acc))
   ```

### MIR lowering changes

The callback body construction in `lower_handle_expr` needs to:
1. Allocate a post-resume stack cell (`StateCellNew` with initial `[]`)
2. For each non-tail clause, the callback:
   - Lowers pre-resume stmts
   - Builds a post-resume closure from post_resume_body + captured bindings
   - Emits `List.cons(closure, stack_cell)` to push onto the stack
   - Returns the resume value
3. After the handle expression returns, emit stack unwind code:
   - Load the stack from the cell
   - Fold over it, calling each closure with the accumulator

### Estimated scope

- ~50-100 LOC in `crates/kea-mir/src/lib.rs` (callback body construction + stack unwind)
- Requires `List` runtime support (cons, fold) — may need intrinsic list ops
- Alternative: use a linked list of closures via heap-allocated pairs (avoids List dependency)

### Pre-resume captures

This design also resolves the current v1 limitation on pre-resume captures. The
post-resume closure captures the pre-resume bindings in its environment, so they
survive across multiple invocations. The `captured_bindings` rejection in
`split_non_tail_resume` can be removed once callback stacking lands.

---

## Alternatives considered

### CPS transformation

Transform the clause body into continuation-passing style at the MIR level.
More general but significantly more complex (~500+ LOC), doubles function
variants, and conflicts with Cranelift's direct-style strengths. Overkill for
this specific problem.

### setjmp/longjmp with stack copying

The original Tier 4 brief proposed this. Rejected because:
- Stack corruption without copying (longjmp to overwritten frames)
- Stack copying adds ~150 LOC platform-specific C code
- Memory management complexity (who frees the copied stack?)
- Thrown away when upgrading to mini-stacks or segmented stacks

Callback stacking solves the same problem with zero platform-specific code.

---

## Definition of Done

- [ ] Post-resume stack allocation in non-tail handler lowering
- [ ] Callback pushes post-resume closure onto stack per invocation
- [ ] Stack unwind after handle expression returns
- [ ] Pre-resume captures work (rejection removed)
- [ ] Multi-yield non-tail handler test: `Choose.choose` called twice
- [ ] Existing Tier 4 tests unchanged and passing
- [ ] `mise run check-full` passes
