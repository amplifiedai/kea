# Agent Note: Step 3 Memory Optimisation Pipeline (0f)

**Read `BRIEFS/in-progress/0f-memory-model.md` Step 3 carefully before continuing.**

Step 3 has been expanded from "basic reuse analysis" to a full six-part
optimisation pipeline based on proven techniques from Lean 4, Koka/Perceus,
and FP² (ICFP 2023). The sub-steps you've already landed (3a) are the
foundation — the remaining sub-steps are where the real performance wins
come from.

## What you've built (Step 3a — DONE)

- `schedule_trailing_releases_after_last_use`
- `elide_adjacent_retain_release_pairs` (trivial + non-interfering windows)
- Linear alias ownership transfer (`let t = s` skips retain when `s` is dead)

This eliminates obvious churn. Good. But it's necessary, not sufficient.

## What to build next (priority order)

### 3b: Auto borrow inference (DO THIS FIRST)

**This is the single highest-impact optimisation.** Lean 4 reports it
eliminates the majority of inc/dec operations.

The insight: most function parameters are read-only (fields read, passed
to other borrowed positions). If a parameter is never stored, returned,
or captured, it should be automatically borrowed — no annotation needed.

You already have `BorrowParamMap`. Layer inference on top:
1. For each function, analyse each parameter's usage in the body
2. If a param is only projected (field access, passed to borrow positions,
   used in pure comparisons) → classify as auto-borrowed
3. At call sites, skip retain/release for auto-borrowed arguments
4. Explicit `borrow` annotation overrides inference

This is a **pure optimisation** — correctness doesn't depend on it.

### 3c: Drop specialisation

Generate per-type drop functions instead of generic recursive drops.
For `Cons(head, tail)`: check refcount, if unique → extract fields,
drop them recursively, free cell; if shared → decrement.

This is essential for 3d (reuse tokens) — the compiler needs to see
inside drops to pair them with allocations.

### 3d: Reuse tokens (Perceus FBIP)

Pair `Release` sites with `Alloc` sites of matching layout. When you
pattern-match `Cons(h, t)` and construct `Cons(f(h), map(t, f))`, the
old cell's memory is reused for the new one. Zero allocator calls.

MIR pass: emit `ReuseToken` instruction at drop site, consume it at
alloc site. Runtime: `if (token != null) reuse else alloc`. With
Unique T: skip the check entirely — unconditional reuse.

**1.8-4.3x speedup measured in Koka** for recursive data structure code.

### 3e: TRMC (Tail Recursion Modulo Context)

Transform `Cons(f(h), map(t, f))` from recursive → loop by allocating
the Cons cell with a hole for the tail, then filling it iteratively.
Combined with 3d, `map` becomes a zero-allocation in-place loop.

Reference: Leijen, POPL 2023. Proved sound with non-linear control flow.

### 3f: FIP verification (`@fip` annotation)

Static proof that a function over Unique values is fully in-place:
zero allocation, zero deallocation, constant stack. Builds on 3d.
Reference: Lorenzen et al., ICFP 2023 (FP²).

## Key references

- **Perceus**: Reinking, Xie, de Moura, Leijen. "Perceus: Garbage Free
  Reference Counting with Reuse." PLDI 2021. (Reuse tokens, FBIP)
- **TRMC**: Leijen. "Tail Recursion Modulo Context: An Equational
  Approach." POPL 2023.
- **FP²**: Lorenzen, Leijen, Swierstra. "FP²: Fully in-Place Functional
  Programming." ICFP 2023. (@fip verification)
- **Lean 4 RC**: Ullrich, de Moura. "Counting Immutable Beans."
  IFL 2019. (Auto borrow inference)

## Also read

- `BRIEFS/SYNTAX-NOTE.md` — use KERNEL syntax, not Rill syntax, in
  all `.kea` code. `struct` not `record`, `~` not `..`, `(a,b)` not `#(a,b)`.
