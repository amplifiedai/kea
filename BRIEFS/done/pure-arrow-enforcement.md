# Brief: Pure Arrow (`->`) Effect Contract Enforcement

**Status:** done
**Priority:** v1-critical
**Depends on:** 0c-effect-handlers, 0e-runtime-effects (both done)
**Blocks:** 0g-advanced-types (correct effect contracts needed before advanced types)

## Motivation

KERNEL.md §5.3 is unambiguous: `->` asserts the empty effect set. The compiler
must reject a function declared with `->` whose body transitively performs
unhandled effects. Today it doesn't — the validator in
`validate_declared_fn_effect_row_with_env_and_records` skips validation entirely
when `effect_annotation` is `None` (lines 9102-9103 in typeck.rs), which is
exactly what `->` produces from the parser.

This is also a prerequisite for optimisation. KERNEL.md §5.4 states pure
functions can be memoised, reordered, parallelised, and dead-code eliminated.
The compiler can only do this if `->` is trustworthy — if a function declared
pure can secretly perform effects, none of these optimisations are safe. The 0f
memory model (reuse analysis, churn fusion) and future parallel pass scheduling
both depend on compile-time purity knowledge being sound.

This was never scoped into 0c or 0e. It fell through the cracks because the
validator was written to check explicitly annotated effect rows (`-[effects]>`)
against inferred ones, and nobody wrote the "`->` means assert-empty" branch.

Discovered during the adversarial test pass (2026-03-01) when a test for mutual
recursion between a pure function and an effectful one passed at runtime instead
of being rejected at compile time.

## The Gap

Two issues, both in the compiler pipeline:

### 1. Validator skips `None` annotations

```rust
// typeck.rs:9102-9103
let Some(ann) = &fn_decl.effect_annotation else {
    return Ok(());  // ← should validate purity, not skip
};
```

When `effect_annotation` is `None` (plain `->` arrow) and the function has a
`return_annotation` (confirming it's a real `fn` declaration, not a synthetic
closure), the validator should check that the inferred effect row is empty.

Guard: only enforce when `fn_decl.return_annotation.is_some()`. Closures and
internal AST nodes have `return_annotation: None` and should not be affected.

### 2. `infer_fn_decl_effect_row` is not handler-aware

The effect inference in `infer_fn_decl_effect_row` (typeck.rs:8504) walks the
function body bottom-up and collects effects from callees. But it does not
subtract effects consumed by `handle` blocks within the function body.

This means a function like:

```kea
fn main() -> Int
  handle run()
    State.get() -> resume 0
    State.put(next) -> resume ()
```

infers `[State Int]` even though the handler neutralises that effect. If we
enforce purity for `->` without fixing this, every `main` that uses `handle`
gets a false positive.

## Implementation Plan

### Step 1: Make `infer_fn_decl_effect_row` handler-aware

In `infer_expr_effect_row` (the recursive walker called by
`infer_fn_decl_effect_row`), when visiting a `Handle` expression:

1. Infer the effect row of the handled computation
2. Determine which effects the handler clauses cover
3. Return the row with handled effects subtracted

This is the core work. The row subtraction machinery already exists for type
checking (`effect_row_without` or similar); it needs to be wired into the
inference walker.

### Step 2: Enforce purity in the validator

In `validate_declared_fn_effect_row_with_env_and_records`, when
`effect_annotation` is `None` and `return_annotation.is_some()`:

- Check that the inferred row (now handler-aware from Step 1) has no concrete
  named effects (empty `fields`)
- Emit a `Category::TypeMismatch` diagnostic:
  `"function 'X' is declared pure ('->') but its body requires effects '[...]'"`
- Include help text:
  `"add an effect annotation: replace '->' with '-[effects]>' to declare the required effects"`

### Step 3: Regression test

Re-add the test that was removed during the adversarial pass:

```rust
fn compile_rejects_pure_function_calling_effectful_forward_reference()
```

Plus additional cases:
- Pure function directly calling an effectful function (no handler) → rejected
- Pure function calling effectful function inside a `handle` block → accepted
- Pure function with nested handlers that don't cover all effects → rejected
- `main` with `handle` that covers all effects → accepted (critical regression)

### Step 4: Polymorphic effect row pre-registration (refinement)

Currently `resolve_effect_annotation_simple` returns `EffectRow::pure()` for
polymorphic rows with rest variables (`-[e]>`). This is conservative but lossy.
A forward-referencing caller won't see polymorphic effects during
pre-registration. The real fix is SCC-based inference (check mutually recursive
groups together), but that's out of scope here. Document the limitation and move
on.

## Testing

- Existing test suite must pass unchanged (especially all `handle`-using tests)
- New negative tests for `->` purity violations
- New positive tests confirming `handle` properly neutralises effects
- Property: if a function is declared `->` and compiles, its body has no
  unhandled effects (can be checked via MCP `get_type`)

## Design Decisions

**Why not fix it in the parser?** The parser could emit `EffectAnnotation::Pure`
for `->` instead of `None`. But changing that representation ripples through
every consumer of `effect_annotation`. The validator fix is local and
non-invasive.

**Why guard on `return_annotation.is_some()`?** Internal AST constructs
(closures, synthetic nodes from desugaring) have both `return_annotation` and
`effect_annotation` as `None`. Real `fn`/`expr` declarations always have
`return_annotation` set (the parser requires it). This cleanly distinguishes
"declared pure" from "not a real declaration."

**Why not defer to 0h?** This is a soundness gap, not a diagnostic quality
issue. A pure function that secretly performs effects violates the core guarantee
that `grep -r "\-\[IO\]"` finds every function that does IO. It should land
before 0g adds more type system complexity.

## Progress

- 2026-03-01 12:30: Landed purity enforcement in `validate_declared_fn_effect_row_with_env_and_records` (typeck.rs:9102). Key insight: `infer_expr_effect_row` was already handler-aware (Handle arm subtracts effects at lines 9501-9631), so the fix was purely in the validator — 10 lines checking `fn_decl.return_annotation.is_some() && !inferred_row.row.fields.is_empty()`. Fixed 4 genuine impurities exposed: `run()` in Fail+State test over-declared effects, mutual recursion test with pure fn calling effectful fn, two MCP `trap` test functions missing effect annotations. Synthetic test infrastructure (generated test mains and test case functions) exempted via `return_annotation = None`. Also fixed pre-existing `add_impl_methods` signature validation test in kea-infer. Verified with `mise run check-full` (1605/1605 pass). Regression tests added: pure-calls-effectful-direct (rejected), pure-with-handle-all-effects (accepted), higher-order-pure-with-callback (accepted).
