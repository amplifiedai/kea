# Brief: Effect Handlers

**Status:** done
**Priority:** v1-critical
**Depends on:** 0b-type-system-core (needs effect rows, trait system)
**Blocks:** 0d-codegen-pure (Fail sugar needed for practical programs), 0e-runtime-effects

## Motivation

This is Kea's novel core. Rill has no algebraic effects or handlers.
The effect row infrastructure from 0b gives us the type-level
representation; this brief covers the language-level constructs:
`effect` declarations, `handle`/`resume` expressions, handler
typing rules, and the `Fail` sugar that makes error handling
ergonomic.

No rill code to cannibalise here — this is genuinely new work.
But rill-infer's architecture (constraint-based inference, provenance
tracking) provides the scaffolding to build on.

## What transfers from Rill

**Nothing directly.** Rill has purity/volatility inference (pure
functions can't call volatile ones) but no user-defined effects,
no handlers, no resumptions.

**Structural reference:**
- rill-infer's constraint generation patterns inform how to add
  effect constraints
- rill-infer's provenance tracking provides the diagnostic
  infrastructure for effect errors
- rill-types' row machinery (extended in 0b) is the substrate

**Literature reference:**
- Koka (Leijen 2017): row-based effect typing, evidence passing
- Eff (Bauer & Pretnar 2015): algebraic effects and handlers
- Frank (Lindley, McBride, McLaughlin 2017): effect handlers
  with shallow/deep distinction
- "Do Be Do Be Do" (Lindley et al. 2017): bidirectional effects

## What's new

### 1. Effect declarations (KERNEL §5.2)

```kea
effect Log
  fn log(_ level: Level, _ msg: String) -> ()

effect State S
  fn get() -> S
  fn put(_ new_state: S) -> ()

effect Fail E
  fn fail(_ error: E) -> Never
```

Parsing: handled in 0a (AST nodes for effect declarations).
Type checking: each effect declaration introduces a set of typed
operations into a namespace. Effect operations are called
qualified: `Log.log(level, msg)`, `State.get()`.

An effect declaration creates:
- A type-level effect name (used in effect rows)
- A set of operation signatures
- A namespace for qualified calls

### 2. Handler blocks (KERNEL §5.6)

```kea
handle expr
  Effect.operation(args) -> handler_body
```

Typing rule (KERNEL §5.13):
```
Given:
  expr : T  with effects {E, R...}
  handler for E.operation(args) -> handler_body
  handler_body : _  with effects {H...}

Then:
  handle expr { E.operation(args) -> handler_body }
    : T  with effects {H..., R...}
```

The handled effect `E` is removed. The handler body's effects
`H` are added. All other effects `R` pass through.

Key implementation details:
- `resume value` returns `value` to the effect call site
- `resume` is at-most-once (KERNEL §5.7): zero or one. Not a
  first-class value — cannot be stored, returned, or captured.
- `then` clause (optional): transforms result when the handled
  computation completes without performing the effect.
- A handler must cover all operations of the handled effect.

### 3. Fail sugar (KERNEL §5.8)

- `fail expr` → `Fail.fail(expr)`
- `expr?` → match on Result, fail on Err with From conversion
- `catch expr` → handler that catches Fail, returns Result

These are desugaring rules, not new type system features. They
should be implemented as AST-to-AST transforms before type
checking, or as special cases in the type checker.

### 4. Effect inference (KERNEL §5.11)

Effects are inferred bottom-up. The effect set of a function
body is the union of effect sets of all expressions. This
should already be mostly working from 0b (effect variables in
function types). This brief adds:
- Performing an effect operation adds it to the current scope
- Handler removes the handled effect
- Explicit annotations checked against inferred effects
- Effect polymorphism: `e` variables generalize at let-bindings

## Implementation Plan

### Step 1: Effect declarations

- AST: `EffectDecl` node with name, type params, and operation
  signatures (should exist from 0a)
- Type checker: register effect declarations in scope, resolve
  qualified effect operation calls (`Log.log(...)`)
- Test: declare an effect, call its operations, verify the effect
  appears in the inferred type

### Step 2: Handler expressions

- AST: `HandleExpr` with handled expression, operation clauses,
  optional `then` clause
- Type checker:
  1. Infer the handled expression's type and effects
  2. Verify the handler covers all operations of the target effect
  3. Infer each handler body's type and effects
  4. Compute result: remove handled effect, add handler body effects
  5. `resume` is typed as returning the operation's return type
- Test: write a State handler, verify State is removed from
  effect set, verify handler body effects are added

### Step 3: Resume checking

- `resume` valid only inside handler body
- At-most-once: static check that `resume` is called at most
  once per handler clause. This means:
  - `resume` cannot appear inside a loop or recursive call
  - `resume` cannot appear in both branches of a conditional
    unless one branch has zero resumptions
  - Implementation: control flow analysis on handler bodies,
    similar to definite assignment analysis
- Test: code that resumes twice is a compile error. Code that
  resumes zero times (Fail handler) is allowed.

### Step 4: Fail sugar

- `fail expr` desugars to `Fail.fail(expr)` — straightforward
- `expr?` desugars to:
  ```
  match expr
    Ok(v) -> v
    Err(e) -> Fail.fail(From.from(e))
  ```
  Needs From trait lookup for error type conversion.
- `catch expr` desugars to handler:
  ```
  handle expr
    Fail.fail(error) -> Err(error)
  then |value| Ok(value)
  ```
- Test: `?` operator works, `catch` converts effectful to Result

### Step 5: Standard effects

Define the standard library effects (KERNEL §5.10):
- `IO` in `kea-io` (or built-in for bootstrap)
- `Fail E` in `kea-core`
- `Alloc` in `kea-core`
- `State S`, `Log`, etc. as library effects (can be deferred)

For bootstrap: `IO` and `Fail` are the essential ones. `IO` is
the runtime-handled effect. `Fail` has sugar.

## Testing

- Effect declarations: declare, perform, verify in inferred type
- Handlers: write handlers for State, Log, Fail; verify effect
  removal and substitution
- Resume: at-most-once enforced; zero-resumption (Fail) works
- Fail sugar: `?`, `fail`, `catch` all work
- Effect polymorphism: `fn map(f: A -[e]> B)` propagates `e`
- Handler composition: nested handlers remove effects one at a time
- Error diagnostics: unhandled effect at main boundary is a
  clear error message
- Property tests: handling an effect removes exactly that effect;
  effect rows remain well-formed after handling

## Definition of Done

- Can declare custom effects and perform their operations
- Can write handlers that intercept and handle effects
- Handler typing removes the handled effect, adds handler effects
- `resume` is enforced at-most-once
- `fail`, `?`, and `catch` work
- Nested handlers compose correctly
- Effect polymorphism works for higher-order functions
- Error messages for effect-related issues are clear
- `mise run check` passes

## Open Questions

- Deep vs shallow handlers? (KERNEL implies deep — the handler
  handles all occurrences of the effect in the computation, not
  just the first one. This is the Koka/Eff default.)
- Should handler clauses be order-dependent? (Proposal: no —
  each clause handles one operation, order doesn't matter. If
  the same operation has multiple clauses, it's a compile error.)
- How do we handle effects in handler bodies? If a handler body
  performs the same effect it's handling, is that a recursive
  handler or an error? (Proposal: it re-performs the effect,
  which must be handled by an outer handler. The current handler
  does not handle its own body's effects.)
- Must a handler cover all operations of the handled effect?
  (Proposal: yes — a handler for `Log` must handle `Log.log`.
  Partial handling (handle some operations, pass others through)
  is not supported in v0. If an effect has multiple operations,
  you handle all of them or none. This keeps the typing rule
  simple: handling effect E removes E entirely. Partial handling
  would need a way to express "E minus operation X" in the type,
  which is possible with row polymorphism but adds complexity.
  Defer to post-v0 if there's demand.)

## Downstream Notes

Things the 0c implementor should know about what comes after:

1. **0d needs Fail to compile as Result-passing.** The 0d brief explicitly
   says: compile `Fail.fail(e)` as `return Err(e)`, `?` as branch-on-error,
   `catch` as match-on-Result. This is just control flow — no handler
   machinery needed. Make sure Fail sugar desugaring is clean enough that
   0d can pattern-match on it in HIR/MIR lowering.

2. **Effect rows must be stable for the formal agent.** The Lean
   formalization migration ([lean-formalization](../todo/lean-formalization.md))
   starts as soon as 0c lands. The formal agent will model the `Ty`
   inductive with effect rows and prove properties. If effect row
   representation changes after 0c, it means rework in Lean. Get the
   representation right.

3. **Handler typing rule is the critical contract.** The exact rule from
   KERNEL §5.13 — handle removes the handled effect, adds handler body
   effects, other effects pass through — is what 0e will compile and
   what the formal agent will prove. Don't deviate from this without
   updating both briefs.

4. **kea-mcp must stay working.** The formal agent and other agents use
   `type_check`, `diagnose`, and `get_type` via MCP to validate behavior.
   When adding effect declarations and handlers, make sure MCP queries
   return effect information in inferred types.

5. **Effect operation classification matters for 0e.** When you implement
   effect operation calls, note whether the operation is:
   - zero-resume (Fail) — never calls `resume`
   - tail-resumptive — `resume` is last expression in handler
   - non-tail-resumptive — `resume` in non-tail position
   This classification drives 0e's compilation strategy. If you can
   surface it during type-checking (even as metadata), 0e benefits.

## Progress
- 2026-02-26: Brief moved to `in-progress/`; workboard updated.
- 2026-02-26: Slice 1 landed — effect declaration registration + qualified operation typing (`dad49e5`).
- 2026-02-26: Slice 2 landed — `handle`/`resume` AST+parser+typeck, `fail`/`?`/`catch` desugaring, and core matrix tests (`01f9e12`).
- 2026-02-26: Slice 3 landed — matrix tightening tests for resume legality detail (`lambda`, loop), resume type matching, handler operation coverage, plus parser coverage for `resume` and empty-handler rejection (`4de4eab`).
- 2026-02-26: Closeout verification complete — `mise run check-full` green (workspace lint/tests/doctests).
- 2026-02-26: Brief moved to `done/`; `BRIEFS/INDEX.md` synchronized.
- **Follow-up (tooling/DX):** add explicit `kea-mcp` regression tests for effect declaration + handler/query flows so these features stay machine-queryable for formal/tooling agents.

### Test Matrix (0c)
- effect declaration parsing
- effect operation call type/effect inference
- handler effect removal
- nested handler shadowing
- `resume` legality + at-most-once rejection
- `fail` / `?` / `catch` desugar + type checking

### Scope Guardrails
- 0c is AST/parser/typeck/desugar only.
- No runtime handler implementation strategy work here (belongs to 0e).
- Handler typing remains row-native only; no legacy fallbacks.
- Every slice commit must pass:
  - `mise run check`
  - `PKG=kea-syntax mise run test-pkg` and/or `PKG=kea-infer mise run test-pkg` based on touched crates
