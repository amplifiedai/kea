# Brief: Lean Formalization Migration

**Status:** active
**Priority:** Phase 0c-0e (parallel track — formal agent works alongside implementation)
**Depends on:** 0c-effect-handlers (effect rows must be in the type system before formalizing them)
**Blocks:** nothing directly — formal proofs validate but don't gate implementation

## Motivation

Rill has a substantial Lean 4 formalization: ~50 source files, 153 MCP-verified
log entries, covering HM inference, Rémy row unification, lacks constraints,
generalize/instantiate, supertrait graphs, declarative/algorithmic typing
soundness, evaluator soundness slices, and nominal/boundary typing bridges.

This work transfers to Kea because Kea's core type system *is* Rill's, extended
with effect rows. The Lean model's `Ty` inductive, `Subst`, `Unify`, `Generalize`,
`LacksConstraints`, and `Traits` modules map directly to kea-types and kea-infer.
The MCP-first verification workflow (predict → probe → classify → act → trace)
transfers unchanged — Kea already has `kea-mcp` with `type_check`, `diagnose`,
and `get_type`.

Migrating gives us:

1. **Formal backing during the riskiest phases.** 0d and 0e are where subtle
   type/effect interactions surface. Having machine-checked proofs for the
   underlying type system catches issues that proptests miss.
2. **Effect typing formalization as new work.** No language we know of has a
   Lean formalization of row-typed algebraic effect handlers. This is novel
   and publishable.
3. **Continuity.** The formal agent has 153 sessions of context and workflow
   discipline. Migrating while that context is fresh is cheaper than recreating
   it later.

## What Transfers (Phase 1: Core Type System)

Direct migration from `rill/formal/Rill/` — rename `Rill` → `Kea`, extend
`Ty` with effect rows.

### Definitions (migrate as-is, extend for effects)

| Rill module | Kea module | Migration notes |
|-------------|-----------|-----------------|
| `Ty.lean` | `Kea/Ty.lean` | Add `EffRow` to `Ty` inductive. Add effect variable kind. |
| `Substitution.lean` | `Kea/Substitution.lean` | Extend `applySubst` for effect rows. |
| `FreeVars.lean` | `Kea/FreeVars.lean` | Add `freeEffectVars` mutual case. |
| `OccursCheck.lean` | `Kea/OccursCheck.lean` | Extend occurs check to effect variables. |
| `LacksConstraints.lean` | `Kea/LacksConstraints.lean` | Transfer as-is. |
| `Unify.lean` | `Kea/Unify.lean` | Extend for effect row unification. |
| `Generalize.lean` | `Kea/Generalize.lean` | Quantify effect variables. |
| `Traits.lean` | `Kea/Traits.lean` | Transfer as-is. |
| `Typing.lean` | `Kea/Typing.lean` | Extend typing judgments with effect annotations. |

### Properties (migrate, re-prove after Ty extension)

Transfer all Properties/ files. Most proofs should survive the `Ty` extension
with minor fixups (additional cases in mutual recursion). Files that need
substantive rework:

- `UnifyReflexive.lean` — add effect row reflexivity case
- `UnifyConsistent.lean` — extend for effect unification
- `SubstIdempotent.lean` — additional effect substitution case
- `RemyPreservesLabels.lean` — effect rows use same Rémy decomposition
- `TraitBoundsPreserved.lean` — effect variables in trait bounds

Files that transfer unchanged:
- `LacksBlocksDuplicate.lean` — no effect interaction
- `RowFieldsSorted.lean` — structural, no effect interaction
- `DecomposeFields.lean` — structural

### Drop (Rill-specific, don't migrate)

- `ColExpr.lean` — Rill column expression DSL
- `DataFrame.lean` — Rill dataframe verb typing
- `Dimensions.lean` — Rill dimension model (Kea has its own in kea-types)
- `Eval.lean` — Rill evaluator semantics (Kea compiles, doesn't interpret)
- All `Properties/DataFrame*`, `Properties/ColumnBoundary*` — Rill domain
- All `Properties/*Parity*.lean` — Rill-specific type constructor parity slices
- All `Properties/*Boundary*.lean`, `Properties/*Bridge*.lean` — Rill boundary typing

### Maybe migrate later (if Kea adds equivalent features)

- `Eval.lean` evaluator soundness — could inform Kea REPL semantics or
  comptime evaluation, but not urgent

## What's New (Phase 2: Effect Typing Formalization)

This is genuinely new work — no Rill equivalent exists.

### Effect declarations and operations

```lean
-- Effect declaration typing
inductive EffectDecl where
  | mk : Name → List TypeParam → List OperationSig → EffectDecl

-- Effect operation typing: performing an operation adds the effect
-- to the current row
```

### Handler typing (KERNEL §5.13)

The core theorem to prove:

```
Given:
  expr : T  with effects {E, R...}
  handler for E covers all operations
  each handler body : _  with effects {H...}
Then:
  handle expr { ... } : T  with effects {H..., R...}
```

This is the **effect removal** theorem — the most important property
of the handler system.

### Target theorems (new)

| Theorem | Statement | Difficulty |
|---------|-----------|------------|
| `handle_removes_effect` | Handler for E removes E from effect row | Medium |
| `handle_adds_handler_effects` | Handler body effects appear in result | Medium |
| `handle_preserves_other_effects` | Unhandled effects pass through | Medium |
| `resume_at_most_once` | Static linearity check is sound | Hard |
| `fail_is_zero_resume` | Fail handler never resumes; equivalent to Result | Medium |
| `fail_result_equivalence` | `catch expr` ≡ Result-passing transformation | Hard |
| `nested_handlers_compose` | Inner handler shadows outer for same effect | Medium |
| `effect_polymorphism_sound` | Effect variable generalization/instantiation preserves soundness | Hard |
| `tail_resumptive_classification` | Tail-resumptive handler compiles equivalently to direct call | Medium |
| `capability_direct_call_sound` | Unintercepted capability effect = direct runtime call | Easy |

### MCP-first workflow

Same protocol as Rill:

1. **Predict**: State Lean conjecture + preconditions
2. **Probe**: Run kea-mcp checks (happy path, boundary, adversarial)
3. **Classify**: Agreement / precondition gap / model divergence
4. **Act**: Prove, revise, or log divergence
5. **Traceability**: Link theorems, file edits, MCP evidence

The formal agent should maintain `formal/mcp-log.md` in the same format.

## Scheduling: Parallel, Not Sequential

The formal agent should run **in parallel** with 0c/0d/0e implementation:

```
0c implementation ←→ Phase 1 migration (core type system)
0d implementation ←→ Phase 1 proof repair (Ty extension fixups)
0e implementation ←→ Phase 2 new work (effect typing proofs)
```

### Why parallel works

1. **Independent codebases.** Lean proofs don't depend on Rust compilation.
   The formal agent uses MCP to probe the running Kea compiler, same as
   it did with Rill.

2. **MCP-first absorbs design churn.** If effect typing rules change during
   0e, the formal agent discovers this via MCP probes before proving. The
   predict→probe→classify loop is designed for exactly this.

3. **The formal agent has context now.** 153 MCP log entries, deep familiarity
   with the Rémy/HM model, the two-judgment architecture, supertrait gaps.
   This context decays if we wait.

4. **Formal work feeds back into implementation.** The Rill formalization
   found real discrepancies (supertrait gap witnesses, substitution bridge
   issues). Same will happen with effect typing.

### Risk: design churn in effect typing

The main risk is that handler typing rules change during 0e prototyping
(e.g., switching from evidence passing to CPS changes how handlers compose).
Mitigation:

- Phase 1 (core migration) is zero risk — the HM+row core is stable.
- Phase 2 effect proofs should start with the **type-level** properties
  (effect removal, handler composition) which are strategy-independent.
  Compilation strategy (evidence vs CPS) only affects **codegen-level**
  properties, which are Phase 2 stretch goals anyway.

## Implementation Plan

### Phase 1: Core migration (start after 0c lands effect rows)

1. Create `kea/formal/` directory with Lake project, batteries dependency.
2. Copy `Rill/Ty.lean` → `Kea/Ty.lean`. Extend `Ty` inductive with effect
   row constructors.
3. Migrate `Substitution`, `FreeVars`, `OccursCheck` — extend mutual
   recursion for effect rows.
4. Migrate `Unify` — add effect row unification cases.
5. Migrate `Generalize` — add effect variable quantification.
6. Migrate `LacksConstraints`, `Traits` — transfer directly.
7. Re-prove all Properties/ theorems. Fix broken cases from Ty extension.
8. Migrate `Typing.lean` — extend with effect annotations.
9. Set up MCP-first workflow against kea-mcp. First log entries.

### Phase 2: Effect typing formalization (start during 0d/0e)

1. Model effect declarations and operation typing.
2. Model handler expressions and typing rule (§5.13).
3. Prove `handle_removes_effect` — the core property.
4. Prove handler composition (nested handlers).
5. Model resume and prove at-most-once linearity.
6. Model Fail as zero-resume and prove Result equivalence.
7. Prove effect polymorphism soundness.
8. (Stretch) Model tail-resumptive classification and prove
   compilation equivalence.

### Phase 2.5: Vertical integration (during/after 0e)

1. Connect effect typing to the existing typing soundness theorems.
2. Prove that the full type+effect system is sound (the big theorem).
3. If evaluator semantics exist in Kea, extend evaluator soundness.

## Testing / Verification

- `lake build` must succeed with zero `sorry` at each milestone.
- MCP log entries for every theorem that touches runtime behavior.
- Rust proptest↔Lean theorem mapping maintained in a FORMAL.md.
- CI integration: `lake build` in Kea CI (separate job, non-blocking
  initially, blocking after Phase 1 completes).

## Definition of Done

### Phase 1

- `kea/formal/` exists with Lake project.
- All core type system modules migrated and extended for effect rows.
- All transferable Properties/ theorems re-proved.
- Zero `sorry`.
- MCP-first workflow operational against kea-mcp.

### Phase 2

- Effect declaration/operation typing modeled.
- Handler typing rule (§5.13) modeled and effect removal proved.
- Resume at-most-once proved.
- Fail/Result equivalence proved.
- Nested handler composition proved.
- Effect polymorphism soundness proved.
- Zero `sorry`.
- FORMAL.md mapping maintained.

## Non-Goals

- Formalizing codegen / MIR lowering (too implementation-specific).
- Formalizing the actor/concurrency model (Phase 3+ work).
- Formalizing memory model / ownership (depends on 0f stabilizing).
- Blocking implementation on formal proofs (formal work validates,
  doesn't gate).

## Progress

- 2026-02-26: Brief moved from `todo/` to `in-progress/` to start Phase 1 migration in parallel with 0d codegen work.
- 2026-02-26: Bootstrapped `formal/` in Kea by cannibalizing `/Users/chris/Projects/rill/formal`, renaming the Lean namespace target from `Rill` to `Kea`, and preserving the roadmap + MCP verification history baseline.
- 2026-02-26: `cd formal && lake build` passes in Kea after namespace-portability proof repairs in `SubstBridge`, `UnifyReflexive`, `PrecisionLeafParity`, and `ShapeConstructorParity` (warning-only simp lint remains).
- 2026-02-26: Repository guardrail check passes after formalization bootstrap (`mise run check`).
- **Next:** prune Rill-only modules from the root target, align `Kea/Ty.lean` with `kea-types` effect-row shape, and log first Kea MCP-first verification entries.
