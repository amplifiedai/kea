# Brief: Remove Remaining Rill Surface from Core (Post-0b Cleanup)

**Status:** ready
**Priority:** v1-critical
**Depends on:** 0a-lexer-parser, 0b-type-system-core
**Blocks:** 0c-effect-handlers, 0d-codegen-pure

## Motivation

0a and 0b are marked done, but core crates still carry substantial
Rill-era surface that is not part of Kea's locked v0 language shape.
If we continue into 0c/0d without removing this, we will compound
checker/codegen complexity on features that are out of scope.

This brief is a focused decontamination pass: keep Kea core aligned
with KERNEL/CALL-SYNTAX and remove unsupported syntax/type-system
substrate from parser, AST, and inference.

## Findings (Broader than the initial spot-check)

### 1) Pipe substrate remains in AST/infer

`|>/$>/!>` token parsing was removed, but pipe AST/inference paths are
still present (`ExprKind::Pipe`, `PipePlaceholder`, pipe inference
helpers). This is dead/unsupported surface that should be deleted.

### 2) DataFrame/SQL/ColumnExpr surface remains in core

Despite 0b cleanup goals, core crates still include:
- AST nodes (`Frame`, `DfVerb`, ColumnExpr grammar, SQL/template blocks)
- parser paths/tests for dataframe verbs and sql/frame literals
- `kea-types` variants (`DataFrame`, `Column`, `GroupedFrame`, `Dynamic`)
- column-expression rule tables and dataframe-specific trait plumbing
- large `kea-infer` dataframe/column typing regions
- `sqlparser` dependency in `kea-infer`

This is a large, active surface in core, not just compatibility stubs.

### 3) HKT-era kind arrows remain

`Kind::Arrow`, `KindAnnotation::Arrow`, and helper paths still exist.
Kea v0 design is `*` + `Eff` only (no HKTs).

### 4) Additional rill-era expression forms remain unscoped

AST/parser still carry non-briefed forms such as `Spawn` expression,
`Await`, `StreamBlock`, `Yield/YieldFrom`, actor send/control-send
syntax. These may become valid later, but they are currently unbriefed
for 0a/0b and should not silently persist in core without an explicit
brief/spec decision.

### 5) Guard against reintroducing deleted 0b effect-lattice scaffolding

0b removed lattice effects (`EffectLevel`, `EffectTerm`,
`EffectConstraint`) in favor of row-native effect checking. This cleanup
brief should keep that invariant explicit as a regression gate while
removing remaining rill substrate.

## Design Constraints

1. **Spec-first:** If a feature is not in KERNEL/CALL-SYNTAX and has no
   active brief, it should not remain in core as executable surface.
2. **No hidden compatibility mode:** Unsupported features should become
   explicit parse/type errors (or be removed), not latent codepaths.
3. **Library over language syntax:** Future data-processing/distributed
   features should re-enter through explicit briefs and library/runtime
   design, not inherited parser internals.

## Implementation Plan

### Step 1: AST and parser contraction

- Remove pipe AST variants and placeholder nodes.
- Remove dataframe/sql/template/column-expr parse paths and tests from
  core syntax crates.
- Remove unbriefed async/stream/actor-send expression forms unless they
  are explicitly covered by an accepted brief/spec update.
- Keep parser diagnostics clear: unsupported syntax should fail with
  actionable errors.

### Step 2: Type and inference contraction

- Remove dataframe/column/dynamic/grouped-frame type variants from
  `kea-types`.
- Remove column-expression rule machinery from `kea-types`.
- Remove dataframe/sql/column typing from `kea-infer`.
- Drop `sqlparser` dependency.
- Delete HKT-era kind-arrow paths (`Kind::Arrow`, related inference and
  annotation handling), keeping only `Kind::Star` and `Kind::Eff`.

### Step 3: Test and docs realignment

- Delete or rewrite tests that rely on removed surface.
- Add regression tests proving unsupported syntax is rejected.
- Update relevant docs/brief references and ensure done briefs reflect
  actual completion state.

## Acceptance Gates

All must pass:

1. `mise run check`
2. `PKG=kea-syntax mise run test-pkg`
3. `PKG=kea-infer mise run test-pkg`
4. `mise run check-full`

Symbol grep gates (no code hits in core crates):

- Pipes:
  - `ExprKind::Pipe`
  - `PipePlaceholder`
- Dataframe/column surface:
  - `DataFrame`
  - `GroupedFrame`
  - `ColumnExpr`
  - `DfVerb`
  - `Frame`
  - `EmbeddedBlock`
  - `SqlBlock`
  - `TemplateBlock`
  - `sqlparser`
- HKT arrows:
  - `Kind::Arrow`
  - `KindAnnotation::Arrow`
  - `from_arity(` (kind-constructor helper)
- 0b lattice regression guard:
  - `EffectLevel`
  - `EffectTerm`
  - `EffectConstraint`
  - `solve_effect_constraints`
  - `effects_leq`
  - `effects_as_row`
  - `effect_annotation_to_effects`
  - `effect_label`

## Definition of Done

- Core AST/parser/infer/types match locked Kea v0 surface for 0a/0b.
- No latent Rill parser/typechecker substrate remains in core crates.
- Any deferred feature area has an explicit brief/spec entry instead of
  inherited implementation residue.
- Workboard updated with this brief moved to done.

## Scope Boundary

**In scope now:** Removing unsupported inherited core surface and
realigning with current Kea docs/brief commitments.

**Out of scope now:** Designing future data-processing/streaming syntax
or distributed-runtime expression forms. Those require separate design
briefs/spec updates.
