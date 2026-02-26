# MCP Verification Log

Log of MCP-assisted verification sessions for the Rill type system formalization. Each entry records when and how the MCP was used to validate Lean conjectures against the running Rust implementation, investigate discrepancies, or develop proofs.

This log serves as primary evidence for the formal verification workflow — it documents the bidirectional semantic bridge between the Lean model and the Rust compiler in practice. When writing up findings, refer to this log for concrete examples.

---

## Entry Format

```
### YYYY-MM-DD: Brief description

**Context**: What theorem/property was being investigated
**MCP tools used**: Which tools (type_check, get_type, evaluate, diagnose, etc.)
**Lean side**: What the formal model predicted
**Rust side**: What the MCP reported
**Outcome**: Agreement / discrepancy found / proof insight gained
**Impact**: What changed as a result (Lean fix, Rust fix, new test, design clarification)
```

## Workflow Protocol (MCP-first)

For bridge and model-alignment work, use this default sequence and record it in each entry:

1. `Predict`: state the Lean-side conjecture and explicit preconditions first.
2. `Probe`: run MCP checks (happy path, boundary case, adversarial case) before proving.
3. `Classify`: mark result as agreement, precondition gap, or model divergence.
4. `Act`: either prove the theorem, revise its statement/preconditions, or log divergence.
5. `Traceability`: link the resulting Lean theorem(s), file edits, and any Rust/MCP evidence.

This protocol is required evidence for future writeups on theorem/implementation co-evolution.

---

## Entries

### 2026-02-12: M1 bridge workflow using MCP-first prediction/probe classification

**Context**: Applying the new MCP-first protocol to bridge work in `SubstBridge.lean`, specifically validating branch behavior assumptions before extending compat/WF lemmas.

**MCP tools used**: `reset_session`, `type_check`, `get_type`

**Predict (Lean side)**:
- Open-row merge should type-check and preserve projected tuple shape.
- Missing required fields should reject with missing-field diagnostics (not silently unify).
- Conflicting field constraints should reject with type mismatch.
- Constructor-level expressions (`list`, `tuple`, record literals) should infer stable closed types when no substitution-domain vars are involved (matches no-domain-vars bridge lemmas).

**Probe (Rust side via MCP)**:
- `(|r| #(r.a, r.b))(#{ a: 1, b: "x", c: true })` -> `ok`, type `#(Int, String)`.
- `(|r| #(r.a, r.b))(#{ a: 1 })` -> `error`, `missing field b`.
- `(|r| r.a + 1)(#{ a: "x" })` -> `error`, field `a` type mismatch (`String` vs `Int`).
- `get_type (|x| x)([1,2,3])` -> `List(Int)`.
- `get_type (|x| x)(["u","v"])` -> `List(String)`.
- `get_type #(#{ x: 1 }, [1,2])` -> `#(#{ x: Int }, List(Int))`.

**Classify**: Agreement.

**Outcome**: The probes match theorem intent for the current bridge step: branch failures remain explicit, and constructor-level typing behaves as expected for no-domain-vars cases.

**Impact**:
- Proceeded to add generic no-domain-vars compat/WF bridge lemmas plus constructor corollaries in `formal/Rill/Properties/SubstBridge.lean`.
- Updated bridge tracking docs (`FORMAL.md`, `formal/ROADMAP.md`) to reflect constructor-level bridge coverage progress.

### 2026-02-12: M1 theorem-schema milestone — reachable domain lookups after successful `unifyRows` updates

**Context**: Closing roadmap milestone M1 item for a single schema theorem capturing compat/WF agreement on values reachable from successful `unifyRows` branch updates under idempotent substitutions.

**MCP tools used**: `reset_session`, `get_type`, `type_check`

**Predict (Lean side)**:
- Domain lookup behavior should be stable across representative instantiations:
  - type-variable lookup behavior observed as stable identity-instantiation (`(|x| x)` at multiple concrete types),
  - row-tail lookup behavior observed as stable field projection (`(|r| r.a)` with and without required field).
- Missing-field paths should reject explicitly rather than producing implicit coercions.

**Probe (Rust side via MCP)**:
- `get_type (|x| x)(1)` -> `Int`.
- `get_type (|x| x)("s")` -> `String`.
- `get_type (|r| r.a)(#{ a: 1, b: true })` -> `Int`.
- `type_check (|r| r.a)(#{ b: true })` -> `error`, missing field `a`.

**Classify**: Agreement.

**Outcome**:
- Added theorem `unifyRows_success_update_domain_lookup_compat_wf_agree` in `UnifyExtends.lean`.
- Added generic row-lookup bridge lemma `applySubstRowCompat_empty_open_eq_applySubstRowWF_of_row_lookup_idempotent` in `SubstBridge.lean`.

**Impact**:
- M1 schema milestone completed in `formal/ROADMAP.md`.
- Mapping updated in `FORMAL.md`.

### 2026-02-12: M2 branch-local wrappers for compat/WF bridge schema

**Context**: Refining the M1 schema theorem into branch-local wrappers (`no-update`, `single-bind`, `open-open`) for direct use in `unifyRows` branch proofs.

**MCP tools used**: `reset_session`, `get_type`

**Predict (Lean side)**:
- No-update branch behavior should preserve type shape (`|r| r` on a closed record).
- Single-bind style behavior should preserve required projection typing (`|r| r.a` over wider input rows).
- Open-open style composition should preserve independent projections from two open inputs.

**Probe (Rust side via MCP)**:
- `get_type (|r| r)(#{ a: 1 })` -> `#{ a: Int }`.
- `get_type (|r| r.a)(#{ a: 1, b: true })` -> `Int`.
- `get_type ((|x| |y| #(x.a, y.b))(#{ a: 1, c: true }))(#{ b: "u", d: 2 })` -> `#(Int, String)`.

**Classify**: Agreement.

**Outcome**:
- Added `unifyRows_no_update_domain_lookup_compat_wf_agree`.
- Added `unifyRows_single_bind_domain_lookup_compat_wf_agree`.
- Added `unifyRows_open_open_domain_lookup_compat_wf_agree`.

**Impact**:
- M2 branch-local substitution equivalence milestone marked complete in `formal/ROADMAP.md`.
- `FORMAL.md` mapping table updated with the three new branch-local bridge lemmas.

### 2026-02-12: M2 capstone theorem — compat/WF swap invariance packaging

**Context**: Completing the M2 capstone by introducing a reusable predicate-level contract (`CompatWFAgreeOnDomainLookups`) and proving named capstone theorem `unifyRows_success_update_compat_wf_swap_invariant`.

**MCP tools used**: `reset_session`, `get_type`, `type_check`

**Predict (Lean side)**:
- This step is proof-structure packaging (no new runtime semantics): same acceptance/rejection behavior should hold for representative row-projection probes used in prior M2 checks.

**Probe (Rust side via MCP)**:
- `get_type (|r| #(r.a, r.b))(#{ a: 2, b: "q", c: false })` -> `#(Int, String)`.
- `type_check (|r| #(r.a, r.b))(#{ a: 2 })` -> `error`, missing field `b`.

**Classify**: Agreement.

**Outcome**:
- Added predicate `CompatWFAgreeOnDomainLookups`.
- Added capstone theorem `unifyRows_success_update_compat_wf_swap_invariant`.

**Impact**:
- M2 swap-invariance theorem milestone completed in `formal/ROADMAP.md`.
- `FORMAL.md` mapping updated with the predicate and capstone theorem.

### 2026-02-12: M3 WF-phrased global contract strengthening

**Context**: Strengthening the global contract by packaging preconditioned extension and compat/WF swap invariance into one theorem (`unifyRows_extends_rowMap_preconditioned_wf`).

**MCP tools used**: `reset_session`, `get_type`, `type_check`

**Predict (Lean side)**:
- This is a theorem-composition step (no semantic expansion), so prior branch behavior should remain stable:
  - valid open-row numeric projection should infer `Int`,
  - conflicting numeric operation on string field should reject with type mismatch.

**Probe (Rust side via MCP)**:
- `get_type (|r| r.a + 1)(#{ a: 3, b: "x" })` -> `Int`.
- `type_check (|r| r.a + 1)(#{ a: "x" })` -> `error`, field `a` type mismatch (`String` vs `Int`).

**Classify**: Agreement.

**Outcome**:
- Added theorem `unifyRows_extends_rowMap_preconditioned_wf` in `UnifyExtends.lean`.

**Impact**:
- M3 “WF phrasing” roadmap milestone completed.
- `FORMAL.md` mapping updated with the strengthened global contract theorem.

### 2026-02-12: M3 assumption split — idempotent vs acyclic contract boundary

**Context**: Isolating which parts of the strengthened global contract require `Idempotent` versus which can be exported with only `Acyclic`.

**MCP tools used**: `reset_session`, `get_type`, `type_check`

**Predict (Lean side)**:
- This step refactors assumptions at theorem boundaries, not runtime semantics.
- Projection behavior should remain unchanged:
  - valid field projection infers concrete type,
  - missing required field rejects with `missing_field`.

**Probe (Rust side via MCP)**:
- `get_type (|r| r.a)(#{ a: 10, c: true })` -> `Int`.
- `type_check (|r| r.a)(#{ c: true })` -> `error`, missing field `a`.

**Classify**: Agreement.

**Outcome**:
- Added `CompatWFAgreeOnDomainLookupsAcyclic`.
- Added bridge theorem `compatWFAgreeOnDomainLookupsAcyclic_of_idempotent`.
- Added split contract theorem `unifyRows_extends_rowMap_preconditioned_wf_split`.

**Impact**:
- M3 assumption-split roadmap milestone completed.
- Contract boundary is now explicit: extension proof remains idempotent-gated; swap-invariance can be consumed in acyclic form.

### 2026-02-12: M3 naming consolidation — canonical WF contract surface

**Context**: Final M3 cleanup to align theorem names and import intent. Introduced one canonical downstream theorem name and retained a compatibility projection theorem for prior naming shape.

**MCP tools used**: `reset_session`, `get_type`, `type_check`

**Predict (Lean side)**:
- Naming consolidation should not affect runtime semantics.
- Representative successful and failing row-projection behavior should remain unchanged.

**Probe (Rust side via MCP)**:
- `get_type (|r| #(r.a, r.b))(#{ a: 4, b: "z", c: false })` -> `#(Int, String)`.
- `type_check (|r| #(r.a, r.b))(#{ a: 4 })` -> `error`, missing field `b`.

**Classify**: Agreement.

**Outcome**:
- Added canonical theorem `unifyRows_contract_wf`.
- Added compatibility theorem `unifyRows_extends_rowMap_preconditioned_wf_of_contract`.

**Impact**:
- M3 naming-alignment roadmap milestone completed.
- `FORMAL.md` mapping updated to reflect canonical import surface plus compatibility bridge.

### 2026-02-12: M4 kickoff — core typing judgment and first soundness theorem

**Context**: Starting M4 with a minimal but executable slice: declarative/core algorithmic typing for literals, variables, closed anonymous records, and projection in `Rill/Typing.lean`.

**MCP tools used**: `reset_session`, `get_type`, `type_check`

**Predict (Lean side)**:
- Closed anonymous records should infer closed structural record types.
- Valid projection should infer projected field type.
- Missing-field projection should reject with explicit diagnostics.
- One-shot multi-line `let` in `get_type` may still hit parser/tooling limitations (previously observed).

**Probe (Rust side via MCP)**:
- `get_type #{ a: 1, b: "x" }` -> `#{ a: Int, b: String }`.
- `get_type (|r| r.a)(#{ a: 1, b: true })` -> `Int`.
- `type_check (|r| r.a)(#{ b: true })` -> `error`, missing field `a`.
- `get_type` on multi-line `let` snippet returned a syntax error (tooling/parsing boundary, not a typing contradiction).

**Classify**: Agreement on typing behavior; expected tooling boundary confirmed for one-shot multi-line probe.

**Outcome**:
- Added `CoreExpr`/`CoreFields`, `inferExpr`/`inferFields`, `HasType`/`HasFieldsType`.
- Proved `inferExpr_sound` (and mutual field soundness companion) in `Typing.lean`.

**Impact**:
- M4 kickoff established with a machine-checked algorithmic-vs-declarative anchor.
- Provides a concrete base to extend toward let/lambda/app and full infer/unify fragment soundness.

### 2026-02-12: M4.1 extension — monomorphic let/lambda/application typing

**Context**: Extending `Rill/Typing.lean` beyond records/projection to include typed lambdas, lambda-head application, and monomorphic let-binding in both algorithmic and declarative layers.

**MCP tools used**: `reset_session`, `get_type`, `type_check`

**Predict (Lean side)**:
- Lambda application should infer concrete result type when argument matches.
- Mismatched application should reject with type mismatch.
- One-shot multi-line `let` snippets may still fail due parser/tooling boundary (already observed in prior sessions).

**Probe (Rust side via MCP)**:
- `get_type (|x| x)(1)` -> `Int`.
- `type_check (|x| x + 1)("s")` -> `error`, function-call type mismatch.
- `type_check` on multi-line `let id = |x| x; ...` style snippets produced syntax errors in this one-shot MCP path.

**Classify**: Agreement on lambda/app behavior; tooling boundary confirmed for one-shot multi-line `let` probes.

**Outcome**:
- `CoreExpr` extended with `lam`, `app`, `letE`.
- `inferExpr` and `HasType` extended accordingly.
- `inferExpr_sound` proof extended to new cases.

**Impact**:
- M4 now has a concrete monomorphic function-typing bridge layer.
- Creates the immediate base for next step: generalizing app soundness from lambda-head-only to function-valued expressions.

### 2026-02-12: M4.2 generalization — function-valued application soundness

**Context**: Generalizing `Typing.lean` application soundness from lambda-head syntax to function-valued expressions inferred by `inferExpr env fn`.

**MCP tools used**: `reset_session`, `get_type`, `type_check`

**Predict (Lean side)**:
- Higher-order application should type-check when function argument and parameter types align.
- Mismatched higher-order application should reject with function-call type mismatch.
- Record-projection functions passed as values should preserve projection result type.

**Probe (Rust side via MCP)**:
- `get_type (|f| f(1))(|x| x + 1)` -> `Int`.
- `type_check (|f| f("a"))(|x| x + 1)` -> `error`, expected `Int`, got `String`.
- `get_type (|f| f(#{ a: 1 }))(|r| r.a)` -> `Int`.

**Classify**: Agreement.

**Outcome**:
- `inferExpr` app branch now accepts function-valued `fn` expressions (single-arg monomorphic shape).
- `inferExpr_sound` app proof rewritten against inferred function type equality (not lambda-head syntax).

**Impact**:
- M4 monomorphic core now supports compositional function application reasoning.
- Reduces the gap to a broader algorithmic-vs-declarative proof for infer/unify fragment.

### 2026-02-12: M4.3 equivalence milestone — declarative <-> algorithmic core typing

**Context**: Completing the current M4 core slice by adding the converse direction (`inferExpr_complete`) and equivalence theorem (`inferExpr_iff_hasType`) for the monomorphic expression subset.

**MCP tools used**: `reset_session`, `get_type`, `type_check`

**Predict (Lean side)**:
- Valid higher-order application remains accepted with inferred `Int`.
- Invalid higher-order argument type remains rejected.
- These probes should match both directions of the new equivalence theorem on the modeled slice.

**Probe (Rust side via MCP)**:
- `get_type (|f| f(1))(|x| x + 1)` -> `Int`.
- `type_check (|f| f("a"))(|x| x + 1)` -> `error`, expected `Int`, got `String`.

**Classify**: Agreement.

**Outcome**:
- Added `inferExpr_complete`.
- Added `inferExpr_iff_hasType`.

**Impact**:
- Current core typing model now has bidirectional correspondence, not just one-way soundness.
- This is the first true algorithmic/declarative equivalence checkpoint in `formal/Rill/Typing.lean`.

### 2026-02-12: M4.4 environment-congruence transport for core typing

**Context**: Adding weakening-style infrastructure for the core model via lookup-equivalent environment transport (`hasType_lookup_congr`, `inferExpr_lookup_congr`).

**MCP tools used**: `reset_session`, `get_type`

**Predict (Lean side)**:
- Programs that differ only by bound-variable names (lookup-equivalent environments) should infer identical types.
- Record projection with renamed binder identifiers should preserve inferred type.

**Probe (Rust side via MCP)**:
- `get_type (|x| x + 1)(1)` -> `Int`.
- `get_type (|y| y + 1)(1)` -> `Int`.
- `get_type (|r| r.a)(#{ a: 1, b: true })` -> `Int`.
- `get_type (|row| row.a)(#{ a: 1, b: true })` -> `Int`.

**Classify**: Agreement.

**Outcome**:
- Added `hasType_lookup_congr`.
- Added `inferExpr_lookup_congr`.

**Impact**:
- Core typing now has explicit environment-transport infrastructure, enabling cleaner future proofs for let/lambda extensions and substitution-style lemmas.

### 2026-02-09: Phase 1 model validation — row polymorphism and let-generalization

**Context**: Validating that the Lean Generalize.lean model (generalize + instantiate) matches Rust behavior before extending Ty.lean with Phase 2 constructors.

**MCP tools used**: `type_check`, `get_type`, `list_bindings`, `reset_session`

**Lean side**: The Lean `generalize` function quantifies type/row vars free in the type but not in the environment. `instantiate` creates fresh vars and transfers lacks constraints. For `let get_name = |r| r.name`, the model predicts generalization to `∀ a r. (r lacks name) => (#{ name: a | r }) -> a`, and instantiation at two different record types should produce different concrete return types.

**Rust side**: MCP confirms:
- `get_type` on `|r| r.name` returns `(#{ name: a | r0 }) -> a` (row-polymorphic, as predicted)
- After `let get_name = |r| r.name`, applying to `#{ name: "alice", age: 30 }` yields `a: String`
- Applying to `#{ name: 42, x: true }` yields `b: Int`
- `list_bindings` shows `get_name: (#{ name: t2 | r0 }) -> t2` (generalized, as predicted)
- Anonymous record fields are sorted: `#{ name: "alice", age: 30 }` becomes `#{ age: Int, name: String }`

**Outcome**: Agreement. The Lean model's generalize/instantiate matches the Rust compiler's behavior exactly. Row variable naming differs (Lean uses abstract Nat IDs, Rust uses `r0`/`t2` display names) but the structure is identical.

**Impact**: Confirms the Phase 1 formalization is correct. Proceeding to add Phase 2 constructors (Record, DataFrame) to Ty.lean.

### 2026-02-09: Phase 2 formalization — structural projection and record registry

**Context**: Validating Phase 2 Lean additions: `Ty.record` constructor, `RecordRegistry`, `TraitRegistry`, `dfMutate`/`dfDrop`. Testing structural projection (named record unifies with anonymous record having same fields).

**MCP tools used**: `type_check`, `get_type`, `list_bindings`, `reset_session`

**Lean side**: The Lean `unify` function has two new cases:
- `| .record _ r1, .anonRecord r2 => unifyRows st fuel r1 r2` (structural projection)
- `| .record n1 r1, .record n2 r2 => if n1 == n2 then unifyRows st fuel r1 r2 else err`
`RecordRegistry.toType` returns `Ty.record name row`, and `recordRegistryRoundTrip` is proved (no sorry). `traitCoherenceRejectsDuplicate` is proved (no sorry).

**Rust side**: MCP confirms:
- `record Point { x: Int, y: Int }` registers as nominal type `Point`
- `fn get_x(r) { r.x }` gets type `(#{ x: a | r0 }) -> a` (row-polymorphic)
- `get_x(Point { x: 1, y: 2 })` returns `Int` — structural projection works
- `get_x(#{ x: "hello", z: true })` returns `String` — same function on anonymous record
- All 5 Phase 2 Rust property tests pass (proptest)

**Outcome**: Agreement. The Lean model's structural projection case matches the Rust compiler. Named records project to their structural row when unified with open rows. Two theorems fully proved: `recordRegistryRoundTrip` (simp) and `traitCoherenceRejectsDuplicate` (simp).

**Impact**: Phase 2 formalization is structurally complete. Definitions: `Ty.record`, `Ty.dataframe`, `RecordRegistry`, `TraitRegistry`, `dfMutate`, `dfDrop`, `dfUpdate`. 2 theorems proved, 3 theorem stubs remain (`recordStructuralProjection`, `dataframeMutateDropRoundTrip`, `dataframeMutateExistingErrors`).

### 2026-02-10: Trait bound enforcement — generalize/instantiate + check_trait_bounds

**Context**: Validating the new trait bound enforcement pipeline. Rust now has `TypeScheme.bounds`, `Unifier.trait_bounds`, `check_trait_bounds`, and `apply_where_clause`. The Lean model was extended with matching definitions: `TypeScheme.bounds`, `UnifyState.traitBounds`, `checkTraitBounds`, `typeNameForTraitCheck`. Theorem stub `traitBoundsSurviveInstantiate` added.

**MCP tools used**: `type_check`, `get_type`, `evaluate`, `list_bindings`, `reset_session`

**Lean side**: The Lean model predicts:
- `generalize` preserves trait bounds for quantified type vars (mirrors lacks constraint preservation for row vars)
- `instantiate` transfers bounds to fresh type vars via `typeMapping` (mirrors lacks transfer via `rowMapping`)
- `checkTraitBounds` resolves type vars through substitution, maps to type names via `typeNameForTraitCheck`, and checks `TraitRegistry.satisfies`. Unresolved (still-polymorphic) vars are skipped.
- For `fn total(x) where x: Summable { x }`, the scheme `∀ a. (a: Summable) => a -> a` should: accept `total(42)` when `impl Summable for Int` exists, reject `total("hello")` when no `impl Summable for String` exists.

**Rust side**: MCP confirms all predictions:
- `trait Summable { fn sum(self) -> Int }` + `impl Summable for Int` — registered OK
- `fn total(x) where x: Summable { x }` — generalized to `(a) -> a` (bounds hidden in scheme)
- `total(42)` → type `Int` (Int implements Summable, bound satisfied)
- `total("hello")` → error: `type 'String' does not implement trait 'Summable'` with help text `required by a 'where' bound: 'Summable'`
- `total(3.14)` → error: `type 'Float' does not implement trait 'Summable'` (same pattern)
- Multiple bounds: `fn process(x) where x: Summable, x: Showable { x }` with `impl Showable for Int`
  - `process(42)` → type `Int` (both bounds satisfied)
  - `process("hello")` → TWO errors reported: `String` doesn't implement `Showable` AND `String` doesn't implement `Summable` (both bounds checked independently)

**Outcome**: Full agreement. The Lean model's trait bound propagation through generalize/instantiate matches the Rust compiler exactly. The deferred-constraint architecture (mirror of lacks constraints) works as designed. Multiple bounds are checked independently and produce separate diagnostics.

**Impact**: Trait bound enforcement is end-to-end validated. Lean definitions added: `TypeScheme.bounds`, `UnifyState.traitBounds`, `UnifyState.addTraitBound`, `checkTraitBounds`, `typeNameForTraitCheck`, `TraitRegistry.satisfies`. Theorem stub: `traitBoundsSurviveInstantiate`. The pattern of "deferred constraints checked post-inference" is now established for both row constraints (lacks) and type constraints (trait bounds), confirming the architecture generalizes.

### 2026-02-10: Phase 3 DataFrame verb formalization — definitions and proofs

**Context**: Formalizing Phase 3 DataFrame verb operations (filter, sort, distinct, select, summarize) and `resolve_atom` from uncommitted Rust code in `typeck.rs:965-1091`. Proving schema preservation and transformation properties.

**MCP tools used**: `type_check` (attempted), `reset_session`

**Lean side**: Added 6 definitions to DataFrame.lean:
- `resolveAtom` — column name → type via row unification (mirrors `resolve_atom` in typeck.rs:1093-1117)
- `dfFilter`, `dfSort`, `dfDistinct` — identity on type (schema preserved)
- `dfSelect` — row restriction via `resolveAtom` + closed output row
- `dfSummarize` — new closed row from (label, type) pairs
- `RowFields.select` — field subset helper

Proved 14 theorems in DataFrameVerbPreservation.lean (zero sorry):
- 3 schema preservation (filter/sort/distinct are identity)
- 3 DataFrame-yields-DataFrame (structural preservation)
- 3 verb composition (preserving verbs compose)
- 3 summarize properties (closed output, empty case, single column)
- 2 select/field helpers (get, select single)

**Rust side**: MCP validation deferred — Phase 3 features (frame literals, `|>` verb syntax, ColExpr) are uncommitted; the MCP binary doesn't support them yet. Attempted `frame { age: [30, 25, 28] } |> filter(:age > 25)` → parse error (expected). Will validate once Phase 3 is committed and MCP binary rebuilt.

**Outcome**: Lean definitions written from Rust source code review (not MCP validation). The formalization is **ahead of the MCP server** for the first time — the Lean model captures Phase 3 type semantics before they're available through MCP. This inverts the usual validation direction: when Phase 3 commits and MCP is rebuilt, the Lean model becomes the specification to validate *against*.

**Impact**: 6 new definitions, 14 proved theorems. Total proved theorem count: 4 → 18. Establishes that schema-preserving verbs (filter/sort/distinct) are provably identity at the type level, and summarize always produces closed rows. The `resolveAtom` definition captures the core mechanism connecting column names to types — the same mechanism used by all verb operations.

### 2026-02-10: Proving dataframeMutateExistingErrors and resolveAtom structural properties

**Context**: Closing sorry stubs for `dataframeMutateExistingErrors` (mutate on existing column always errors) and replacing the trivial `resolveAtomSingleColumn` (both branches mapped to True) with genuinely non-trivial theorems about resolveAtom.

**MCP tools used**: None — pure proof engineering session. MCP binary doesn't yet reflect Phase 3 verb changes.

**Lean side**:

*dataframeMutateExistingErrors*: The proof required connecting `applySubstRowFields_has_first` (substitution preserves field labels) through `dfMutate`'s inline column-existence check. After 8+ proof attempts, discovered that Lean 4's compiled match case trees are opaque to `simp`/`rw` — two syntactically different but definitionally equal match expressions compile to different internal representations that tactics can't unify.

**Solution**: Extracted `resolvedHasColumn` as a named function used by both `dfMutate` and the lemma. This ensures syntactic identity in compiled code, allowing `simp only [resolvedHasColumn_true, ite_true]` to close the goal. This is a general Lean 4 proof engineering pattern: when a proof needs to reason about behavior inside a definition's match expression, extract the relevant match into a named helper.

*resolveAtom properties*: Replaced the trivial theorem with three substantive ones:
1. `resolveAtom_returns_resolved_var` (proved) — on success, return type is substitution applied to fresh var; on error, return type is the unresolved fresh var
2. `decomposeFields_same_single` (proved) — matching single-field rows share the label as a common field with no left/right-only fields
3. `resolveAtom_single_col_succeeds` (sorry) — full success proof requires tracing 5 levels of mutual recursion through the unifier, blocked by BEq for mutual inductives being opaque to `simp`

**Outcome**: Two theorems fully proved (zero sorry), one sorry stub with documented proof strategy. Key proof engineering lesson: extract named functions to avoid opaque compiled match issues.

**Impact**: `dataframeMutateExistingErrors` moves from sorry to proved. Total proved count: 18 → 20. The `resolvedHasColumn` extraction pattern is reusable — any future proof that needs to reason about behavior inside `dfMutate` (or similar definitions with inline matches) should follow the same approach.

### 2026-02-10: Proving substIdempotent — foundation theorem with corrected precondition

**Context**: `substIdempotent` (`apply(s, apply(s, t)) = apply(s, t)`) is the foundation theorem that unblocks downstream proofs (`unifyReflexive`, `unifyConsistent`, and ultimately the Rémy row polymorphism theorems — the #1 risk from the Phase 1 risk review). As originally stated (`∀ s fuel ty`), it is **FALSE**.

**MCP tools used**: None — pure proof engineering session.

**Lean side**:

*Critical discovery*: The theorem as stated is false for substitutions with chains and limited fuel. Counterexample: `s = {0 → Var(1), 1 → Var(2), 2 → Int}`, `fuel = 2`, `ty = Var(0)`. First apply yields `Var(2)`, second yields `Int`. The fuel exhaustion on the first pass leaves resolvable variables that the second pass resolves further.

*Rust proptest comparison*: The Rust `substitution_idempotent` proptest only constructs substitutions with ground-type bindings (Int, String, Bool, Float) — no chains. Rust's `apply()` has no fuel limit. So the proptest implicitly tests only idempotent substitutions.

*Solution*: Defined `Subst.Idempotent` predicate requiring range variables are disjoint from domain (standard definition from unification theory). Proved the theorem conditionally:

1. `applySubst_noop` (4-way, proved) — types/rows with no domain vars are fixed points of `applySubst`
2. `applySubstRowFields_append_stable` (proved) — handles row-merge case where fields from resolved row variable are appended
3. `substIdempotent_all` (4-way combined, proved) — full idempotence by fuel induction. The hardest case is row variable merge: when `s.rowMap rv = some resolvedRow`, the first application merges `resolvedRow.fields` into the row, and the second must be a no-op on the merged result. Requires noop on resolved row fields, append stability, and handling of `resolvedRow.rest` (if `some rv2`, idempotent condition guarantees `s.rowMap rv2 = none`).

Key proof engineering patterns:
- Helper lemmas for `applySubst` var case (`applySubst_var_some`, `applySubst_var_none`) to avoid opaque match reduction
- `congr 1` for compound type constructors after `simp only [applySubst]`
- Constructor injectivity extraction via `congrArg (fun | .cons _ t _ => t | _ => default) ha` for mutual inductives
- `obtain ⟨rfields, rrest⟩ := resolvedRow` to destructure single-constructor mutual inductives with proper hypothesis substitution

**Rust side**: No MCP validation needed — this is about the substitution algebra, not type inference behavior. The Rust proptest's restriction to ground-type bindings is the runtime equivalent of the `Subst.Idempotent` precondition.

**Outcome**: Both `substIdempotent` and `substRowIdempotent` fully proved (zero sorry). The discovery that the unconditional theorem is false is itself a significant finding — it reveals that fuel-based termination conflates chain depth with structural depth, and the standard idempotence property requires the standard precondition.

**Impact**: Total proved count: 20 → 22 (sorry count: 12 → 10). This is the first foundation-layer theorem to be proved — it was identified as the highest-value target because it unblocks `unifyReflexive` and `unifyConsistent`, which in turn unblock the Rémy row unification theorems.

### 2026-02-10: Proving unifyReflexive — BEq reflexivity for mutual inductives

**Context**: `unifyReflexive` (`unify(t, t)` always succeeds) is the first theorem to use `substIdempotent` as a foundation. Required proving BEq reflexivity for all four mutual type families first, since `deriving BEq` doesn't work for mutual inductives and the manual `beqTy` must have reflexivity established explicitly.

**MCP tools used**: None — pure proof engineering session.

**Lean side**:

*BEq reflexivity*: Proved `beqTy_refl`, `beqRow_refl`, `beqTyList_refl`, `beqRowFields_refl` by mutual structural recursion in UnifyReflexive.lean. `simp [beqTy]` handles base cases; `simp [beqTy, beqTy_refl inner]` handles recursive cases.

*BEq vs == gap*: After `simp only [unify]`, the goal uses `==` (BEq.beq) not `beqTy` directly. Bridge with `show beqTy _ _ = true; exact beqTy_refl _`. This is a reusable pattern for all proofs that need to reason about the BEq shortcut in `unify`.

*unifyReflexive proof*: Immediate once BEq reflexivity is established — `unify` does BEq shortcut before any recursive calls, so proof is fuel-independent.

*unifyRowsReflexive discovery*: The statement `∃ st', unifyRows st (fuel + 1) r r = .ok st'` is FALSE for rows with many fields (fuel consumed proportional to field count). Corrected to existential fuel: `∃ fuel st', unifyRows st fuel r r = .ok st'`. Still sorry — requires decomposeFields properties.

**Outcome**: `unifyReflexive` fully proved (zero sorry). `unifyRowsReflexive` corrected but still sorry.

**Impact**: Total proved count: 15 → 16 (sorry count: 10 → 10, corrected from earlier miscounting). Establishes the BEq reflexivity infrastructure that all proofs reasoning about `unify`'s BEq shortcut will need.

### 2026-02-10: Proving occursCheckSound — corrected statement for substituted types

**Context**: `occursCheckSound` (occurs check prevents infinite types) was the next target after `unifyReflexive`. Discovery during proof attempt: the original statement is **false** for non-empty substitutions.

**MCP tools used**: None — pure proof engineering session.

**Lean side**:

*Critical discovery*: The original statement `occursIn v ty = true → ty ≠ .var v → ∃ e, bindTypeVar st v ty fuel = .err e` is false. Counterexample: `ty = List(Var(v))` with `st.subst` mapping `v → Int`. Then `occursIn v ty = true` but `applySubst st.subst fuel ty = List(Int)` doesn't contain `v`, so `bindTypeVar` succeeds.

*Root cause*: `bindTypeVar` checks `occursIn v (applySubst st.subst fuel ty)` — the substituted form — not `occursIn v ty` (raw form). The Rust proptest uses a fresh unifier (empty substitution) where raw and substituted coincide.

*Solution*: Changed hypothesis from `occursIn v ty = true` to `occursIn v (applySubst st.subst fuel ty) = true`, and from `ty ≠ .var v` (propositional) to `(ty == .var v) = false` (BEq). The proof is then immediate: `simp only [bindTypeVar, hneq, hoccurs, ↓reduceIte]`.

**Outcome**: `occursCheckSound` proved with corrected statement (zero sorry). Pattern: when a sorry theorem's statement doesn't match the definition it reasons about, fix the statement first, then the proof is often trivial.

**Impact**: Total proved count: 16 → 17 (sorry count: 10 → 9). Establishes occurs check soundness as a lemma for downstream proofs about `unify` error cases.

### 2026-02-10: Proving traitBoundsSurviveInstantiate — MCP-validated deferred constraint propagation

**Context**: `traitBoundsSurviveInstantiate` (trait bounds survive generalize → instantiate round-trip) is the formal analog of the Rust `trait_bounds_survive_generalize_instantiate` proptest. The Lean model predicts that `generalize` preserves trait bounds for quantified type vars (mirroring lacks constraint preservation for row vars), and `instantiate` transfers them to fresh vars.

**MCP tools used**: `type_check`, `get_type`, `list_bindings`, `reset_session`

**Lean side**: The theorem traces through `generalize` (empty env, empty subst, single type var `tv` with one trait bound) → `instantiate` (creates fresh var, transfers bound). Key proof engineering challenges:
- `applySubst Subst.empty fuel ty = ty` — proved via `applySubst_noop` from SubstIdempotent.lean
- `List.eraseDupsBy.loop` with symbolic `tv : Nat` — required full `simp` (not `simp only`) for beta reduction and `decide (tv = tv) = true`
- Two-phase proof: first reduce `generalize` (unfold + simp), then reduce `instantiate` (unfold + simp)

**Rust side**: MCP confirms all predictions:
- `trait Summable { fn sum(self) -> Int }` + `impl Summable for Int` — registered OK
- `fn total(x) where x: Summable { x }` — generalizes to `(a) -> a` (bounds hidden in scheme)
- `total(42)` → type `Int` (bound satisfied)
- `total("hello")` → error: "type `String` does not implement trait `Summable`"
- `total(3.14)` → error: "type `Float` does not implement trait `Summable`"
- Multiple bounds (`where x: Summable, x: Showable`): each checked independently, separate diagnostics
- **Bounds survive aliasing**: `let alias = process; alias("hello")` produces same errors (double generalize/instantiate round-trip)

**Outcome**: Full agreement. The Lean model's trait bound propagation through generalize/instantiate matches the Rust compiler exactly, validated bidirectionally via MCP.

**Impact**: Total proved count: 17 → 18 (sorry count: 9 → 8). Confirms that the deferred-constraint architecture generalizes from row constraints (lacks) to type constraints (trait bounds). The `applySubst_empty` helper (via `applySubst_noop`) is reusable for any proof involving empty substitutions.

---

## Session 7: Column(T) Type Boundary Verification (2026-02-10)

**Context**: Implemented `Column(T)` as an explicit type boundary for ColumnExpr — all `infer_col_expr` results now wrapped in `Column(T)`, with nullable propagation and `== nil` ban. Verified via MCP that the running compiler produces correct types.

**MCP Predictions (from implementation):**
1. `frame { x: [1, 2, 3] } |> filter(:x > 1)` → `DataFrame(#{ x: Int })` (non-nullable, Column unwrapped at filter boundary)
2. `frame { x: [1, None, 3] } |> filter(:x > 1)` → `DataFrame(#{ x: Int? })` (nullable preserved in schema, filter accepts Bool?)
3. `frame { x: [1, None, 3] } |> filter(:x == nil)` → compile error suggesting is_none()
4. `frame { x: [1, None, 3] } |> filter(:x != nil)` → compile error suggesting is_some()
5. `frame { x: [1, None, 3] } |> filter(is_none(:x))` → `DataFrame(#{ x: Int? })` (is_none returns non-nullable Bool)
6. `frame { x: [1.0, None, 3.0] } |> mutate(y: :x + 1.0)` → `DataFrame(#{ x: Float?, y: Float? })` (nullable propagated)
7. `frame { x: [1.0, 2.0, 3.0] } |> mutate(y: :x + 1.0)` → `DataFrame(#{ x: Float, y: Float })` (non-nullable stays)
8. `frame { x: [1, 2, 3] } |> group_by(:x) |> summarize(total: sum(:x))` → `DataFrame(#{ total: Int?, x: Int })` (sum always nullable)
9. `frame { x: [1.0, None, 3.0] } |> mutate(safe: coalesce(:x, 0.0))` → `DataFrame(#{ safe: Float, x: Float? })` (coalesce strips nullable)
10. `frame { x: [1, None, 3] } |> filter(nil == :x)` → compile error (reversed nil caught)
11. `frame { x: [1, 2, 3] } |> group_by(:x) |> summarize(avg_x: mean(:x), n: count(:x))` → `DataFrame(#{ avg_x: Float?, n: Int, x: Int })` (mean nullable, count non-nullable)
12. With `threshold: Int?` in scope: `frame { x: [1, 2, 3] } |> filter(:x > $threshold)` → `DataFrame(#{ x: Int })` (capture of nullable, filter accepts Bool?)

**MCP Results**: All 12 predictions matched exactly.

**Key verifications:**
- **Nullable propagation**: `Float? + Float` → `Float?` ✓, `Float + Float` → `Float` ✓
- **`== nil` ban**: Both operand positions caught (`:x == nil` and `nil == :x`) with correct suggestions ✓
- **Aggregate always-nullable**: `sum(Int)` → `Int?`, `mean(Int)` → `Float?`, `count(Int)` → `Int` ✓
- **Coalesce**: `coalesce(Float?, Float)` → `Float` (second arg's nullability) ✓
- **Filter accepts Bool?**: No error when predicate is nullable ✓
- **Capture with Option**: `$threshold: Int?` correctly participates in nullable propagation ✓

**Lean impact**: Column(T) needs to be added to the Ty inductive, with corresponding cases in unify, applySubst, beqTy_refl, occursIn, and freeVars. New theorems: `unwrap_col_column_identity`, `infer_col_expr_always_returns_column`. See FORMAL.md mapping table for updated line references.

**Outcome**: Full agreement on all 12 test cases. The Column(T) type boundary works as designed — it enforces the columnar/scalar boundary statically, enables nullable propagation, and bans == nil with clear diagnostics.

### 2026-02-10: Validating ColExpr model + recordStructuralProjection + unifyConsistent conjectures

**Context**: After formalizing ColExpr.lean (inferColExpr_always_returns_column proved), and before proving unifyConsistent and fixing recordStructuralProjection, validating the key conjectures against the running compiler.

**MCP tools used**: `type_check`, `get_type`, `evaluate`, `list_bindings`, `reset_session`, `rill://types`, `rill://modules`, `rill://examples`

**Lean side predictions**:
1. `inferColExpr_always_returns_column`: Every ColumnExpr internally produces Column(T), unwrapped at verb boundaries. User should never see Column(T) in inferred types — only bare types in DataFrame schemas.
2. `recordStructuralProjection`: Named record `Point { x: Int, y: Int }` unifies with `#{ x: a | r0 }` (row-polymorphic anonymous record).
3. `unifyConsistent`: After unification, both sides resolve to the same type. E.g., `apply_twice(f, x)` forces `f: (a) -> a` (not `(a) -> b`).

**Rust side (MCP results)**:
1. **ColExpr/Column(T) boundary** — confirmed invisible:
   - `fn test_filter(df) { df |> filter(:price > 100) }` → `(DataFrame(#{ price: Int | r2 })) -> DataFrame(#{ price: Int | r2 })` — schema preserved, no Column(T) visible
   - `fn test_mutate(df) { df |> mutate(total: :price * :qty) }` → `(DataFrame(#{ price: a, qty: a | r6 })) -> DataFrame(#{ price: a, qty: a, total: a | r6 })` — `total: a` is bare type, confirming unwrapCol at verb boundary
   - `fn test_lit_mutate(df) { df |> mutate(flag: true) }` → `flag: Bool` in output schema — literal `true` produces Column(Bool), unwrapped to Bool. Matches `lit_produces_column`.
   - `fn test_capture(df, threshold) { df |> filter(:price > $threshold) }` → `(DataFrame(#{ price: a | r2 }), a) -> DataFrame(#{ price: a | r2 })` — capture `$threshold` unified with `:price` type. Matches `capture_produces_column`.

2. **Structural projection** — confirmed:
   - `record Point { x: Int, y: Int }` registered
   - `fn get_x(p) { p.x }` → `(#{ x: a | r0 }) -> a`
   - `get_x(Point { x: 10, y: 20 })` → `Int` — named record projects structurally

3. **Unification consistency** — confirmed:
   - `fn apply_twice(f, x) { f(f(x)) }` → `((a) -> a, a) -> a` — return type unified with parameter type, forcing `a = a` (not `b`). This is unifyConsistent in action: after unifying `f`'s return with `f`'s parameter, both resolve to `a`.
   - `fn pair(x, y) { #{ first: x, second: y } }` then `pair(1, "hello")` → `#{ first: Int, second: String }` — instantiation resolves `a → Int`, `b → String` consistently.

**Outcome**: Full agreement on all predictions. The three conjectures being formalized (inferColExpr_always_returns_column, recordStructuralProjection, unifyConsistent) all match the compiler's runtime behavior.

**Impact**: Validates proof targets before investing in the proofs. Key insight: `apply_twice` is the simplest test case for unifyConsistent — the constraint `return_type = param_type` forces the substitution to be consistent.

---

### 2026-02-10: Post-proof validation of recordStructuralProjection + beqTy_sound

**Context**: After proving `recordStructuralProjection` (fully, no sorry) and `beqTy_sound` (BEq soundness for mutual types), used MCP to re-confirm the runtime behavior matches.

**Session**:

1. `record Point { x: Int, y: Int }` → registered
2. `fn get_x(p) { p.x }` → `(#{ x: a | r0 }) -> a` — row-polymorphic, accepts any record with `x` field
3. `get_x(Point { x: 1, y: 2 })` → `Int`, value `1` — named record structurally projects

**Lean theorem proved**: `recordStructuralProjection` — for any `name` and `row`, `∃ fuel st', unify empty fuel (record name row) (anonRecord row) = .ok st'`. The proof uses:
- `applySubst_empty` (empty subst is identity)
- `decomposeFields_self` + `decomposeFields_self_common_length` (identical fields decompose cleanly)
- `unifyCommonFields_refl_ge` (matching types unify)
- `beqTy_record_anonRecord` (different constructors → BEq false)
- `unifyRows_self_empty` (row unification with empty subst on identical rows)

**Lean theorem proved**: `beqTy_sound` — `beqTy a b = true → a = b` for all mutual types. Used in the BEq shortcut case of `unifyConsistent`.

**Outcome**: Full agreement. The Lean proof captures exactly the computation the MCP server performs.

---

### Entry 7: unifyRows reflexivity and fuel-field tension (2026-02-10)

**Context**: Extended row unification reflexivity proofs. The goal was to prove `unifyRowsReflexive` — that `unifyRows st fuel r r` succeeds for some fuel, for ANY row `r` and state `st`.

**Theorems proved**:

1. `unifyRows_self_via_resolution` — the general workhorse: if we know `applySubstRow st.subst (fuel-1) row = resolvedRow` and `fuel ≥ resolvedRow.fields.length + 2`, then `unifyRows st fuel row row = .ok st`. Proof: both sides resolve identically → `decomposeFields_self` gives all-common matching entries → `unifyCommonFields_refl_ge` handles all fields → rest variable matches trivially.

2. `unifyRows_self_fixed` — corollary of above for the fixed-point case (resolvedRow = row).

3. `applySubstRowFields_preserves_length` — substitution on row fields preserves field count.

4. `applySubstRow_closed_fields_length` / `applySubstRow_open_unbound_fields_length` — field count preservation for closed/unbound rows.

5. `unifyRowsReflexive'` — proved for closed rows and unbound row variables. Bound row variable case left as sorry.

6. Simplified `recordStructuralProjection`: `unifyRows_self_empty` is now a one-liner corollary of `unifyRows_self_fixed`, removing ~50 lines of duplicated proof from RecordStructuralProjection.lean.

**Discovery — fuel-field tension**: The bound row variable case of `unifyRowsReflexive` reveals a fundamental tension in the fuel-based model. `unifyRows` uses the SAME fuel parameter for both `applySubstRow` (which may expand row variables, adding fields) and `unifyCommonFields` (which needs fuel ≥ field count). More fuel means more expansion means more fields means more fuel needed — a self-referential constraint. The constraint IS satisfiable (substitutions are finite and acyclic), but proving it requires a termination argument about substitution chain depth that would need substantial additional infrastructure. This is an instance of the general fuel model divergence documented in FORMAL.md.

**Outcome**: 6 new theorems proved, 1 sorry reduced to bound-row-var-only. The `unifyRows_self_via_resolution` infrastructure handles all practical use cases (empty subst, generalized schemes, concrete rows) without requiring the full chain termination argument.

### 2026-02-10: Proving resolveAtom_single_col_succeeds — 5-level mutual recursion trace

**Context**: `resolveAtom_single_col_succeeds` (resolveAtom on a single-column DataFrame succeeds) was the deepest end-to-end property in the formalization, requiring tracing through 5 levels of mutual recursion: resolveAtom → unify(DataFrame) → unify(AnonRecord) → unifyRows → unifyCommonFields → unify(bind var).

**MCP tools used**: None — pure proof engineering session. MCP binary doesn't yet reflect Phase 3 changes.

**Lean side**:

*Key infrastructure built*:
1. `applySubst_empty` / `applySubstRow_empty` — empty substitution is identity (via `applySubst_noop`)
2. `beqRow_none_vs_some` — when row rests differ (none vs some), beqRow is false regardless of fields. Key insight: abstracts over the universally-quantified `colTy`.
3. `bindTypeVar_succeeds` — factored out from `unify`: given `(ty == .var v) = false` and `occursIn v ty = false`, bindTypeVar at fuel 0 succeeds.
4. `unify_against_fresh_var` — unifying any type against a fresh variable succeeds with fuel 1, when the fresh variable doesn't occur in the type. Full case split on all Ty constructors.
5. `lacksViolation_nil` — nil fields never violate lacks constraints.
6. `unify_single_col_df` — the 5-level chain proof. Layer-by-layer unfolds (`unfold unify; unfold unify; unfold unifyRows; unfold unifyCommonFields`), then staged `simp only` calls for applySubst_empty, BEq, ite_false, Row accessors, decomposeFields, then `unify_against_fresh_var` for innermost level.

*Proof engineering lessons*:
- `simp (config := { decide := true }) only [ite_false]` needed to reduce `if false = true then ... else ...` — standard `simp only [ite_false]` works with `if False` but not `if (false = true)`.
- Record literal `{ subst := ... }` in `have` causes parse errors; use `UnifyState.mk ...` constructor form instead.
- `Row.fields` accessor not reduced by `dsimp only []`; needs explicit `simp only [Row.fields, Row.rest]`.
- The key abstraction: `beqRow_none_vs_some` lets us handle the BEq check for DataFrames/AnonRecords with an abstract `colTy` without needing to case-split on the column type itself.

**Outcome**: `resolveAtom_single_col_succeeds` fully proved (zero sorry). Sorry count: 8 → 7. This is the deepest theorem proved in the formalization — no other theorem traces through 5 levels of mutual recursion with an abstract type parameter.

**Impact**: Total proved count increases. Establishes reusable infrastructure: `unify_against_fresh_var` can be used by any future proof that needs to show unification against a fresh variable succeeds. `bindTypeVar_succeeds` factored out a common unification step. The layer-by-layer unfold + staged simp pattern is the general strategy for proofs about mutual recursive definitions.

---

### Session 12: Label preservation infrastructure + remyPreservesLabels (inl case)

**Date**: 2026-02-10 (continued session)

**Context**: Closing remaining Lean sorries. Previous session proved `unifyRowsReflexive'` (bound row var case with Subst.Idempotent), discovered `unifyConsistent` and `applyRowPreservesSort` are FALSE as stated, corrected statements and documented. Sorry count went from 7 → 5.

**What was done**: Built label-preservation infrastructure for remyPreservesLabels, proved the `inl` case (labels from r1 are preserved by any substitution), and documented what's needed for the `inr` case (labels from r2 appear via row variable binding).

**Infrastructure lemmas proved** (in RemyPreservesLabels.lean):
1. `RowFields.mem_labels_implies_has` — converts `l ∈ labels rf` (List.Mem) to `has rf l = true` (Bool)
2. `applySubstRowFields_preserves_has` — substitution on row fields preserves `has` (labels don't change)
3. `RowFields.has_append_left` — if `has a l = true`, then `has (a.append b) l = true`
4. `applySubstRow_fields_closed` — closed row fields after substitution
5. `applySubstRow_fields_unbound` — unbound open row fields after substitution
6. `applySubstRow_preserves_original_has` — **key lemma**: applying any substitution at any fuel preserves the original field labels. Covers closed, unbound-open, and bound-open (via append) cases.

**remyPreservesLabels proof structure**:
- `inl` case (l from r1.fields): Closed by `applySubstRow_preserves_original_has` — original labels are always preserved regardless of what substitution does.
- `inr` case (l from r2.fields): Still sorry. Requires:
  - Decomposition coverage: `decomposeFields` partitions labels into common ∪ onlyLeft ∪ onlyRight
  - Substitution extension monotonicity: extending a substitution only adds labels, never removes them
  - Case analysis on unifyRows match arms (5 cases)

**Proof engineering lessons**:
- `generalize` pitfall: when both LHS and RHS of a goal reference the same function call, but one is nested inside a projection (`.fields`), `generalize` only replaces the "bare" occurrence. Workaround: prove `has` properties directly instead of intermediate equalities about `.fields`.
- `Bool.false_or` lemma handles `(false || b) = b`, useful after `cases h_eq : (label == l)` in the `false` branch.
- `simp` can pick up local hypotheses like `h_eq` automatically, so passing them explicitly as simp arguments triggers "unused argument" lint warnings.

**Outcome**: No sorry count change (still 5), but substantial infrastructure established. FORMAL.md updated with 7 new helper lemma entries. The `inl` case of remyPreservesLabels is proved, reducing the remaining obligation to the `inr` case only.

**Remaining 5 sorries analysis**:
1. `applyRowPreservesSort` — FALSE as stated (needs Rémy invariant precondition)
2. `unifyConsistent` — needs substitution composition lemma
3. `dataframeMutateDropRoundTrip` — needs full computation trace (very mechanical)
4. `remyPreservesLabels` — `inr` case needs decomposition coverage + subst extension
5. `remyTailLacks` — needs lacks propagation analysis

---

### 2026-02-10: Proving applySubstRow_rest_unbound_idempotent + fuel gap discovery

**Context**: Investigating `unify_extends_rowMap` (unification preserves row bindings). This is infrastructure for `remyPreservesLabels` — if unification only adds bindings, then labels present after partial unification are preserved through subsequent steps.

**MCP tools used**: None — pure proof engineering session.

**Lean side**:

*Critical discovery*: `unify_extends_rowMap` as stated (`∀ st fuel a b st'`) is **FALSE** without preconditions. Counterexample: substitution with chain `rv0 → Row([], some rv1)`, `rv1 → Row([a: Int], none)`, fuel = 1. `applySubstRow s 1 (Row [] (some rv0))` resolves `rv0` to `Row([], some rv1)` but doesn't follow `rv1` (fuel exhausted). Result has rest = `some rv1`. Then `unifyRows` may call `bindRow rv1 <newRow>`, overwriting the existing binding `rv1 → Row([a: Int], none)`.

*Key structural lemma proved*: `applySubstRow_rest_unbound_idempotent` — with an idempotent substitution, the rest variable of a resolved row is always unbound. This is because:
- For unbound row variables: applySubstRow preserves them as-is (trivially unbound)
- For bound row variables: idempotency ensures range variables are outside the domain, so the resolved row's rest is unbound

This means: with idempotent substitutions, `bindRow` in `unifyRows` always targets fresh/unbound variables, so `ExtendsRowBindings` holds. The full proof of `unify_extends_rowMap` would additionally need "unification preserves idempotency."

*Supporting lemma proved*: `Subst.bindRow_self_lookup` — looking up the bound variable in `bindRow` returns the bound row. Trivial but useful.

**Proof engineering lessons**:
- `Option.some.inj` returns `a = b` from `some a = some b` — direction matters
- `rw [← h]` vs `rw [h]`: when h is `rv0 = rv`, to rewrite rv to rv0, use `rw [← h]`
- `simp [freeRowVarsRow]` can close membership goals that look like they need `.head _` — don't add redundant closers

**Outcome**: Two new theorems proved, plus documentation of the fuel gap counterexample. Sorry count unchanged (6) — `unify_extends_rowMap` remains sorry but now has a clear path: needs `Subst.Idempotent` precondition + "unification preserves idempotency."

**Impact**: Establishes that the fuel gap is the fundamental barrier for `unify_extends_rowMap`, `remyPreservesLabels`, and `unifyConsistent`. All remaining genuine sorries converge on fuel-bounded substitution not composing well. The `applySubstRow_rest_unbound_idempotent` lemma is the key bridge between idempotent substitutions and safe row variable binding.

---

### 2026-02-10: extends_mutual counterexample — theorem is FALSE

**Context**: Attempted to close the 3 remaining bindRow sorries in `extends_mutual` (UnifyExtends.lean). Deep analysis of what preconditions would be needed.

**MCP tools used**: None (pure proof-theoretic analysis)

**Lean side**: Constructed concrete counterexample showing `extends_mutual` is **false without preconditions**:
- `s = { rv0 → Row.mk .nil (some rv1), rv1 → Row.mk (cons "a" Int .nil) none }`
- `r1 = Row.mk .nil (some rv0)`, `r2 = Row.mk (cons "b" String .nil) none`, `fuel = 2`
- `applySubstRow s 1 r1` resolves rv0 but fuel exhausts before resolving rv1 → `Row.mk .nil (some rv1)`
- `unifyRows` sees `(some rv1, none)` and binds `rv1 → Row.mk (cons "b" String .nil) none`
- This **overwrites** the existing `rv1 → Row.mk (cons "a" Int .nil) none`
- At sufficient fuel (≥ 3), the same unification correctly **fails** ("extra fields in closed rows")

**Rust side**: The Rust implementation has unbounded `apply()`, so `applySubstRow` always fully resolves. The counterexample substitution (with a chain longer than fuel) can never produce unsound results in the Rust code. The Rust implementation IS correct — all 831+ tests pass.

**Outcome**: The 3 bindRow sorries are not "hard to prove" — they are **unprovable** because the theorem is false. This upgrades the finding from "blocked on idempotency preservation" to "theorem FALSE, needs precondition."

**Analysis of fix options**:
1. **Add `Subst.Idempotent` precondition**: Would make theorem true (idempotent ⟹ chain-free ⟹ resolved rest vars are unbound). But `Subst.Idempotent` is NOT preserved by `bindTypeVar` (which binds raw types, not resolved types), so it cannot be a loop invariant in the mutual induction.
2. **Weaker "row-chain-free" invariant**: Only constrain the row map (chains ≤ 1). Preserved by `bindTypeVar` (which only touches typeMap). But whether it's preserved by the `some rv1, some rv2` case of `unifyRows` (which creates fresh row vars and double-binds) needs careful analysis.
3. **Well-founded recursion**: Eliminate fuel entirely, matching the Rust implementation. Clean but requires significant refactoring of all mutual definitions.

**Impact**: Updated UnifyExtends.lean file header with counterexample. Updated FORMAL.md theorem table (marked FALSE), Model Divergence section (added concrete counterexample), and added Sorry Assessment summary. This is a key finding: the formalization has identified the **exact boundary** where the fuel model diverges from the Rust implementation semantics. All sorry sites are now fully explained — none are due to proof engineering difficulty; all trace to the same fundamental model limitation.

---

### 2026-02-11: MCP reconnect validation + row-polymorphism sanity check

**Context**: Codex MCP server configuration was added and the session was restarted. Goal: re-establish live MCP validation for formal work and confirm core HM + row-polymorphism behavior in the running implementation.

**MCP tools used**: `reset_session`, `evaluate`, `get_type`, `type_check`, `list_bindings`, `rill://syntax`, `rill://examples`

**Lean side (expectations)**:
- Let-bound identity should generalize: `id : (a) -> a`, with instantiations at `Int` and `String`.
- Record projection should infer an open-row function: `get_age : (#{ age: a | r }) -> a`.
- Instantiations of `get_age` should specialize to concrete field types (`Int`, `Float`) while permitting extra fields.

**Rust side (MCP results)**:
- `evaluate "let id = |x| x"` returned binding `id` with type `(a) -> a`.
- `get_type "id(1)"` returned `Int`; `get_type "id(\"hi\")"` returned `String`; `evaluate "id(1)"` returned value `1 : Int`.
- `evaluate "let get_age = |r| r.age"` returned binding type `(#{ age: a | r0 }) -> a`.
- `get_type "get_age(#{ age: 30, name: \"a\" })"` returned `Int`.
- `get_type "get_age(#{ age: 1.5 })"` returned `Float`.

**Additional note**:
- MCP `type_check/get_type/evaluate` in this server accept expression-oriented inputs; top-level `fn ... { ... }` declarations in one-shot requests produced parser diagnostics ("expected declaration ..."). Using `let`-bound lambdas is the reliable path for interactive theorem-to-runtime probes.

**Outcome**: Runtime behavior matches the Lean model's core expectations for polymorphic let-generalization and open-row projection typing. MCP validation workflow is active again for subsequent formalization iterations.

---

### 2026-02-11: WF migration slice — bounded bindTypeVar consistency

**Context**: Continued migration away from fuel-dependent conclusions by introducing WF/acyclic bridge lemmas and applying them to `UnifyConsistent` without destabilizing existing theorem contracts.

**MCP tools used**: None (pure proof-engineering session; runtime behavior already revalidated earlier in Session 2026-02-11 above).

**Lean side (what changed)**:
- In `SubstBridge.lean`:
  - Added `applySubstWF_noop` and `applySubstRowWF_noop` (acyclic no-op lemmas).
  - Added `applySubstWF_range_noop_of_idempotent` and `applySubstRowWF_range_noop_of_idempotent` (idempotent range terms are WF fixed points).
  - Added `applySubstBounded_bindType_consistent_of_idempotent`:
    for `sb = bindType s v ty`, bounded WF substitution at `(tlim=2, rlim=1)` maps `.var v` consistently with `ty`.
- In `UnifyConsistent.lean`:
  - Added `bindTypeVarConsistentWFBoundedIdempotent`, a bounded-WF counterpart to `bindTypeVarConsistentIdempotent`:
    after successful `bindTypeVar` with idempotent result substitution, `applySubstBounded ... 2 1 (.var v) = applySubstBounded ... 2 1 ty`.

**Key proof insight**:
- A direct full-`applySubstWF` theorem for the bind branch ran into a dependent/measure mismatch in the no-op branch (comparing different implicit rank limits).
- The bounded-WF form with fixed limits avoids that mismatch while still removing fuel from the theorem conclusion.

**Validation**:
- `cd formal && lake build` passes.
- `mise run check` passes.

**Outcome**:
- First concrete nontrivial theorem in `UnifyConsistent` now has a WF-flavored counterpart (bounded form), built on reusable acyclic/idempotent bridge infrastructure.
- This sets up the next step: either lift bounded-WF consistency to full `applySubstWF` where limits can be normalized, or migrate additional idempotent/fuel lemmas through the same bounded bridge first.

### 2026-02-11: WF row-tail bridge sanity check against live type inference

**Context**: After promoting row-tail bridge lemmas from bounded substitution to full `applySubstRowWF`, validate that live type inference still enforces stable row constraints (no accidental field-type overwrite behavior from partial resolution).

**MCP tools used**: `reset_session`, `list_bindings`, `get_type`, `type_check`

**Lean side**: The new bridge theorems (`applySubstRowWF_empty_open_lookup`, `applySubstRowWF_bindRow_consistent_of_idempotent`, `bindRowTailConsistentWFIdempotent`) predict stable row-tail substitution under idempotence. Practically, row constraints should compose, not overwrite.

**Rust side**: MCP confirmed:
- `get_type` on `|r| #(r.a, r.b)` returns `(#{ a: a, b: b | r2 }) -> #(a, b)` (joint row constraints inferred)
- `get_type` on `|r| #(r.a + 1, r.a + 2)` returns `(#{ a: Int | r2 }) -> #(Int, Int)` (single field constraint stabilized across uses)
- `type_check` on `(|r| r.a + 1)(#{ a: "x", b: 2 })` fails with field mismatch (`a` inferred `Int`, got `String`)
- `type_check` on `(|r| #(r.a + 1, r.a == "x"))(#{ a: 1 })` fails with incompatible equality operands (`Int` vs `String`)

**Outcome**: Agreement. Live behavior matches the formal expectation that row-related constraints remain coherent rather than being overwritten.

**Impact**: Confirms the WF bridge refactor preserves observable inference behavior for row-tail constraints. No Rust changes required.

### 2026-02-11: Milestone theorem framing validation (`unifyRows_extends_rowMap_preconditioned`)

**Context**: Validate runtime-facing consequences of the new preconditioned global extension theorem framing: successful open-row composition should typecheck; missing-field and conflicting constraints should fail (no silent overwrite behavior).

**MCP tools used**: `reset_session`, `type_check`

**Lean side**: `unifyRows_extends_rowMap_preconditioned` requires idempotent intermediate substitution + recognized success-update shape. Practically, that predicts stable row constraints: valid open-row merges succeed, and conflicting/missing constraints fail with explicit diagnostics.

**Rust side**: MCP confirmed:
- `type_check "(|r| #(r.a, r.b))(#{ a: 1, b: \"x\", c: true })"` => `ok`, type `#(Int, String)`
- `type_check "(|r| #(r.a, r.b))(#{ a: 1 })"` => `error` category `missing_field`, message `missing field \`b\` — required by the function`
- `type_check "(|r| #(r.a + 1, r.a == \"x\"))(#{ a: 1 })"` => `error` category `type_mismatch`, message `left is Int and right is String`

**Outcome**: Agreement. Runtime behavior matches the milestone theorem's intended contract surface: accepted updates are coherent open-row merges; incompatible updates fail explicitly.

**Impact**: Strengthens the write-up linkage between the proved preconditioned extension theorem and observable type-checker behavior. No model or implementation changes required.

### 2026-02-12: Vertical typing slice sanity check (app/proj hooks)

**Context**: After introducing `inferExprUnify`/`inferFieldsUnify` and branch-local hook interfaces (`AppUnifySoundHook`, `ProjUnifySoundHook`), verify that runtime behavior still matches the intended app/proj branch expectations.

**MCP tools used**: `reset_session`, `evaluate`, `list_bindings`, `get_type`, `type_check`

**Lean side (prediction)**:
- App branch should behave as a unification-constrained function application step.
- Projection branch should infer open-row access and specialize at call sites.
- Projection combined with arithmetic should reject non-`Int` field payloads.

**Rust side (MCP results)**:
- `evaluate "let f = |x| x + 1"` binds `f : (Int) -> Int`.
- `get_type "f(41)"` returns `Int`.
- `evaluate "let projA = |r| r.a"` binds `projA : (#{ a: a | r0 }) -> a`.
- `get_type "projA(#{ a: 1, b: \"x\" })"` returns `Int`.
- `type_check "(|r| r.a + 1)(#{ a: \"x\", b: 1 })"` returns `type_mismatch` (`a` inferred `Int`, got `String`).

**Outcome**: Agreement. Observed runtime behavior matches the new vertical hook contracts for app/proj branches.

**Impact**: Confirms the M4 vertical slice is aligned enough to proceed with the next step: full recursive preconditioned soundness for `inferExprUnify`.

### 2026-02-12: Full preconditioned vertical theorem pass (app/proj + recursive structure)

**Context**: While proving `inferExprUnify_sound_preconditioned` / `inferFieldsUnify_sound_preconditioned`, validate both successful and rejecting app/proj paths against runtime behavior.

**MCP tools used**: `reset_session`, `evaluate`, `type_check`

**Lean side (prediction)**:
- App branch: typed function application succeeds when unify succeeds; mismatched argument types reject.
- Proj branch: open-row projection constraints compose through surrounding expressions; wrong field payload types reject.
- Let/lambda wrappers should preserve these branch outcomes.

**Rust side (MCP results)**:
- `evaluate "let id = |x| x"` binds `id : (a) -> a`.
- `evaluate "let pickA = |r| r.a"` binds `pickA : (#{ a: a | r0 }) -> a`.
- `type_check "id(2)"` => `ok`, type `Int`.
- `type_check "pickA(#{ a: 2, b: true })"` => `ok`, type `Int`.
- `type_check "(|x| x + 1)(2)"` => `ok`, type `Int`.
- `type_check "(|r| r.a + 1)(#{ a: 2, b: true })"` => `ok`, type `Int`.
- `type_check "(|x| x + 1)(\"x\")"` => `error` (`type_mismatch` in call).
- `type_check "(|r| r.a + 1)(#{ a: \"x\", b: true })"` => `error` (`field \`a\`` mismatch).

**Outcome**: Agreement. Runtime behavior matches the intended branch contracts used in the full preconditioned theorem proof.

**Impact**: Confirms theorem-side branch obligations reflect implementation behavior, including both success and failure paths.

### 2026-02-12: App-hook discharge attempt and boundary check

**Context**: Attempted to discharge `AppUnifySoundHook` directly. Lean proof found a concrete model-level counterexample (`not_AppUnifySoundHook`): unification can succeed by binding a function-position type variable even when declarative `HasType.app` cannot derive a function type from the existing environment typing.

**MCP tools used**: `reset_session`, `evaluate`, `type_check`

**Lean side (finding)**:
- `not_AppUnifySoundHook` is now proved.
- Boundary is in the declarative judgment vs infer/unify interface, not in app runtime behavior.

**Rust side (MCP results)**:
- `evaluate "let f = |x| x + 1"` gives `f : (Int) -> Int`.
- `type_check "f(1)"` => `ok`, type `Int`.
- `type_check "f(\"x\")"` => `error` (`type_mismatch` in function call).
- `evaluate "let id = |x| x"` gives `id : (a) -> a`.
- `type_check "id(1)"` => `ok`, type `Int`.
- `type_check "id(\"x\")"` => `ok`, type `String`.

**Outcome**: Runtime app behavior remains coherent. The failed hook discharge is a formal interface boundary: the hook is too strong for the current declarative relation without additional premises/normalization relation between inferred and declarative function types.

**Impact**: Converts the attempted hook-discharge step into explicit boundary documentation with a proved negative theorem, while preserving implementation alignment evidence.

### 2026-02-12: Two-judgment scaffold sanity check (`HasTypeU` direction)

**Context**: Added unification-aware declarative scaffold (`HasTypeU`) and weak app-hook route. Validate higher-order app behavior that mirrors the new substitution-admissibility framing.

**MCP tools used**: `reset_session`, `evaluate`, `type_check`

**Lean side (prediction)**:
- Application should succeed when function argument and value argument align (including polymorphic identity).
- Mismatched argument payloads should fail at app boundary with explicit mismatch.

**Rust side (MCP results)**:
- `type_check "(|f, x| f(x))(|n| n + 1, 2)"` => `ok`, type `Int`.
- `type_check "(|f, x| f(x))(|n| n == 1, 2)"` => `ok`, type `Bool`.
- `type_check "(|f, x| f(x))(|n| n + 1, \"x\")"` => `error` (`type_mismatch` in call).
- `type_check "(|f, x| f(x))(|n| n + 1, true)"` => `error` (`type_mismatch` in call).
- `evaluate "let id = |x| x"` => `id : (a) -> a`; `type_check "id(1)"` and `type_check "id(\"x\")"` both `ok` with corresponding result types.

**Outcome**: Agreement. Runtime behavior is consistent with the direction of the `HasTypeU` scaffold and weak app-hook decomposition.

**Impact**: Supports moving from “hook false in monomorphic declarative judgment” to “hook recoverable under substitution-aware declarative architecture.”

### 2026-02-12: App-bridge decomposition sanity check (function-position application)

**Context**: Added app-bridge lemmas that package function-branch shape assumptions (`unifyTyList` success + tail `bindTypeVar` success) into the weak-hook equality premise. Validate representative function-position application behavior that this bridge is targeting.

**MCP tools used**: `reset_session`, `type_check`

**Lean side (prediction)**:
- `(|f| f(1))` should accept function arguments that consume `Int`, and reject function arguments that consume non-`Int`.
- Return type should track the function argument's return type (`Int` vs `Bool` in test cases).

**Rust side (MCP results)**:
- `type_check "(|f| f(1))(|n| n + 1)"` => `ok`, type `Int`.
- `type_check "(|f| f(1))(|n| n == 1)"` => `ok`, type `Bool`.
- `type_check "(|f| f(1))(|b| if b { 1 } else { 0 })"` => `error` (`type_mismatch` in function call: expected `Bool`, got `Int`).

**Outcome**: Agreement. Runtime function-position application behavior matches the bridge decomposition assumptions and intended weak-hook equality use.

**Impact**: Supports the remaining proof task: derive the packaged app-branch shape witnesses directly from successful `unify` in the app branch.

### 2026-02-12: Closed+fresh app-step bridge sanity check (`HasTypeU` path)

**Context**: Added `inferExprUnify_app_step_sound_hasTypeU_closed_fresh_succ` and helper `app_unify_resolved_fn_shape_of_success_closed_fresh_succ` to discharge a closed+fresh app step without introducing a new app hook.

**MCP tools used**: `reset_session`, `type_check`

**Lean side (prediction)**:
- Closed app/function-position calls should resolve deterministically along the same app branch shape used by the new bridge.
- Compatible argument payloads should succeed with expected return type; incompatible payloads should reject at call boundary.

**Rust side (MCP results)**:
- `type_check "(|x| x + 1)(2)"` => `ok`, type `Int`.
- `type_check "(|x| x + 1)(true)"` => `error` (`type_mismatch`: expected `Bool`, got `Int`).
- `type_check "(|f, x| f(x))(|n| n + 1, 2)"` => `ok`, type `Int`.
- `type_check "(|f, x| f(x))(|n| n == 1, 2)"` => `ok`, type `Bool`.
- `type_check "(|f, x| f(x))(|n| n + 1, \"x\")"` => `error` (`type_mismatch` in function call).

**Outcome**: Agreement. Runtime app behavior remains consistent with the closed+fresh bridge shape: successful calls preserve expected result type, and incompatible calls fail explicitly.

**Impact**: Supports using the new closed+fresh `HasTypeU` app-step theorem as a vertical slice milestone while generalizing toward broader app-branch automation.

### 2026-02-12: Projection-hook empty-subst boundary sanity check

**Context**: Added `ProjUnifySoundHookEmptySubst` and proved `not_ProjUnifySoundHookEmptySubst` to mirror the app-hook empty-subst boundary: monomorphic `HasType` remains too weak to absorb unification-discovered projection shapes, even from empty substitution start.

**MCP tools used**: `reset_session`, `type_check`

**Lean side (prediction)**:
- Projection behavior in the implementation should remain coherent (success on compatible open-row projection, explicit failure on incompatible field payloads), while the formal negative theorem is about declarative-judgment expressiveness, not runtime projection correctness.

**Rust side (MCP results)**:
- `type_check "(|r| r.a)(#{ a: 1, b: true })"` => `ok`, type `Int`.
- `type_check "(|r| r.a + 1)(#{ a: 1, b: true })"` => `ok`, type `Int`.
- `type_check "(|r| r.a + 1)(#{ a: \"x\", b: true })"` => `error` (`type_mismatch`: field `a` is `String`, expected `Int`).

**Outcome**: Agreement. Runtime projection behavior is stable and expected; the new theorem isolates a formal interface boundary (hook closure vs declarative shape), not an implementation bug.

**Impact**: Strengthens Option-A timebox evidence: both app and proj hook closure fail in the monomorphic declarative system even under empty-subst starts, reinforcing the two-judgment architecture requirement.

### 2026-02-12: Projection `HasTypeU` resolved-shape slice sanity check

**Context**: Added `ProjUnifySoundHookUResolved`, `projUnifySoundHookUResolved_proved`, and `inferExprUnify_proj_step_sound_hasTypeU_resolved` (projection counterpart to the app resolved-shape path).

**MCP tools used**: `reset_session`, `evaluate`, `type_check`

**Lean side (prediction)**:
- Once the receiver resolves to an open-record-compatible shape, projection should specialize field type from call-site payload.
- Projection should compose with arithmetic on `Int` payloads and fail for incompatible payloads.

**Rust side (MCP results)**:
- `evaluate "let projA = |r| r.a"` => `projA : (#{ a: a | r0 }) -> a`.
- `type_check "projA(#{ a: 1, b: true })"` => `ok`, type `Int`.
- `type_check "projA(#{ a: \"x\", b: true })"` => `ok`, type `String`.
- `type_check "(|r| r.a + 1)(#{ a: 1, b: true })"` => `ok`, type `Int`.

**Outcome**: Agreement. Runtime projection behavior matches the resolved-shape `HasTypeU` bridge intent: receiver shape is inferred structurally and field type specializes at use.

**Impact**: Extends the hook-free `HasTypeU` vertical slice from app-only to symmetric app+projection resolved-shape interfaces.

### 2026-02-12: Stats module MCP re-validation after MCP binary rebuild

**Context**: Re-ran the stats brief verification snippets after rebuilding and restarting the MCP server. Also probed `min`/`max` exposure in `system.functions` to clarify what is discoverable via MCP.

**MCP tools used**: `reset_session`, `type_check`, `evaluate`

**Lean side (prediction)**:
- `stddev` over numeric columns should type-check and infer nullable float aggregate output.
- `stddev` over string columns should fail with a `Numeric` trait-bound error.
- `min`/`max` should work in `summarize` for orderable columns, but only functions registered as `Rill.Stats` builtins should appear under `system.functions` with that module.

**Rust side (MCP results)**:
- `type_check "{ let sales = frame { revenue: [10.0, 20.0, 30.0], name: [\"a\", \"b\", \"c\"] }; sales |> group_by(:name) |> summarize(s: stddev(:revenue)) }"` => `ok`, type `DataFrame(#{ name: String, s: Float? })`.
- `type_check "{ let sales = frame { revenue: [10.0, 20.0, 30.0], name: [\"a\", \"b\", \"c\"] }; sales |> group_by(:name) |> summarize(s: stddev(:name)) }"` => `error`, message `type String does not implement trait Numeric`.
- `type_check` with `summarize(lo: min(:name), hi: max(:name))` succeeds (orderable string aggregation path works).
- `evaluate` SQL probe for stats exposure:
  - `SELECT ... FROM system.functions WHERE module = 'Rill.Stats' AND (name = 'min' OR name = 'max')` => `nrow = Ok(0)`.
  - `SELECT ... FROM system.functions WHERE module = 'Rill.Stats' AND name = 'stddev'` => `nrow = Ok(1)`.
  - `SELECT module FROM system.functions WHERE name = 'min'` + `collect_scalar(..., "module")` => `Ok("Rill.Math")`.

**Outcome**: Agreement with implementation status. Stats trait-bound behavior is correct and now visible in MCP for newly added stats functions. `min`/`max` aggregate behavior exists at the ColumnExpr/type-rule layer, but explicit `Rill.Stats` function exposure remains absent.

**Impact**: Confirms readiness to decide `min`/`max` exposure strategy:
- either keep scalar-only discovery (`Rill.Math`) and treat aggregate `min`/`max` as implicit,
- or add explicit stats-facing aliases/entries so MCP discovery reflects aggregate intent without colliding with scalar `min`/`max` names.

### 2026-02-12: Evaluator fragment soundness (record/projection) MCP-first check

**Context**: Before proving `eval_sound_evalFragment` / `inferEval_sound_evalFragment`, validated that record/projection behavior in the running implementation matches the intended static→dynamic contract for the non-`lam`/`app` fragment.

**MCP tools used**: `reset_session`, `get_type`, `type_check`

**Predict (Lean side)**:
- Valid projection from an open-row-compatible record should infer the projected field type.
- Record reconstruction from projections should preserve field types.
- Missing required fields and arithmetic-over-wrong-field-type should fail explicitly.

**Probe (Rust side via MCP)**:
- `get_type "(|r| r.a)(#{ a: 1, b: true })"` -> `Int`.
- `get_type "(|r| #{ x: r.a, y: r.b })(#{ a: 1, b: true })"` -> `#{ x: Int, y: Bool }`.
- `type_check "(|r| r.a)(#{ b: true })"` -> `error`, `missing_field` (`a`).
- `type_check "(|r| r.a + 1)(#{ a: \"x\" })"` -> `error`, `type_mismatch` (`String` vs `Int`).

**Classify**: Agreement.

**Outcome**: The probes match the intended evaluator-fragment theorem shape: successful projection/reconstruction preserves expected types; incompatible inputs fail with explicit diagnostics.

**Impact**:
- Proceeded with full fragment executable soundness in `formal/Rill/Eval.lean`:
  - `ValueFieldsHasType`, `valueFieldsHasType_get`
  - `envWellTyped_cons`
  - `eval_sound_evalFragment`, `evalFields_sound_evalFragment`
  - `inferEval_sound_evalFragment`
- Updated `FORMAL.md` and `formal/ROADMAP.md` to record the second vertical slice milestone.

### 2026-02-12: App-lam executable slice validation (beta-style evaluator extension)

**Context**: Before proving `eval_sound_evalFragmentFull` / `inferEval_sound_evalFragmentFull`, validated the reduced app-lam semantics: evaluator executes direct `(.app (.lam ...) arg)` while keeping general function values out of the fragment.

**MCP tools used**: `reset_session`, `get_type`, `type_check`

**Predict (Lean side)**:
- Direct app-lam on numeric argument should infer `Int` under arithmetic body.
- Direct app-lam on incompatible argument should fail with call-site type mismatch.
- App-lam with open-record projection body should infer projected field type.

**Probe (Rust side via MCP)**:
- `get_type "(|x| x + 1)(2)"` -> `Int`.
- `type_check "(|x| x + 1)(true)"` -> `error`, `type_mismatch` in function call.
- `get_type "(|r| r.a)(#{ a: 1, b: true })"` -> `Int`.

**Classify**: Agreement.

**Outcome**: Runtime behavior matches the reduced vertical target: direct beta-style app-lam succeeds on coherent arguments and rejects incompatible calls.

**Impact**:
- Proceeded with the reduced lam/app formalization in `formal/Rill/Eval.lean`:
  - evaluator rule for `.app (.lam ...) arg`
  - helper lemma `eval_app_lam_of_eval_arg`
  - fragment predicates `EvalFragmentFull` / `EvalFragmentFullFields`
  - theorems `eval_sound_evalFragmentFull`, `evalFields_sound_evalFragmentFull`, `inferEval_sound_evalFragmentFull`.

### 2026-02-13: New MCP observability tools baseline for evidence-passing formalization

**Context**: Validating newly added MCP observability endpoints (`explain_infer`, `trace_unify`, `normalize_type`, `resolve_traits`, `elaborate_evidence`) as inputs to the next evidence-passing/trait formalization loop.

**MCP tools used**: `reset_session`, `explain_infer`, `trace_unify`, `normalize_type`, `resolve_traits`, `elaborate_evidence`

**Predict (Lean side)**:
- `to_string(1)` should require `Display(Int)` evidence and infer `String`.
- app-lam arithmetic should show unification steps converging to `Int`.
- type normalization on identity application should collapse to `Int`.
- `Int` trait resolution should expose built-in trait set and evidence availability.

**Probe (Rust side via MCP)**:
- `explain_infer "to_string(1)"` -> `inferred_type = String`; unification trace reports function decomposition and `Int`/`String` bindings.
- `trace_unify "(|x| x + 1)(2)"` -> `inferred_type = Int`; four-step unify trace including decompose + bind steps.
- `normalize_type "(|x| x)(1)"` -> `normalized = Int`, `evidence = []`.
- `resolve_traits type=Int` -> built-in trait list with per-trait `evidence_available` flags.
- `elaborate_evidence "to_string(1)"` -> one required site: `Display(Int)`, resolved, with explicit dispatch chain.

**Classify**: Agreement.

**Outcome**: The new MCP tooling exposes exactly the observability surface needed for trait-evidence formalization: inference trace, unifier trace, normalized type view, trait resolution provenance, and evidence dispatch chain.

**Impact**:
- Confirms readiness to formalize explicit evidence-passing contracts against implementation traces.
- Establishes a concrete MCP-first probe template for upcoming evidence/traits theorems.

### 2026-02-13: Stream unification parity check after unifier update

**Context**: Rust unifier gained an explicit `Stream(A) ~ Stream(B)` decomposition arm. Lean model was updated to add `Ty.stream` and stream-aware substitution/occurs/free-vars handling; this MCP probe validates runtime behavior before widening theorem claims.

**MCP tools used**: `reset_session`, `get_type`, `trace_unify`, `type_check`

**Predict (Lean side)**:
- `stream_from_list([1,2,3])` should infer `Stream(Int)`.
- Unification inside `stream_map(...)` should include a `Stream(A) ~ Stream(B)` decomposition step (not a fallback mismatch).
- Stream-heavy expression should normalize to `Stream(Int)`.

**Probe (Rust side via MCP)**:
- `get_type "stream_from_list([1, 2, 3])"` -> `Stream(Int)`.
- `trace_unify "stream_map(stream_from_list([1, 2, 3]), |x| x + 1)"` -> `status=ok`, `inferred_type=Stream(Int)`, includes step:
  - `detail: "Stream(A) ~ Stream(B) → unify A ~ B"`.
- `type_check "stream_map(stream_from_list([1, 2, 3]), |x| x + 1)"` -> `ok`.

**Classify**: Agreement.

**Outcome**: Runtime and formal intent now agree on the stream constructor path in unification and substitution application.

**Impact**:
- Stream parity can be treated as restored for the core substitution/unification model.
- Remaining parity gaps are now mostly type-universe breadth (`Html/Markdown/Date/DateTime/Tagged/Sum/Actor/Arc/Dynamic/GroupedFrame`) and evidence/trait semantics, not the Stream unifier path.

### 2026-02-13: MCP-first supertrait/evidence boundary probe

**Context**: Before formalizing trait-evidence closure, probed runtime supertrait behavior using new MCP observability (`resolve_traits`) and declaration/evaluation flow.

**MCP tools used**: `reset_session`, `evaluate`, `resolve_traits`, `type_check`

**Predict (formal target)**:
- If `trait MyOrd: MyEq`, then satisfying `MyOrd` for a concrete type should require `MyEq` as a supertrait obligation.
- Trait-obligation closure should be inspectable separately from direct impl presence.

**Probe (Rust side via MCP)**:
1. Registered:
   - `trait MyEq {}`
   - `trait MyOrd: MyEq {}`
   - `impl MyOrd for Int {}`
2. `resolve_traits type=Int trait=MyOrd` reports:
   - `status = implemented` (direct impl exists),
   - `supertraits = [{ trait_name: "MyEq", satisfied: false }]`.
3. With `impl MyEq for Int {}` added, same probe reports `satisfied: true` for supertrait.
4. With only `impl MyOrd for Int {}`, `fn needs_ord(x: a) -> a where a: MyOrd { x }` followed by `type_check "needs_ord(1)"` succeeds.

**Classify**: Partial agreement + boundary signal.

**Outcome**:
- MCP cleanly exposes the distinction between direct impl presence and supertrait satisfaction.
- Current runtime acceptance path can still accept a call site with only the direct impl in this scenario, while provenance marks supertrait unsatisfied.

**Impact**:
- Added `formal/Rill/Traits.lean` with an explicit supertrait graph model (`TraitGraph`) and closure-aware satisfaction/checking surface:
  - `TraitGraph.directSupers`, `TraitGraph.closure`, `TraitGraph.requiredTraits`
  - `TraitRegistry.satisfiesWithGraph`
  - `checkTraitBoundsWithGraph`
- This becomes the formal bridge layer for upcoming evidence-passing proofs and MCP trace alignment.

### 2026-02-13: Supertrait-gap witness closure (theorem alignment pass)

**Context**: After landing the `Traits.lean` bridge model, re-ran the same supertrait scenario to pin concrete witness theorems to observed MCP behavior.

**MCP tools used**: `reset_session`, `evaluate`, `resolve_traits`, `type_check`

**Predict (Lean side)**:
- `satisfies_direct_ord_only`: direct registry satisfaction for `MyOrd` on `Int` succeeds.
- `requiredTraits_ord_requires_eq`: graph closure for `MyOrd` includes `MyEq`.
- `satisfiesWithGraph_ord_only_false`: closure-aware satisfaction fails without `MyEq`.
- `supertrait_gap_witness`: direct satisfaction can be `true` while closure-aware satisfaction is `false`.

**Probe (Rust side via MCP)**:
1. Declared only `impl MyOrd for Int` under `trait MyOrd: MyEq`.
2. `resolve_traits type=Int trait=MyOrd` showed:
   - direct impl status `implemented`,
   - provenance supertrait `MyEq` with `satisfied: false`.
3. `type_check "needs_ord(1)"` still returned `ok`.
4. After adding `impl MyEq for Int`, `resolve_traits` flipped supertrait to `satisfied: true`.

**Classify**: Agreement (boundary witness confirmed).

**Outcome**: MCP behavior matches the new witness theorem set in `Rill/Traits.lean`; the formal model now has named statements that capture the observed direct-vs-closure discrepancy.

**Impact**:
- Added/confirmed witness theorems: `satisfies_direct_ord_only`, `requiredTraits_ord_requires_eq`, `satisfiesWithGraph_ord_only_false`, `supertrait_gap_witness`.
- Updated `FORMAL.md` theorem mapping and `formal/ROADMAP.md` milestone checklist accordingly.

### 2026-02-13: Trait-bound checker gap witness alignment

**Context**: Extended the supertrait witness into the bound-checker surface to formalize the exact direct-vs-closure acceptance gap.

**MCP tools used**: `reset_session`, `evaluate`, `resolve_traits`, `type_check`

**Predict (Lean side)**:
- `checkTraitBounds_direct_ord_only_accepts`: direct bound checker accepts `a: MyOrd` with only `impl MyOrd for Int`.
- `checkTraitBoundsWithGraph_ord_only_reports_missing_super`: closure-aware checker reports missing `("MyEq", "Int")` in the same state.
- `checkTraitBoundsWithGraph_ord_and_eq_accepts`: adding `impl MyEq for Int` clears the closure-aware checker output.

**Probe (Rust side via MCP)**:
1. With only `impl MyOrd for Int`, `resolve_traits type=Int trait=MyOrd` reported `supertraits: [{ trait_name: "MyEq", satisfied: false }]`.
2. In that state, `type_check "needs_ord(1)"` returned `ok`.
3. After `impl MyEq for Int`, `resolve_traits` reported `MyEq` supertrait `satisfied: true`.

**Classify**: Agreement (with documented implementation boundary).

**Outcome**: MCP confirms the runtime-observed gap that the new bound-checker witness theorems model explicitly: direct trait acceptance can proceed while closure-aware supertrait obligations remain unsatisfied.

**Impact**:
- Added bound-checker witness theorem trio in `Rill/Traits.lean`:
  - `checkTraitBoundsWithGraph_ord_only_reports_missing_super`
  - `checkTraitBounds_direct_ord_only_accepts`
  - `checkTraitBoundsWithGraph_ord_and_eq_accepts`
- Added packaged citation bundle `TraitClosureGapSlice` with proof witness `traitClosureGapSlice_proved` so downstream writeups can reference one named contract.
- Updated `FORMAL.md` and `formal/ROADMAP.md` to reflect the new theorem surface.

### 2026-02-13: Missing-impl acceptance boundary probe

**Context**: Probed the stricter missing-impl case (no `MyOrd` and no `MyEq` impl) to compare runtime acceptance against trait-bound-checker expectations.

**MCP tools used**: `reset_session`, `evaluate`, `elaborate_evidence`, `resolve_traits`, `type_check`

**Predict (Lean side)**:
- `checkTraitBounds_direct_no_impl_reports_ord`: direct bound checker should report `[("MyOrd", "Int")]`.
- `checkTraitBoundsWithGraph_no_impl_reports_ord_and_eq`: closure-aware checker should report `[("MyOrd", "Int"), ("MyEq", "Int")]`.
- Therefore a call requiring `a: MyOrd` should be rejected in a fully enforced trait-bound path.

**Probe (Rust side via MCP)**:
1. Declared only:
   - `trait MyEq {}`
   - `trait MyOrd: MyEq {}`
   - `fn pass_ord(x: a) -> a where a: MyOrd { x }`
2. `resolve_traits type=Int trait=MyOrd` reported `manual_impl_required` and unsatisfied supertrait `MyEq`.
3. `elaborate_evidence "pass_ord(1)"` returned `evidence_required: []`.
4. `type_check "pass_ord(1)"` returned `ok` with type `Int`.

**Classify**: Divergence (implementation boundary).

**Outcome**: Runtime currently accepts a call that the formal trait-bound checker model marks as unsatisfied in both direct and closure-aware variants.

**Impact**:
- Added explicit no-impl witness theorems in `Rill/Traits.lean`:
  - `checkTraitBounds_direct_no_impl_reports_ord`
  - `checkTraitBoundsWithGraph_no_impl_reports_ord_and_eq`
- Recorded this as an implementation/formalization boundary for the evidence-passing roadmap.

### 2026-02-13: Trait call-site gate boundary probe (`MyEq` no-impl)

**Context**: Probed a minimal no-impl call-site (`a: MyEq`) to anchor the newly added call-site gate model (`callSiteAcceptsDirect` / `callSiteAcceptsWithGraph`) against runtime behavior.

**MCP tools used**: `reset_session`, `evaluate`, `type_check`, `elaborate_evidence`

**Predict (Lean side)**:
- `checkTraitBounds_direct_no_impl_reports_eq`: direct checker reports `[("MyEq", "Int")]`.
- `callSiteAcceptsDirect_no_impl_eq_false`: modeled direct call-site gate rejects this state.

**Probe (Rust side via MCP)**:
1. Declared:
   - `trait MyEq {}`
   - `fn pass_eq(x: a) -> a where a: MyEq { x }`
2. `type_check "pass_eq(1)"` returned `ok` with type `Int`.
3. `elaborate_evidence "pass_eq(1)"` returned `evidence_required: []`.

**Classify**: Divergence (implementation boundary).

**Outcome**: Runtime accepts a no-impl `MyEq` bounded call while the formal call-site gate model rejects it.

**Impact**:
- Added `checkTraitBounds_direct_no_impl_reports_eq`.
- Added call-site acceptance model surfaces:
  - `callSiteAcceptsDirect`, `callSiteAcceptsWithGraph`
  - `TraitCallSiteEnforcementSlice`, `traitCallSiteEnforcementSlice_proved`
- Updated `FORMAL.md` and `formal/ROADMAP.md` to track this new boundary layer.

### 2026-02-13: Fully-implemented witness refinement probe (`MyOrd` + `MyEq`)

**Context**: Probed the fully-implemented witness state to align the new refinement bundle (`TraitCallSiteRefinementWitnessSlice`) with observed MCP behavior.

**MCP tools used**: `reset_session`, `evaluate`, `resolve_traits`, `type_check`, `elaborate_evidence`

**Predict (Lean side)**:
- `callSiteAcceptsWithGraph_ord_and_eq_true`: closure-aware gate accepts when both impls exist.
- `callSiteAcceptsWithGraph_ord_and_eq_implies_direct`: in that state, closure-aware acceptance implies direct acceptance.

**Probe (Rust side via MCP)**:
1. Declared:
   - `trait MyEq {}`
   - `trait MyOrd: MyEq {}`
   - `impl MyEq for Int {}`
   - `impl MyOrd for Int {}`
   - `fn pass_ord(x: a) -> a where a: MyOrd { x }`
2. `resolve_traits type=Int trait=MyOrd` reported `status=implemented` with supertrait `MyEq` marked `satisfied: true`.
3. `type_check "pass_ord(1)"` returned `ok` with type `Int`.
4. `elaborate_evidence "pass_ord(1)"` returned `evidence_required: []`.

**Classify**: Agreement (witness-level refinement state).

**Outcome**: MCP behavior matches the formal refinement witness path for the fully-implemented state.

**Impact**:
- Added witness-level refinement theorems:
  - `callSiteAcceptsWithGraph_ord_and_eq_implies_direct`
  - `TraitCallSiteRefinementWitnessSlice`
  - `traitCallSiteRefinementWitnessSlice_proved`
- Updated `FORMAL.md` + `formal/ROADMAP.md` with the new refinement bundle.

### 2026-02-14: Premise-instantiated refinement check (`TraitBoundRefinementPremise` witness path)

**Context**: Validated the new witness-premise bridge path while finalizing
`callSiteAcceptsWithGraph_ord_and_eq_implies_direct_via_premise`.

**MCP tools used**: `reset_session`, `evaluate`, `resolve_traits`, `type_check`, `elaborate_evidence`

**Predict (Lean side)**:
- `traitBoundRefinementPremise_ord_and_eq_witness_proved` should hold in the fully-implemented witness state.
- `callSiteAcceptsWithGraph_ord_and_eq_implies_direct_via_premise` should refine closure-aware acceptance to direct acceptance in that same state.
- Direct-only witness (`impl MyOrd` without `impl MyEq`) should continue to expose the enforcement gap.

**Probe (Rust side via MCP)**:
1. Fully-implemented state:
   - `trait MyEq {}`
   - `trait MyOrd: MyEq {}`
   - `impl MyEq for Int {}`
   - `impl MyOrd for Int {}`
   - `fn pass_ord(x: a) -> a where a: MyOrd { x }`
   - `resolve_traits type=Int trait=MyOrd` -> `status=implemented`, supertrait `MyEq` `satisfied: true`.
   - `type_check "pass_ord(1)"` -> `ok`, type `Int`.
   - `elaborate_evidence "pass_ord(1)"` -> `evidence_required: []`.
2. Direct-only state (`impl MyOrd for Int` only):
   - `resolve_traits type=Int trait=MyOrd` -> `status=implemented`, supertrait `MyEq` `satisfied: false`.
   - `type_check "pass_ord(1)"` -> `ok`, type `Int`.
   - `elaborate_evidence "pass_ord(1)"` -> `evidence_required: []`.

**Classify**: Agreement on witness-premise state; divergence remains on direct-only boundary.

**Outcome**: Runtime behavior matches the new witness-premise refinement theorem in the fully-implemented state, and still exhibits the modeled direct-vs-closure enforcement gap in the direct-only state.

**Impact**:
- Finalized witness-premise bridge theorem:
  - `callSiteAcceptsWithGraph_ord_and_eq_implies_direct_via_premise`
- Kept the divergence boundary explicit for future trait-call-site discharge work.

### 2026-02-14: Post-`61bd3a1` language-shift regression probes (actor messages, prelude policy, trait closure, row-unification sanity)

**Context**: Re-validated formalization assumptions after `feat: align function-only syntax, imports, prelude, and actor docs/tests` changed parser/eval/infer surfaces.

**MCP tools used**: `reset_session`, `evaluate`, `type_check`, `get_type`, `resolve_traits`

**Predict (Lean side)**:
- Row-unification bridge assumptions should remain stable (no unifier algorithm rewrite expected).
- Trait-closure divergence witness should still reproduce (`MyOrd` implemented, `MyEq` missing).
- Actor message-style syntax should type-check under the new `impl Actor for T where Message = ...` shape.
- Interactive prelude should expose only the new extended-prelude subset as bare names.

**Probe (Rust side via MCP)**:
1. Actor message-style setup:
   - `type CounterMsg = Inc | Get`
   - `record Counter { count: Int }`
   - `impl Actor for Counter where Message = CounterMsg { fn handle(...) -> Counter { ... } }`
   - `type_check "{ let c = spawn Counter { count: 0 }\nsend(c, Inc) }"` -> `ok`, type `()`.
   - `type_check "{ let c = spawn Counter { count: 0 }\ncall(c, Get) }"` -> `ok`, type `Result((), ActorError)`.
   - `type_check "{ let c = spawn Counter { count: 0 }\nsend(c, :inc) }"` -> `error`, no method `inc`.
2. Extended-prelude boundary:
   - `type_check "sqrt(16.0)"` -> `ok`, type `Float`.
   - `type_check "to_json(1)"` -> `error`, undefined variable `to_json` (not bare-bound).
3. Trait-closure divergence witness:
   - `trait MyEq {}; trait MyOrd: MyEq {}; impl MyOrd for Int {}; fn pass_ord(x: a) -> a where a: MyOrd { x }`
   - `resolve_traits type=Int trait=MyOrd` -> `implemented`, supertrait `MyEq` `satisfied: false`.
   - `type_check "pass_ord(1)"` -> `ok`, type `Int`.
4. Row-unification sanity:
   - `get_type "(|r| #(r.a, r.b))(#{ a: 1, b: \"x\", c: true })"` -> `#(Int, String)`.
   - `type_check "(|r| #(r.a, r.b))(#{ a: 1 })"` -> `error`, missing field `b`.

**Classify**: Mixed.
- Agreement: actor-message syntax/typing, extended-prelude policy, row-unification behavior.
- Divergence (known boundary): trait-closure enforcement remains weaker at runtime call sites than formal direct/closure checkers.

**Outcome**: The language shift changes parser/runtime policy surfaces, but the formal row-unification core assumptions remain behaviorally intact in MCP probes.

**Impact**:
- Added `M5` post-shift delta checklist to `formal/ROADMAP.md`.
- Kept trait-call-site divergence as an active evidence-passing/formalization boundary.
- Added actor message-style formal boundary surface in `formal/Rill/Traits.lean`:
  - `ActorDispatchModel`
  - `ActorMessageDispatchBoundarySlice`
  - `actorMessageDispatchBoundarySlice_proved`

### 2026-02-21: WP7.1 temporal leaf parity probe (Date/DateTime)

**Context**: Validating the first M7 vertical slice while adding new leaf constructors
(`Date`, `DateTime`, plus leaf-constructor expansion path) to the Lean model and proving
`TemporalLeafParity` lemmas.

**MCP tools used**: `reset_session`, `type_check`, `diagnose`, `get_type`

**Predict (Lean side)**:
- `Date` and `DateTime` should type-check reflexively in function signatures.
- `Date` should not unify with `DateTime` (typed mismatch at annotation boundary).
- Container ascriptions should preserve temporal element identity (`List(Date)`, `List(DateTime)`).

**Probe (Rust side via MCP)**:
1. Reflexive typing:
   - `fn same_date(x: Date, y: Date) -> Date { if true { x } else { y } }` -> `ok`.
   - `fn same_datetime(x: DateTime, y: DateTime) -> DateTime { if true { x } else { y } }` -> `ok`.
2. Cross-type mismatch:
   - `fn bad_temporal(x: Date) -> DateTime { x }` via `diagnose` ->
     `type_mismatch` (`declared DateTime`, value `Date`).
3. Container identity:
   - `get_type "[] as List(Date)"` -> `List(Date)`.
   - `get_type "[] as List(DateTime)"` -> `List(DateTime)`.

**Classify**: Agreement.

**Outcome**: Runtime/typechecker behavior matches the temporal-leaf conjectures used by
`Rill/Properties/TemporalLeafParity.lean`.

**Impact**:
- Kept WP7.1 constructor expansion on a vertical proof path (not just datatype plumbing).
- Added explicit temporal parity theorem module and retained MCP evidence trace for paper/worklog use.

### 2026-02-21: WP7.2 precision numeric parity probe (IntN/FloatN) after MCP restart

**Context**: Revalidated precision numeric constructor behavior on the restarted MCP server while landing
`IntN`/`FloatN` parity proofs (`PrecisionLeafParity`) and exhaustiveness fixes across core proof modules.

**MCP tools used**: `reset_session`, `get_type`, `type_check`, `diagnose`

**Predict (Lean side)**:
- Precision numerics should type-check reflexively (e.g., `Int32 -> Int32`, `Float32` container ascriptions).
- Width mismatches should fail at annotation boundaries (`Int32` vs `Int64`, `Float32` vs `Float64`).
- Short aliases (`I32`, `F32`) are not guaranteed by the model and should not be assumed.

**Probe (Rust side via MCP)**:
1. Reflexive typing:
   - `get_type "[] as List(Int32)"` -> `List(Int32)`.
   - `get_type "[] as List(Float32)"` -> `List(Float32)`.
   - `type_check "fn id32(x: Int32) -> Int32 { x }"` -> `ok`.
2. Cross-type/width mismatch:
   - `diagnose "fn bad32(x: Int32) -> Float32 { x }"` ->
     `type_mismatch` (`declared Float32`, value `Int32`).
   - `diagnose "fn bad_int_width(x: Int32) -> Int64 { x }"` ->
     `type_mismatch` (`declared Int64`, value `Int32`).
   - `diagnose "fn bad_float_width(x: Float32) -> Float64 { x }"` ->
     `type_mismatch` (`declared Float64`, value `Float32`).
3. Alias surface check:
   - `diagnose "[] as List(I32)"` -> unknown type `List(I32)`.
   - `diagnose "[] as List(F32)"` -> unknown type `List(F32)`.

**Classify**: Agreement.

**Outcome**: Restarted-MCP behavior matches the Lean precision-leaf conjectures used in
`Rill/Properties/PrecisionLeafParity.lean`: reflexive width-qualified typing succeeds and
cross-width/type mismatches are rejected.

**Impact**:
- Confirms WP7.2 `IntN`/`FloatN` parity on a vertical proof path, not just constructor plumbing.
- Documents naming boundary (`Int32`/`Float32` supported; `I32`/`F32` absent) for future parser/model alignment.

### 2026-02-21: WP7.2 Dim-kernel surface probe

**Context**: After adding a standalone Dim/DimVar formal kernel (`Rill/Dimensions.lean`), checked how much of that surface is currently visible through runtime type annotations.

**MCP tools used**: `diagnose`, `type_check`

**Predict (Lean side)**:
- Dim/DimVar kernel lemmas are model-internal until Decimal/shape constructors are wired.
- Runtime/MCP may not expose `Dim` as a first-class container element type.

**Probe (Rust side via MCP)**:
1. `diagnose "[] as List(Dim)"` -> `unknown type List(Dim)`.
2. `type_check "fn dim_id(x: Dim) -> Dim { x }"` -> accepted as polymorphic `(a) -> a` (annotation not treated as a concrete runtime type constructor in this path).

**Classify**: Partial agreement (boundary confirmed).

**Outcome**: MCP confirms the current implementation boundary: precision numerics are first-class in user-visible types, while `Dim` remains a non-public/internal concept for now.

**Impact**:
- Keeps WP7.2 vertical scope honest: Dim kernel is formally proved, but production-language exposure still depends on Decimal/shape integration.

### 2026-02-21: WP7.3 decimal surface probe

**Context**: After adding `Ty.decimal` and the `DecimalParity` theorem slice, checked MCP exposure for decimal type annotations and parameterization syntax.

**MCP tools used**: `get_documentation`, `diagnose`, `type_check`

**Predict (Lean side)**:
- Decimal constructor parity should hold in the model (reflexive + mismatch witnesses).
- Runtime syntax/exposure may lag, especially for parameterized forms and generic containers.

**Probe (Rust side via MCP)**:
1. Documentation surface:
   - `get_documentation "Decimal"` returns builtin type metadata.
2. Annotation behavior:
   - `diagnose "fn decimal_id(x: Decimal) -> Decimal { x }"` -> no diagnostics.
   - `type_check "fn decimal_id(x: Decimal) -> Decimal { x }"` -> inferred `(a) -> a` (annotation treated generically in this path).
   - `diagnose "fn decimal_to_float(x: Decimal) -> Float { x }"` -> no diagnostics.
3. Container/parameter syntax:
   - `diagnose "[] as List(Decimal)"` -> unknown type `List(Decimal)`.
   - `diagnose "[] as List(Decimal(10,2))"` -> syntax error at type annotation.

**Classify**: Boundary confirmed (partial divergence).

**Outcome**: MCP indicates decimal runtime/type-annotation exposure is currently inconsistent with a first-class parameterized decimal type surface, so the Lean decimal parity work remains a model-side vertical slice awaiting fuller implementation parity.

**Impact**:
- Keeps WP7.3 claims scoped: constructor-level formal progress landed without overclaiming runtime syntax parity.

### 2026-02-22: WP7.3 decimal post-fix revalidation (loop closure)

**Context**: Re-ran the decimal MCP probes after implementation fix `e6dbe50`
(`fix: support decimal annotation semantics and syntax`) and MCP server rebuild/restart.

**MCP tools used**: `reset_session`, `type_check`, `get_type`, `diagnose`, `get_documentation`

**Predict (Lean side)**:
- Bare decimal annotations should remain concrete (`Decimal`), not collapse to unconstrained generics.
- Container and parameterized decimal type syntax should parse/type-check (`List(Decimal)`, `Decimal(10, 2)` in annotations).
- Cross-type annotation mismatch should report a type error (`Decimal` not silently accepted as `Float`).

**Probe (Rust side via MCP)**:
1. Annotation behavior:
   - `type_check "fn decimal_id(x: Decimal) -> Decimal { x }"` ->
     binding type `(Decimal) -> Decimal`.
   - `get_type "decimal_id"` -> `(Decimal) -> Decimal`.
2. Container/parameter syntax:
   - `get_type "[] as List(Decimal)"` -> `List(Decimal)`.
   - `get_type "[] as List(Decimal(10, 2))"` -> `List(Decimal(10, 2))`.
3. Mismatch surface:
   - `diagnose "fn decimal_to_float(x: Decimal) -> Float { x }"` ->
     `type_mismatch` (`declared Float`, value `Decimal`).
4. Docs metadata:
   - `get_documentation "Decimal"` -> builtin fixed-point decimal metadata present.

**Classify**: Agreement.

**Outcome**: The previous decimal divergence is resolved. MCP behavior now aligns with the
intended first-class decimal surface and supports the formalization feedback-loop claim:
model-side boundary identification -> MCP reproduction -> implementation patch -> MCP convergence.

**Impact**:
- Closes the WP7.3 runtime parity loop with concrete before/after evidence.
- Upgrades decimal from "known divergence" to "resolved implementation/formal alignment point."

### 2026-02-22: WP7.4 shape constructor surface probe (`FixedSizeList` / `Tensor`)

**Context**: After wiring `Ty.fixedSizeList` / `Ty.tensor` through substitution and unifier match arms, probed MCP/runtime annotation exposure for shape constructors.

**MCP tools used**: `reset_session`, `get_documentation`, `diagnose`, `type_check`, `get_type`

**Predict (Lean side)**:
- Constructor-level parity should hold in the model (substitution step, reflexive unify, mismatch witnesses).
- Runtime syntax/docs may lag for parameterized shape annotations.

**Probe (Rust side via MCP)**:
1. Documentation surface:
   - `get_documentation "FixedSizeList"` -> no documentation found.
   - `get_documentation "Tensor"` -> no documentation found.
2. Parameterized annotation behavior:
   - `diagnose "[] as List(FixedSizeList(Int, 4))"` ->
     integer literal not valid as a type + unknown type `List(FixedSizeList(Int, 4))`.
   - `diagnose "[] as List(Tensor(Int, [2, 3]))"` ->
     syntax errors around shape list annotation.
3. Bare annotation fallback behavior:
   - `type_check "fn shape_id(x: Tensor) -> Tensor { x }"` -> `(a) -> a`.
   - `type_check "fn tensor_to_int(x: Tensor) -> Int { x }"` -> `(Int) -> Int`.
   - `type_check "fn fsl_to_int(x: FixedSizeList) -> Int { x }"` -> `(Int) -> Int`.

**Classify**: Partial divergence (model/runtime boundary confirmed).

**Outcome**: The Lean WP7.4 slice is ahead of user-facing runtime surface for shape constructors. The model now includes constructor-level unifier behavior, but MCP evidence indicates parameterized `FixedSizeList`/`Tensor` annotations are not yet first-class in the exposed type syntax/documentation path.

**Impact**:
- Keeps WP7.4 claims scoped to formal core parity, without overclaiming runtime syntax parity.
- Adds another concrete formalization-to-implementation boundary artifact for the MCP loop evidence trail.

### 2026-02-22: WP7.5 nominal ADT/opaque surface probe (`Sum` / `Opaque`)

**Context**: After adding `Ty.sum`/`Ty.opaque`, unifier branches, and the
`NominalAdtParity` theorem slice, probed MCP/runtime nominal typing behavior.

**MCP tools used**: `reset_session`, `type_check`, `get_type`, `diagnose`

**Predict (Lean side)**:
- Nominal constructors should type-check reflexively (`Shape -> Shape`, `UserId -> UserId`).
- Nominal name mismatches should fail even when structures look similar (`Alpha` vs `Gamma`, `UserId` vs `OrderId`).
- Opaque should remain nominal at annotation boundaries (`UserId` not accepted as `Int`).

**Probe (Rust side via MCP)**:
1. Sum/ADT reflexive typing:
   - `type_check "type Shape = Circle(Float) | Rectangle(Float, Float)"` -> type registered.
   - `type_check "fn sum_id(x: Shape) -> Shape { x }"` -> `(Shape) -> Shape`.
   - `get_type "sum_id"` -> `(Shape) -> Shape`.
2. Opaque reflexive typing:
   - `type_check "opaque UserId = Int"` -> opaque registered.
   - `type_check "fn opaque_id(x: UserId) -> UserId { x }"` -> `(UserId) -> UserId`.
   - `get_type "opaque_id"` -> `(UserId) -> UserId`.
3. Nominal mismatch boundaries:
   - `type_check "type Alpha = Box(Int)"`; `type_check "type Gamma = Cup(Int)"`.
   - `diagnose "fn alpha_to_gamma(x: Alpha) -> Gamma { x }"` ->
     `type_mismatch` (`declared Gamma`, value `Alpha`).
   - `type_check "opaque OrderId = Int"`.
   - `diagnose "fn user_to_order(x: UserId) -> OrderId { x }"` ->
     `type_mismatch` (`declared OrderId`, value `UserId`).
   - `diagnose "fn opaque_to_int(x: UserId) -> Int { x }"` ->
     `type_mismatch` (`declared Int`, value `UserId`).
4. Runtime naming nuance:
   - `type_check "type Beta = Box(Int)"` fails because variant name `Box` is already defined in `Alpha` (global variant-name namespace rule).

**Classify**: Agreement (with a documented runtime naming nuance).

**Outcome**: MCP behavior matches the Lean WP7.5 nominal/opaque constructor
claims: same-name reflexive acceptance plus nominal mismatch rejection.

**Impact**:
- Advances WP7.5 from unmodeled to a proved constructor-parity slice.
- Adds executable evidence that nominal boundaries are enforced in the implementation path.

### 2026-02-22: WP7.6 internal constructor-app probe (`App` / `Constructor`) + surface boundary

**Context**: After adding Lean `Ty.app` / `Ty.constructor` and the
`HigherOrderConstructorParity` theorem slice, probed MCP-facing constructor
annotation behavior and nearby higher-order type syntax exposure.

**MCP tools used**: `diagnose`, `type_check`

**Predict (Lean side)**:
- Constructor-app style annotations should enforce parameterized constructor structure (`List(Int)`/`Map(String, Int)` accepted; mismatches rejected).
- Internal `App`/`Constructor` terms are implementation-internal and may not have direct user-facing syntax.
- WP7.6 remainder (`Forall`/`Existential`) should stay explicitly scoped if syntax/runtime exposure is partial.

**Probe (Rust side via MCP)**:
1. Parameterized constructor annotations:
   - `diagnose "fn list_id(x: List(Int)) -> List(Int) { x }"` -> no diagnostics.
   - `type_check "fn list_id(x: List(Int)) -> List(Int) { x }"` -> `(List(Int)) -> List(Int)`.
   - `diagnose "fn map_id(x: Map(String, Int)) -> Map(String, Int) { x }"` -> no diagnostics.
2. Constructor-argument mismatch behavior:
   - `diagnose "fn list_to_option(x: List(Int)) -> Option(Int) { x }"` ->
     `type_mismatch` (declared option/int path, value `List(Int)`).
   - `diagnose "fn map_key_mismatch(x: Map(String, Int)) -> Map(Int, Int) { x }"` ->
     `type_mismatch` on key type (`declared Int`, value `String`).
3. Adjacent higher-order surface boundary:
   - `diagnose "fn rank2_id(f: forall a. (a) -> a, x: Int) -> Int { f(x) }"` ->
     syntax diagnostics at the `forall` annotation path in this surface.
   - `diagnose "fn takes_any(x: any Show) -> any Show { x }"` -> no diagnostics.
   - `type_check "fn takes_any(x: any Show) -> any Show { x }"` -> `(any Show) -> any Show`.

**Classify**: Partial agreement (constructor-app parity agrees; WP7.6 surface breadth still partial).

**Outcome**: MCP evidence matches the WP7.6 vertical slice claims for
constructor-application behavior while also confirming that broader
higher-order surfaces are uneven (`any` works; `forall` path here is not yet
accepted in this probe context).

**Impact**:
- Moves WP7.6 from fully unmodeled to a concrete constructor-app parity slice with executable evidence.
- Keeps remaining WP7.6 scope explicit: `Forall` and fuller higher-rank theorem/runtime parity remain pending.

### 2026-02-22: WP7.7 runtime-wrapper surface probe (`Dynamic` / `Task` / `Actor` / `Arc`)

**Context**: After adding Lean `Ty.dynamic`/`Ty.task`/`Ty.actor`/`Ty.arc`
constructors and the `RuntimeWrapperParity` theorem slice, probed MCP/runtime
annotation behavior for wrapper types and dynamic unification boundaries.

**MCP tools used**: `diagnose`, `type_check`

**Predict (Lean side)**:
- Wrapper constructors should type-check reflexively (`Task(Int)`, `Actor(Int)`, `Arc(Int)`).
- Wrapper inner-type mismatches should reject.
- `Dynamic` should unify permissively and may absorb annotation boundaries.

**Probe (Rust side via MCP)**:
1. Wrapper reflexive behavior:
   - `diagnose "fn task_id(x: Task(Int)) -> Task(Int) { x }"` -> no diagnostics.
   - `type_check "fn task_id(x: Task(Int)) -> Task(Int) { x }"` -> `(Task(Int)) -> Task(Int)`.
   - `diagnose "fn actor_id(x: Actor(Int)) -> Actor(Int) { x }"` -> no diagnostics.
   - `type_check "fn actor_id(x: Actor(Int)) -> Actor(Int) { x }"` -> `(Actor(Int)) -> Actor(Int)`.
   - `diagnose "fn arc_id(x: Arc(Int)) -> Arc(Int) { x }"` -> no diagnostics.
   - `type_check "fn arc_id(x: Arc(Int)) -> Arc(Int) { x }"` -> `(Arc(Int)) -> Arc(Int)`.
2. Wrapper mismatch witness:
   - `diagnose "fn task_mismatch(x: Task(Int)) -> Task(String) { x }"` ->
     `type_mismatch` (`declared String`, value `Int` inside wrapper path).
3. Dynamic permissive boundary:
   - `diagnose "fn dyn_id(x: Dynamic) -> Dynamic { x }"` -> no diagnostics.
   - `diagnose "fn dyn_to_int(x: Dynamic) -> Int { x }"` -> no diagnostics.
   - `type_check "fn dyn_to_int(x: Dynamic) -> Int { x }"` -> `(Dynamic) -> Dynamic`
     (annotation narrows less than declared `Int` in this path).

**Classify**: Partial agreement (wrapper parity agrees; dynamic boundary remains permissive/annotation-absorbing).

**Outcome**: MCP behavior matches the wrapper-constructor parity slice and
confirms the intentionally permissive dynamic boundary, including the current
annotation-absorption nuance for `Dynamic`.

**Impact**:
- Advances WP7.7 with a concrete proved wrapper slice (`Dynamic`/`Task`/`Actor`/`Arc`) and executable evidence.
- Keeps remaining WP7.7 scope explicit: `GroupedFrame`/`Tagged` modeling and fuller dynamic-boundary theorem coverage remain pending.

### 2026-02-22: WP7.7 grouped/tagged surface probe + dynamic policy boundary

**Context**: After adding Lean `Ty.groupedFrame`/`Ty.tagged` and
`GroupedTaggedParity`, probed MCP/runtime surface behavior for grouped/tagged
annotations and re-checked dynamic-annotation boundary semantics.

**MCP tools used**: `diagnose`, `type_check`

**Predict (Lean side)**:
- `GroupedFrame`/`Tagged` constructor parity should hold in the model (reflexive + mismatch witnesses).
- Runtime surface may expose only partial annotation syntax, especially parameterized tagged forms.
- Dynamic boundary remains permissive unless implementation policy tightens.

**Probe (Rust side via MCP)**:
1. Bare grouped/tagged annotations:
   - `diagnose "fn grouped_id(x: GroupedFrame) -> GroupedFrame { x }"` -> no diagnostics.
   - `type_check "fn grouped_id(x: GroupedFrame) -> GroupedFrame { x }"` -> `(a) -> a`.
   - `diagnose "fn tagged_id(x: Tagged) -> Tagged { x }"` -> no diagnostics.
   - `type_check "fn tagged_id(x: Tagged) -> Tagged { x }"` -> `(a) -> a`.
2. Boundary coercion behavior:
   - `diagnose "fn grouped_to_df(x: GroupedFrame) -> DataFrame { x }"` -> no diagnostics.
   - `type_check "fn grouped_to_df(x: GroupedFrame) -> DataFrame { x }"` ->
     `(DataFrame(#{ ra })) -> DataFrame(#{ ra })`.
   - `diagnose "fn tagged_to_int(x: Tagged) -> Int { x }"` -> no diagnostics.
   - `type_check "fn tagged_to_int(x: Tagged) -> Int { x }"` -> `(Int) -> Int`.
3. Parameterized tagged syntax:
   - `diagnose "fn tagged_int_id(x: Tagged(Int, [unit=1])) -> Tagged(Int, [unit=1]) { x }"` ->
     syntax diagnostics at annotation parse points.
4. Dynamic policy re-check:
   - `type_check "fn dyn_to_int(x: Dynamic) -> Int { x }"` -> `(Dynamic) -> Dynamic`.

**Classify**: Partial divergence (model constructor parity ahead of precise runtime annotation policy/surface).

**Outcome**: The Lean grouped/tagged constructor slice is landed, but MCP shows
runtime annotation behavior remains permissive/coercive at bare boundaries and
parameterized tagged syntax is not yet exposed in this path.

**Impact**:
- Advances WP7.7 from wrapper-only to full constructor modeling (`Dynamic`/`GroupedFrame`/`Task`/`Actor`/`Arc`/`Tagged`) with executable boundary evidence.
- Elevates dynamic annotation absorption (`Dynamic -> Int` infers `(Dynamic) -> Dynamic`) from “nuance” to an explicit typing-policy decision point (candidate direction: require explicit cast/assertion for `Dynamic -> concrete` boundaries).

### 2026-02-22: WP7.6 existential parity probe (`any`) + `forall` boundary re-check

**Context**: After landing `Ty.existential` propagation + `Rill/Properties/ExistentialParity.lean`,
re-probed MCP surface behavior for existential annotations and re-checked adjacent
`forall` annotation parsing in the same scope.

**MCP tools used**: `reset_session`, `diagnose`, `type_check`

**Predict (Lean side)**:
- Existential constructor parity should hold in the model (reflexive + mismatch witnesses).
- Surface `any` annotations should type-check where supported.
- `forall` surface may remain a separate boundary if parser/type-annotation support is incomplete in this path.

**Probe (Rust side via MCP)**:
1. Existential reflexive behavior:
   - `diagnose "fn takes_any(x: any Show) -> any Show { x }"` -> no diagnostics.
   - `type_check "fn takes_any(x: any Show) -> any Show { x }"` -> `(any Show) -> any Show`.
2. Existential mismatch boundary:
   - `diagnose "fn any_to_int(x: any Show) -> Int { x }"` ->
     `type_mismatch` (`declared Int`, value `any Show`).
3. Adjacent rank-2 surface boundary:
   - `diagnose "fn rank2_id(f: forall a. (a) -> a, x: Int) -> Int { f(x) }"` ->
     syntax diagnostics at the `forall` annotation path.

**Classify**: Partial divergence.

**Outcome**: MCP confirms the new existential constructor slice is aligned at the
user-facing annotation boundary (`any` accepted, existential-to-concrete mismatch rejected),
while `forall` annotation syntax remains unavailable in this probe path.

**Impact**:
- Advances WP7.6 from constructor-app-only to constructor-app+existential parity with executable evidence.
- Sharpens the remaining WP7.6 boundary to `Forall` modeling/runtime-surface parity.

### 2026-02-22: WP7.6 `forall` syntax correction probe (probe-error fix)

**Context**: Re-checked the earlier WP7.6 `forall` boundary probe after noticing
the tested syntax used `forall a. (a) -> a` instead of the parser-supported
`forall a. fn(a) -> a`.

**MCP tools used**: `reset_session`, `diagnose`, `type_check`

**Predict (Lean side)**:
- The previous syntax failure may have been probe error, not implementation divergence.
- Correct syntax (`forall a. fn(a) -> a`) should parse/type-check if rank-2 surface is present.

**Probe (Rust side via MCP)**:
1. Previous (incorrect) syntax:
   - `diagnose "fn rank2_bad(f: forall a. (a) -> a, x: Int) -> Int { f(x) }"` ->
     syntax diagnostics.
2. Correct syntax:
   - `diagnose "fn rank2_id(f: forall a. fn(a) -> a, x: Int) -> Int { f(x) }"` ->
     no diagnostics.
   - `type_check "fn rank2_id(f: forall a. fn(a) -> a, x: Int) -> Int { f(x) }"` ->
     `(forall a. (a) -> a, Int) -> Int`.

**Classify**: Agreement (previous partial divergence was probe syntax error).

**Outcome**: `forall` annotation syntax is present in the implementation surface;
the previous failure came from probing the wrong form. WP7.6 remaining gap is
formal coverage (`Forall` modeling/theorems), not parser/runtime syntax absence.

**Impact**:
- Clears a false divergence from the MCP evidence trail.
- Tightens WP7.6 status to a genuine formalization gap rather than an implementation gap.

### 2026-02-22: WP7.6 `Forall` constructor parity probe (post-model landing)

**Context**: After adding `Ty.forall` propagation through substitution/free-vars/occurs/generalize/unify
and landing `Rill/Properties/ForallParity.lean`, revalidated rank-2 annotation behavior on MCP.

**MCP tools used**: `reset_session`, `diagnose`, `type_check`

**Predict (Lean side)**:
- Correct rank-2 annotation syntax (`forall a. fn(a) -> a`) should type-check.
- Mis-specified return use should report type mismatch.
- Legacy incorrect syntax (`forall a. (a) -> a`) should continue to fail as syntax.

**Probe (Rust side via MCP)**:
1. Correct rank-2 usage:
   - `diagnose "fn apply_rank2(f: forall a. fn(a) -> a, x: Int) -> Int { f(x) }"` -> no diagnostics.
   - `type_check "fn apply_rank2(f: forall a. fn(a) -> a, x: Int) -> Int { f(x) }"` ->
     `(forall a. (a) -> a, Int) -> Int`.
2. Type boundary witness:
   - `diagnose "fn bad_rank2_ret(f: forall a. fn(a) -> a, x: Int) -> String { f(x) }"` ->
     `type_mismatch` (`expected String`, got `Int`).
3. Syntax boundary witness:
   - `diagnose "fn bad_rank2_syntax(f: forall a. (a) -> a, x: Int) -> Int { f(x) }"` ->
     syntax diagnostics at the incorrect post-`forall` type form.

**Classify**: Agreement.

**Outcome**: MCP behavior matches the `Forall` constructor parity slice and
confirms the expected surface contract: `forall` is available with `fn(...)`
function-type syntax, while the parenthesized non-`fn` form remains invalid.

**Impact**:
- Advances WP7.6 from App/Constructor/Existential-only parity to full constructor coverage including `Forall`.
- Narrows remaining WP7.6 work to language-level higher-rank theorem depth (alpha-equivalence/subsumption/evidence interactions), not constructor modeling.

### 2026-02-22: WP7.6 `forall` canonicalization probe (alpha/arity boundary)

**Context**: After landing `ForallParity`, probed whether runtime `forall` behavior is
nominal over binder lists (as current Lean constructor does) or canonicalized.

**MCP tools used**: `reset_session`, `diagnose`, `type_check`

**Predict (Lean side)**:
- Current model uses nominal binder-list equality in the `Ty.forall` unifier branch.
- If implementation canonicalizes binders, alpha-equivalent or unused-binder variants may still be accepted.

**Probe (Rust side via MCP)**:
1. Alpha-equivalent binder names:
   - `diagnose "fn alpha_assign(f: forall a. fn(a) -> a, g: forall b. fn(b) -> b) -> forall a. fn(a) -> a { g }"` ->
     no diagnostics.
   - `type_check ...` -> `(forall a. (a) -> a, forall a. (a) -> a) -> forall a. (a) -> a`
     (binder names normalized).
2. Unused-binder arity variants (comma syntax):
   - `diagnose "fn forall_arity_assign(f: forall a. fn(a) -> a) -> forall a, b. fn(a) -> a { f }"` ->
     no diagnostics.
   - `diagnose "fn forall_arity_assign2(f: forall a, b. fn(a) -> a) -> forall a. fn(a) -> a { f }"` ->
     no diagnostics.
   - `type_check "fn forall_arity_assign(...)"` -> `(forall a. (a) -> a) -> forall a. (a) -> a`
     (unused extra binder normalized away in this surface).
3. Control boundary:
   - `diagnose "fn bad_rank2_ret(f: forall a. fn(a) -> a, x: Int) -> String { f(x) }"` ->
     `type_mismatch` (`expected String`, got `Int`).

**Classify**: Partial divergence.

**Outcome**: Implementation behaves with `forall` binder canonicalization in this
surface, while the current Lean constructor/unifier is nominal in binder-list
comparison. This does not invalidate constructor-level progress, but it is a real
alignment gap for higher-rank metatheory claims.

**Impact**:
- Keeps WP7.6 claims honest: constructor slice is landed, but binder-canonicalization
  semantics remain an explicit model/implementation boundary.
- Raises priority of alpha-equivalence/subsumption alignment before stronger
  rank-2 theorem claims.

### 2026-02-22: WP7.6 `forall` model-alignment follow-up (divergence closure)

**Context**: Closed the constructor-level `forall` binder-canonicalization gap by
updating Lean unification to match MCP-observed behavior.

**Lean-side change**:
1. `Rill/Unify.lean`:
   - `Ty.forall` branch now unifies quantified bodies directly (binder-list names and
     vacuous extra binders no longer block constructor-level compatibility).
2. `Rill/Properties/ForallParity.lean`:
   - Added constructor-level alpha/vacuous theorem surface:
     - `forall_alpha_equiv_unifies`
   - Added concrete acceptance witnesses:
     - `forall_alpha_renaming_accepts`
     - `forall_vacuous_binder_accepts`
   - Kept mismatch witness on body incompatibility:
     - `forall_body_mismatch`

**Classify**: Agreement (constructor-level parity restored).

**Outcome**: The previous partial divergence is closed at constructor parity level:
Lean now matches the implementation’s observed `forall` alpha/vacuous-binder
compatibility behavior in MCP probes.

**Impact**:
- Reclassifies the WP7.6 gap from model/implementation constructor mismatch to
  higher-rank theorem depth (subsumption/evidence/principal-typing-level claims).

### 2026-02-22: WP7.6 `forall` canonicalization re-probe (post-canonical-equivalence lemmas)

**Context**: After extending `ForallParity` with canonical-equivalence closure
lemmas and a normalized `forall` branch-reduction contract, re-ran the core MCP
canonicalization probes to keep implementation evidence fresh in the log.

**MCP tools used**: `diagnose`, `type_check`

**Predict (Lean side)**:
- Alpha-equivalent binder names should be accepted and normalize in signatures.
- Vacuous extra binders should not block assignment compatibility.
- Incorrect legacy syntax (`forall a. (a) -> a`) should still fail.

**Probe (Rust side via MCP)**:
1. Alpha-equivalent binder names:
   - `diagnose "fn alpha_assign(f: forall a. fn(a) -> a, g: forall b. fn(b) -> b) -> forall a. fn(a) -> a { g }"` ->
     no diagnostics.
   - `type_check ...` -> `(forall a. (a) -> a, forall a. (a) -> a) -> forall a. (a) -> a`.
2. Vacuous-binder variants:
   - `diagnose "fn forall_arity_assign(f: forall a. fn(a) -> a) -> forall a, b. fn(a) -> a { f }"` ->
     no diagnostics.
   - `diagnose "fn forall_arity_assign2(f: forall a, b. fn(a) -> a) -> forall a. fn(a) -> a { f }"` ->
     no diagnostics.
   - `type_check "fn forall_arity_assign(f: forall a. fn(a) -> a) -> forall a, b. fn(a) -> a { f }"` ->
     `(forall a. (a) -> a) -> forall a. (a) -> a`.
   - `type_check "fn forall_arity_assign2(f: forall a, b. fn(a) -> a) -> forall a. fn(a) -> a { f }"` ->
     `(forall a, b. (a) -> a) -> forall a, b. (a) -> a`.
3. Syntax control:
   - `diagnose "fn bad_rank2_syntax(f: forall a. (a) -> a, x: Int) -> Int { f(x) }"` ->
     syntax diagnostics at the non-`fn` function-type annotation.

**Classify**: Agreement.

**Outcome**: MCP behavior remains consistent with the Lean-side canonicalization
alignment (`forall` alpha/vacuous compatibility) and with the intended parser
surface contract (`forall a. fn(...) -> ...` syntax only).

**Impact**:
- Keeps WP7.6 evidence current after the canonical-equivalence theorem expansion.
- Supports using `ForallParity`’s canonical-equivalence lemmas as a stable bridge
  for the next higher-rank theorem layer.

### 2026-02-22: WP7.7 dynamic return-boundary re-probe (non-Int + reverse direction)

**Context**: After extending `RuntimeWrapperParity` with additional function-return
absorption witnesses, re-checked MCP behavior for non-`Int` and reverse-direction
`Dynamic` return-annotation paths.

**MCP tools used**: `diagnose`, `type_check`

**Predict (Lean side)**:
- `Dynamic -> concrete` return annotations remain permissive and collapse.
- `concrete -> Dynamic` return annotations remain permissive and can collapse to the
  concrete return in inferred signatures.

**Probe (Rust side via MCP)**:
1. Non-`Int` concrete target:
   - `diagnose "fn dyn_to_bool(x: Dynamic) -> Bool { x }"` -> no diagnostics.
   - `type_check ...` -> `(Dynamic) -> Dynamic`.
2. Reverse-direction annotation:
   - `diagnose "fn int_to_dyn(x: Int) -> Dynamic { x }"` -> no diagnostics.
   - `type_check ...` -> `(Int) -> Int`.

**Classify**: Agreement.

**Outcome**: MCP confirms both directions of the permissive function-return boundary:
concrete annotations can be absorbed by `Dynamic`, and `Dynamic` annotations can be
absorbed by concrete returns.

**Impact**:
- Extends WP7.7 evidence beyond the single `Int`-anchored witness.
- Supports the expanded `RuntimeWrapperParity` theorem family and keeps the
  explicit dynamic-boundary policy discussion grounded in executable behavior.

### 2026-02-22: WP7.5 ADT constructor-arity probe (post-arity witness expansion)

**Context**: After adding explicit `sum_arity_mismatch` / `opaque_arity_mismatch`
theorems in `NominalAdtParity`, re-checked MCP diagnostics for ADT constructor
arity enforcement on the implementation path.

**MCP tools used**: `type_check`, `diagnose`

**Predict (Lean side)**:
- Nominal constructor arity mismatches should reject (theorem-level: type-list
  arity mismatch path).
- Correct arity usage should be accepted.

**Probe (Rust side via MCP)**:
1. ADT registration:
   - `type_check "type Shape = Circle(Float) | Rectangle(Float, Float)"` ->
     type registered with variants.
2. Arity mismatch:
   - `diagnose "fn bad_circle() -> Shape { Circle(1.0, 2.0) }"` ->
     `arity_mismatch` (`Circle` expects 1 argument, got 2`).
3. Control:
   - `diagnose "fn good_circle() -> Shape { Circle(1.0) }"` ->
     no diagnostics.

**Classify**: Agreement.

**Outcome**: MCP confirms runtime ADT constructor-arity enforcement is aligned
with the formal nominal arity-mismatch slice.

**Impact**:
- Strengthens WP7.5 parity evidence beyond nominal-name mismatch to include arity boundaries.
- Improves confidence that the new arity witnesses are modeling live behavior, not only internal constructor structure.

### 2026-02-22: WP7.3 decimal annotation boundary re-check (post decision/iff lemmas)

**Context**: After extending `DecimalParity` with `decimal_unify_decision` and
`decimal_unify_ok_iff_constructor_beq_true`, re-validated decimal annotation and
mismatch behavior through MCP.

**MCP tools used**: `diagnose`, `type_check`

**Predict (Lean side)**:
- Decimal identity annotation should type-check as `(Decimal) -> Decimal`.
- Decimal-to-Int return annotation should reject with a type mismatch.

**Probe (Rust side via MCP)**:
1. Decimal identity:
   - `diagnose "fn decimal_id(x: Decimal) -> Decimal { x }"` -> no diagnostics.
   - `type_check ...` -> `(Decimal) -> Decimal`.
2. Decimal mismatch boundary:
   - `diagnose "fn decimal_to_int(x: Decimal) -> Int { x }"` ->
     `type_mismatch` (`declared Int`, value `Decimal`).
   - `type_check ...` -> same mismatch diagnostics (status `error`).

**Classify**: Agreement.

**Outcome**: MCP behavior aligns with the constructor-level decimal decision
model and confirms that decimal annotations are now enforced as expected on the
implementation path.

**Impact**:
- Keeps WP7.3 evidence current after the strengthened decision/iff theorem slice.
- Supports treating decimal constructor parity as an aligned vertical slice while
  full dim-aware decomposition remains pending.

### 2026-02-22: WP7.7 wrapper annotation probe (`Task` / `Actor`) after normalized contracts

**Context**: After adding normalized wrapper reduction contracts
(`task_unify_reduces_to_inner_of_normalized`, `actor_unify_reduces_to_inner_of_normalized`,
`arc_unify_reduces_to_inner_of_normalized`), re-checked MCP annotation behavior on
the runtime wrapper surface.

**MCP tools used**: `diagnose`, `type_check`

**Predict (Lean side)**:
- Reflexive wrapper annotations should type-check.
- Cross-wrapper annotation mismatch should reject.

**Probe (Rust side via MCP)**:
1. Reflexive wrapper checks:
   - `diagnose "fn task_id(x: Task(Int)) -> Task(Int) { x }"` -> no diagnostics.
   - `type_check ...` -> `(Task(Int)) -> Task(Int)`.
   - `diagnose "fn actor_id(x: Actor(String)) -> Actor(String) { x }"` -> no diagnostics.
   - `type_check ...` -> `(Actor(String)) -> Actor(String)`.
2. Wrapper mismatch boundary:
   - `diagnose "fn task_to_arc(x: Task(Int)) -> Arc(Int) { x }"` ->
     `type_mismatch` (`declared Arc(Int)`, value `Task(Int)`).

**Classify**: Agreement.

**Outcome**: MCP confirms the wrapper annotation behavior expected by the
runtime-wrapper parity slice: same-wrapper reflexive acceptance and cross-wrapper
mismatch rejection.

**Impact**:
- Keeps WP7.7 wrapper evidence current after the normalized reduction-contract expansion.
- Reinforces that the formal wrapper slice tracks observed annotation-level behavior,
  independent of the still-open Dynamic policy design decision.

### 2026-02-22: WP7.6 existential annotation re-check after normalized contracts

**Context**: After extending `ExistentialParity` with normalized reduction/rejection
contracts (`existential_unify_reduces_to_assoc_of_normalized`,
`existential_unify_rejects_of_normalized`), re-validated existential annotation
behavior through MCP.

**MCP tools used**: `diagnose`, `type_check`

**Predict (Lean side)**:
- Reflexive existential annotations should type-check.
- Existential-to-concrete annotation boundary should reject.

**Probe (Rust side via MCP)**:
1. Reflexive existential check:
   - `diagnose "fn any_id(x: any Show) -> any Show { x }"` -> no diagnostics.
   - `type_check ...` -> `(any Show) -> any Show`.
2. Existential mismatch boundary:
   - `diagnose "fn any_to_int(x: any Show) -> Int { x }"` ->
     `type_mismatch` (`declared Int`, value `any Show`).

**Classify**: Agreement.

**Outcome**: MCP behavior remains aligned with the existential constructor parity
slice and with the strengthened normalized-contract theorem layer.

**Impact**:
- Keeps WP7.6 existential evidence current after the theorem-surface expansion.
- Strengthens confidence that existential constructor parity continues to track
  implementation annotation behavior.

### 2026-02-22: WP7.6 constructor-app annotation re-check after normalized app contracts

**Context**: After extending `HigherOrderConstructorParity` with normalized
`App`/`Constructor` branch contracts, re-validated constructor-application style
annotation behavior on the MCP surface via parameterized list annotations.

**MCP tools used**: `diagnose`, `type_check`

**Predict (Lean side)**:
- Reflexive parameterized constructor annotation should type-check.
- Element-type mismatch through constructor-app annotations should reject.

**Probe (Rust side via MCP)**:
1. Reflexive `List(Int)` annotation:
   - `diagnose "fn list_int_id(xs: List(Int)) -> List(Int) { xs }"` -> no diagnostics.
   - `type_check ...` -> `(List(Int)) -> List(Int)`.
2. Constructor-app mismatch boundary:
   - `diagnose "fn list_int_to_string(xs: List(Int)) -> List(String) { xs }"` ->
     `type_mismatch` (element `Int` vs declared `String` path).

**Classify**: Agreement.

**Outcome**: MCP behavior remains consistent with the constructor-app parity
slice and supports the new normalized app-branch contract layer.

**Impact**:
- Keeps WP7.6 constructor-app evidence current after theorem-surface expansion.
- Strengthens confidence that formal app-branch contracts are grounded in observed
  annotation-level behavior.

### 2026-02-22: WP7.2 precision annotation re-check after dim-kernel decision lemmas

**Context**: After extending `Rill/Dimensions.lean` with decision lemmas
(`unifyDim_of_beq_true`, `unifyDim_const_decision`), re-validated precision
annotation behavior on MCP.

**MCP tools used**: `diagnose`, `type_check`

**Predict (Lean side)**:
- Reflexive precision annotations (`Int32`) should type-check.
- Width-mismatch annotations (`Int32` to `Int64`) should reject.

**Probe (Rust side via MCP)**:
1. Reflexive precision check:
   - `diagnose "fn int32_id(x: Int32) -> Int32 { x }"` -> no diagnostics.
   - `type_check ...` -> `(Int32) -> Int32`.
2. Width mismatch boundary:
   - `diagnose "fn int32_to_int64(x: Int32) -> Int64 { x }"` ->
     `type_mismatch` (`declared Int64`, value `Int32`).

**Classify**: Agreement.

**Outcome**: MCP behavior remains aligned with the precision/dimension parity
surface and supports the strengthened dim-kernel decision layer.

**Impact**:
- Keeps WP7.2 evidence current after dim-kernel theorem expansion.
- Supports the new precision unification decision/iff theorem layer in `PrecisionLeafParity`.
- Tightens the bridge from dim-kernel proofs to observable precision annotation behavior.

### 2026-02-22: WP7.7 dynamic var-boundary probe after normalized var-path lemmas

**Context**: After adding `dynamic_unify_var_right_of_normalized` and
`dynamic_unify_var_left_of_normalized`, probed the annotation surface for a
generic parameter against a `Dynamic` return boundary.

**MCP tools used**: `diagnose`, `type_check`

**Predict (Lean side)**:
- Dynamic/var interactions should follow the var-binding path before the
  permissive Dynamic branch.
- A generic variable annotated to `Dynamic` may collapse to `Dynamic`.

**Probe (Rust side via MCP)**:
1. Required annotation policy check:
   - `diagnose "fn var_to_dynamic(y) -> Dynamic { y }"` ->
     `missing_annotation` (named function parameters must be annotated).
2. Annotated var-boundary probe:
   - `diagnose "fn var_to_dynamic(y: a) -> Dynamic { y }"` -> no diagnostics.
   - `type_check ...` -> `(Dynamic) -> Dynamic`.

**Classify**: Agreement.

**Outcome**: MCP behavior aligns with the formal dynamic-var path modeling:
the generic boundary collapses through Dynamic on this path, consistent with the
current permissive Dynamic policy.

**Impact**:
- Extends WP7.7 evidence beyond concrete-return absorption to var-boundary behavior.
- Makes the var-precedence aspect of the Dynamic boundary explicit in the
  formalization/implementation loop.

### 2026-02-22: WP7.4 shape surface re-check after dim-bridge expansion

**Context**: After extending `ShapeConstructorParity` with generalized
successor-fuel mismatch contracts and constant-dimension kernel-failure rejection
lemmas, re-ran MCP probes to keep the formal/runtime loop current.

**MCP tools used**: `diagnose`, `type_check`, `get_documentation`

**Predict (Lean side)**:
- Decimal boundary should enforce declared return types after the implementation
  fix.
- Shape constructor annotation surface may still lag the formal constructor model.

**Probe (Rust side via MCP)**:
1. Decimal strictness sanity check:
   - `diagnose "fn decimal_id(x: Decimal) -> Decimal { x }"` -> no diagnostics.
   - `type_check ...` -> `(Decimal) -> Decimal`.
   - `diagnose "fn decimal_to_float(x: Decimal) -> Float { x }"` ->
     `type_mismatch` (`declared Float`, value `Decimal`).
2. Shape annotation/doc surface:
   - `diagnose "fn fixed_id(x: FixedSizeList(Int, 4)) -> FixedSizeList(Int, 4) { x }"` ->
     `type_error` (integer literal not valid in type position for this annotation path).
   - `diagnose "fn tensor_id(x: Tensor(Int, [1, 2])) -> Tensor(Int, [1, 2]) { x }"` ->
     syntax errors around type annotation parsing.
   - `get_documentation "Tensor"` -> no documentation found.

**Classify**: Mixed (decimal agreement, shape-surface divergence retained).

**Outcome**: MCP confirms the decimal implementation fix is active (annotations
are now enforced), while shape constructor annotation/docs remain behind the
formal model, matching the current scoped WP7.4 divergence narrative.

**Impact**:
- Supports the new WP7.4 dim-bridge reject contracts with fresh runtime-loop
  evidence.
- Keeps the known `FixedSizeList`/`Tensor` surface gap explicit so it is not
  mistaken for formal/model drift.

### 2026-02-22: WP7.3 decimal dimension-equivalence probe after bridge iff theorem

**Context**: After adding decimal constant-dimension bridge rejection lemmas and
the equivalence theorem `decimal_unify_consts_ok_iff_dim_kernel_success`, re-ran
MCP probes to verify success/mismatch behavior across precision and scale paths.

**MCP tools used**: `diagnose`, `type_check`

**Predict (Lean side)**:
- Matching decimal dimensions should type-check.
- Precision mismatch should reject.
- Scale mismatch should reject.

**Probe (Rust side via MCP)**:
1. Matching dimensions:
   - `diagnose "fn dec_12_2_id(x: Decimal(12,2)) -> Decimal(12,2) { x }"` -> no diagnostics.
   - `type_check ...` -> `(Decimal(12, 2)) -> Decimal(12, 2)`.
2. Precision mismatch:
   - `diagnose "fn dec_12_2_to_10_2(x: Decimal(12,2)) -> Decimal(10,2) { x }"` ->
     `type_mismatch` (`dimension mismatch: expected 10, got 12`).
3. Scale mismatch:
   - `diagnose "fn dec_12_2_to_12_3(x: Decimal(12,2)) -> Decimal(12,3) { x }"` ->
     `type_mismatch` (`dimension mismatch: expected 3, got 2`).

**Classify**: Agreement.

**Outcome**: MCP behavior remains consistent with the strengthened decimal
bridge surface: success on matching constant dimensions and rejection when either
dimension component mismatches.

**Impact**:
- Backs the new decimal bridge equivalence theorem with direct runtime evidence.
- Confirms the decimal implementation fix remains intact while formal claims are
  tightened.

### 2026-02-22: WP7.7 dynamic-wrapper return-boundary probe

**Context**: After extending `RuntimeWrapperParity` with successor-fuel Dynamic
contracts and `Task(Int)` return-absorption witnesses, checked MCP behavior for
function return annotations across `Dynamic` and `Task(Int)`.

**MCP tools used**: `diagnose`, `type_check`

**Predict (Lean side)**:
- Under current permissive Dynamic policy, both `Dynamic -> Task(Int)` and
  `Task(Int) -> Dynamic` return annotation boundaries can collapse without a
  diagnostic.

**Probe (Rust side via MCP)**:
1. Dynamic-parameter to task-annotated return:
   - `diagnose "fn dyn_to_task(x: Dynamic) -> Task(Int) { x }"` -> no diagnostics.
   - `type_check ...` -> `(Dynamic) -> Dynamic`.
2. Task-parameter to dynamic-annotated return:
   - `diagnose "fn task_to_dyn(x: Task(Int)) -> Dynamic { x }"` -> no diagnostics.
   - `type_check ...` -> `(Task(Int)) -> Task(Int)`.

**Classify**: Agreement with current permissive model, but policy-significant.

**Outcome**: MCP confirms wrapper-level return-annotation collapse in both
directions at the Dynamic boundary. This matches the formal permissive slice but
remains a notable language-policy issue (`explicit-dynamic-boundaries.md`).

**Impact**:
- Grounds the new `Task(Int)` Dynamic absorption lemmas in observed behavior.
- Sharpens the recorded divergence/policy point: return annotations crossing
  Dynamic are currently non-binding unless explicit boundary semantics are added.

### 2026-02-22: WP7.7 grouped/tagged bare-annotation boundary probe

**Context**: After extending `GroupedTaggedParity` with successor-fuel key/tag
mismatch contracts, re-probed MCP to characterize current bare
`GroupedFrame`/`Tagged` annotation behavior.

**MCP tools used**: `diagnose`, `type_check`

**Predict (Lean side)**:
- Constructor-local mismatch contracts remain valid in the model.
- Bare runtime annotations may still collapse generically/concretely rather than
  preserving grouped/tagged wrappers.

**Probe (Rust side via MCP)**:
1. Bare reflexive annotations:
   - `diagnose "fn grouped_id(x: GroupedFrame) -> GroupedFrame { x }"` -> no diagnostics.
   - `type_check ...` -> `(a) -> a`.
   - `diagnose "fn tagged_id(x: Tagged) -> Tagged { x }"` -> no diagnostics.
   - `type_check ...` -> `(a) -> a`.
2. Bare-to-concrete return boundary:
   - `diagnose "fn grouped_to_int(x: GroupedFrame) -> Int { x }"` -> no diagnostics.
   - `type_check ...` -> `(Int) -> Int`.
   - `diagnose "fn tagged_to_int(x: Tagged) -> Int { x }"` -> no diagnostics.
   - `type_check ...` -> `(Int) -> Int`.

**Classify**: Boundary retained (partial divergence).

**Outcome**: MCP confirms grouped/tagged bare annotations are currently
non-binding in this surface path, collapsing to generic/concrete types without
diagnostics. This remains compatible with the constructor-local Lean slice but is
an implementation-surface policy gap.

**Impact**:
- Keeps WP7.7 grouped/tagged divergence explicit and current.
- Prevents overclaiming wrapper-annotation strictness in formal status summaries.

### 2026-02-22: WP7.7 post-restart re-check after explicit Dynamic boundary commit

**Context**: After restart against commit `a8758bb` (`explicit Dynamic boundaries +
expect_type + GroupedFrame/Tagged fix`), re-ran the prior divergence probes.

**MCP tools used**: `diagnose`, `type_check`

**Predict**:
- Dynamic-to-concrete narrowing should now reject with an explicit `expect_type`
  guidance diagnostic.
- Grouped/tagged annotation behavior should be re-validated (expected to improve,
  but uncertain).

**Probe**:
1. Dynamic narrowing boundary:
   - `diagnose "fn f(x: Dynamic) -> Int { x }"` ->
     `type_mismatch` (`cannot use Dynamic value as Int`) with `expect_type` suggestion.
   - `type_check ...` -> error (same diagnostic).
   - `diagnose "fn dyn_to_task(x: Dynamic) -> Task(Int) { x }"` ->
     `type_mismatch` (`cannot use Dynamic value as Task(Int)`) with `expect_type` suggestion.
2. Dynamic widening boundary:
   - `diagnose "fn task_to_dyn(x: Task(Int)) -> Dynamic { x }"` -> no diagnostics.
   - `type_check ...` -> `(Task(Int)) -> Task(Int)` (annotation accepted but inferred concretely).
3. Grouped/tagged annotation surface:
   - `type_check "fn grouped_id(x: GroupedFrame) -> GroupedFrame { x }"` -> `(a) -> a`.
   - `type_check "fn grouped_to_int(x: GroupedFrame(Int)) -> Int { x }"` -> `(Int) -> Int`.
   - `type_check "fn tagged_param_id(x: Tagged(Int)) -> Tagged(Int) { x }"` -> `(a) -> a`.
   - `type_check "fn tagged_to_int(x: Tagged(Int)) -> Int { x }"` -> `(Int) -> Int`.

**Classify**: Mixed.

**Outcome**:
- Dynamic narrowing divergence is closed: explicit-boundary diagnostics now fire.
- Grouped/tagged annotation collapse remains (bare and applied forms in this path),
  so that divergence is still open.

**Impact**:
- Confirms the key Dynamic-boundary fix shipped and is visible via MCP.
- Identifies remaining grouped/tagged annotation-path gap for follow-up parity work.

### 2026-02-22: WP7.7 rebuilt-MCP re-check (post `resolve_annotation_or_bare_df` patch)

**Context**: After MCP rebuild/restart and the follow-up annotation-resolution patch
for `resolve_annotation_or_bare_df`, re-ran the same divergence probes.

**MCP tools used**: `diagnose`, `type_check`

**Probe**:
1. Dynamic explicit-boundary behavior:
   - `diagnose/type_check "fn f(x: Dynamic) -> Int { x }"` ->
     `type_mismatch` (`cannot use Dynamic value as Int`) with `expect_type` guidance.
   - `type_check "fn dyn_to_task(x: Dynamic) -> Task(Int) { x }"` ->
     `type_mismatch` (`cannot use Dynamic value as Task(Int)`).
2. GroupedFrame applied annotations:
   - `type_check "fn grouped_param_id(x: GroupedFrame(Int)) -> GroupedFrame(Int) { x }"` ->
     `(GroupedFrame(Int, keys: [])) -> GroupedFrame(Int, keys: [])`.
   - `type_check "fn grouped_to_int(x: GroupedFrame(Int)) -> Int { x }"` ->
     mismatch diagnostic (declared `Int`, value `GroupedFrame(Int, keys: [])`).
3. Tagged annotations:
   - `type_check "fn tagged_param_id(x: Tagged(Int)) -> Tagged(Int) { x }"` ->
     `(Int) -> Int` (display flattens empty-tag `Tagged` to inner type).
   - `type_check "fn tagged_to_int(x: Tagged(Int)) -> Int { x }"` ->
     mismatch diagnostic (message text currently shows `Int` on both sides due display flattening).
4. Bare grouped/tagged remain permissive:
   - `type_check "fn grouped_id(x: GroupedFrame) -> GroupedFrame { x }"` -> `(a) -> a`.
   - `type_check "fn grouped_to_int_bare(x: GroupedFrame) -> Int { x }"` -> `(Int) -> Int`.
   - Same collapse for bare `Tagged`.

**Classify**: Mixed (major closure + residual boundary).

**Outcome**:
- Dynamic narrowing divergence is closed.
- Applied GroupedFrame annotation path is closed.
- Bare GroupedFrame/Tagged collapse remains open; Tagged diagnostics are also obscured by
  empty-tag display flattening.

**Impact**:
- Confirms the explicit Dynamic boundary implementation now matches the intended policy.
- Narrows the remaining runtime/formal loop gap to grouped/tagged bare-annotation handling
  and Tagged display/diagnostic clarity.

### 2026-02-22: WP7.7 tagged-fix rebuild confirmation (bare grouped/tagged semantics)

**Context**: After a fresh rebuild/restart with the follow-up Tagged annotation fix,
re-checked grouped/tagged annotation behavior to decide whether bare-form collapse
is a true divergence or expected surface syntax.

**MCP tools used**: `diagnose`, `type_check`

**Probe**:
1. Applied grouped/tagged annotations:
   - `diagnose "fn tagged_to_int(x: Tagged(Int)) -> Int { x }"` ->
     mismatch (`declared Int`, `value Tagged(Int)`).
   - `type_check "fn tagged_int_id(x: Tagged(Int)) -> Tagged(Int) { x }"` ->
     `(Tagged(Int)) -> Tagged(Int)`.
   - `diagnose "fn grouped_to_int(x: GroupedFrame(Int)) -> Int { x }"` ->
     mismatch (`declared Int`, `value GroupedFrame(Int, keys: [])`).
   - `type_check "fn grouped_param_id(x: GroupedFrame(Int)) -> GroupedFrame(Int) { x }"` ->
     `(GroupedFrame(Int, keys: [])) -> GroupedFrame(Int, keys: [])`.
2. Bare grouped/tagged annotations:
   - `type_check "fn grouped_bare_id(x: GroupedFrame) -> GroupedFrame { x }"` -> `(a) -> a`.
   - `type_check "fn tagged_bare_id(x: Tagged) -> Tagged { x }"` -> `(a) -> a`.

**Classify**: Agreement (with implementation-surface intent).

**Outcome**:
- Tagged applied-annotation mismatch/preservation behavior is now correct and explicit.
- Bare `GroupedFrame`/`Tagged` collapse is retained, but this is expected: these
  forms have no meaningful schema/metadata parameter and are treated like other
  bare generic-like annotation forms in this path.

**Impact**:
- Closes the grouped/tagged divergence item opened by earlier probe passes.
- Leaves Dynamic narrowing policy realignment as the primary remaining WP7.7
  model-vs-implementation boundary task.

### 2026-02-22: Nominal-boundary fix verification (post `1e7f479`)

**Context**: User reported the record nominal-boundary fix was implemented and MCP
rebuilt/restarted. Verified the latest commit and re-ran boundary probes.

**MCP tools used**: `reset_session`, `type_check`, `diagnose`

**Probe**:
1. Commit sanity:
   - `git log -1` -> `1e7f479 fix: enforce nominal record boundaries at type-check sites`
   - touched `crates/rill-infer/src/typeck.rs` + `crates/rill-infer/src/typeck_tests.rs`
2. Indirection rejection (previous loophole):
   - register `record User { name: String, age: Int }`
   - `diagnose` on:
     ```rill
     {
       let tmp = #{ name: "Alice", age: 30 }
       let u: User = tmp
       u
     }
     ```
     -> `type_mismatch`: expected `User`, got anonymous record; actionable `User { ... }` guidance.
3. Call-boundary rejection:
   - `type_check "fn takes_user(u: User) -> String { u.name }"` -> ok
   - `diagnose "takes_user(#{ name: \"Alice\", age: 30 })"` -> same anonymous-record mismatch.
4. Positive control:
   - `diagnose "takes_user(User { name: \"Alice\", age: 30 })"` -> no diagnostics.
   - `diagnose "{ let u = User { name: \"Alice\", age: 30 } ; u.name }"` -> no diagnostics.

**Classify**: Agreement.

**Outcome**:
- Structural->nominal flow is now rejected at type-check boundaries, including
  indirection and function-call sites.
- Explicit nominal construction path remains accepted.

**Impact**:
- Closes the nominal-boundary divergence tracked in the brief.
- Confirms formal direction: keep unifier permissive, enforce directional policy
  at assignability boundaries.

### 2026-02-22: WP7.7 wrapper-inner parity re-check (Task/Actor/Arc)

**Context**: Added any-fuel wrapper-inner propagation theorems in `RuntimeWrapperParity`
for `Task`/`Actor`/`Arc` and re-validated runtime surface behavior via MCP.

**MCP tools used**: `reset_session`, `diagnose`, `type_check`

**Probe**:
1. Positive identity annotations:
   - `type_check "fn task_id(x: Task(Int)) -> Task(Int) { x }"` -> `(Task(Int)) -> Task(Int)`.
   - `type_check "fn actor_id(x: Actor(Int)) -> Actor(Int) { x }"` -> `(Actor(Int)) -> Actor(Int)`.
   - `type_check "fn arc_id(x: Arc(Int)) -> Arc(Int) { x }"` -> `(Arc(Int)) -> Arc(Int)`.
2. Negative inner mismatch at annotation boundary:
   - `diagnose "fn task_to_bool(x: Task(Int)) -> Bool { x }"` -> `type_mismatch` (`declared Bool`, value `Task(Int)`).
   - `diagnose "fn actor_to_bool(x: Actor(Int)) -> Bool { x }"` -> `type_mismatch` (`declared Bool`, value `Actor(Int)`).
   - `diagnose "fn arc_to_bool(x: Arc(Int)) -> Bool { x }"` -> `type_mismatch` (`declared Bool`, value `Arc(Int)`).

**Classify**: Agreement.

**Outcome**:
- Wrapper-preserving annotations for `Task`/`Actor`/`Arc` succeed as expected.
- Wrapper-to-concrete annotation mismatch remains explicitly rejected.

**Impact**:
- Confirms runtime behavior aligned with the new `RuntimeWrapperParity` any-fuel
  inner-branch success/error propagation slice.

### 2026-02-22: WP7.5 nominal arity parity re-check (Sum/Opaque)

**Context**: Added any-fuel arity-mismatch propagation lemmas for normalized
`Sum`/`Opaque` branches in `NominalAdtParity` and re-validated annotation/arity
surface behavior via MCP.

**MCP tools used**: `reset_session`, `type_check`, `diagnose`

**Probe**:
1. Sum constructor arity behavior:
   - `type_check "type Shape = Circle(Int)"` -> type registered.
   - `diagnose "Circle(1)"` -> no diagnostics.
   - `diagnose "Circle(1, 2)"` -> `arity_mismatch` (`Circle` expects 1 argument, got 2).
2. Opaque nominal boundary behavior:
   - `type_check "opaque UserId = Int"` -> opaque registered.
   - `type_check "fn user_id(x: UserId) -> UserId { x }"` -> `(UserId) -> UserId`.
   - `diagnose "fn user_to_int(x: UserId) -> Int { x }"` -> `type_mismatch`
     (`declared Int`, value `UserId`).

**Classify**: Agreement.

**Outcome**:
- Sum constructor arity checking remains explicit and stable.
- Opaque nominal boundary remains directional (`UserId` does not collapse to `Int`).

**Impact**:
- Confirms runtime behavior still matches the strengthened nominal ADT
  arity-propagation theorem slice.

### 2026-02-22: WP7.7 grouped/tagged mismatch generalization probe

**Context**: Added arbitrary-inner successor-fuel mismatch theorems in
`GroupedTaggedParity`:
`groupedFrame_keys_mismatch_any_inner_any_fuel` and
`tagged_metadata_mismatch_any_inner_any_fuel`.

**MCP tools used**: `reset_session`, `diagnose`, `type_check`

**Probe**:
1. Grouped key-parameterized annotation syntax exposure:
   - `diagnose "fn grouped_key_id(x: GroupedFrame(Int, keys: [\"a\"])) -> GroupedFrame(Int, keys: [\"a\"]) { x }"`
     -> syntax error (`expected ')' in type application`).
   - `diagnose "fn grouped_key_mismatch(x: GroupedFrame(Int, keys: [\"a\"])) -> GroupedFrame(Int, keys: [\"b\"]) { x }"`
     -> same syntax-path error.
2. Grouped wrapper behavior on currently supported applied form:
   - `diagnose "fn grouped_id(x: GroupedFrame(Int)) -> GroupedFrame(Int) { x }"` -> no diagnostics.
   - `type_check "fn grouped_id(x: GroupedFrame(Int)) -> GroupedFrame(Int) { x }"`
     -> `(GroupedFrame(Int, keys: [])) -> GroupedFrame(Int, keys: [])`.
   - `diagnose "fn grouped_to_int(x: GroupedFrame(Int)) -> Int { x }"`
     -> `type_mismatch` (`declared Int`, value `GroupedFrame(Int, keys: [])`).
3. Tagged wrapper boundary behavior:
   - `diagnose "fn tagged_id(x: Tagged(Int)) -> Tagged(Int) { x }"` -> no diagnostics.
   - `diagnose "fn tagged_to_int(x: Tagged(Int)) -> Int { x }"`
     -> `type_mismatch` (`declared Int`, value `Tagged(Int)`).

**Classify**: Mixed (surface-syntax gap + semantic agreement on exposed forms).

**Outcome**:
- Constructor-internal grouped key/metadata-parameter annotation syntax is not
  yet exposed in this parser path (`keys: [...]` parse failure).
- Exposed grouped/tagged wrapper behavior remains consistent (wrapper-preserving
  annotations succeed, wrapper-to-concrete mismatches reject).

**Impact**:
- Supports keeping key/metadata mismatch generalization as Lean-level parity
  coverage now, with direct surface probes to be expanded when keyed metadata
  annotation syntax becomes available.

### 2026-02-22: WP7.7 Dynamic boundary widening/closure re-check

**Context**: Added Dynamic boundary closure/widening alignment lemmas in
`RuntimeWrapperParity`:
- `dynamic_boundary_closes_unifier_absorption_bool_all_sites`
- `dynamic_boundary_allows_unifier_widening_int_all_sites`
- `dynamic_boundary_allows_unifier_widening_task_all_sites`

**MCP tools used**: `reset_session`, `diagnose`, `type_check`

**Probe**:
1. Dynamic narrowing remains rejected:
   - `diagnose "fn dyn_to_bool(x: Dynamic) -> Bool { x }"`
     -> `type_mismatch` (`cannot use Dynamic value as Bool`) with `expect_type` guidance.
   - `diagnose "fn dyn_to_task(x: Dynamic) -> Task(Int) { x }"`
     -> `type_mismatch` (`cannot use Dynamic value as Task(Int)`) with `expect_type` guidance.
2. Concrete->Dynamic widening remains accepted:
   - `diagnose "fn bool_to_dyn(x: Bool) -> Dynamic { x }"` -> no diagnostics.
   - `diagnose "fn int_to_dyn(x: Int) -> Dynamic { x }"` -> no diagnostics.
   - `diagnose "fn task_to_dyn(x: Task(Int)) -> Dynamic { x }"` -> no diagnostics.
3. Type-check display behavior on widening path:
   - `type_check "fn bool_to_dyn(x: Bool) -> Dynamic { x }"` -> `(Bool) -> Bool`.
   - `type_check "fn int_to_dyn(x: Int) -> Dynamic { x }"` -> `(Int) -> Int`.
   - `type_check "fn task_to_dyn(x: Task(Int)) -> Dynamic { x }"` -> `(Task(Int)) -> Task(Int)`.

**Classify**: Agreement.

**Outcome**:
- Explicit narrowing rejection and widening acceptance remain stable.
- The known type-check display normalization for widening annotations persists
  (diagnostics + acceptance behavior are still consistent with boundary policy).

**Impact**:
- Confirms runtime behavior aligns with the new all-sites Dynamic closure and
  widening-alignment theorem slice.

### 2026-02-23: WP7.6 constructor-arity divergence closure re-check

**Context**: After runtime fix commit `ec504de` (`reject wrong-arity built-in type constructors in annotations`), re-ran the exact constructor-arity probes that previously collapsed silently.

**MCP tools used**: `reset_session`, `diagnose`, `type_check`

**Probe**:
1. Previous divergence reproductions:
   - `diagnose "fn list_arity_mismatch(x: List(Int)) -> List(Int, Int) { x }"`
     -> `arity_mismatch` (`type List expects 1 type argument but got 2`).
   - `type_check` same snippet -> status `error` with same `arity_mismatch`.
   - `diagnose "fn map_arity_missing(x: Map(Int, Int)) -> Map(Int) { x }"`
     -> `arity_mismatch` (`type Map expects 2 type arguments but got 1`).
   - `type_check` same snippet -> status `error` with same `arity_mismatch`.
   - `diagnose "fn map_arity_extra(x: Map(Int, Int)) -> Map(Int, Int, Int) { x }"`
     -> `arity_mismatch` (`type Map expects 2 type arguments but got 3`).
   - `type_check` same snippet -> status `error` with same `arity_mismatch`.
2. Control probe (constructor-name mismatch still rejects):
   - `diagnose "fn list_to_map(x: List(Int)) -> Map(Int, Int) { x }"`
     -> `type_mismatch` (`declared Map(Int, Int), value List(Int)`).

**Classify**: Agreement (divergence closed).

**Outcome**:
- Built-in constructor wrong-arity annotations now fail explicitly instead of
  being silently normalized.
- Constructor mismatch diagnostics remain intact on non-arity paths.

**Impact**:
- Closes the previously tracked WP7.6 runtime/formal divergence around
  constructor arity absorption in annotation positions.

### 2026-02-23: WP7.4 shape annotation surface re-check after restart

**Context**: After adding explicit any-fuel inner-branch propagation lemmas in
`ShapeConstructorParity`:
- `fixedSizeList_inner_error_propagates_any_fuel`
- `fixedSizeList_inner_success_propagates_any_fuel`
- `tensor_inner_error_propagates_any_fuel`
- `tensor_inner_success_propagates_any_fuel`

re-ran the shape-annotation probes on the rebuilt/restarted MCP runtime.

**MCP tools used**: `reset_session`, `diagnose`, `type_check`

**Probe**:
1. Fixed-size-list annotation path:
   - `diagnose "fn fsl_id(x: FixedSizeList(Int, 4)) -> FixedSizeList(Int, 4) { x }"`
     -> `E0012` (`integer literal \`4\` is not valid as a type...`) on both
     parameter and return annotations.
   - `type_check` same snippet -> status `error` with same `E0012` diagnostics.
   - `diagnose "fn fsl_to_int(x: FixedSizeList(Int, 4)) -> Int { x }"`
     -> `E0012` on the parameter annotation.
   - `type_check` same snippet -> status `error` with same `E0012`.
2. Tensor annotation path:
   - `diagnose "fn tensor_id(x: Tensor(Int, [2, 3])) -> Tensor(Int, [2, 3]) { x }"`
     -> syntax diagnostics (`expected type annotation`) in the annotation parse path.
   - `type_check` same snippet -> status `error` with same syntax diagnostics.
   - `diagnose "fn tensor_to_int(x: Tensor(Int, [2, 3])) -> Int { x }"`
     -> syntax diagnostics (`expected type annotation`) on the parameter annotation.
   - `type_check` same snippet -> status `error` with same syntax diagnostics.

**Classify**: Divergence persists (known surface-syntax gap).

**Outcome**:
- Lean constructor-level WP7.4 parity remains ahead of the current exposed
  annotation surface for shape metadata syntax.
- Runtime still rejects `FixedSizeList(..., const)` integer metadata in type
  positions (outside decimal-style dimension parsing) and still lacks the
  `Tensor(..., [...])` annotation parse path.

**Impact**:
- Keeps WP7.4 scoped correctly: constructor-level unifier parity is proved,
  while shape annotation surface parity remains pending runtime syntax work.

### 2026-02-23: WP7.5 nominal probe hygiene re-check (declared vs undeclared names)

**Context**: While sanity-checking nominal boundaries after restart, verified
that probes must use declared nominal types (`opaque`/`type`) to avoid false
signals from unbound annotation names.

**MCP tools used**: `reset_session`, `type_check`, `diagnose`

**Probe**:
1. Undeclared nominal-looking names:
   - `type_check "fn user_id(x: UserId) -> UserId { x }"` -> `(a) -> a`.
   - `diagnose "fn user_to_int(x: UserId) -> Int { x }"` -> no diagnostics.
2. Declared opaque boundary:
   - `diagnose "opaque UserId = Int\nfn user_to_int(x: UserId) -> Int { x }"`
     -> `type_mismatch` (`declared Int`, value `UserId`).
   - `diagnose "opaque UserId = Int\nfn int_to_user(x: Int) -> UserId { x }"`
     -> `type_mismatch` (`declared UserId`, value `Int`).

**Classify**: Agreement (with probe-scope clarification).

**Outcome**:
- Declared nominal boundaries behave as expected.
- Unbound uppercase names are treated polymorphically in annotation position,
  so they are not valid nominal-boundary probes.

**Impact**:
- Prevents future false-positive divergence reports in WP7.5 by making probe
  preconditions explicit (declare nominal types before boundary checks).

### 2026-02-23: WP7.2 decimal dim-kernel spot-check after dim-list kernel expansion

**Context**: After extending `Rill/Dimensions.lean` with pointwise list-kernel
contracts (`unifyDimList_reflexive`, `unifyDimList_consts_some_iff_eq`), re-ran
a focused decimal annotation check to confirm runtime dimension behavior remains
stable.

**MCP tools used**: `reset_session`, `diagnose`, `type_check`

**Probe**:
1. Decimal reflexive annotation:
   - `diagnose "fn dec_id(x: Decimal(10, 2)) -> Decimal(10, 2) { x }"` -> no diagnostics.
   - `type_check` same snippet -> `(Decimal(10, 2)) -> Decimal(10, 2)`.
2. Decimal scale mismatch:
   - `diagnose "fn dec_mismatch(x: Decimal(10, 2)) -> Decimal(10, 3) { x }"`
     -> `type_mismatch` (`dimension mismatch: expected \`3\`, got \`2\``).
   - `type_check` same snippet -> status `error` with the same dimension mismatch.

**Classify**: Agreement.

**Outcome**:
- Runtime decimal dimension behavior remains unchanged and explicit.
- The new dim-list kernel lemmas strengthen formal dim reasoning without
  introducing runtime mismatch in currently exposed decimal surfaces.

**Impact**:
- Grounds the expanded WP7.2 dimension-kernel theorem surface with fresh MCP
  evidence on the live decimal annotation path.

### 2026-02-23: WP7.4 shape annotation surface spot-check (post arbitrary-inner lemma slice)

**Context**: After generalizing arbitrary-rank tensor constant-shape bridge
lemmas in `ShapeConstructorParity` to arbitrary shared inner element types,
re-ran a minimal MCP surface probe to confirm the runtime annotation gap remains
tracked as implementation-side scope (not a new formal divergence).

**MCP tools used**: `diagnose`

**Probe**:
1. Fixed-size-list annotation path:
   - `diagnose "fn takes_fixed(x: FixedSizeList(Int, 4)) -> Int { 0 }"`
     -> `E0012` (`integer literal \`4\` is not valid as a type...`).
2. Tensor annotation path:
   - `diagnose "fn takes_tensor(x: Tensor(Int, [2, 3])) -> Int { 0 }"`
     -> syntax diagnostics (`expected type annotation`) at the list-shape site.

**Classify**: Divergence persists (known WP7.4 annotation-surface gap).

**Outcome**:
- Runtime still rejects integer metadata for `FixedSizeList` type annotations.
- Runtime still lacks the list-shape annotation parse path for `Tensor`.
- No new divergence class observed; this is the already-tracked surface gap.

**Impact**:
- Confirms current formal progress is still constructor/unifier-level parity,
  with annotation-surface closure deferred to implementation briefs.

### 2026-02-24: WP7.4 annotation-surface re-check on latest MCP binary (expected model-ahead state)

**Context**: Re-checked the known shape-annotation surface gap after user-side MCP rebuild/restart.
This is still expected while formal WP7.4 tracks ahead of implementation.

**MCP tools used**: `reset_session`, `diagnose`, `type_check`

**Probe**:
1. `FixedSizeList` annotation path:
   - `diagnose "fn fsl_id(x: FixedSizeList(Int, 4)) -> FixedSizeList(Int, 4) { x }"`
     -> `E0012` (`integer literal \`4\` is not valid as a type...`) on both parameter and return.
   - `type_check` same snippet -> status `error` with same `E0012` diagnostics.
2. `Tensor` list-shape annotation path:
   - `diagnose "fn tensor_id(x: Tensor(Int, [2, 3])) -> Tensor(Int, [2, 3]) { x }"`
     -> syntax diagnostics (`expected type annotation`) in annotation parse path.
   - `type_check` same snippet -> status `error` with the same syntax diagnostics.

**Classify**: Expected divergence persists (formal model intentionally ahead on this surface).

**Outcome**:
- No new divergence class.
- Confirms unchanged implementation surface: `FixedSizeList(..., const)` annotation metadata and `Tensor(..., [..])` type-position list shapes remain unavailable.

**Impact**:
- Keeps WP7.4 split explicit:
  - constructor/unifier contracts continue advancing in Lean,
  - annotation surface closure remains pending implementation briefs.

### 2026-02-25: WP7.5 nominal mismatch-slice parity spot-check

**Context**: After landing packaged nominal mismatch slice theorems in
`NominalAdtParity` (name mismatch and arity mismatch bundles, plus normalized
name-inequality rejection conveniences), re-checked the corresponding runtime
surfaces through MCP diagnostics.

**MCP tools used**: `reset_session`, `diagnose`

**Probe**:
1. Opaque nominal boundary mismatch:
   - `diagnose "opaque UserId = Int\nfn int_to_user(x: Int) -> UserId { x }"`
     -> `type_mismatch` (`declared UserId`, value `Int`).
2. ADT constructor arity mismatch:
   - `diagnose "type Shape = Circle(Float) | Rect(Float, Float)\nfn bad() -> Shape { Circle(1.0, 2.0) }"`
     -> `arity_mismatch` (`Circle` expects 1 argument, got 2).
3. Distinct nominal ADT mismatch:
   - `diagnose "type A = Mk(Int)\ntype B = Mk(Int)\nfn bad(x: A) -> B { x }"`
     -> `type_mismatch` (`declared B`, value `A`).
4. Reflexive nominal annotation sanity check:
   - `diagnose "type A = Mk(Int)\nfn id(x: A) -> A { x }"`
     -> no diagnostics.

**Classify**: Agreement.

**Outcome**:
- Runtime diagnostics align with nominal mismatch contracts captured in Lean.
- No new divergence class observed on nominal-name/arity surfaces.

**Impact**:
- Grounds the new WP7.5 mismatch packaging theorems with fresh MCP evidence on
  live ADT/opaque annotation and constructor-arity paths.

### 2026-02-25: Record nominal-boundary site-directionality spot-check

**Context**: After extending `RecordStructuralProjection` with site-level directional policy packaging (`record_boundary_allows_named_to_structural_all_sites`, `record_boundary_directional_policy_all_sites`, `record_nominal_boundary_closes_unifier_symmetry_all_sites`), re-checked exposed runtime nominal-boundary behavior on return/call paths.

**MCP tools used**: `diagnose`

**Probe**:
1. Return boundary (structural -> nominal) rejects:
   - `diagnose "record User { name: String }\nfn from_struct() -> User { #{ name: \"a\" } }"`
     -> `type_mismatch` (`expected User, got anonymous record. Use \`User { ... }\` to construct a User`).
2. Call boundary (structural argument -> nominal parameter) rejects:
   - `diagnose "record User { name: String }\nfn needs_user(u: User) -> Int { 1 }\nfn run_call() -> Int { needs_user(#{ name: \"a\" }) }"`
     -> `type_mismatch` (`expected User, got anonymous record. Use \`User { ... }\` to construct a User`).
3. Nominal construction control (named constructor -> nominal return) accepts:
   - `diagnose "record User { name: String }\nfn from_named() -> User { User { name: \"a\" } }"`
     -> no diagnostics.

**Classify**: Agreement.

**Outcome**:
- Runtime enforces structural-to-nominal rejection at return and call boundaries.
- Nominal construction with `User { ... }` remains accepted.
- Matches the directional policy encoded in `RecordStructuralProjection`.

**Impact**:
- Grounds the new site-directional nominal-boundary theorem package with fresh MCP evidence on exposed runtime sites.

### 2026-02-25: WP7.6 forall canonical-closure spot-check

**Context**: After extending `ForallParity` with canonical-equivalence closure/unification packaging (`forallCanonicalEq_unifies_symm`, `forallCanonicalEq_unifies_trans`, `forall_canonical_equivalence_slice`), re-checked runtime behavior for alpha-renamed binders, vacuous binder compatibility, and quantified-body mismatch.

**MCP tools used**: `diagnose`

**Probe**:
1. Alpha-renamed binder compatibility:
   - `diagnose "fn take_alpha(f: forall a. fn(a) -> a) -> Int { 0 }\nfn pass_alpha(g: forall b. fn(b) -> b) -> Int { take_alpha(g) }"`
     -> no diagnostics.
2. Vacuous-binder compatibility:
   - `diagnose "fn take_vacuous(f: forall a, b. fn(a) -> a) -> Int { 0 }\nfn pass_vacuous(g: forall c. fn(c) -> c) -> Int { take_vacuous(g) }"`
     -> no diagnostics.
3. Quantified-body mismatch rejection:
   - `diagnose "fn take_id(f: forall a. fn(a) -> a) -> Int { 0 }\nfn pass_bad(g: forall b. fn(b) -> Int) -> Int { take_id(g) }"`
     -> `type_mismatch` (`argument 1 is not polymorphic enough: expected \`forall a. (a) -> a\``).

**Classify**: Agreement.

**Outcome**:
- Runtime accepts alpha-equivalent and vacuous-binder-compatible quantified values.
- Runtime still rejects non-equivalent quantified body shapes at call boundaries.
- Matches the canonical-equivalence closure and rejection surfaces encoded in `ForallParity`.

**Impact**:
- Grounds the new WP7.6 canonical-equivalence closure theorem slice with fresh MCP evidence on live rank-2 call-site behavior.

### 2026-02-25: WP7.6 constructor-guard mismatch suite spot-check

**Context**: After adding `constructor_guard_mismatch_suite_any_fuel` in
`HigherOrderConstructorParity`, re-checked exposed constructor-guard mismatch
surfaces on built-in constructor annotations.

**MCP tools used**: `diagnose`

**Probe**:
1. Constructor-name mismatch (`List` vs `Map`):
   - `diagnose "fn list_to_map(x: List(Int)) -> Map(Int, Int) { x }"`
     -> `type_mismatch` (`declared Map(Int, Int), value List(Int)`).
2. Constructor-arity mismatch (`Map` expects 2 args):
   - `diagnose "fn map_arity_missing(x: Map(Int, Int)) -> Map(Int) { x }"`
     -> `arity_mismatch` (`type Map expects 2 type arguments but got 1`).
3. Control (`List` reflexive) accepts:
   - `diagnose "fn list_id(x: List(Int)) -> List(Int) { x }"`
     -> no diagnostics.

**Classify**: Agreement.

**Outcome**:
- Runtime rejects constructor-name and constructor-arity guard mismatches on the
  exposed annotation path.
- Matching constructor guards remain accepted.
- Aligns with the new packaged constructor/app guard-mismatch theorem suite.

**Impact**:
- Grounds the WP7.6 guard-mismatch packaging theorem with fresh runtime evidence
  on exposed constructor-surface diagnostics.

### 2026-02-25: WP7.5 normalized nominal branch-decision slice spot-check

**Context**: After adding `nominal_adt_unify_branch_decision_slice_of_normalized`
in `NominalAdtParity`, re-checked runtime nominal decision behavior across `Sum`
and `Opaque` mismatch/accept paths.

**MCP tools used**: `diagnose`

**Probe**:
1. Distinct nominal ADT mismatch (`A` vs `B`) rejects:
   - `diagnose "type A = Mk(Int)\ntype B = Mk(Int)\nfn bad(x: A) -> B { x }"`
     -> `type_mismatch` (`declared B`, value A).
2. Opaque nominal mismatch (`Int` -> `UserId`) rejects:
   - `diagnose "opaque UserId = Int\nfn int_to_user(x: Int) -> UserId { x }"`
     -> `type_mismatch` (`declared UserId`, value Int).
3. Reflexive ADT control accepts:
   - `diagnose "type A = Mk(Int)\nfn id(x: A) -> A { x }"`
     -> no diagnostics.

**Classify**: Agreement.

**Outcome**:
- Runtime maintains nominal-name gating for both ADT and opaque annotations.
- Reflexive nominal cases remain accepted.
- Aligns with the cross-constructor normalized branch-decision slice in Lean.

**Impact**:
- Grounds the new WP7.5 normalized branch-decision packaging theorem with fresh
  runtime evidence on nominal mismatch/accept surfaces.

### 2026-02-25: WP7.6 forall surface-boundary package spot-check

**Context**: After adding `forall_surface_boundary_slice` in `ForallParity`,
ran a combined rank-2 surface probe covering alpha-renaming acceptance,
vacuous-binder acceptance, and quantified-body mismatch rejection.

**MCP tools used**: `diagnose`

**Probe**:
- `diagnose` with combined declarations:
  - `take_alpha/pass_alpha` (`forall a. fn(a)->a` expected, `forall b. fn(b)->b` passed)
  - `take_vacuous/pass_vacuous` (`forall a,b. fn(a)->a` expected, `forall c. fn(c)->c` passed)
  - `take_id/pass_bad` (`forall a. fn(a)->a` expected, `forall b. fn(b)->Int` passed)
- Result:
  - Alpha-renaming and vacuous-binder cases accepted.
  - Body-mismatch case rejected with `type_mismatch` (`argument 1 is not polymorphic enough: expected \`forall a. (a) -> a\``).

**Classify**: Agreement.

**Outcome**:
- Runtime behavior matches the new packaged concrete surface theorem:
  alpha/vacuous compatibility acceptance and quantified-body mismatch rejection.

**Impact**:
- Grounds `forall_surface_boundary_slice` with a single combined live MCP probe.

### 2026-02-25: WP7.6 constructor-guard surface slice spot-check

**Context**: After adding `constructor_guard_surface_slice` in
`HigherOrderConstructorParity`, re-ran a combined List/Map surface probe to
cover name mismatch rejection, arity mismatch rejection, and matching control.

**MCP tools used**: `diagnose`

**Probe**:
- `diagnose "fn list_to_map(x: List(Int)) -> Map(Int, Int) { x }\nfn map_arity_missing(x: Map(Int, Int)) -> Map(Int) { x }\nfn list_id(x: List(Int)) -> List(Int) { x }"`
- Result:
  - `list_to_map` rejects with `type_mismatch` (`declared Map(Int, Int), value List(Int)`).
  - `map_arity_missing` rejects with `arity_mismatch` (`Map` expects 2 type arguments, got 1).
  - `list_id` contributes no diagnostics (matching constructor control).

**Classify**: Agreement.

**Outcome**:
- Runtime surface behavior matches the packaged concrete constructor-guard
  theorem slice (name mismatch reject, arity mismatch reject, matching control).

**Impact**:
- Grounds `constructor_guard_surface_slice` with a single combined MCP probe on
  exposed constructor annotation diagnostics.

### 2026-02-25: WP7.6 explicit forall boundary-policy spot-check

**Context**: After adding an explicit higher-rank boundary layer in
`ForallParity` (`ForallBoundarySite`, `forallBoundaryAllowsAtSite`,
`forall_boundary_surface_slice`), re-ran a combined rank-2 probe including
alpha/vacuous acceptance, quantified-body mismatch rejection, and non-`forall`
argument rejection.

**MCP tools used**: `diagnose`

**Probe**:
- Combined declarations:
  - `take_alpha/pass_alpha` (alpha-renamed binder argument)
  - `take_vacuous/pass_vacuous` (vacuous-binder-compatible argument)
  - `take_id/pass_bad` (`forall b. fn(b)->Int` passed to `forall a. fn(a)->a`)
  - `mono/pass_nonforall` (monomorphic `Int -> Int` passed to `forall` parameter)
- Result:
  - Alpha/vacuous compatibility cases accepted (no diagnostics on those declarations).
  - Both mismatch cases reject with `type_mismatch`:
    `argument 1 is not polymorphic enough: expected \`forall a. (a) -> a\``.

**Classify**: Agreement.

**Outcome**:
- Runtime behavior matches the explicit site-level `forall` boundary policy:
  compatible quantified arguments accepted, non-equivalent or non-quantified
  arguments rejected at call boundaries.

**Impact**:
- Provides a vertical WP7.6 bridge artifact tying constructor-level `forall`
  unification behavior to boundary-sensitive call-site policy semantics.

### 2026-02-25: WP7.5 explicit nominal ADT boundary-policy spot-check

**Context**: After adding explicit nominal ADT boundary-policy artifacts in
`NominalAdtParity` (`NominalAdtBoundarySite`, `nominalAdtBoundaryAllowsAtSite`,
`nominal_adt_boundary_surface_slice`), re-ran a combined nominal/non-nominal
surface probe.

**MCP tools used**: `diagnose`

**Probe**:
- Combined declarations:
  - `type A = Mk(Int)`, `type B = Mk(Int)`, `sum_bad(x: A) -> B { x }`
  - `opaque UserId = Int`, `opaque OrderId = Int`,
    `opaque_bad(x: UserId) -> OrderId { x }`
  - `expect_a(x: A) -> Int`, `pass_int(x: Int) -> Int { expect_a(x) }`
  - `sum_id(x: A) -> A { x }` (control)
- Result:
  - `sum_bad` rejects (`declared B`, value A).
  - `opaque_bad` rejects (`declared OrderId`, value UserId).
  - `pass_int` rejects (`expected A, got Int`).
  - `sum_id` contributes no diagnostics (matching nominal control).

**Classify**: Agreement.

**Outcome**:
- Runtime matches explicit nominal boundary policy behavior for ADT/opaque
  name mismatch and non-nominal-to-nominal rejection at boundary-sensitive
  call/return paths.

**Impact**:
- Provides a vertical WP7.5 boundary-policy bridge above constructor-level
  unification parity, aligned with live nominal diagnostics.

### 2026-02-25: WP7.6 explicit constructor-guard boundary-policy spot-check

**Context**: After adding explicit constructor-head boundary artifacts in
`HigherOrderConstructorParity` (`ConstructorGuardBoundarySite`,
`constructorGuardBoundaryAllowsAtSite`,
`constructor_guard_boundary_surface_slice`), re-ran a combined constructor
surface probe.

**MCP tools used**: `diagnose`

**Probe**:
- Combined declarations:
  - `list_to_map` (`List(Int)` returned as `Map(Int, Int)`)
  - `map_arity_missing` (`Map(Int)` arity mismatch)
  - `expect_list/pass_int` (`Int` passed where `List(Int)` expected)
  - `list_id` control
- Result:
  - `list_to_map` rejects (`declared Map(Int, Int), value List(Int)`).
  - `map_arity_missing` rejects (`Map` expects 2 type arguments, got 1).
  - `pass_int` rejects (`expected List(Int), got Int`).
  - `list_id` contributes no diagnostics.

**Classify**: Agreement.

**Outcome**:
- Runtime behavior matches explicit constructor-head boundary policy:
  name/arity/non-constructor mismatches reject, matching constructor control
  remains accepted.

**Impact**:
- Adds a vertical WP7.6 boundary-policy bridge for constructor-head guard
  behavior above constructor-level unifier parity.

### 2026-02-25: WP7.7 explicit grouped/tagged boundary-policy spot-check

**Context**: After adding explicit grouped/tagged boundary-policy artifacts in
`GroupedTaggedParity` (`GroupedTaggedBoundarySite`,
`groupedTaggedBoundaryAllowsAtSite`, `grouped_tagged_boundary_surface_slice`),
ran a combined grouped/tagged surface probe.

**MCP tools used**: `diagnose`

**Probe**:
- Combined declarations:
  - `grouped_inner_bad(x: GroupedFrame(Int)) -> GroupedFrame(Bool) { x }`
  - `tagged_inner_bad(x: Tagged(Int)) -> Tagged(Bool) { x }`
  - `grouped_from_int(x: Int) -> GroupedFrame(Int) { x }`
  - `tagged_from_int(x: Int) -> Tagged(Int) { x }`
  - `grouped_id` / `tagged_id` controls
- Result:
  - `grouped_inner_bad` rejects (`declared GroupedFrame(Bool, keys: [])`, value `GroupedFrame(Int, keys: [])`).
  - `tagged_inner_bad` rejects (`declared Bool`, value `Int` inside `Tagged`).
  - `grouped_from_int` rejects (`declared GroupedFrame(Int, keys: [])`, value `Int`).
  - `tagged_from_int` rejects (`declared Tagged(Int)`, value `Int`).
  - `grouped_id` / `tagged_id` contribute no diagnostics.

**Classify**: Agreement.

**Outcome**:
- Runtime behavior matches explicit grouped/tagged boundary policy surfaces:
  wrapper mismatch and non-wrapper-to-wrapper boundary rejection, with matching
  controls accepted.

**Impact**:
- Adds a vertical WP7.7 boundary-policy bridge for grouped/tagged wrappers above
  constructor-local unification parity.

### 2026-02-25: WP7.7 explicit Dynamic boundary-policy surface spot-check

**Context**: After adding packaged Dynamic boundary closure theorem
`dynamic_boundary_surface_slice` in `RuntimeWrapperParity`, re-ran explicit
Dynamic narrowing/widening probes.

**MCP tools used**: `diagnose`

**Probe**:
- Declarations:
  - `dyn_to_int(x: Dynamic) -> Int { x }`
  - `dyn_to_task_int(x: Dynamic) -> Task(Int) { x }`
  - `int_to_dyn(x: Int) -> Dynamic { x }`
  - `task_to_dyn(x: Task(Int)) -> Dynamic { x }`
- Result:
  - `dyn_to_int` rejects with `cannot use Dynamic value as Int`.
  - `dyn_to_task_int` rejects with `cannot use Dynamic value as Task(Int)`.
  - Both rejections carry `expect_type` guidance.
  - No diagnostics emitted for `int_to_dyn` or `task_to_dyn`.

**Classify**: Agreement.

**Outcome**:
- Runtime behavior matches explicit Dynamic boundary policy:
  Dynamic narrowing rejects at boundary sites, while concrete-to-Dynamic
  widening remains accepted.

**Impact**:
- Adds a vertical WP7.7 Dynamic boundary-policy package bridge tying concrete
  MCP surface behavior to the new packaged theorem.

### 2026-02-25: WP7.3 explicit decimal boundary-policy surface spot-check

**Context**: After adding explicit decimal boundary-policy artifacts in
`DecimalParity` (`DecimalBoundarySite`, `decimalBoundaryAllowsAtSite`,
`decimal_boundary_surface_slice`), ran a decimal surface probe covering
scale-mismatch and non-decimal boundary rejection.

**MCP tools used**: `diagnose`

**Probe**:
- Combined declarations:
  - `dec_scale_bad(x: Decimal(10, 2)) -> Decimal(10, 3) { x }`
  - `dec_from_int(x: Int) -> Decimal(10, 2) { x }`
  - `dec_id(x: Decimal(10, 2)) -> Decimal(10, 2) { x }`
- Result:
  - `dec_scale_bad` rejects with `dimension mismatch: expected 3, got 2`.
  - `dec_from_int` rejects with
    `type annotation mismatch: declared Decimal(10, 2), but value has type Int`.
  - `dec_id` contributes no diagnostics.

**Classify**: Agreement.

**Outcome**:
- Runtime behavior matches explicit decimal boundary policy:
  decimal metadata mismatch and non-decimal-to-decimal boundary rejection,
  with matching decimal controls accepted.

**Impact**:
- Adds a vertical WP7.3 boundary-policy bridge above decimal constructor-local
  unification parity.

### 2026-02-25: WP7.2 explicit precision boundary-policy surface spot-check

**Context**: After adding explicit precision boundary-policy artifacts in
`PrecisionLeafParity` (`PrecisionBoundarySite`,
`precisionBoundaryAllowsAtSite`, `precision_boundary_surface_slice`), ran a
precision surface probe.

**MCP tools used**: `diagnose`

**Probe**:
- Combined declarations:
  - `i32_bad(x: Int32) -> Int64 { x }`
  - `f32_bad(x: Float32) -> Float64 { x }`
  - `i32_from_int(x: Int) -> Int32 { x }`
  - `i32_id(x: Int32) -> Int32 { x }`
- Result:
  - `i32_bad` rejects (`declared Int64`, value `Int32`).
  - `f32_bad` rejects (`declared Float64`, value `Float32`).
  - `i32_from_int` rejects (`declared Int32`, value `Int`).
  - `i32_id` contributes no diagnostics.

**Classify**: Agreement.

**Outcome**:
- Runtime behavior matches explicit precision boundary policy:
  precision mismatch and non-precision-to-precision boundary rejection, with
  matching controls accepted.

**Impact**:
- Adds a vertical WP7.2 boundary-policy bridge above precision constructor-local
  unification parity.

### 2026-02-25: WP7.6 explicit existential boundary-policy surface spot-check

**Context**: After adding explicit existential boundary-policy artifacts in
`ExistentialParity` (`ExistentialBoundarySite`,
`existentialBoundaryAllowsAtSite`, `existential_boundary_surface_slice`), ran
existential surface probes.

**MCP tools used**: `diagnose`

**Probe**:
- Combined declarations:
  - `any_show_to_int(x: any Show) -> Int { x }`
  - `any_bounds_mismatch(x: any Show) -> any Eq { x }`
  - `int_to_any_show(x: Int) -> any Show { x }`
  - `any_show_id(x: any Show) -> any Show { x }`
- Result:
  - `any_show_to_int` rejects (`declared Int`, value `any Show`).
  - `any_bounds_mismatch` rejects (`declared any Eq`, value `any Show`).
  - `int_to_any_show` rejects (`declared any Show`, value `Int`).
  - `any_show_id` contributes no diagnostics.

**Classify**: Agreement.

**Outcome**:
- Runtime behavior matches explicit existential boundary policy:
  bounds/associated-type mismatch and non-existential-to-existential boundary
  rejection, with matching existential controls accepted.

**Impact**:
- Adds a vertical WP7.6 boundary-policy bridge above existential
  constructor-local unification parity.

### 2026-02-25: WP7.7 explicit Task/Actor/Arc wrapper boundary-policy spot-check

**Context**: After adding explicit wrapper boundary-policy artifacts in
`RuntimeWrapperParity` (`WrapperBoundarySite`, `wrapperBoundaryAllowsAtSite`,
`wrapper_boundary_surface_slice`), ran a wrapper surface probe.

**MCP tools used**: `diagnose`

**Probe**:
- Combined declarations:
  - `task_inner_bad(x: Task(Int)) -> Task(Bool) { x }`
  - `task_from_int(x: Int) -> Task(Int) { x }`
  - `arc_inner_bad(x: Arc(Int)) -> Arc(Bool) { x }`
  - `actor_inner_bad(x: Actor(Int)) -> Actor(Bool) { x }`
  - `task_id(x: Task(Int)) -> Task(Int) { x }`
- Result:
  - `task_inner_bad`, `arc_inner_bad`, and `actor_inner_bad` reject
    (`declared Bool`, value `Int` inside wrappers).
  - `task_from_int` rejects (`declared Task(Int)`, value `Int`).
  - `task_id` contributes no diagnostics.

**Classify**: Agreement.

**Outcome**:
- Runtime behavior matches explicit Task/Actor/Arc wrapper boundary policy:
  wrapper-inner mismatch and non-wrapper-to-wrapper rejection, with matching
  controls accepted.

**Impact**:
- Adds a vertical WP7.7 wrapper boundary-policy bridge above constructor-local
  unification parity for Task/Actor/Arc.

### 2026-02-25: WP7.1 explicit low-risk leaf boundary-policy spot-check

**Context**: After adding explicit low-risk leaf boundary-policy artifacts in
`TemporalLeafParity` (`LeafBoundarySite`, `leafBoundaryAllowsAtSite`,
`leaf_boundary_surface_slice`), ran a leaf surface probe.

**MCP tools used**: `diagnose`

**Probe**:
- Combined declarations:
  - `html_to_markdown(x: Html) -> Markdown { x }`
  - `atom_to_html(x: Atom) -> Html { x }`
  - `html_from_string(x: String) -> Html { x }`
  - `html_id(x: Html) -> Html { x }`
- Result:
  - `html_to_markdown` rejects (`declared Markdown`, value `Html`).
  - `atom_to_html` rejects (`declared Html`, value `Atom`).
  - `html_from_string` rejects (`declared Html`, value `String`).
  - `html_id` contributes no diagnostics.

**Classify**: Agreement.

**Outcome**:
- Runtime behavior matches explicit low-risk leaf boundary policy:
  leaf mismatch and non-leaf-to-leaf boundary rejection, with matching controls
  accepted.

**Impact**:
- Adds a vertical WP7.1 boundary-policy bridge above constructor-local
  unification parity for `Html`/`Markdown`/`Atom` (alongside `Date`/`DateTime`).

### 2026-02-25: Column boundary-policy surface spot-check

**Context**: After adding explicit site-level column boundary-policy artifacts
in `ColumnBoundary` (`ColumnBoundarySite`, `columnBoundaryAllowsAtSite`,
`column_boundary_surface_slice`), ran a column boundary probe.

**MCP tools used**: `diagnose`

**Probe**:
- Combined declarations:
  - `col_to_bare(x: Column(Int)) -> Int { x }`
  - `bare_to_col(x: Int) -> Column(Int) { x }`
  - `col_id(x: Column(Int)) -> Column(Int) { x }`
- Result:
  - `col_to_bare` rejects (`declared Int`, value `Column(Int)`).
  - `bare_to_col` rejects (`declared Column(Int)`, value `Int`).
  - `col_id` contributes no diagnostics.

**Classify**: Agreement.

**Outcome**:
- Runtime behavior matches explicit column boundary policy:
  bidirectional `Column(T)`/bare `T` boundary rejection with matching column
  controls accepted.

**Impact**:
- Adds a formal cardinality-boundary package bridge from existing unifier
  mismatch witnesses to site-level boundary policy.

### 2026-02-25: Trait call-site boundary-policy spot-check

**Context**: After adding explicit site-level trait call boundary artifacts in
`Rill/Traits.lean` (`TraitCallBoundarySite`, `callSiteAcceptsDirectAtSite`,
`callSiteAcceptsWithGraphAtSite`, `trait_call_boundary_surface_slice`), re-ran
the MyOrd/MyEq supertrait witness probes.

**MCP tools used**: `reset_session`, `resolve_traits`

**Probe**:
1. Reset session; register only:
   - `trait MyEq {}`
   - `trait MyOrd: MyEq {}`
   - `impl MyOrd for Int {}`
   Then `resolve_traits(type = Int, trait = MyOrd)` reports supertrait
   `MyEq` with `satisfied: false`.
2. Reset session; register:
   - `trait MyEq {}`
   - `trait MyOrd: MyEq {}`
   - `impl MyOrd for Int {}`
   - `impl MyEq for Int {}`
   Then `resolve_traits(type = Int, trait = MyOrd)` reports supertrait
   `MyEq` with `satisfied: true`.

**Classify**: Agreement.

**Outcome**:
- Runtime trait provenance matches formal direct-vs-closure witness states used
  by the new site-level boundary package.

**Impact**:
- Adds a vertical trait-call boundary-policy bridge at boundary-sensitive sites
  without changing the existing supertrait-gap witness semantics.

### 2026-02-25: Actor dispatch boundary-policy spot-check

**Context**: After adding explicit site-level actor dispatch boundary artifacts
in `Rill/Traits.lean` (`ActorDispatchBoundarySite`,
`actorDispatchAcceptsMessageAtSite`, `actorDispatchAcceptsLegacyAtSite`,
`actor_dispatch_boundary_surface_slice`), re-ran actor message-style probes.

**MCP tools used**: `reset_session`, `evaluate`, `type_check`

**Probe**:
1. Reset session and register:
   - `type CounterMsg = Inc | Get`
   - `record Counter { count: Int }`
   - `impl Actor for Counter where Message = CounterMsg { fn handle(self, msg: CounterMsg) -> Counter { self } }`
2. `type_check "{ let c = spawn Counter { count: 0 }\nsend(c, Inc) }"` returns `ok`.
3. `type_check "{ let c = spawn Counter { count: 0 }\ncall(c, Get) }"` returns `ok`.
4. `type_check "{ let c = spawn Counter { count: 0 }\nsend(c, :inc) }"` rejects with
   `actor type Counter has no method inc`.

**Classify**: Agreement.

**Outcome**:
- Runtime behavior matches explicit actor dispatch boundary policy:
  message-style dispatch remains accepted, legacy `:inc` dispatch rejects on
  handle-only protocols, and legacy explicit `handle` remains accepted.

**Impact**:
- Adds a vertical actor dispatch boundary-policy bridge at boundary-sensitive
  sites on top of the existing post-migration actor dispatch contract.

### 2026-02-25: Nominal boundary post-fix convergence spot-check

**Context**: After the implementation-side nominal-boundary fix (indirection
paths and type-level boundary checks), re-ran record nominal boundary probes
across all boundary-sensitive sites plus a named->structural control.

**MCP tools used**: `reset_session`, `evaluate`, `type_check`

**Probe**:
1. Reset session and register:
   - `record User { name: String, age: Int }`
   - `fn takes_user(u: User) -> User { u }`
2. `type_check "{ let tmp = #{ name: \"Alice\", age: 30 }\n  let u: User = tmp\n  u }"` rejects with
   `expected User, got anonymous record`.
3. `type_check "{ let tmp = #{ name: \"Alice\", age: 30 }\n  takes_user(tmp) }"` rejects with
   `expected User, got anonymous record`.
4. `type_check "fn mk_user() -> User {\n  let tmp = #{ name: \"Alice\", age: 30 }\n  tmp\n}"` rejects with
   `expected User, got anonymous record`.
5. `type_check "{ let tmp = #{ name: \"Alice\", age: 30 }\n  tmp as User }"` rejects with
   `expected User, got anonymous record`.
6. Positive control:
   `type_check "{ let get_name = r -> r.name\n  let u = User { name: \"Alice\", age: 30 }\n  get_name(u) }"` returns `ok` (`String`).

**Classify**: Agreement.

**Outcome**:
- Runtime behavior matches formal directional record nominal-boundary policy:
  structural->nominal implicit flow rejects at let/call/return/ascription
  boundaries, while named->structural projection remains accepted.

**Impact**:
- Confirms post-fix runtime convergence with
  `RecordStructuralProjection` boundary theorems at all modeled boundary sites.

### 2026-02-25: Cross-family boundary suite composition checkpoint

**Context**: Added `Rill/Properties/BoundarySurfaceSuite.lean` with
`boundary_surface_suite`, a theorem-level composition of existing
per-family boundary slices (leaf, precision, decimal, nominal ADT/record,
higher-rank/constructor, runtime wrappers, grouped/tagged, column, trait-call,
actor-dispatch). Later extended to include language-level
`dynamic_boundary_typing_bridge_ascription` and
`grouped_tagged_typing_bridge_ascription`.

**MCP tools used**: none (composition-only Lean packaging).

**Classify**: N/A (no new runtime behavior introduced).

**Outcome**:
- No new divergence surface; this step only adds a unified citation contract
  over previously MCP-validated boundary slices.

**Impact**:
- Reduces theorem-surface fragmentation for downstream vertical proofs and paper
  references by exposing one cross-family boundary package theorem.

### 2026-02-25: Dynamic boundary typing-bridge spot-check

**Context**: After adding `DynamicBoundaryTypingBridge` (`hasType_var_dynamic`,
`hasType_var_dynamic_not_int`, `dynamic_boundary_typing_bridge_var`), re-checked
the Dynamic function-return boundary surface that motivated the bridge.

**MCP tools used**: `reset_session`, `type_check`

**Probe**:
1. `type_check "fn dyn_to_int(x: Dynamic) -> Int { x }"` rejects with
   `cannot use \`Dynamic\` value as \`Int\`` and `expect_type` guidance.
2. `type_check "fn dyn_id(x: Dynamic) -> Dynamic { x }"` returns `ok`.

**Classify**: Agreement.

**Outcome**:
- Runtime boundary behavior matches the new language-level bridge direction:
  implicit `Dynamic -> Int` narrowing rejects, while `Dynamic -> Dynamic`
  controls remain accepted.

**Impact**:
- Establishes a first explicit bridge from Dynamic boundary policy to
  declarative typing-level artifacts (variable boundary case), reducing WP7.7
  language-level integration risk.

### 2026-02-25: Dynamic call-argument boundary spot-check

**Context**: After extending `DynamicBoundaryTypingBridge` with app-path lemmas
(`hasType_app_dynamic_arg_not_int`, `hasType_app_dynamic_arg_dynamic`,
`dynamic_boundary_typing_bridge_app`), checked runtime call-argument behavior.

**MCP tools used**: `reset_session`, `type_check`

**Probe**:
1. `type_check "fn apply_int(f: fn(Int) -> Int, x: Dynamic) -> Int { f(x) }"` rejects with
   `cannot use \`Dynamic\` value as \`Int\`` (duplicate diagnostic surfaced twice at the same span).
2. `type_check "fn apply_dyn(f: fn(Dynamic) -> Dynamic, x: Dynamic) -> Dynamic { f(x) }"` returns `ok`.

**Classify**: Agreement.

**Outcome**:
- Runtime call-argument behavior aligns with the app-path bridge:
  Dynamic->Int argument narrowing rejects, Dynamic-compatible call path accepts.

**Impact**:
- Extends WP7.7 language-level Dynamic bridge coverage from variable-only to
  variable+app without introducing new divergence.

### 2026-02-25: Dynamic let-boundary spot-check

**Context**: After extending `DynamicBoundaryTypingBridge` with let-path lemmas
(`hasType_let_dynamic_not_int`, `hasType_let_dynamic_dynamic`,
`dynamic_boundary_typing_bridge_let`), checked runtime let-boundary behavior.

**MCP tools used**: `reset_session`, `type_check`

**Probe**:
1. `type_check "fn let_narrow(x: Dynamic) -> Int { let y: Int = x\n  y\n}"` rejects with
   `cannot use \`Dynamic\` value as \`Int\`` (reported at let binding and return use).
2. `type_check "fn let_keep(x: Dynamic) -> Dynamic { let y: Dynamic = x\n  y\n}"` returns `ok`.

**Classify**: Agreement.

**Outcome**:
- Runtime let-boundary behavior aligns with the let-path bridge:
  Dynamic->Int narrowing rejects, Dynamic-preserving let path accepts.

**Impact**:
- Extends WP7.7 language-level Dynamic bridge coverage to variable+app+let
  while maintaining agreement with runtime behavior.

### 2026-02-25: Dynamic ascription boundary spot-check

**Context**: After adding modeled-ascription bridge artifacts in
`DynamicBoundaryTypingBridge` (`HasTypeAtAscriptionBoundary`,
`hasType_ascription_dynamic_to_int_rejected`,
`hasType_ascription_dynamic_to_dynamic_accepts`,
`dynamic_boundary_typing_bridge_ascription`), re-checked runtime ascription
surface behavior.

**MCP tools used**: `reset_session`, `type_check`

**Probe**:
1. `type_check "fn ascribe_narrow(x: Dynamic) -> Int { x as Int }"` rejects with
   `cannot use \`Dynamic\` value as \`Int\``.
2. `type_check "fn ascribe_keep(x: Dynamic) -> Dynamic { x as Dynamic }"` returns `ok`.

**Classify**: Agreement.

**Outcome**:
- Runtime ascription behavior matches the modeled ascription bridge:
  Dynamic->Int ascription rejects; Dynamic->Dynamic ascription accepts.

**Impact**:
- Extends WP7.7 language-level Dynamic bridge coverage to
  variable+app+let+return plus a modeled ascription gate, with no new
  divergence observed.

### 2026-02-25: Grouped/Tagged typing-bridge spot-check

**Context**: After adding `GroupedTaggedTypingBridge`
(`HasTypeAtGroupedTaggedBoundary`, grouped/tagged uniqueness and modeled
ascription bridge theorems), checked grouped/tagged wrapper surface behavior.

**MCP tools used**: `reset_session`, `type_check`

**Probe**:
1. `type_check "fn grouped_inner_bad(x: GroupedFrame(Int)) -> GroupedFrame(Bool) { x }"` rejects.
2. `type_check "fn grouped_from_int(x: Int) -> GroupedFrame(Int) { x }"` rejects.
3. `type_check "fn grouped_id(x: GroupedFrame(Int)) -> GroupedFrame(Int) { x }"` returns `ok`.
4. `type_check "fn tagged_inner_bad(x: Tagged(Int)) -> Tagged(Bool) { x }"` rejects.
5. `type_check "fn tagged_from_int(x: Int) -> Tagged(Int) { x }"` rejects.
6. `type_check "fn tagged_id(x: Tagged(Int)) -> Tagged(Int) { x }"` returns `ok`.

**Classify**: Agreement.

**Outcome**:
- Runtime grouped/tagged wrapper behavior matches the modeled bridge
  direction: wrapper inner mismatch and non-wrapper flows reject; matching
  identity controls accept.
- Diagnostic note: for `Tagged` inner mismatch, runtime currently reports the
  inner `Bool` vs `Int` mismatch shape directly rather than wrapper-shaped type
  text; behavior is still reject/accept aligned.

**Impact**:
- Establishes first explicit language-level grouped/tagged typing bridge at a
  modeled ascription boundary, reducing WP7.7 residual risk.

### 2026-02-25: Boundary bridge re-check after assignability abstraction refactor

**Context**: After introducing shared `BoundaryAssignability`
(`HasTypeAtBoundary`, `allowsByBool`, `allowsByBoolAndUnify`) and rebasing
`DynamicBoundaryTypingBridge` / `GroupedTaggedTypingBridge` on that abstraction,
re-ran boundary probes against the rebuilt MCP.

**MCP tools used**: `diagnose`

**Probe**:
1. `diagnose "fn dyn_to_int(x: Dynamic) -> Int { x }"` reports
   `cannot use \`Dynamic\` value as \`Int\`` with `expect_type` guidance.
2. `diagnose "fn dyn_id(x: Dynamic) -> Dynamic { x }"` reports no diagnostics.
3. `diagnose "fn grouped_bad(x: GroupedFrame(Bool)) -> GroupedFrame(Int) { x }"` reports
   grouped wrapper mismatch (`GroupedFrame(Int, keys: [])` vs `GroupedFrame(Bool, keys: [])`).
4. `diagnose "fn grouped_id(x: GroupedFrame(Int)) -> GroupedFrame(Int) { x }"` reports no diagnostics.
5. `diagnose "fn tagged_bad(x: Tagged(Bool)) -> Tagged(Int) { x }"` reports inner mismatch (`declared Int, got Bool`).
6. `diagnose "fn tagged_id(x: Tagged(Int)) -> Tagged(Int) { x }"` reports no diagnostics.
7. `diagnose "fn int_to_grouped(x: Int) -> GroupedFrame(Int) { x }"` reports non-wrapper rejection
   (`declared GroupedFrame(Int, keys: []), got Int`).
8. `diagnose "fn grouped_bad(x: GroupedFrame(Bool, [\"a\"])) -> GroupedFrame(Int, [\"a\"]) { x }"` is a syntax error
   (`expected type annotation`) on this parser path.

**Classify**: Agreement (with existing documented parser-surface limitation for parameterized grouped/tagged annotations).

**Outcome**:
- Dynamic and grouped/tagged reject/accept behavior remains aligned with the
  modeled bridge theorems after refactoring the shared assignability layer.
- Parameterized grouped/tagged annotation syntax remains unavailable in this
  path; non-parameterized wrapper probes continue to exercise the runtime
  boundary behavior.

**Impact**:
- Confirms the abstraction refactor is proof-structure only and does not hide a
  runtime divergence in the active boundary surface.

### 2026-02-25: Post-refresh MCP re-probe (WP7.7 boundaries + syntax surfaces)

**Context**: After MCP server refresh with recent implementation updates,
re-checked active WP7.7 boundary behavior plus known syntax-sensitive surfaces.

**MCP tools used**: `diagnose`

**Probe**:
1. Dynamic boundaries:
   - `fn dyn_to_int(x: Dynamic) -> Int { x }` rejects (`cannot use Dynamic as Int`).
   - `fn dyn_id(x: Dynamic) -> Dynamic { x }` accepts.
   - `fn apply_int(f: fn(Int) -> Int, x: Dynamic) -> Int { f(x) }` rejects.
   - `fn apply_dyn(f: fn(Dynamic) -> Dynamic, x: Dynamic) -> Dynamic { f(x) }` accepts.
   - `fn let_narrow(x: Dynamic) -> Int { let y: Int = x\n  y\n}` rejects.
   - `fn let_keep(x: Dynamic) -> Dynamic { let y: Dynamic = x\n  y\n}` accepts.
   - `fn ascribe_narrow(x: Dynamic) -> Int { x as Int }` rejects.
   - `fn ascribe_keep(x: Dynamic) -> Dynamic { x as Dynamic }` accepts.
2. Grouped/tagged boundaries (active surface syntax):
   - `fn grouped_bad(x: GroupedFrame(Bool)) -> GroupedFrame(Int) { x }` rejects.
   - `fn grouped_id(x: GroupedFrame(Int)) -> GroupedFrame(Int) { x }` accepts.
   - `fn tagged_bad(x: Tagged(Bool)) -> Tagged(Int) { x }` rejects (inner mismatch text).
   - `fn tagged_id(x: Tagged(Int)) -> Tagged(Int) { x }` accepts.
   - `fn int_to_grouped(x: Int) -> GroupedFrame(Int) { x }` rejects.
3. Parser/surface checks:
   - `GroupedFrame(Bool, ["a"])` annotation form still syntax-errors on this path.
   - `FixedSizeList(Int, 4)` still rejects integer type-arg (`integer literal is not valid as a type`).
   - `Tensor(Int, [2, 3])` still syntax-errors in type annotation path.
   - `forall a. fn(a) -> a` syntax in rank-2 position accepts.

**Classify**:
- Agreement for WP7.7 Dynamic + grouped/tagged boundary behavior.
- Known expected divergence persists for WP7.4 shape annotation surface
  (`FixedSizeList`/`Tensor` type-annotation syntax support).

**Outcome**:
- No new WP7.7 divergence after refresh.
- Shape-constructor annotation divergence remains stable and documented.

### 2026-02-25: Wrapper boundary typing-bridge spot-check (Task/Actor/Arc)

**Context**: After adding `WrapperBoundaryTypingBridge`
(`HasTypeAtWrapperBoundary`, wrapper uniqueness lemmas, modeled ascription
rejection/acceptance theorems), checked runtime wrapper boundary behavior on
the active annotation surface.

**MCP tools used**: `diagnose`

**Probe**:
1. `fn task_bad(x: Task(Bool)) -> Task(Int) { x }` rejects (inner mismatch).
2. `fn task_id(x: Task(Int)) -> Task(Int) { x }` accepts.
3. `fn int_to_task(x: Int) -> Task(Int) { x }` rejects (non-wrapper actual).
4. `fn actor_bad(x: Actor(Bool)) -> Actor(Int) { x }` rejects (inner mismatch).
5. `fn actor_id(x: Actor(Int)) -> Actor(Int) { x }` accepts.
6. `fn int_to_actor(x: Int) -> Actor(Int) { x }` rejects (non-wrapper actual).
7. `fn arc_bad(x: Arc(Bool)) -> Arc(Int) { x }` rejects (inner mismatch).
8. `fn arc_id(x: Arc(Int)) -> Arc(Int) { x }` accepts.
9. `fn int_to_arc(x: Int) -> Arc(Int) { x }` rejects (non-wrapper actual).

**Classify**: Agreement.

**Outcome**:
- Runtime Task/Actor/Arc wrapper boundary behavior matches the modeled wrapper
  typing-bridge direction: inner mismatch and non-wrapper flows reject, while
  identity controls accept.

**Impact**:
- Extends WP7.7 language-level boundary bridge coverage from
  Dynamic+Grouped/Tagged to Dynamic+Wrapper+Grouped/Tagged with runtime
  agreement on the active surface path.

### 2026-02-25: WP7.7 boundary site-matrix re-probe (call/let/ascription)

**Context**: After site-generalizing Dynamic/wrapper/grouped-tagged typing
bridges in Lean (`*_all_sites`), re-checked runtime behavior at additional
boundary sites (call-argument, let-binding annotation, and `as` ascription).

**MCP tools used**: `diagnose`

**Probe**:
1. Task site matrix:
   - Call: `Task(Bool)` to `Task(Int)` rejects; `Task(Int)` control accepts;
     `Int` to `Task(Int)` rejects.
   - Let: `let y: Task(Int) = x` rejects for `x: Task(Bool)`; accepts for
     `x: Task(Int)`; rejects for `x: Int`.
   - Ascription: `x as Task(Int)` rejects for `x: Task(Bool)`; accepts for
     `x: Task(Int)`; rejects for `x: Int`.
2. Actor site matrix:
   - Same call/let/ascription pattern as Task (`Actor(Bool)` mismatch rejects,
     `Actor(Int)` controls accept, `Int` non-wrapper flows reject).
3. Arc site matrix:
   - Same call/let/ascription pattern as Task/Actor (`Arc(Bool)` mismatch
     rejects, `Arc(Int)` controls accept, `Int` non-wrapper flows reject).
4. GroupedFrame site matrix:
   - Call/let/ascription reject `GroupedFrame(Bool)` -> `GroupedFrame(Int)`.
   - Matching `GroupedFrame(Int)` controls accept.
   - Non-wrapper `Int` -> `GroupedFrame(Int)` rejects in all three sites.
5. Tagged site matrix:
   - Call/let/ascription reject `Tagged(Bool)` -> `Tagged(Int)` (inner mismatch
     text).
   - Matching `Tagged(Int)` controls accept.
   - Non-wrapper `Int` -> `Tagged(Int)` rejects in all three sites.

**Classify**: Agreement.

**Outcome**:
- No new divergence observed: runtime boundary behavior matches the newly
  generalized all-sites Lean bridge contracts for Dynamic/wrapper/grouped-tagged
  surfaces.

### 2026-02-25: Boundary ascription syntax-bridge spot-check (expression-level slice)

**Context**: After adding `BoundaryAscriptionSyntax`
(`CoreExprWithAscription`, `HasTypeWithAscription`,
`BoundaryAscriptionSyntaxSliceAtSites`) and wiring it into
`BoundarySurfaceSuite`, re-ran boundary probes on the same Dynamic/wrapper/
grouped ascription surfaces.

**MCP tools used**: `diagnose`

**Probe**:
1. `fn dyn_to_int(x: Dynamic) -> Int { x }` reports
   `cannot use \`Dynamic\` value as \`Int\`` with `expect_type` guidance.
2. `fn dyn_id(x: Dynamic) -> Dynamic { x }` reports no diagnostics.
3. `fn task_bad(t: Task(Bool)) -> Task(Int) { t }` reports
   `declared \`Int\`, but value has type \`Bool\``.
4. `fn task_ok(t: Task(Int)) -> Task(Int) { t }` reports no diagnostics.
5. `fn grouped_bad(g: GroupedFrame(Bool)) -> GroupedFrame(Int) { g }` reports
   grouped mismatch (`GroupedFrame(Int, keys: [])` vs
   `GroupedFrame(Bool, keys: [])`).
6. `fn grouped_ok(g: GroupedFrame(Int)) -> GroupedFrame(Int) { g }` reports no
   diagnostics.

**Classify**: Agreement.

**Outcome**:
- Runtime behavior matches the new expression-level ascription bridge slice:
  Dynamic narrowing rejects while identity controls accept; wrapper/grouped
  inner mismatches reject while matching controls accept.

**Impact**:
- Moves WP7.7 boundary modeling one step closer to syntax/judgment integration
  by making ascription explicit in a typing relation, with fresh MCP evidence on
  the same runtime surfaces.

### 2026-02-25: Expression-level ascription site-invariance re-probe (WP7.7)

**Context**: After adding packaged expression-level ascription site-invariance
artifacts in `BoundaryAscriptionSyntax`
(`hasTypeWith*Ascription_ascribe_iff_ascription`,
`BoundaryAscriptionSyntaxSiteInvarianceSliceAtSites`) and lifting them into
`boundary_surface_suite`, re-checked call/let/`as` site behavior for
Dynamic/Task/Grouped wrappers.

**MCP tools used**: `diagnose`

**Probe**:
1. Dynamic mismatch path rejects at all three sites:
   - Call: `fn call_dyn_narrow(f: fn(Int) -> Int, x: Dynamic) -> Int { f(x) }`
   - Let: `fn let_dyn_narrow(x: Dynamic) -> Int { let y: Int = x; y }`
   - Ascription: `fn ascribe_dyn_narrow(x: Dynamic) -> Int { x as Int }`
2. Dynamic control accepts:
   - `fn ascribe_dyn_ok(x: Dynamic) -> Dynamic { x as Dynamic }`
3. Task wrapper mismatch path rejects at all three sites:
   - Call: `fn call_task_bad(f: fn(Task(Int)) -> Task(Int), x: Task(Bool)) -> Task(Int) { f(x) }`
   - Let: `fn let_task_bad(x: Task(Bool)) -> Task(Int) { let y: Task(Int) = x; y }`
   - Ascription: `fn ascribe_task_bad(x: Task(Bool)) -> Task(Int) { x as Task(Int) }`
4. Task control accepts:
   - `fn ascribe_task_ok(x: Task(Int)) -> Task(Int) { x as Task(Int) }`
5. GroupedFrame wrapper mismatch path rejects at all three sites:
   - Call: `fn call_grouped_bad(f: fn(GroupedFrame(Int)) -> GroupedFrame(Int), x: GroupedFrame(Bool)) -> GroupedFrame(Int) { f(x) }`
   - Let: `fn let_grouped_bad(x: GroupedFrame(Bool)) -> GroupedFrame(Int) { let y: GroupedFrame(Int) = x; y }`
   - Ascription: `fn ascribe_grouped_bad(x: GroupedFrame(Bool)) -> GroupedFrame(Int) { x as GroupedFrame(Int) }`
6. GroupedFrame control accepts:
   - `fn ascribe_grouped_ok(x: GroupedFrame(Int)) -> GroupedFrame(Int) { x as GroupedFrame(Int) }`

**Classify**: Agreement.

**Outcome**:
- Runtime behavior remains site-consistent across call/let/ascription for the
  probed mismatch/control paths, matching the new expression-level
  site-invariance packaging.

**Impact**:
- Grounds `BoundaryAscriptionSyntaxSiteInvarianceSliceAtSites` with fresh MCP
  evidence and keeps WP7.7 boundary-site invariance claims synchronized with
  runtime behavior.

### 2026-02-25: Wrapper/grouped algorithmic ascription slice spot-check

**Context**: After adding algorithmic wrapper/grouped ascription checkers in
`BoundaryAscriptionSyntax`
(`inferWrapperAscriptionAtSite`, `inferGroupedTaggedAscriptionAtSite`,
`WrapperAscriptionAlgorithmicSliceAtSite`,
`GroupedTaggedAscriptionAlgorithmicSliceAtSite`) and lifting them into
`boundary_surface_suite`, re-checked the corresponding runtime `as` surfaces.

**MCP tools used**: `diagnose`

**Probe**:
1. Dynamic controls:
   - `fn ascribe_dyn_narrow(x: Dynamic) -> Int { x as Int }` rejects.
   - `fn ascribe_dyn_ok(x: Dynamic) -> Dynamic { x as Dynamic }` accepts.
2. Wrapper controls:
   - `fn ascribe_task_bad(x: Task(Bool)) -> Task(Int) { x as Task(Int) }`
     rejects (`expected Int, got Bool`).
   - `fn ascribe_task_ok(x: Task(Int)) -> Task(Int) { x as Task(Int) }`
     accepts.
3. Grouped controls:
   - `fn ascribe_grouped_bad(x: GroupedFrame(Bool)) -> GroupedFrame(Int) { x as GroupedFrame(Int) }`
     rejects.
   - `fn ascribe_grouped_ok(x: GroupedFrame(Int)) -> GroupedFrame(Int) { x as GroupedFrame(Int) }`
     accepts.

**Classify**: Agreement.

**Outcome**:
- Runtime `as` behavior matches the new algorithmic wrapper/grouped ascription
  witness slices: mismatch paths reject and identity controls accept.

**Impact**:
- Grounds the newly-added wrapper/grouped algorithmic ascription bridge
  artifacts with current MCP evidence and keeps the WP7.7 boundary suite
  vertically synchronized.

### 2026-02-25: Ascription algorithmic↔declarative alignment re-probe

**Context**: After packaging
`AscriptionAlgorithmicDeclarativeAlignmentSliceAtSites` and lifting it into
`boundary_surface_suite`, re-checked the same Dynamic/wrapper/grouped `as`
reject-vs-accept boundaries.

**MCP tools used**: `diagnose`

**Probe**:
1. Dynamic:
   - `fn dyn_ascribe_narrow(x: Dynamic) -> Int { x as Int }` rejects
     (`cannot use Dynamic value as Int` with `expect_type` guidance).
   - `fn dyn_ascribe_keep(x: Dynamic) -> Dynamic { x as Dynamic }` accepts.
2. Task:
   - `fn task_ascribe_narrow(t: Task(Bool)) -> Task(Int) { t as Task(Int) }`
     rejects (`expected Int, got Bool`).
   - `fn task_ascribe_keep(t: Task(Int)) -> Task(Int) { t as Task(Int) }`
     accepts.
3. GroupedFrame:
   - `fn grouped_ascribe_narrow(g: GroupedFrame(Bool)) -> GroupedFrame(Int) { g as GroupedFrame(Int) }`
     rejects (`GroupedFrame(Int, keys: [])` vs `GroupedFrame(Bool, keys: [])`).
   - `fn grouped_ascribe_keep(g: GroupedFrame(Int)) -> GroupedFrame(Int) { g as GroupedFrame(Int) }`
     accepts.

**Classify**: Agreement.

**Outcome**:
- Runtime `as` behavior remains aligned with the new packaged
  algorithmic↔declarative ascription slice: mismatch paths reject and identity
  controls accept across Dynamic/wrapper/grouped boundaries.

### 2026-02-25: Ascription bridge-suite packaging sanity probe

**Context**: After adding
`BoundaryAscriptionBridgeSuiteAtSites` and replacing the ascription clause in
`boundary_surface_suite` with this single package, re-ran a minimal Dynamic
ascription boundary sanity check.

**MCP tools used**: `diagnose`

**Probe**:
1. `fn dyn_ascribe_narrow(x: Dynamic) -> Int { x as Int }` still rejects with
   `cannot use Dynamic value as Int` and `expect_type` guidance.

**Classify**: Agreement.

**Outcome**:
- No runtime behavior change observed after theorem-package refactor; boundary
  rejection remains aligned.

### 2026-02-25: Expression-level inferExpr-ascription integration slice probe

**Context**: After adding expression-level ascription inference adapters
(`inferDynamicExprWithAscriptionAtSite`,
`inferWrapperExprWithAscriptionAtSite`,
`inferGroupedTaggedExprWithAscriptionAtSite`) and packaging
`AscriptionInferExprBridgeSliceAtSites` into
`BoundaryAscriptionBridgeSuiteAtSites`, re-checked representative base +
ascription paths.

**MCP tools used**: `diagnose`

**Probe**:
1. Base expression control:
   - `fn base_int() -> Int { 1 }` accepts.
2. Dynamic ascription:
   - `fn dyn_ascribe_narrow(x: Dynamic) -> Int { x as Int }` rejects with
     `expect_type` guidance.
   - `fn dyn_ascribe_keep(x: Dynamic) -> Dynamic { x as Dynamic }` accepts.
3. Wrapper/grouped ascription mismatch controls:
   - `fn task_ascribe_narrow(t: Task(Bool)) -> Task(Int) { t as Task(Int) }`
     rejects.
   - `fn grouped_ascribe_narrow(g: GroupedFrame(Bool)) -> GroupedFrame(Int) { g as GroupedFrame(Int) }`
     rejects.

**Classify**: Agreement.

**Outcome**:
- Runtime behavior remains aligned with the new expression-level inferExpr
  ascription-integration slice and the existing boundary witness suite.

### 2026-02-25: boundary_surface_suite direct inferExpr-slice lift sanity probe

**Context**: After exposing `AscriptionInferExprBridgeSliceAtSites` as an
explicit conjunct in `boundary_surface_suite` (in addition to inclusion via
`BoundaryAscriptionBridgeSuiteAtSites`), re-ran a minimal base-expression
control probe.

**MCP tools used**: `diagnose`

**Probe**:
1. `fn base_int() -> Int { 1 }` accepts.

**Classify**: Agreement.

**Outcome**:
- No runtime behavior change observed after the top-level theorem-contract lift.

### 2026-02-25: inferExpr-ascription completeness slice re-probe

**Context**: After adding expression-level completeness artifacts
(`inferDynamicExprWithAscriptionAtSite_complete`,
`inferWrapperExprWithAscriptionAtSite_complete`,
`inferGroupedTaggedExprWithAscriptionAtSite_complete`,
`AscriptionInferExprCompletenessSliceAtSites`) and folding the slice into
`BoundaryAscriptionBridgeSuiteAtSites`, re-checked representative acceptance
paths.

**MCP tools used**: `diagnose`

**Probe**:
1. Base expression control:
   - `fn base_bool() -> Bool { true }` accepts.
2. Dynamic ascription acceptance:
   - `fn dyn_ascribe_keep(x: Dynamic) -> Dynamic { x as Dynamic }` accepts.
3. Grouped ascription identity acceptance:
   - `fn grouped_ascribe_keep(g: GroupedFrame(Int)) -> GroupedFrame(Int) { g as GroupedFrame(Int) }`
     accepts.

**Classify**: Agreement.

**Outcome**:
- Acceptance-side runtime behavior remains aligned with the new
  expression-level inferExpr-ascription completeness packaging.

### 2026-02-25: boundary_surface_suite direct completeness-slice lift probe

**Context**: After exposing
`AscriptionInferExprCompletenessSliceAtSites` as an explicit conjunct in
`boundary_surface_suite` (in addition to inclusion via
`BoundaryAscriptionBridgeSuiteAtSites`), re-ran a grouped identity control.

**MCP tools used**: `diagnose`

**Probe**:
1. `fn grouped_ascribe_keep(g: GroupedFrame(Int)) -> GroupedFrame(Int) { g as GroupedFrame(Int) }`
   accepts.

**Classify**: Agreement.

**Outcome**:
- No runtime behavior change observed after the direct completeness-slice lift.

### 2026-02-25: base-embedding slice probe

**Context**: After adding `AscriptionBaseEmbeddingSliceAtSites` (showing
`.base` nodes in ascription adapters coincide with core `inferExpr`/`HasType`)
and folding it into `BoundaryAscriptionBridgeSuiteAtSites`, re-checked a
base-expression control with local `let`.

**MCP tools used**: `diagnose`

**Probe**:
1. `fn base_let_id(x: Int) -> Int { let y: Int = x; y }` (rendered with valid
   newline-separated body syntax) accepts.

**Classify**: Agreement.

**Outcome**:
- Base-expression runtime behavior remains aligned with the new `.base`
  embedding slice.

### 2026-02-25: boundary_surface_suite direct base-embedding lift probe

**Context**: After exposing `AscriptionBaseEmbeddingSliceAtSites` as an
explicit conjunct in `boundary_surface_suite` (in addition to inclusion via
`BoundaryAscriptionBridgeSuiteAtSites`), re-ran a minimal base-expression
control.

**MCP tools used**: `diagnose`

**Probe**:
1. `fn base_int() -> Int { 1 }` accepts.

**Classify**: Agreement.

**Outcome**:
- No runtime behavior change observed after the direct `.base`-embedding lift.

### 2026-02-25: Typing-level ascription core integration re-probe

**Context**: After moving ascription core artifacts into `Rill/Typing.lean`
(`HasTypeAtCoreBoundary`, `CoreExprWithAscription`, `HasTypeWithAscription`,
`inferExprWithAscription`, and soundness/completeness/iff contracts) and
rewiring boundary modules to consume those core definitions, re-ran Dynamic
boundary controls.

**MCP tools used**: `diagnose`, `type_check`

**Probe**:
1. Dynamic narrowing return annotation:
   - `fn dyn_to_int(x: Dynamic) -> Int { x }` rejects with `expect_type`
     guidance.
2. Dynamic identity control:
   - `fn dyn_id(x: Dynamic) -> Dynamic { x }` accepts with
     `(Dynamic) -> Dynamic`.
3. Dynamic explicit ascription narrowing:
   - `fn ascribe_narrow(x: Dynamic) -> Int { x as Int }` rejects.

**Classify**: Agreement.

**Outcome**:
- Runtime surface remains aligned after the Typing-level ascription
  integration slice; no new divergence observed on the probed Dynamic
  boundaries.

### 2026-02-25: wrapper/grouped ascription checker core-routing re-probe

**Context**: After routing `inferWrapperAscriptionAtSite` and
`inferGroupedTaggedAscriptionAtSite` through Typing core
`inferExprWithAscription` (instead of local duplicated infer/match logic),
re-checked wrapper and grouped ascription controls.

**MCP tools used**: `diagnose`

**Probe**:
1. Wrapper mismatch control:
   - `fn task_ascribe_narrow(t: Task(Bool)) -> Task(Int) { t as Task(Int) }`
     rejects (`expected Int, got Bool`).
2. Wrapper identity control:
   - `fn task_ascribe_keep(t: Task(Int)) -> Task(Int) { t as Task(Int) }`
     accepts.
3. Grouped mismatch control:
   - `fn grouped_ascribe_narrow(g: GroupedFrame(Bool)) -> GroupedFrame(Int) { g as GroupedFrame(Int) }`
     rejects (inner type mismatch).
4. Grouped identity control:
   - `fn grouped_ascribe_keep(g: GroupedFrame(Int)) -> GroupedFrame(Int) { g as GroupedFrame(Int) }`
     accepts.

**Classify**: Agreement.

**Outcome**:
- Runtime surface remains aligned after moving wrapper/grouped algorithmic
  ascription checks onto the Typing core ascription inference path.

### 2026-02-25: expression-level infer routing slice sanity probe

**Context**: After adding `AscriptionCoreInferRoutingSliceAtSites` and lifting it
into the boundary suites (showing expression-level ascription adapters route to
Typing core `inferExprWithAscription` for Dynamic/wrapper/grouped surfaces),
ran a minimal acceptance sanity probe.

**MCP tools used**: `diagnose`

**Probe**:
1. Base expression control:
   - `fn base_int() -> Int { 1 }` accepts.
2. Wrapper identity control:
   - `fn task_ascribe_keep(t: Task(Int)) -> Task(Int) { t as Task(Int) }`
     accepts.

**Classify**: Agreement.

**Outcome**:
- No runtime behavior change observed after the expression-level infer-routing
  theorem packaging/lift.

### 2026-02-26: wrapper/grouped gate-semantics relaxation re-probe

**Context**: After relaxing the shared boundary gate relation
`allowsByBoolAndUnify` from strict empty-substitution success
(`unify ... = .ok UnifyState.empty`) to existential unifier success
(`∃ st', unify ... = .ok st'`) and rewiring wrapper/grouped completeness proofs
to consume the existential witness, re-ran runtime boundary controls.

**MCP tools used**: `diagnose`

**Probe**:
1. Wrapper mismatch control:
   - `fn task_ascribe_narrow(t: Task(Bool)) -> Task(Int) { t as Task(Int) }`
     rejects (`type mismatch in as ascription: expected Int, got Bool`).
2. Wrapper identity control:
   - `fn task_ascribe_keep(t: Task(Int)) -> Task(Int) { t as Task(Int) }`
     accepts (no diagnostics).
3. Grouped mismatch control:
   - `fn grouped_ascribe_narrow(g: GroupedFrame(Bool)) -> GroupedFrame(Int) { g as GroupedFrame(Int) }`
     rejects (`expected GroupedFrame(Int, keys: []), got GroupedFrame(Bool, keys: [])`).
4. Grouped identity control:
   - `fn grouped_ascribe_keep(g: GroupedFrame(Int)) -> GroupedFrame(Int) { g as GroupedFrame(Int) }`
     accepts (no diagnostics).
5. Dynamic narrowing control:
   - `fn dyn_to_int(x: Dynamic) -> Int { x }`
     rejects (`cannot use Dynamic value as Int` with `expect_type` guidance).

**Classify**: Agreement.

**Outcome**:
- Runtime behavior remains unchanged after the formal gate-semantics alignment;
  the relaxed declarative gate now matches the algorithmic/runtime acceptance
  criterion without introducing a new surface divergence.

### 2026-02-26: fully quantified wrapper/grouped infer-soundness lift re-probe

**Context**: After lifting wrapper/grouped expression-level `inferExpr`
soundness to fully quantified surfaces
(`inferWrapperExprWithAscriptionAtSite_sound`,
`inferGroupedTaggedExprWithAscriptionAtSite_sound`) and promoting
`AscriptionInferExprBridgeSliceAtSites` to a fully quantified soundness slice
across Dynamic/wrapper/grouped families, re-ran minimal controls.

**MCP tools used**: `diagnose`

**Probe**:
1. Wrapper identity control:
   - `fn task_ascribe_keep(t: Task(Int)) -> Task(Int) { t as Task(Int) }`
     accepts (no diagnostics).
2. Grouped identity control:
   - `fn grouped_ascribe_keep(g: GroupedFrame(Int)) -> GroupedFrame(Int) { g as GroupedFrame(Int) }`
     accepts (no diagnostics).
3. Dynamic narrowing control:
   - `fn dyn_to_int(x: Dynamic) -> Int { x }`
     rejects (`cannot use Dynamic value as Int`).

**Classify**: Agreement.

**Outcome**:
- No runtime surface change from the quantified soundness lift; formal
  ascription-inference contracts remain aligned with MCP-observed behavior.

### 2026-02-26: wrapper/grouped ascription-node iff lift re-probe

**Context**: After adding explicit wrapper/grouped ascription-node equivalence
theorems (`inferWrapperAscriptionAtSite_iff`,
`inferGroupedTaggedAscriptionAtSite_iff`) to close local algorithmic↔
declarative bridges on `.ascribe` nodes, re-checked mismatch controls.

**MCP tools used**: `diagnose`

**Probe**:
1. Wrapper mismatch control:
   - `fn task_ascribe_narrow(t: Task(Bool)) -> Task(Int) { t as Task(Int) }`
     rejects (`expected Int, got Bool`).
2. Grouped mismatch control:
   - `fn grouped_ascribe_narrow(g: GroupedFrame(Bool)) -> GroupedFrame(Int) { g as GroupedFrame(Int) }`
     rejects (`expected GroupedFrame(Int, keys: []), got GroupedFrame(Bool, keys: [])`).

**Classify**: Agreement.

**Outcome**:
- Runtime mismatch behavior remains stable after adding local `.ascribe` iff
  theorems for wrapper/grouped adapters.

### 2026-02-26: infer-iff slice lift re-probe (cross-family)

**Context**: After adding `AscriptionInferExprIffSliceAtSites` and lifting it
into both `BoundaryAscriptionBridgeSuiteAtSites` and
`boundary_surface_suite`, re-ran a minimal cross-family acceptance sanity set.

**MCP tools used**: `diagnose`

**Probe**:
1. Dynamic identity control:
   - `fn dyn_id(x: Dynamic) -> Dynamic { x }` accepts.
2. Wrapper identity control:
   - `fn task_ascribe_keep(t: Task(Int)) -> Task(Int) { t as Task(Int) }`
     accepts.
3. Grouped identity control:
   - `fn grouped_ascribe_keep(g: GroupedFrame(Int)) -> GroupedFrame(Int) { g as GroupedFrame(Int) }`
     accepts.

**Classify**: Agreement.

**Outcome**:
- No runtime behavior change observed after introducing the packaged
  cross-family `infer`↔`HasType` slice.

### 2026-02-26: algorithmic/declarative alignment slice quantification re-probe

**Context**: After generalizing
`AscriptionAlgorithmicDeclarativeAlignmentSliceAtSites` from witness-level
probes to fully quantified ascription-level equivalence (via
`inferDynamicAscriptionAtSite_iff`, `inferWrapperAscriptionAtSite_iff`,
`inferGroupedTaggedAscriptionAtSite_iff`), re-ran cross-family acceptance
controls.

**MCP tools used**: `diagnose`

**Probe**:
1. Dynamic identity control:
   - `fn dyn_id(x: Dynamic) -> Dynamic { x }` accepts.
2. Wrapper identity control:
   - `fn task_ascribe_keep(t: Task(Int)) -> Task(Int) { t as Task(Int) }`
     accepts.
3. Grouped identity control:
   - `fn grouped_ascribe_keep(g: GroupedFrame(Int)) -> GroupedFrame(Int) { g as GroupedFrame(Int) }`
     accepts.

**Classify**: Agreement.

**Outcome**:
- Runtime remains aligned after quantifying the remaining
  algorithmic↔declarative ascription alignment slice.

### 2026-02-26: boundary_surface_suite explicit alignment-lift probe

**Context**: After lifting
`AscriptionAlgorithmicDeclarativeAlignmentSliceAtSites` explicitly into
`boundary_surface_suite` (in addition to inclusion via
`BoundaryAscriptionBridgeSuiteAtSites`), ran a minimal sanity probe.

**MCP tools used**: `diagnose`

**Probe**:
1. Base-expression control:
   - `fn base_int() -> Int { 1 }` accepts.

**Classify**: Agreement.

**Outcome**:
- No runtime behavior change observed after the direct boundary-suite alignment
  lift.

### 2026-02-26: Typing-level `.base` conservativity lemma probe

**Context**: After adding Typing-level core lemmas
`inferExprWithAscription_base_eq` and `inferExprWithAscription_base_iff`
(showing `inferExprWithAscription` is conservative on `.base` expressions),
ran a base-expression sanity probe.

**MCP tools used**: `diagnose`

**Probe**:
1. Base identity control:
   - `fn id_int(x: Int) -> Int { x }` accepts.

**Classify**: Agreement.

**Outcome**:
- Runtime base-expression behavior remains unchanged, consistent with the new
  Typing-level conservativity lemmas.

### 2026-02-26: Typing-level `.ascribe` boundary-equivalence lemma probe

**Context**: After adding
`inferExprWithAscription_ascribe_iff_boundary` in `Rill/Typing.lean`
(linking algorithmic ascription inference directly to
`HasTypeAtCoreBoundary` on `.ascribe` nodes), re-ran an explicit ascription
acceptance control.

**MCP tools used**: `diagnose`

**Probe**:
1. Dynamic ascription identity control:
   - `fn ascribe_keep(x: Dynamic) -> Dynamic { x as Dynamic }` accepts.

**Classify**: Agreement.

**Outcome**:
- Runtime ascription acceptance remains aligned after adding the Typing-level
  `.ascribe` boundary-equivalence lemma.

### 2026-02-26: iff-slice implication theorem pass-through probe

**Context**: After adding
`ascriptionInferExprIffSliceAtSites_implies_bridge` and
`ascriptionInferExprIffSliceAtSites_implies_completeness` (making explicit that
the packaged `infer`↔`HasType` slice implies packaged soundness/completeness
slices), ran a wrapper acceptance control.

**MCP tools used**: `diagnose`

**Probe**:
1. Wrapper identity control:
   - `fn task_ascribe_keep(t: Task(Int)) -> Task(Int) { t as Task(Int) }`
     accepts.

**Classify**: Agreement.

**Outcome**:
- Runtime behavior remains unchanged after adding the slice-strength
  implication theorems.

### 2026-02-26: wrapper/grouped boundary-core iff refactor re-probe

**Context**: After adding boundary-level wrapper/grouped ascription iff
theorems (`inferWrapperAscriptionAtSite_iff_boundary`,
`inferGroupedTaggedAscriptionAtSite_iff_boundary`) and rewriting local
`inferWrapperAscriptionAtSite_iff`/`inferGroupedTaggedAscriptionAtSite_iff`
to derive from Typing-core boundary bridges, re-ran wrapper/grouped mismatch
and identity controls.

**MCP tools used**: `diagnose`

**Probe**:
1. Wrapper mismatch rejects:
   - `fn task_ascribe_narrow(t: Task(Bool)) -> Task(Int) { t as Task(Int) }`
     rejects (`expected Int, got Bool`).
2. Grouped mismatch rejects:
   - `fn grouped_ascribe_narrow(g: GroupedFrame(Bool)) -> GroupedFrame(Int) { g as GroupedFrame(Int) }`
     rejects (`expected GroupedFrame(Int, keys: []), got GroupedFrame(Bool, keys: [])`).
3. Wrapper identity accepts:
   - `fn task_ascribe_keep(t: Task(Int)) -> Task(Int) { t as Task(Int) }`
     accepts.
4. Grouped identity accepts:
   - `fn grouped_ascribe_keep(g: GroupedFrame(Int)) -> GroupedFrame(Int) { g as GroupedFrame(Int) }`
     accepts.

**Classify**: Agreement.

**Outcome**:
- Runtime ascription behavior remains stable after routing wrapper/grouped
  local iff proofs through Typing-core boundary contracts.

### 2026-02-26: WP7.5 nominal typing-bridge ascription re-probe

**Context**: After adding `Rill/Properties/NominalAdtTypingBridge.lean`
(`HasTypeAtNominalAdtBoundaryAtSite`,
`nominal_adt_typing_bridge_ascription`,
`NominalAdtTypingBridgeSliceAtSites`) and lifting that slice into
`boundary_surface_suite`, re-checked nominal ascription mismatch and identity
controls.

**MCP tools used**: `diagnose`

**Probe**:
1. ADT nominal mismatch rejects:
   - `type A = MkA(Int)\n type B = MkB(Int)\n fn bad(x: B) -> A { x as A }`
     rejects (`expected A, got B`).
2. Opaque nominal mismatch rejects:
   - `opaque UserId = Int\n opaque OrderId = Int\n fn bad(x: OrderId) -> UserId { x as UserId }`
     rejects (`expected UserId, got OrderId`).
3. ADT identity ascription accepts:
   - `type A = MkA(Int)\n fn ok(x: A) -> A { x as A }` accepts.
4. Opaque identity ascription accepts:
   - `opaque UserId = Int\n fn ok(x: UserId) -> UserId { x as UserId }`
     accepts.

**Classify**: Agreement.

**Outcome**:
- Runtime nominal ascription behavior matches the new nominal typing-bridge
  slice (distinct-name rejection, identity acceptance).

### 2026-02-26: WP7.5 nominal algorithmic-ascription slice re-probe

**Context**: After adding the minimal algorithmic nominal ascription checker
and equivalence slice in `NominalAdtTypingBridge`
(`nominalAscriptionAllowsBoolAtSite`, `inferNominalAscriptionAtSite`,
`inferNominalAscriptionAtSite_iff`,
`NominalAdtAscriptionAlgorithmicSliceAtSite`) and lifting it into
`boundary_surface_suite`, re-ran nominal `as` controls.

**MCP tools used**: `diagnose`

**Probe**:
1. ADT nominal mismatch rejects:
   - `type A = MkA(Int)\n type B = MkB(Int)\n fn bad(x: B) -> A { x as A }`
     rejects (`expected A, got B`).
2. Opaque nominal mismatch rejects:
   - `opaque UserId = Int\n opaque OrderId = Int\n fn bad(x: OrderId) -> UserId { x as UserId }`
     rejects (`expected UserId, got OrderId`).
3. ADT identity ascription accepts:
   - `type A = MkA(Int)\n fn ok(x: A) -> A { x as A }` accepts.
4. Opaque identity ascription accepts:
   - `opaque UserId = Int\n fn ok(x: UserId) -> UserId { x as UserId }`
     accepts.

**Classify**: Agreement.

**Outcome**:
- Runtime nominal `as` behavior remains aligned after adding the algorithmic
  nominal ascription checker/equivalence slice.

### 2026-02-26: effect-row annotation boundary re-probe for WF ladder packaging

**Context**: After extending the Phase-1 effect-row WF surface
(`WfSubstitution`/`WfGeneralize` wrappers and `WfEffectRowLadder` packaging),
re-probed `kea-mcp` for declared effect-row preservation and mismatch
rejection to keep Lean-side assumptions grounded in live behavior.

**MCP tools used**: `reset_session`, `type_check`, `get_type`, `diagnose`

**Probe**:
1. Declared effect row is preserved:
   - `type_check` on
     `effect Log ...; fn write(msg: String) -[Log]> Unit; Log.log(msg)`
     returns `ok` with binding type `(String) -[Log]> ()`.
   - `get_type` on the same declarations returns `(String) -[Log]> ()`.
2. Pure control remains pure:
   - `type_check "fn id(x: Int) -> Int\n  x"` returns `ok` with `(Int) -> Int`.
3. Too-weak declared effect row is rejected:
   - `type_check` on
     `effect Log ...; fn wrong(msg: String) -[IO]> Unit; Log.log(msg)`
     returns `error` with
     `declared effect '[IO]' is too weak; body requires '[Log]'`.
   - `diagnose` on the same snippet reports structured `type_mismatch`
     diagnostics with the same message.

**Classify**: Agreement.

**Outcome**:
- Runtime effect-row annotation behavior matches the Lean-side WF ladder
  assumptions used by `functionEff` substitution/generalize/instantiate
  packaging.

**Impact**:
- Confirms no Lean↔MCP divergence for current Phase-1 effect-row WF theorem
  surfaces before moving further toward Phase-2 handler-specific theorems.

### 2026-02-26: WfUnifyExtends branch-contract re-probe after MCP refresh

**Context**: After adding branch-complete full-contract wrappers in
`Kea/Properties/WfUnifyExtends` (`no-update`, `single-bind`, `open-open fresh`)
and restarting `kea-mcp`, re-probed representative row-unification boundary
cases to validate Lean preconditions against the live implementation.

**MCP tools used**: `reset_session`, `get_type`, `type_check`, `diagnose`

**Probe**:
1. No-update shape (identity over closed row):
   - `get_type "(r -> r)(#{ a: 1 })"` -> `#{ a: Int }`.
2. Single-bind shape (required field projection with extras):
   - `get_type "(r -> r.a)(#{ a: 1, b: true })"` -> `Int`.
3. Open-open shape (independent projection composition):
   - `get_type "((x -> y -> #(x.a, y.b))(#{ a: 1, c: true }))(#{ b: \"u\", d: 2 })"`
     -> `#(Int, String)`.
4. Missing-field boundary:
   - `type_check "(r -> r.a)(#{ b: true })"` -> `error` (`missing_field`,
     missing `a`).
5. Type-mismatch boundary:
   - `type_check "(r -> r.a + 1)(#{ a: \"x\" })"` -> `error` (`type_mismatch`,
     field `a` expected `Int`, got `String`).
6. Diagnostic shape sanity for mismatch:
   - `diagnose "(r -> r.a + 1)(#{ a: \"x\" })"` -> structured
     `type_mismatch` diagnostics for field `a`.

**Classify**: Agreement.

**Outcome**:
- Runtime row behavior matches the current WF-contract theorem surface for the
  branch shapes consumed by `unifyRows_contract_full_wf`.

**Impact**:
- Confirms no Lean↔MCP divergence for the latest Phase-1 WF contract wrappers.
- Keeps Phase-1 progression on track toward full-language WF coverage before
  Phase-2 handler/effect theorems.

### 2026-02-26: effect-row annotation re-probe on restarted MCP binary

**Context**: After restarting `kea-mcp` and extending
`WfEffectRowLadder` with full-state bundle + projection helpers, re-ran the
effect-row boundary probes to confirm runtime behavior still matches the
Phase-1 WF ladder assumptions.

**MCP tools used**: `reset_session`, `type_check`, `get_type`, `diagnose`

**Probe**:
1. Declared effect row is preserved (updated parser surface):
   - `type_check` on
     `effect Log; fn log(msg: String) -> Unit; fn emit(msg: String) -[Log]> Unit; Log.log(msg)`
     returns `ok` with `(String) -[Log]> ()`.
   - `get_type` on the same declarations returns `(String) -[Log]> ()`.
2. Pure control remains pure:
   - `type_check "fn id(x: Int) -> Int\n  x"` returns `ok` with `(Int) -> Int`.
3. Too-weak declared effect row is rejected:
   - `type_check` on
     `effect Log; fn log(msg: String) -> Unit; fn wrong(msg: String) -[IO]> Unit; Log.log(msg)`
     returns `error` with
     `declared effect '[IO]' is too weak; body requires '[Log]'`.
   - `diagnose` on the same snippet reports structured `type_mismatch`
     diagnostics with the same message.

**Classify**: Agreement (with a precondition update).

**Outcome**:
- Runtime behavior remains aligned with the Lean-side `functionEff` WF ladder
  assumptions.
- Probe snippets needed parser-surface refresh (`effect` op signature uses
  `fn ... -> Unit`), but this is syntax precondition drift, not a semantic
  Lean↔MCP divergence.

### 2026-02-26: higher-order effect propagation probe (possible divergence)

**Context**: After adding symmetric var-left/var-right `unify` bridge wrappers
in `WfUnifyExtends` and corresponding `WfEffectRowLadder` bundle surfaces,
probed higher-order `functionEff` call paths to sanity-check runtime effect
propagation against the formal intent.

**MCP tools used**: `reset_session`, `type_check`, `diagnose`

**Probe**:
1. Syntax/typing precondition updates on restarted MCP surface:
   - Named `fn` declarations require parameter annotations (`E0801`).
   - Bare lambdas (`x -> ...`) are rejected; parser requires `|x| -> ...`.
2. Higher-order call path:
   - `type_check` on
     `effect Log; fn log(msg: String) -> Unit; fn run() -[Log]> Unit { let apply = |f| -> |x| -> f(x); let logger = |y| -> Log.log(y); apply(logger)(\"x\") }`
     returns `ok` with `run : () -[e0]> ()`.
   - Same shape with `fn pure_run() -> Unit` also returns `ok` with
     `pure_run : () -[e0]> ()`.
3. Direct control:
   - `type_check` on
     `fn pure_bad() -> Unit { let logger = |y| -> Log.log(y); logger(\"x\") }`
     returns `ok` with `pure_bad : () -[Log]> ()`.

**Classify**: Possible divergence (effect propagation through higher-order
application appears under-constrained in this probe shape).

**Outcome**:
- Direct local invocation of the effectful closure propagates `Log` as expected.
- Through the higher-order `apply` combinator, the outer function effect
  remains polymorphic (`e0`) instead of concretely reflecting `Log`.
- This looks like an implementation-side effect-constraint propagation gap
  in higher-order unification/inference paths, not a parser-only issue.

### 2026-02-26: higher-order effect propagation re-probe after binary restart

**Context**: Re-ran the same higher-order `functionEff` propagation probes
after user-provided `kea-mcp` restart with the latest binary, to verify
whether the previous divergence report was resolved.

**MCP tools used**: `reset_session`, `type_check`, `diagnose`

**Probe**:
1. Higher-order wrapper path (declared effectful outer fn):
   - `type_check` on
     `effect Log; fn log(msg: String) -> Unit; fn run() -[Log]> Unit { let apply = |f| -> |x| -> f(x); let logger = |y| -> Log.log(y); apply(logger)(\"x\") }`
     returns `ok` with binding `run : () -[e0]> ()`.
2. Same higher-order wrapper path (declared pure outer fn):
   - `type_check` on
     `effect Log; fn log(msg: String) -> Unit; fn pure_run() -> Unit { let apply = |f| -> |x| -> f(x); let logger = |y| -> Log.log(y); apply(logger)(\"x\") }`
     returns `ok` with binding `pure_run : () -[e0]> ()`.
   - `diagnose` on the same snippet reports no diagnostics.
3. Direct control:
   - `type_check` on
     `effect Log; fn log(msg: String) -> Unit; fn pure_bad() -> Unit { let logger = |y| -> Log.log(y); logger(\"x\") }`
     returns `ok` with binding `pure_bad : () -[Log]> ()`.

**Classify**: Divergence persists.

**Outcome**:
- Restarted binary behavior matches the prior divergence report.
- Direct local calls propagate `Log`; higher-order wrapper calls remain
  under-constrained (`e0`) and do not enforce/reflect `Log` at the outer
  function boundary in this probe shape.

### 2026-02-26: higher-order effect divergence split (annotated vs unannotated)

**Context**: Follow-up probe to separate the two suspected failure modes in
higher-order `functionEff` propagation: (a) annotated function parameter path
and (b) unannotated inference path.

**MCP tools used**: `reset_session`, `type_check`, `diagnose`

**Probe**:
1. Annotated parameter path:
   - `type_check` on
     `effect Log; fn log(msg: String) -> Unit; fn anno_run() -[Log]> Unit { let apply = |f: fn(String) -[Log]> Unit| -> |x| -> f(x); let logger = |y| -> Log.log(y); apply(logger)(\"x\") }`
     returns `error` with `missing_field` / `the function is missing field Log`.
   - `diagnose` on the same snippet reports the same `missing_field` result.
2. Unannotated parameter path:
   - `type_check` on
     `effect Log; fn log(msg: String) -> Unit; fn unanno_run() -[Log]> Unit { let apply = |f| -> |x| -> f(x); let logger = |y| -> Log.log(y); apply(logger)(\"x\") }`
     returns `ok` with binding `unanno_run : () -[e0]> ()`.

**Classify**: Divergence persists, now split into two distinct sub-bugs.

**Outcome**:
- Annotated path indicates effect-row annotations on function parameters are
  entering row-field unification (`missing field Log`) rather than effect-row
  unification.
- Unannotated path still leaves the higher-order effect variable unconstrained
  (`e0`) through the curried application chain.
- These are separate manifestations in the same higher-order/effect-unify
  family and should be tracked as distinct implementation defects.

### 2026-02-26: higher-order effect divergence closure re-probe

**Context**: Re-ran the exact split probes (annotated and unannotated
higher-order application) against the latest restarted `kea-mcp` binary to
verify whether the previously logged divergence family is fixed.

**MCP tools used**: `reset_session`, `type_check`, `diagnose`

**Probe**:
1. Annotated path (previously `missing_field Log`):
   - `type_check` on
     `fn anno_run() -[Log]> Unit { let apply = |f: fn(String) -[Log]> Unit| -> |x| -> f(x); ...; apply(logger)(\"x\") }`
     now returns `ok` with `anno_run : () -[Log]> ()`.
   - `diagnose` on the same snippet reports no diagnostics.
2. Unannotated path (previously `e0` leak):
   - `type_check` on
     `fn unanno_run() -[Log]> Unit { let apply = |f| -> |x| -> f(x); ...; apply(logger)(\"x\") }`
     now returns `ok` with `unanno_run : () -[Log]> ()`.
3. Additional check:
   - `type_check` on `fn pure_run() -> Unit { ... apply(logger)(\"x\") }` returns
     `pure_run : () -[Log]> ()`, matching direct control
     `fn pure_bad() -> Unit { logger(\"x\") } -> () -[Log]> ()`.

**Classify**: Agreement (divergence resolved).

**Outcome**:
- The annotated path no longer misroutes to row-field unification.
- The unannotated higher-order chain no longer leaves effect variables
  unconstrained (`e0`); `Log` is propagated as expected.

### 2026-02-26: handler effect-removal kickoff probes (with overlap divergence)

**Context**: Phase-2 kickoff for handler effect typing. Lean side introduced a
row-level elimination model (`EffectRow.handleRemove`) with capstone theorems
`handle_removes_effect` and `handle_preserves_other_effects` for the removal
step. Probes checked runtime alignment on pure-removal and residual-preservation
cases, plus overlap behavior where handler-body effects and residual effects
share labels.

**MCP tools used**: `initialize`, `notifications/initialized`, `tools/list`,
`tools/call` (`reset_session`, `type_check`) via direct `kea-mcp` stdio probe.

**Predict (Lean side)**:
1. Handling `Log` in a `Log`-only computation yields pure (`[]`).
2. Handling `Log` in `[IO, Log]` with pure handler body yields `[IO]`
   (preserve other effects).
3. In full handler composition (future theorem slice), overlap between residual
   and handler-body effects should normalize as a row (no duplicate labels).

**Probe (Rust side via kea-mcp)**:
1. Pure-removal case:
   - `fn run() -> Unit` with `handle Log.log("x") ...` returns `run : () -> ()`.
2. Preserve-other, non-overlap case:
   - `mixed : () -[IO, Log]> ()`, `handled : () -[IO]> ()` with
     `handle mixed()` and `Log` clause body `()`.
3. Overlap case (residual `IO` + handler body emits `IO`):
   - inferred binding `handled : () -[IO, IO]> ()`.
   - declaring `-[IO]>` is rejected as too weak (`body requires [IO, IO]`).
   - declaring duplicate annotation `-[IO, IO]>` is rejected by parser as
     invalid effect-row contract syntax.

**Classify**: Mixed.
- Agreement for removal and non-overlap preservation.
- Divergence for overlap normalization: implementation currently materializes
  duplicate effect labels in inferred rows.

**Outcome**:
- Phase-2 theorem kickoff remains valid for the removal slice.
- Full handler-composition theorem work now needs an explicit normalization
  precondition or an implementation fix to canonicalize overlapping effect rows.

**Impact**:
- Logged as a Lean↔MCP semantic divergence for Phase-2 handler composition.
- `Kea/Properties/HandlerEffectRemoval.lean` stays scoped to the elimination
  slice while overlap normalization is resolved.

### 2026-02-26: phase-2 continuation under spec-normalized union precondition

**Context**: Follow-through after the overlap divergence above. The formal track
continues by adopting the spec's idempotent-union semantics at the row level,
instead of mirroring current duplicate-label runtime behavior.

**MCP tools used**: none (uses immediately prior probe evidence in this log).

**Lean side**:
- Added row-level idempotent union primitives:
  - `RowFields.insertIfAbsent`
  - `RowFields.unionIdem`
- Added normalized handler composition:
  - `EffectRow.handleComposeNormalized`
- Proved composition surfaces:
  - `handle_adds_handler_effects`
  - `handle_preserves_other_effects_normalized`
  - `handle_removes_effect_normalized_of_handler_absent`
  - `handleComposeNormalized_preserves_wellFormed`

**Rust side (from prior probe context)**:
- Non-overlap removal/preservation behavior aligns with spec-normalized model.
- Overlap still yields duplicate inferred labels (`[IO, IO]`) in runtime typing.

**Classify**: Preconditioned agreement.

**Outcome**:
- Formal proofs proceed under normalized/idempotent union semantics (the spec).
- Implementation divergence remains explicitly documented as a normalization
  gap rather than encoded into theorem statements.

**Impact**:
- Proofs remain stable and reusable when implementation-side dedup lands.
- The overlap normalization fix in implementation should make the current
  preconditions trivially satisfied.

### 2026-02-26: nested same-target handler consequences on normalized model

**Context**: Continued Phase-2 theorem work on top of the normalized-idempotent
composition model, focusing on nested same-target handler consequences.

**MCP tools used**: none (proof-layer extension over previously classified
preconditioned agreement).

**Lean side**:
- Added `handleComposeNormalized_preserves_row_tail`.
- Added `nested_same_target_outer_removal_noop_of_inner_absent`.
- Added `nested_same_target_remains_absent_of_outer_absent`.

**Classify**: Agreement under existing preconditions.

**Outcome**:
- Nested same-target behavior now has explicit theorem surfaces in the formal
  model without coupling to current implementation duplicate-label behavior.

### 2026-02-26: resume linearity scaffold (proof-layer, no new runtime probes)

**Context**: Began the `resume_at_most_once` theorem track with an abstract
compositional summary model (`ResumeUse`) in
`Kea/Properties/ResumeLinearity.lean`.

**MCP tools used**: none (proof-layer scaffold; no direct runtime-facing claim
changes yet).

**Lean side**:
- Added `ResumeUse` (`zero | one | many`) and `ResumeUse.atMostOnce`.
- Added saturating composition `ResumeUse.combine`.
- Proved exclusivity/zero-side preservation lemmas and named
  `resume_at_most_once`/`resume_at_most_once_sound` surfaces.

**Classify**: N/A (no new probe required at this abstraction layer).

**Outcome**:
- Resume-linearity theorem work can now proceed incrementally by connecting
  concrete handler typing constraints to this summary algebra.

### 2026-02-26: resume combine characterization (proof-layer refinement)

**Context**: Refined the resume scaffold with a complete condition for when
composed summaries stay at-most-once.

**MCP tools used**: none (proof-layer refinement; no new runtime probes).

**Lean side**:
- Added `resume_combine_atMostOnce_iff`.
- Added `resume_combine_atMostOnce_implies_one_side_zero`.
- Added `resume_combine_one_one_not_atMostOnce`.

**Classify**: N/A (no direct runtime-facing claim delta at this layer).

**Outcome**:
- The scaffold now has a direct theorem hook for enforcing branch exclusivity
  in future concrete resume-typing proofs.

### 2026-02-26: overlap-normalization divergence closure on restarted kea-mcp

**Context**: Re-checked the previously logged overlap-normalization divergence
after user restart with the latest `kea-mcp` binary.

**MCP tools used**: direct `kea-mcp` stdio (`initialize`,
`notifications/initialized`, `tools/call` with `reset_session`, `type_check`,
`diagnose`).

**Probe**:
1. User-provided overlap case:
   - `body_fn : () -[Log, Trace]> ()`
   - `overlap_case : () -[Trace]> ()`
   - `diagnose` reports no diagnostics.
2. Prior duplicate-label regression shape:
   - `mixed : () -[IO, Log]> ()`
   - `handled : () -[IO]> ()` (previously observed as `()-[IO, IO]> ()`)
   - `diagnose` reports no diagnostics.
3. Non-overlap control remains stable:
   - `handled : () -[IO]> ()`
   - `diagnose` reports no diagnostics.

**Classify**: Agreement (divergence closed).

**Outcome**:
- Implementation now normalizes overlap unions in the probed cases.
- The earlier “overlap-normalization precondition” for spec/model alignment is
  now satisfied by runtime behavior on current probes.

**Impact**:
- Phase-2 formalization can treat idempotent-union alignment as observed
  runtime behavior (not only a spec-side assumption) for these handler cases.

### 2026-02-26: resume-linearity runtime alignment probes (E0012)

**Context**: Validate the new `ResumeLinearity` branch legality surfaces against
current `kea-mcp` behavior, especially "at most once" enforcement in handler
clauses.

**MCP tools used**: direct `kea-mcp` stdio (`initialize`,
`notifications/initialized`, `tools/call` with `reset_session`, `type_check`,
`diagnose`).

**Probe**:
1. Zero-resume clause:
   - `fn zero_ok() -> Unit` with handler clause body `()`
   - result: `ok`, `zero_ok : () -> ()`, no diagnostics.
2. Sequential double-resume:
   - clause body `resume(); resume()`
   - result: `error`, `E0012`, message `handler clause may resume at most once`.
3. Both-branches resume:
   - clause body `if true ... else ...` with `resume()` in both branches
   - result: `error`, `E0012`, same message.

**Classify**: Agreement.

**Lean side**:
- Matches `ResumeUse` model:
  - zero-resume is legal (`resume_atMostOnce_zero`)
  - two-resume compositions are rejected (`resume_combine_one_one_not_atMostOnce`,
    `resume_conditional_forbids_two_resuming_branches`).

**Outcome**:
- Current runtime behavior aligns with the abstract at-most-once branch model
  used in `Kea/Properties/ResumeLinearity.lean`.

### 2026-02-26: handler-typing integration contract layer (proof-only step)

**Context**: Added a formal integration surface that combines effect-removal
and resume-linearity assumptions into one clause-level contract.

**MCP tools used**: none (proof-only composition of previously validated
surfaces).

**Lean side**:
- Added `Kea/Properties/HandlerTypingContracts.lean`.
- Introduced `HandleClauseContract` and `wellTypedSlice`.
- Proved bridge theorems:
  - `wellTypedSlice_implies_handled_removed`
  - `branch_linearity_ok_of_exclusive`
  - `loop_linearity_requires_zero`

**Classify**: N/A (no new runtime-facing claim introduced).

**Outcome**:
- Phase-2 now has an explicit integration layer to attach future concrete
  handler typing judgments without re-deriving effect/resume bridges.

### 2026-02-26: handler-typing contract refinement (proof-only)

**Context**: Refined `HandlerTypingContracts` from abstract summaries to
concrete clause-level premises and result-effect assembly, then revalidated the
formal workspace build.

**MCP tools used**: none (proof-only refinement; no new runtime-facing claim).

**Lean side**:
- Extended `HandleClauseContract` with `thenEffects` and
  `clauseCoverageComplete`.
- Added explicit assembly path
  (`resultEffectsCore` -> `applyThenEffects` -> `resultEffects`).
- Added `coverageOk`/`linearityOk`, no-reintroduction checks
  (`noHandledReintroHandler`, `noHandledReintroThen`), and updated
  `wellTypedSlice` accordingly.
- Added resume provenance extraction
  (`linearityOk_implies_resumeProvenance`,
  `wellTypedSlice_implies_resumeProvenance`).
- Verified with `cd formal && lake build` (pass).

**Classify**: N/A (no runtime probe delta).

**Outcome**:
- The handler typing integration layer now mirrors concrete typing premises
  closely enough to start Fail-as-zero-resume and Fail/Result equivalence
  proofs without reworking the contract shape.

### 2026-02-26: fail/result contract kickoff (proof-only)

**Context**: Added the first Fail-specialized contract layer on top of the
refined handler-typing slice, targeting Fail-as-zero-resume and Result-lowering
surfaces.

**MCP tools used**: none (proof-only contract composition; no new runtime claim
introduced beyond previously logged handler/resume alignment probes).

**Lean side**:
- Added `Kea/Properties/FailResultContracts.lean`.
- Defined `failAsZeroResume` and `resultLowering`.
- Added `FailResultContract` with capstone consequences:
  - `failResultContract_sound` (Fail removed from result effects, resume
    provenance available, lowered return type is `Result`)
  - `failResultContract_loopLegal` (zero-resume loop legality bridge).
- Imported the module in `formal/Kea.lean`.
- Verified with `cd formal && lake build` (pass).

**Classify**: N/A (proof-only step).

**Outcome**:
- Phase-2 now has an explicit Fail/Result contract surface to extend into
  stronger typing-equivalence theorems.

### 2026-02-26: fail/result typing-equivalence slice extension (proof-only)

**Context**: Extended the new Fail/Result contract module from clause-level
contract consequences to explicit function-type lowering/equivalence surfaces.

**MCP tools used**: none (proof-only extension; no new runtime-facing claim
delta).

**Lean side**:
- Added effect-row lowering surface `lowerFailEffects` with:
  - `lowerFailEffects_removes_fail`
  - `lowerFailEffects_preserves_other`
  - `lowerFailEffects_noop_of_absent`
- Added function-type lowering surface `lowerFailFunctionType` with
  no-op-when-absent theorem `lowerFailFunctionType_noop_effect_of_absent`.
- Added equivalence relation `failResultFunctionEquivalent` and projection
  theorem `failResultFunctionEquivalent_implies_result_return`.
- Verified with `cd formal && lake build` (pass).

**Classify**: N/A (proof-only step).

**Outcome**:
- The Fail/Result track now has an explicit typing-equivalence slice suitable
  for reuse in the next effect-polymorphism soundness contract layer.

### 2026-02-26: effect-polymorphism soundness contract kickoff (proof-only)

**Context**: Added a dedicated Phase-2 module to package polymorphic effect-row
soundness guarantees for Fail lowering.

**MCP tools used**: none (proof-only theorem packaging; no new runtime-facing
claim delta).

**Lean side**:
- Added `Kea/Properties/EffectPolymorphismSoundness.lean`.
- Defined reusable relations:
  - `rowTailStable`
  - `labelsPreservedExcept`
- Proved row-level soundness for Fail lowering:
  - `lowerFailEffects_rowTailStable`
  - `lowerFailEffects_labelsPreservedExceptFail`
  - `lowerFailEffects_failRemoved`
  - `lowerFailEffects_effectPoly_sound`
- Added polymorphic function contract surface
  (`EffectPolyFailLoweringContract`) and capstone theorems:
  - `effectPolyFailLowering_sound`
  - `effectPolyFailLowering_noop_if_fail_absent`
- Imported module in `formal/Kea.lean`.
- Verified with `cd formal && lake build` (pass).

**Classify**: N/A (proof-only step).

**Outcome**:
- Effect-polymorphism soundness now has an explicit reusable theorem surface
  bridging Fail lowering with row-tail-preserving polymorphic effects.

### 2026-02-26: effect-polymorphism concrete schema bridge (proof-only)

**Context**: Connected the effect-polymorphism soundness surfaces to concrete
handler-typing premises so downstream proofs can start from realistic schema
assumptions (`wellTypedSlice` + Fail-zero-resume).

**MCP tools used**: none (proof-only bridge; no new runtime-facing claim
introduced).

**Lean side**:
- Extended `Kea/Properties/EffectPolymorphismSoundness.lean` with:
  - `EffectPolyHandlerSchema`
  - `effectPolyHandlerSchema_sound`
  - `effectPolyHandlerSchema_noop_if_fail_absent`
- The bridge theorem packages:
  - clause-level handled-effect removal from `HandleClauseContract`
  - polymorphic function-type Fail-lowering guarantees
  into one reusable surface.
- Verified with `cd formal && lake build` (pass).

**Classify**: N/A (proof-only step).

**Outcome**:
- Concrete handler typing premises now map directly to polymorphic Fail-lowered
  function guarantees without manual theorem composition at call sites.

### 2026-02-26: effect-polymorphism probe sweep (Fail-absent divergence)

**Context**: Ran targeted MCP probes for the new polymorphic Fail-lowering
theorem slice.

**MCP tools used**: direct `kea-mcp` stdio (`initialize`,
`notifications/initialized`, `tools/call` with `reset_session`, `get_type`,
`diagnose`).

**Probe**:
1. Residual-effect preservation with present `Fail`:
   - `body : () -[Log, Fail]> Int`
   - `wrapped : () -[Log]> Result(Int, String)` via `catch body()`
   - result: `ok`, inferred `() -[Log]> Result(Int, String)`, no diagnostics.
2. Higher-order polymorphic shape:
   - `wrap_poly : (fn() -[Log, Fail]> Int) -[Log]> Result(Int, String)`
     via `catch f()`
   - result: `ok`, inferred `(() -[Fail, Log]> Int) -[Log]> Result(Int, String)`,
     no diagnostics.
3. Fail-absent case (`pureish : () -[Log]> Int`) via `catch pureish()`:
   - declared `wrapped_no_fail : () -[Log]> Result(Int, String)` ->
     rejected (`E0001`): declared `[Log]` too weak, body requires `[IO]`.
   - declared `wrapped_no_fail : () -[IO, Log]> Result(Int, String)` ->
     accepted, but inferred type normalizes to `() -[IO]> Result(Int, String)`
     (residual `Log` not preserved).

**Classify**: Divergence (Lean model vs MCP behavior).

**Lean side impacted**:
- `FailResultContracts.lowerFailFunctionType_noop_effect_of_absent`
- `EffectPolymorphismSoundness.effectPolyFailLowering_noop_if_fail_absent`
- `EffectPolymorphismSoundness.effectPolyHandlerSchema_noop_if_fail_absent`

These remain valid as spec/model theorems for idempotent/no-op Fail-removal, but
do not currently match observed MCP behavior on Fail-absent `catch` paths.

**Outcome**:
- Marked a concrete divergence to resolve before claiming runtime alignment for
  Fail-absent no-op polymorphism properties.

### 2026-02-26: fail-absent catch divergence closure (post-fix re-probe)

**Context**: Re-checked the previously logged Fail-absent `catch` divergence
after implementation fix `cbb70b3` (`fix: reject catch on fail-absent bodies`).

**MCP tools used**: direct `kea-mcp` stdio (`initialize`,
`notifications/initialized`, `tools/call` with `reset_session`, `get_type`,
`diagnose`).

**Probe**:
1. Fail-absent case:
   - `pureish : () -[Log]> Int`
   - `wrapped_no_fail : () -[Log]> Result(Int, String)` via `catch pureish()`
   - result: rejected with `E0012`, message
     `expression cannot fail; catch is unnecessary`.
2. Fail-present control:
   - `body : () -[Log, Fail]> Int`
   - `wrapped : () -[Log]> Result(Int, String)` via `catch body()`
   - result: `ok`, inferred `() -[Log]> Result(Int, String)`, no diagnostics.

**Classify**: Agreement (divergence closed).

**Lean side impact**:
- `lowerFailFunctionType_noop_effect_of_absent` and downstream no-op-if-absent
  theorems now align as vacuous runtime cases (the fail-absent `catch` program
  class is rejected), rather than a runtime counterexample surface.

**Outcome**:
- Restores runtime alignment for the Phase-2 Fail/Result + effect-polymorphism
  slice and removes the prior "wait for fix" caveat.

### 2026-02-26: catch-admissibility theorem packaging (proof-only)

**Context**: After divergence closure, promoted fail-presence/fail-absence into
explicit formal preconditions so runtime `E0012` behavior is represented in
theorem surfaces (not only in prose/log notes).

**MCP tools used**: none (proof-layer packaging that relies on the immediately
preceding divergence-closure probes).

**Lean side**:
- Extended `Kea/Properties/FailResultContracts.lean` with:
  - `catchAdmissible`
  - `catchUnnecessary`
  - `catchAdmissible_or_unnecessary`
  - `catchUnnecessary_implies_not_admissible`
  - `lowerFailFunctionType_noop_if_catch_unnecessary`
- Extended `Kea/Properties/EffectPolymorphismSoundness.lean` with
  admissibility-gated wrappers and exclusivity bridges:
  - `effectPolyFailLowering_sound_of_catchAdmissible`
  - `effectPolyFailLowering_noop_if_catch_unnecessary`
  - `catchUnnecessary_implies_no_admissible_poly_lowering`
  - `effectPolyHandlerSchema_noop_if_catch_unnecessary`
  - `catchUnnecessary_implies_no_admissible_schema`
- Verified with `cd formal && lake build` (pass).

**Classify**: N/A (proof-only step on top of already verified runtime behavior).

**Outcome**:
- Phase-2 theorem entrypoints now carry the same admissibility boundary as the
runtime (`catch` requires Fail presence), preventing future drift between model
claims and executable behavior.

### 2026-02-26: admissible-schema capstone entrypoints (proof-only)

**Context**: Strengthened the admissibility packaging by introducing explicit
runtime-aligned wrapper structures, so downstream proofs cannot accidentally
instantiate fail-absent `catch` paths.

**MCP tools used**: none (proof-only surface refinement over already verified
`E0012` runtime behavior).

**Lean side**:
- Extended `Kea/Properties/EffectPolymorphismSoundness.lean` with:
  - `AdmissibleEffectPolyFailLoweringContract`
  - `AdmissibleEffectPolyHandlerSchema`
  - `admissibleEffectPolyFailLowering_sound`
  - `admissibleEffectPolyHandlerSchema_sound`
  - `admissibleEffectPolyHandlerSchema_not_unnecessary`
- These wrappers require `catchAdmissible` as a field-level premise, so capstone
  theorem entrypoints are runtime-aligned by construction.
- Verified with `cd formal && lake build` (pass).

**Classify**: N/A (proof-only step).

**Outcome**:
- Phase-2 proofs now have a clean admissible-only API surface, reducing
call-site precondition threading and removing accidental dependence on
inadmissible fail-absent paths.

### 2026-02-26: admissible premise adapters (proof-only)

**Context**: Added one-hop adapters from raw premises to admissible capstone
theorems, so callers can start from existing handler-typing assumptions
directly.

**MCP tools used**: none (proof-only API ergonomics layer; no new runtime
claim).

**Lean side**:
- Extended `Kea/Properties/EffectPolymorphismSoundness.lean` with:
  - `mkAdmissibleEffectPolyFailLoweringContract`
  - `admissibleEffectPolyFailLowering_sound_of_premises`
  - `mkAdmissibleEffectPolyHandlerSchema`
  - `admissibleEffectPolyHandlerSchema_sound_of_premises`
- Verified with `cd formal && lake build` (pass).

**Classify**: N/A (proof-only step).

**Outcome**:
- Downstream proofs can now discharge admissible Fail-lowering capstones from
  premise bundles in a single theorem call, with no manual structure wiring.

### 2026-02-26: admissible one-hop projections (proof-only)

**Context**: Added direct projection helpers so individual guarantees can be
consumed without destructuring full capstone conjunctions.

**MCP tools used**: none (proof-only API decomposition layer).

**Lean side**:
- Extended `Kea/Properties/EffectPolymorphismSoundness.lean` with one-hop
  projections from admissible assumptions:
  - `admissibleEffectPolyFailLowering_rowTailStable`
  - `admissibleEffectPolyFailLowering_preserves_nonFail`
  - `admissibleEffectPolyFailLowering_failRemoved`
  - `admissibleEffectPolyHandlerSchema_rowTailStable`
  - `admissibleEffectPolyHandlerSchema_preserves_nonFail`
  - `admissibleEffectPolyHandlerSchema_failRemoved_in_lowered_effects`
- Verified with `cd formal && lake build` (pass).

**Classify**: N/A (proof-only step).

**Outcome**:
- Admissible capstones now support clean one-hop chaining across downstream
  proofs that need only one consequence facet at a time.

### 2026-02-26: admissible named bundles (proof-only)

**Context**: Added stable named bundle outputs for admissible capstone results,
mirroring the earlier Phase-1 bundle ergonomics pattern.

**MCP tools used**: none (proof-only packaging layer).

**Lean side**:
- Extended `Kea/Properties/EffectPolymorphismSoundness.lean` with:
  - `AdmissibleEffectPolyLoweringBundle`
  - `AdmissibleEffectPolyHandlerBundle`
  - `admissibleEffectPolyFailLowering_bundle` (+ projections)
  - `admissibleEffectPolyHandler_bundle` (+ projections)
- Bundle constructors are `noncomputable` (`Classical.choose`) over existing
  existential capstone theorems.
- Verified with `cd formal && lake build` (pass).

**Classify**: N/A (proof-only step).

**Outcome**:
- Downstream formal work can now reference one stable bundle name instead of
  repeatedly reconstructing conjunction/exists shapes from raw capstones.

### 2026-02-26: admissibility partition refinement (proof-only)

**Context**: Added explicit branch-partition lemmas so theorem consumers can
reason about admissible vs unnecessary `catch` paths without re-deriving
boolean case splits.

**MCP tools used**: none (proof-only refinement over already logged `E0012`
runtime behavior).

**Lean side**:
- Extended `Kea/Properties/FailResultContracts.lean` with:
  - `catchAdmissible_implies_not_unnecessary`
  - `catchAdmissible_xor_unnecessary`
- Extended `Kea/Properties/EffectPolymorphismSoundness.lean` with:
  - `admissibleEffectPolyFailLowering_admissibility_branch`
  - `admissibleEffectPolyHandlerSchema_admissibility_branch`
- Verified with `cd formal && lake build` (pass).

**Classify**: N/A (proof-only step).

**Outcome**:
- Admissibility branch classification is now first-class and one-hop, aligned
  with the runtime “catch required vs catch unnecessary (E0012)” split.

### 2026-02-26: catch typing bridge lift (proof-only)

**Context**: Lifted admissible capstones into a judgment-shaped API so this
Phase-2 track is not purely contract-layer.

**MCP tools used**: none (proof-only bridge construction on top of already
validated runtime behavior).

**Lean side**:
- Added `Kea/Properties/CatchTypingBridge.lean`.
- Introduced `CatchTypingJudgment` as a typing-style premise bundle.
- Added theorem adapters:
  - `catchTypingJudgment_sound`
  - `catchTypingJudgment_rowTailStable`
  - `catchTypingJudgment_preserves_nonFail`
  - `catchTypingJudgment_admissibility_branch`
- Imported module in `formal/Kea.lean`.
- Verified with `cd formal && lake build` (pass).

**Classify**: N/A (proof-only step).

**Outcome**:
- Phase-2 now has a judgment-surface bridge from typing-style premises to the
admissible catch capstones, ready for future concrete typing-rule integration.

### 2026-02-26: catch bridge bundle ergonomics (proof-only)

**Context**: Added judgment-level bundle/projection ergonomics in
`CatchTypingBridge` to match the existing schema-side bundle style.

**MCP tools used**: none (proof-only API shaping).

**Lean side**:
- Extended `Kea/Properties/CatchTypingBridge.lean` with:
  - `CatchTypingBundle`
  - `catchTypingJudgment_bundle`
  - `catchTypingJudgment_bundle_clauseFailRemoved`
  - `catchTypingJudgment_bundle_rowTailStable`
  - `catchTypingJudgment_bundle_preserves_nonFail`
  - `catchTypingJudgment_bundle_failRemoved_in_lowered`
- Verified with `cd formal && lake build` (pass).

**Classify**: N/A (proof-only step).

**Outcome**:
- Judgment-level consumers now have one-name bundle outputs and one-hop
projections, consistent with the rest of the Phase-2 capstone surface.

### 2026-02-26: catch bridge direct premise adapters (proof-only)

**Context**: Added judgment-free adapters in `CatchTypingBridge` so users can
enter bridge capstones directly from raw premises, matching the schema-side
adapter pattern.

**MCP tools used**: none (proof-only API extension).

**Lean side**:
- Extended `Kea/Properties/CatchTypingBridge.lean` with:
  - `mkCatchTypingJudgment`
  - `catchTypingJudgment_sound_of_premises`
  - noncomputable `catchTypingJudgment_bundle_of_premises`
- Resolved definition-shape constraints by using `def` (not theorem) for
  non-`Prop` outputs and marking bundle adapter noncomputable where required.
- Verified with `cd formal && lake build` (pass).

**Classify**: N/A (proof-only step).

**Outcome**:
- Bridge entrypoints now support both judgment-structured and raw-premise usage
  with a consistent runtime-aligned admissibility boundary.

### 2026-02-26: catch bridge one-hop `of_premises` projections (proof-only)

**Context**: Extended the new raw-premise bridge adapters with one-hop
projection helpers so theorem consumers can request only the facet they need.

**MCP tools used**: none (proof-only API refinement).

**Lean side**:
- Extended `Kea/Properties/CatchTypingBridge.lean` with:
  - `catchTypingJudgment_rowTailStable_of_premises`
  - `catchTypingJudgment_preserves_nonFail_of_premises`
  - `catchTypingJudgment_bundle_clauseFailRemoved_of_premises`
  - `catchTypingJudgment_bundle_rowTailStable_of_premises`
- Verified with `cd formal && lake build` (pass).

**Classify**: N/A (proof-only step).

**Outcome**:
- Raw-premise call sites now have direct one-hop access to selected
catch-lowering consequences without constructing or destructuring intermediate
judgment/bundle values.

### 2026-02-26: higher-order catch admissibility regression (typed Fail rows)

**Context**: Sanity re-probe after recent proof-surface expansions surfaced a
new higher-order behavior mismatch on the current MCP binary.

**MCP tools used**: direct `kea-mcp` stdio (`initialize`,
`notifications/initialized`, `tools/call` with `reset_session`, `get_type`,
`diagnose`).

**Probe**:
1. First-order typed Fail row (control):
   - `body : () -[Log, Fail String]> Int`, `wrapped : () -[Log]> Result(Int, String)`
   - `catch body()` => `ok`, inferred `() -[Log]> Result(Int, String)`.
2. Fail-absent control:
   - `catch pureish()` where `pureish : () -[Log]> Int`
   - rejected with `E0012` (`expression cannot fail; catch is unnecessary`) as expected.
3. Higher-order typed Fail row:
   - `wrap_poly(f: fn() -[Log, Fail String]> Int) -[Log]> Result(Int, String)`
   - body `catch f()`
   - unexpectedly rejected with `E0012` (`expression cannot fail; catch is unnecessary`).

**Classify**: Divergence (higher-order effect propagation / catch admissibility).

**Lean side impacted**:
- `EffectPolymorphismSoundness` higher-order usage expectations under admissible
  function-typed premises.
- `CatchTypingBridge` runtime-alignment claims for higher-order parameterized
  catch paths.

**Outcome**:
- Runtime alignment remains valid for first-order catch slices, but higher-order
  admissible catch with typed Fail rows is currently divergent and should be
  fixed before claiming full higher-order alignment.

### 2026-02-26: higher-order catch admissibility divergence closure

**Context**: Re-probed after restart on the latest MCP binary following the
reported higher-order catch fix.

**MCP tools used**: direct `kea-mcp` stdio (`initialize`,
`notifications/initialized`, `tools/call` with `reset_session`, `get_type`,
`diagnose`).

**Probe**:
1. Higher-order typed Fail row (previous divergence case):
   - `wrap_poly(f: fn() -[Log, Fail String]> Int) -[Log]> Result(Int, String)`
   - body `catch f()`
   - result: `ok`, inferred
     `(() -[Fail(String), Log]> Int) -[Log]> Result(Int, String)`, no diagnostics.
2. First-order typed Fail row control:
   - `body : () -[Log, Fail String]> Int`, `catch body()`
   - result: `ok`, inferred `() -[Log]> Result(Int, String)`, no diagnostics.
3. Fail-absent control:
   - `catch pureish()` with `pureish : () -[Log]> Int`
   - rejected with `E0012` (`expression cannot fail; catch is unnecessary`).

**Classify**: Agreement (divergence closed).

**Outcome**:
- Higher-order typed-Fail catch behavior now aligns with the formal
  effect-polymorphism/catch-admissibility model.

### 2026-02-26: higher-order catch specialization module (proof-only)

**Context**: Added explicit higher-order theorem surfaces now that the runtime
higher-order catch regression is closed.

**MCP tools used**: none (proof-only specialization, relying on the immediately
preceding higher-order divergence-closure probes).

**Lean side**:
- Added `Kea/Properties/HigherOrderCatchContracts.lean`.
- Introduced:
  - `higherOrderParamType`
  - `higherOrderCatchType`
  - `HigherOrderCatchTypingJudgment`
  - `higherOrderCatchTypingJudgment_sound`
  - `higherOrderCatchTypingJudgment_admissibility_branch`
- Imported module in `formal/Kea.lean`.
- Verified with `cd formal && lake build` (pass).

**Classify**: N/A (proof-only step).

**Outcome**:
- The higher-order catch shape now has dedicated, citable theorem surfaces
instead of relying only on generic bridge instantiation.

### 2026-02-26: higher-order raw-premise adapters (proof-only)

**Context**: Added direct `of_premises` theorem adapters for higher-order catch
surfaces to match the ergonomics of the generic bridge layers.

**MCP tools used**: none (proof-only API refinement; runtime behavior already
validated in preceding higher-order closure probes).

**Lean side**:
- Extended `Kea/Properties/HigherOrderCatchContracts.lean` with:
  - `higherOrderCatchTypingJudgment_sound_of_premises`
  - `higherOrderCatchTypingJudgment_admissibility_branch_of_premises`
- Verified with `cd formal && lake build` (pass).

**Classify**: N/A (proof-only step).

**Outcome**:
- Higher-order theorem consumers can now start from raw premise sets directly,
  without constructing intermediate judgment records manually.

### 2026-02-26: higher-order named bundles (proof-only)

**Context**: Added named bundle/projection ergonomics for higher-order catch
surfaces, matching the established Phase-2 pattern used in other modules.

**MCP tools used**: none (proof-only packaging refinement).

**Lean side**:
- Extended `Kea/Properties/HigherOrderCatchContracts.lean` with:
  - `HigherOrderCatchBundle`
  - `higherOrderCatchTypingJudgment_bundle`
  - `higherOrderCatchTypingJudgment_bundle_*` projections
  - noncomputable `higherOrderCatchTypingJudgment_bundle_of_premises`
- Verified with `cd formal && lake build` (pass).

**Classify**: N/A (proof-only step).

**Outcome**:
- Higher-order theorem consumers now have a stable one-name bundle surface and
one-hop projections for clause-removal, row-tail, non-Fail preservation, and
Fail-removal consequences.

### 2026-02-26: higher-order bundle one-hop `of_premises` projections (proof-only)

**Context**: Extended higher-order bundle ergonomics with one-hop premise
projection helpers so raw-premise theorem call sites can extract individual
bundle consequences directly.

**MCP tools used**: none (proof-only API refinement; no runtime-facing semantic
change).

**Lean side**:
- Extended `Kea/Properties/HigherOrderCatchContracts.lean` with:
  - `higherOrderCatchTypingJudgment_bundle_clauseFailRemoved_of_premises`
  - `higherOrderCatchTypingJudgment_bundle_rowTailStable_of_premises`
  - `higherOrderCatchTypingJudgment_bundle_preserves_nonFail_of_premises`
- Verified with `cd formal && lake build` (pass).

**Classify**: N/A (proof-only step).

**Outcome**:
- Raw-premise higher-order call sites now have direct one-hop access to selected
  bundle guarantees without intermediate record construction/destructuring.

### 2026-02-26: higher-order combined raw-premise capstone (proof-only)

**Context**: Added a single higher-order capstone theorem that combines lowered
effect guarantees and admissibility branch facts from raw premises.

**MCP tools used**: none (proof-only packaging; runtime alignment already
validated in prior higher-order closure probes).

**Lean side**:
- Extended `Kea/Properties/HigherOrderCatchContracts.lean` with:
  - `higherOrderCatchTypingJudgment_bundle_failRemoved_of_premises`
  - `higherOrderCatchTypingJudgment_capstone_of_premises`
- Verified with `cd formal && lake build` (pass).

**Classify**: N/A (proof-only step).

**Outcome**:
- Higher-order catch now has a single raw-premise theorem surface that packages
  clause Fail removal, lowered-row tail/non-Fail preservation, lowered Fail
  removal, and admissible-vs-unnecessary branch consequences.

### 2026-02-26: higher-order Fail-presence/absence wrappers (proof-only)

**Context**: Added practical higher-order wrappers so theorem consumers can
enter the capstone or unnecessary branch directly from Fail-label evidence.

**MCP tools used**: none (proof-only API ergonomics; no runtime semantic
change).

**Lean side**:
- Extended `Kea/Properties/HigherOrderCatchContracts.lean` with:
  - `higherOrderCatchTypingJudgment_capstone_of_fail_present`
  - `higherOrderCatchUnnecessary_of_fail_absent`
- Verified with `cd formal && lake build` (pass).

**Classify**: N/A (proof-only step).

**Outcome**:
- Higher-order catch call sites can now use direct Fail label
  presence/absence facts as entry assumptions, without first constructing
  explicit admissibility/unnecessary witnesses.

### 2026-02-26: higher-order single-entry classifier (proof-only)

**Context**: Added a higher-order classifier that starts from raw premises and
returns either full capstone consequences or the unnecessary branch.

**MCP tools used**: none (proof-only theorem-surface consolidation).

**Lean side**:
- Extended `Kea/Properties/HigherOrderCatchContracts.lean` with:
  - `HigherOrderCatchCapstoneOutcome`
  - `higherOrderCatchTypingJudgment_classify_of_premises`
- Re-targeted existing capstone wrappers to the new named outcome type.
- Verified with `cd formal && lake build` (pass).

**Classify**: N/A (proof-only step).

**Outcome**:
- Higher-order catch now has a single entry theorem over raw premises that
  captures the runtime-aligned admissible-vs-unnecessary split while preserving
  access to full lowering guarantees on the admissible branch.

### 2026-02-26: generic catch bridge classifier alignment (proof-only)

**Context**: Mirrored the higher-order capstone/classifier entry pattern in the
generic catch bridge so both surfaces expose the same runtime-aligned split.

**MCP tools used**: none (proof-only API consolidation).

**Lean side**:
- Extended `Kea/Properties/CatchTypingBridge.lean` with:
  - `CatchTypingCapstoneOutcome`
  - `catchTypingJudgment_capstone_of_premises`
  - `catchTypingJudgment_capstone_of_fail_present`
  - `catchTypingUnnecessary_of_fail_absent`
  - `catchTypingJudgment_classify_of_premises`
- Verified with `cd formal && lake build` (pass).

**Classify**: N/A (proof-only step).

**Outcome**:
- Generic and higher-order catch theorem surfaces now share the same
  admissible-vs-unnecessary classifier shape and direct Fail-label entry
  wrappers.

### 2026-02-26: effect declaration/operation typing scaffold (proof-only)

**Context**: Added the Phase-2 effect-declaration/operation-typing scaffold and
connected it to the normalized handler model for direct-call soundness.

**MCP tools used**: none (proof-only scaffold and theorem-surface expansion).

**Lean side**:
- Added `Kea/Properties/EffectOperationTyping.lean` with:
  - `OperationSig`, `EffectDecl`
  - `operationDeclared`, `operationCallTyping`
  - `performOperationEffects` + row-preservation lemmas
  - `operationCallTyping_adds_declared_effect`
  - `capability_direct_call_sound`
- Imported the module in `formal/Kea.lean`.
- Verified with `cd formal && lake build` (pass).

**Classify**: N/A (proof-only step).

**Outcome**:
- Phase-2 now has explicit formal coverage for effect declaration/operation
  typing scaffolding and a citable direct-call soundness theorem for
  unintercepted capabilities.

### 2026-02-26: capability direct-call runtime alignment probe

**Context**: Validated the new `capability_direct_call_sound` theorem surface
against the latest restarted MCP binary.

**MCP tools used**: direct `kea-mcp` stdio (`initialize`,
`notifications/initialized`, `tools/call` with `reset_session`, `type_check`,
`get_type`, `diagnose`).

**Probe**:
1. Handle `Trace` while body performs `Log` and `Trace`:
   - declarations:
     - `body : () -[Log, Trace]> ()`
     - `run` handles `Trace.trace` with `resume ()`
   - `type_check` bindings include:
     - `run : () -[Log]> ()`
   - `get_type "run"` returns `() -[Log]> ()`
   - `diagnose "run"` returns no diagnostics.
2. Symmetric control (handle `Log` while body performs `Log` and `Trace`):
   - `type_check` bindings include:
     - `run2 : () -[Trace]> ()`
   - `get_type "run2"` returns `() -[Trace]> ()`
   - `diagnose "run2"` returns no diagnostics.

**Classify**: Agreement.

**Outcome**:
- Runtime behavior matches the formal direct-call model: when handling one
  effect, the other capability effect remains in the residual row.

### 2026-02-26: tail-resumptive classification scaffold (proof-only)

**Context**: Added a dedicated Phase-2 module for classifying resume shapes and
exposing a tail-resumptive direct-call contract surface.

**MCP tools used**: none (proof-only theorem-surface expansion).

**Lean side**:
- Added `Kea/Properties/TailResumptiveClassification.lean` with:
  - `TailResumptiveClass`, `classifyResumeUse`, `classifyClause`
  - `tailResumptiveEligible`
  - `tail_resumptive_classification`
  - `directCallEquivalent`, `tail_resumptive_direct_call_sound`
  - eligibility projections (`tail_resumptive_eligible_implies_*`)
- Imported the module in `formal/Kea.lean`.
- Verified with `cd formal && lake build` (pass).

**Classify**: N/A (proof-only step).

**Outcome**:
- Phase-2 now has an explicit, citable theorem surface for the
  tail-resumptive fast-path classification and direct-call equivalence claim.

### 2026-02-26: operation-call WF transport (proof-only)

**Context**: Extended effect operation typing with a WF-preservation bridge so
operation-call row updates compose with the existing WF theorem ladder.

**MCP tools used**: none (proof-only WF API extension).

**Lean side**:
- Extended `Kea/Properties/EffectOperationTyping.lean` with:
  - `performOperationEffects_preserves_wellFormed`
- Verified with `cd formal && lake build` (pass).

**Classify**: N/A (proof-only step).

**Outcome**:
- Operation-call effect-row updates now have a direct WF-preservation theorem,
  reducing glue work for downstream Phase-2 soundness composition.

### 2026-02-26: tail-resumptive bundle packaging (proof-only)

**Context**: Added named bundle packaging for tail-resumptive classification so
consumers can depend on one theorem surface instead of multiple projections.

**MCP tools used**: none (proof-only packaging refinement).

**Lean side**:
- Extended `Kea/Properties/TailResumptiveClassification.lean` with:
  - `TailResumptiveBundle`
  - `tail_resumptive_bundle_of_wellTyped`
  - `tail_resumptive_bundle_notInvalid`
- Verified with `cd formal && lake build` (pass).

**Classify**: N/A (proof-only step).

**Outcome**:
- Tail-resumptive classification now has one-name bundle consumption and direct
  non-invalid projection from well-typed clause premises.

### 2026-02-26: tail-resumptive runtime alignment probe

**Context**: Validated the tail-resumptive direct-call slice against current
`kea-mcp` behavior with and without a `then` clause.

**MCP tools used**: direct `kea-mcp` stdio (`initialize`,
`notifications/initialized`, `tools/call` with `reset_session`, `type_check`,
`get_type`, `diagnose`).

**Probe**:
1. Declarations:
   - `body : () -[Log]> ()`
   - `run_no_then` handles `Log.log` with `resume ()`
   - `run_then` same clause plus `then value -> value`
2. `type_check` bindings:
   - `run_no_then : () -> ()`
   - `run_then : () -> ()`
3. `get_type`:
   - `run_no_then` => `() -> ()`
   - `run_then` => `() -> ()`
4. `diagnose`:
   - both names return empty diagnostics.

**Classify**: Agreement.

**Outcome**:
- Runtime behavior matches the tail-resumptive contract slice in this surface:
  no-`then` and identity-`then` variants preserve the same pure function type.

### 2026-02-26: operation-call effect-row runtime alignment probe

**Context**: Validated operation-call effect-row behavior against
`EffectOperationTyping` expectations.

**MCP tools used**: direct `kea-mcp` stdio (`initialize`,
`notifications/initialized`, `tools/call` with `reset_session`, `type_check`,
`get_type`, `diagnose`).

**Probe**:
1. Declared operation call (positive):
   - `effect Log { fn log(msg: Int) -> Unit }`
   - `fn call_log() -[Log]> Unit = Log.log(1)` (surface syntax equivalent)
   - `type_check` binds `call_log : () -[Log]> ()`
   - `get_type "call_log"` returns `() -[Log]> ()`
   - `diagnose "call_log"` returns no diagnostics.
2. Explicit too-weak effect annotation (negative):
   - `effect Log`, `effect Trace`
   - `fn bad() -[Trace]> Unit` with body `Log.log(1)`
   - `type_check` rejects with `E0001`:
     `declared effect [Trace] is too weak; body requires [Log]`.
   - `diagnose` reports the same error payload.

**Classify**: Agreement.

**Outcome**:
- Runtime checks align with operation-call contract claims:
  operation calls require/preserve the corresponding effect label, and explicit
  under-approximation of declared effect rows is rejected.

### 2026-02-26: tail-capability composition module (proof-only)

**Context**: Added a cross-module composition layer between operation-call
capability preservation and tail-resumptive equivalence.

**MCP tools used**: none (proof-only composition surface).

**Lean side**:
- Added `Kea/Properties/TailCapabilityComposition.lean` with:
  - `core_capability_direct_call_sound`
  - `tail_resumptive_eligible_capability_direct_call_sound`
  - `tail_resumptive_wellTyped_capability_direct_call_sound`
- Imported module in `formal/Kea.lean`.
- Verified with `cd formal && lake build` (pass).

**Classify**: N/A (proof-only step).

**Outcome**:
- Phase-2 now has a citable theorem surface that composes capability and
  tail-resumptive contracts under explicit assumptions.

### 2026-02-26: handled-absent resumptive composition probe (well-typed boundary)

**Context**: Tested a direct runtime shape corresponding to a handled-absent
resumptive clause to confirm the intended well-typed precondition boundary on
the composition surface.

**MCP tools used**: direct `kea-mcp` stdio (`initialize`,
`notifications/initialized`, `tools/call` with `reset_session`, `type_check`,
`get_type`, `diagnose`).

**Probe**:
- Snippet:
  - `effect Log`, `effect Trace`
  - `fn run_tail_cap() -[Log]> Unit`
  - body: `handle Log.log(1)` with clause `Trace.trace(x) -> resume ()`
- `type_check` rejects with `E0001`:
  - `declared effect [Log] is too weak; body requires [IO]`
- `diagnose` reports the same error.

**Classify**: Agreement (with well-typedness precondition boundary).

**Outcome**:
- Rejection is expected for this non-well-typed declaration: handling `Trace`
  does not eliminate required `Log` effects from the body. Composition claims
  remain intentionally **well-typed-clause preconditioned**. The diagnostic text
  currently references `[IO]` in this path, but the acceptance/rejection
  boundary matches the formal precondition.

### 2026-02-26: full-result capability lift in composition layer (proof-only)

**Context**: Strengthened tail-capability composition so capability preservation
is available directly on full clause result effects, not only core effects.

**MCP tools used**: none (proof-only theorem refinement built on already-probed
operation and tail-resumptive slices).

**Lean side**:
- Extended `Kea/Properties/TailCapabilityComposition.lean` with:
  - `resultEffects_preserves_core_label_true`
  - `wellTyped_capability_direct_call_sound`
- Rebased
  `tail_resumptive_wellTyped_capability_direct_call_sound` on the new
  well-typed lift (tail-resumptive theorem remains as a specialized surface).
- Verified with `cd formal && lake build` (pass).

**Classify**: N/A (proof-only step).

**Outcome**:
- Capability-preservation composition now works directly through
  `HandleClauseContract.resultEffects`, including optional `then` unions, under
  the explicit well-typed-clause boundary.
