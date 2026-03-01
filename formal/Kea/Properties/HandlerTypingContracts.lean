import Kea.Properties.HandlerEffectRemoval
import Kea.Properties.ResumeLinearity

/-!
  Kea.Properties.HandlerTypingContracts — Phase 2 integration surface.

  This module connects two Phase-2 proof tracks:
  - effect-row handler composition/removal (`HandlerEffectRemoval`)
  - resume at-most-once legality (`ResumeLinearity`)

  It provides a lightweight contract layer that can be wired to concrete
  handler typing judgments later.
-/

/-- Abstract per-clause typing contract summary. -/
structure HandleClauseContract where
  handled : Label
  exprEffects : EffectRow
  handlerEffects : EffectRow
  thenEffects : Option EffectRow
  clauseCoverageComplete : Prop
  resumeUse : ResumeUse

namespace HandleClauseContract

/-- Result effects immediately after clause handling (before `then`). -/
def resultEffectsCore (c : HandleClauseContract) : EffectRow :=
  EffectRow.handleComposeNormalized c.exprEffects c.handlerEffects c.handled

/-- Apply optional `then`-clause effects to a base effect row. -/
def applyThenEffects (base : EffectRow) (thenEffects : Option EffectRow) : EffectRow :=
  match thenEffects with
  | none => base
  | some te =>
      .mk (.mk
        (RowFields.unionIdem (EffectRow.fields base) (EffectRow.fields te))
        (EffectRow.rest base))

@[simp] theorem applyThenEffects_none (base : EffectRow) :
    applyThenEffects base none = base := rfl

@[simp] theorem applyThenEffects_some (base te : EffectRow) :
    applyThenEffects base (some te) =
      .mk (.mk
        (RowFields.unionIdem (EffectRow.fields base) (EffectRow.fields te))
        (EffectRow.rest base)) := rfl

@[simp] theorem applyThenEffects_rest
    (base : EffectRow) (thenEffects : Option EffectRow) :
    EffectRow.rest (applyThenEffects base thenEffects) = EffectRow.rest base := by
  cases thenEffects <;> rfl

/-- Full result effects including optional `then`-clause effects. -/
def resultEffects (c : HandleClauseContract) : EffectRow :=
  applyThenEffects (resultEffectsCore c) c.thenEffects

/-- Clause coverage premise (all handled operations covered). -/
def coverageOk (c : HandleClauseContract) : Prop :=
  c.clauseCoverageComplete

/-- Resume-linearity premise for clause legality. -/
def linearityOk (c : HandleClauseContract) : Prop :=
  ResumeUse.atMostOnce c.resumeUse

/--
Judgment-shaped resume summary relation for handler clauses.

`clauseHasResumeSummary c u` means clause `c` is assigned resume summary `u`.
This is a lightweight stand-in for a full clause typing judgment.
-/
inductive clauseHasResumeSummary : HandleClauseContract → ResumeUse → Prop where
  | mk (c : HandleClauseContract) :
      clauseHasResumeSummary c c.resumeUse

/--
Effect-side premise used by the current removal theorem:
handler-body effects do not re-introduce the handled label.
-/
def noHandledReintroHandler (c : HandleClauseContract) : Prop :=
  RowFields.has (EffectRow.fields c.handlerEffects) c.handled = false

/-- Optional `then`-clause must also avoid reintroducing the handled effect. -/
def noHandledReintroThen (c : HandleClauseContract) : Prop :=
  match c.thenEffects with
  | none => True
  | some te => RowFields.has (EffectRow.fields te) c.handled = false

/-- Combined Phase-2 contract (current integration slice). -/
def wellTypedSlice (c : HandleClauseContract) : Prop :=
  coverageOk c ∧ linearityOk c ∧ noHandledReintroHandler c ∧ noHandledReintroThen c

theorem wellTypedSlice_coverage (c : HandleClauseContract)
    (h : wellTypedSlice c) :
    coverageOk c := h.1

theorem wellTypedSlice_linearity (c : HandleClauseContract)
    (h : wellTypedSlice c) :
    linearityOk c := h.2.1

theorem clauseHasResumeSummary_eq_resumeUse
    (c : HandleClauseContract) (u : ResumeUse)
    (h_summary : clauseHasResumeSummary c u) :
    u = c.resumeUse := by
  cases h_summary with
  | mk => rfl

/--
Main linearity bridge: if a clause is well-typed in the current contract slice,
its assigned resume summary satisfies the named at-most-once contract.
-/
theorem clauseHasResumeSummary_implies_atMostOnce_of_wellTypedSlice
    (c : HandleClauseContract) (u : ResumeUse)
    (h_typed : wellTypedSlice c)
    (h_summary : clauseHasResumeSummary c u) :
    resume_at_most_once u := by
  have h_lin : ResumeUse.atMostOnce c.resumeUse :=
    wellTypedSlice_linearity c h_typed
  have h_eq : u = c.resumeUse :=
    clauseHasResumeSummary_eq_resumeUse c u h_summary
  subst h_eq
  exact resume_at_most_once_sound c.resumeUse h_lin

/--
Existence form of the resume-linearity bridge:
every well-typed clause has a summary witness that is at-most-once.
-/
theorem wellTypedSlice_hasResumeSummary_atMostOnce
    (c : HandleClauseContract)
    (h_typed : wellTypedSlice c) :
    ∃ u, clauseHasResumeSummary c u ∧ resume_at_most_once u := by
  refine ⟨c.resumeUse, clauseHasResumeSummary.mk c, ?_⟩
  exact clauseHasResumeSummary_implies_atMostOnce_of_wellTypedSlice
    c c.resumeUse h_typed (clauseHasResumeSummary.mk c)

/--
Packaged resume-linearity consequences for a clause typing witness.
-/
structure ClauseResumeLinearityBundle (c : HandleClauseContract) where
  summary : ResumeUse
  hasSummary : clauseHasResumeSummary c summary
  atMostOnce : resume_at_most_once summary

/-- Explicit component alias for `ClauseResumeLinearityBundle`. -/
abbrev ClauseResumeLinearityBundleComponents
    (c : HandleClauseContract) : Prop :=
  ∃ u, clauseHasResumeSummary c u ∧ resume_at_most_once u

/-- `ClauseResumeLinearityBundle` is equivalent to explicit components. -/
theorem clauseResumeLinearityBundle_iff_components
    (c : HandleClauseContract) :
    Nonempty (ClauseResumeLinearityBundle c) ↔
      ClauseResumeLinearityBundleComponents c := by
  constructor
  · intro h_bundle
    rcases h_bundle with ⟨b⟩
    exact ⟨b.summary, b.hasSummary, b.atMostOnce⟩
  · intro h_comp
    rcases h_comp with ⟨u, h_summary, h_atMostOnce⟩
    exact ⟨{ summary := u, hasSummary := h_summary, atMostOnce := h_atMostOnce }⟩

/-- Build `ClauseResumeLinearityBundle` from explicit components. -/
theorem clauseResumeLinearityBundle_of_components
    (c : HandleClauseContract)
    (h_comp : ClauseResumeLinearityBundleComponents c) :
    Nonempty (ClauseResumeLinearityBundle c) :=
  (clauseResumeLinearityBundle_iff_components c).2 h_comp

/-- Decompose `ClauseResumeLinearityBundle` into explicit components. -/
theorem clauseResumeLinearityBundle_as_components
    (c : HandleClauseContract)
    (b : ClauseResumeLinearityBundle c) :
    ClauseResumeLinearityBundleComponents c :=
  (clauseResumeLinearityBundle_iff_components c).1 ⟨b⟩

/-- Direct components-route decomposition for `ClauseResumeLinearityBundle`. -/
theorem clauseResumeLinearityBundle_as_components_of_components
    (c : HandleClauseContract)
    (h_comp : ClauseResumeLinearityBundleComponents c) :
    ClauseResumeLinearityBundleComponents c :=
  (clauseResumeLinearityBundle_iff_components c).1
    ((clauseResumeLinearityBundle_iff_components c).2 h_comp)

/--
The resume-linearity component witness is equivalent to the primitive
linearity premise for the clause.
-/
theorem clauseResumeLinearityBundleComponents_iff_linearityOk
    (c : HandleClauseContract) :
    ClauseResumeLinearityBundleComponents c ↔ linearityOk c := by
  constructor
  · intro h_comp
    rcases h_comp with ⟨u, h_summary, h_atMostOnce⟩
    have h_eq : u = c.resumeUse :=
      clauseHasResumeSummary_eq_resumeUse c u h_summary
    subst h_eq
    exact h_atMostOnce
  · intro h_lin
    exact ⟨c.resumeUse, clauseHasResumeSummary.mk c, h_lin⟩

/--
Bundle existence is equivalent to the primitive clause linearity premise.
-/
theorem clauseResumeLinearityBundle_iff_linearityOk
    (c : HandleClauseContract) :
    Nonempty (ClauseResumeLinearityBundle c) ↔ linearityOk c := by
  rw [clauseResumeLinearityBundle_iff_components c]
  exact clauseResumeLinearityBundleComponents_iff_linearityOk c

/-- Build the packaged resume-linearity bundle from `wellTypedSlice`. -/
def clauseResumeLinearityBundle_of_wellTypedSlice
    (c : HandleClauseContract)
    (h_typed : wellTypedSlice c) :
    ClauseResumeLinearityBundle c := by
  refine
    { summary := c.resumeUse
      hasSummary := clauseHasResumeSummary.mk c
      atMostOnce := ?_ }
  exact clauseHasResumeSummary_implies_atMostOnce_of_wellTypedSlice
    c c.resumeUse h_typed (clauseHasResumeSummary.mk c)

/-- One-hop at-most-once projection from the packaged resume-linearity bundle. -/
theorem clauseResumeLinearityBundle_atMostOnce
    (c : HandleClauseContract)
    (b : ClauseResumeLinearityBundle c) :
    resume_at_most_once b.summary := b.atMostOnce

/-- One-hop summary projection from the packaged resume-linearity bundle. -/
theorem clauseResumeLinearityBundle_hasSummary
    (c : HandleClauseContract)
    (b : ClauseResumeLinearityBundle c) :
    clauseHasResumeSummary c b.summary := b.hasSummary

/--
One-hop at-most-once wrapper from `wellTypedSlice` via the packaged
resume-linearity bundle.
-/
theorem clauseResumeLinearityBundle_atMostOnce_of_wellTypedSlice
    (c : HandleClauseContract)
    (h_typed : wellTypedSlice c) :
    resume_at_most_once (clauseResumeLinearityBundle_of_wellTypedSlice c h_typed).summary :=
  (clauseResumeLinearityBundle_of_wellTypedSlice c h_typed).atMostOnce

theorem wellTypedSlice_noHandledReintroHandler (c : HandleClauseContract)
    (h : wellTypedSlice c) :
    noHandledReintroHandler c := h.2.2.1

theorem wellTypedSlice_noHandledReintroThen (c : HandleClauseContract)
    (h : wellTypedSlice c) :
    noHandledReintroThen c := h.2.2.2

theorem resultEffectsCore_handled_removed
    (c : HandleClauseContract)
    (h_no_reintro : noHandledReintroHandler c) :
    RowFields.has (EffectRow.fields (resultEffectsCore c)) c.handled = false := by
  exact EffectRow.handle_removes_effect_normalized_of_handler_absent
    c.exprEffects
    c.handlerEffects
    c.handled
    h_no_reintro

theorem applyThenEffects_preserves_handled_absent_of_then_absent
    (base thenEff : EffectRow) (handled : Label)
    (h_base_abs : RowFields.has (EffectRow.fields base) handled = false)
    (h_then_abs : RowFields.has (EffectRow.fields thenEff) handled = false) :
    RowFields.has (EffectRow.fields (applyThenEffects base (some thenEff))) handled = false := by
  simp [applyThenEffects]
  exact RowFields.has_unionIdem_false_of_false_false
    (EffectRow.fields base)
    (EffectRow.fields thenEff)
    handled
    h_base_abs
    h_then_abs

/--
Integration theorem: from the combined slice, handled effect remains removed
in the final result effect row (core handler + optional `then`).
-/
theorem wellTypedSlice_implies_handled_removed
    (c : HandleClauseContract)
    (h : wellTypedSlice c) :
    RowFields.has (EffectRow.fields (resultEffects c)) c.handled = false := by
  have h_core_abs :
      RowFields.has (EffectRow.fields (resultEffectsCore c)) c.handled = false :=
    resultEffectsCore_handled_removed c (wellTypedSlice_noHandledReintroHandler c h)
  cases h_then : c.thenEffects with
  | none =>
      simpa [resultEffects, applyThenEffects, h_then] using h_core_abs
  | some te =>
      have h_then_abs :
          RowFields.has (EffectRow.fields te) c.handled = false := by
        have h_no_then := wellTypedSlice_noHandledReintroThen c h
        simpa [noHandledReintroThen, h_then] using h_no_then
      have h_final_abs :
          RowFields.has
            (EffectRow.fields (applyThenEffects (resultEffectsCore c) (some te)))
            c.handled = false :=
        applyThenEffects_preserves_handled_absent_of_then_absent
          (resultEffectsCore c)
          te
          c.handled
          h_core_abs
          h_then_abs
      simpa [resultEffects, h_then] using h_final_abs

/-- Resume provenance summary extracted from linearity. -/
def resumeProvenance (c : HandleClauseContract) : Prop :=
  c.resumeUse = .zero ∨ c.resumeUse = .one

theorem linearityOk_implies_resumeProvenance
    (c : HandleClauseContract)
    (h_lin : linearityOk c) :
    resumeProvenance c := by
  cases h_use : c.resumeUse with
  | zero =>
      exact Or.inl h_use
  | one =>
      exact Or.inr h_use
  | many =>
      simp [linearityOk, h_use] at h_lin

theorem wellTypedSlice_implies_resumeProvenance
    (c : HandleClauseContract)
    (h : wellTypedSlice c) :
    resumeProvenance c := by
  exact linearityOk_implies_resumeProvenance c (wellTypedSlice_linearity c h)

/--
Branch merge legality for resume summaries in clause-level reasoning.
-/
theorem branch_linearity_ok_of_exclusive
    (thenUse elseUse : ResumeUse)
    (h_then : ResumeUse.atMostOnce thenUse)
    (h_else : ResumeUse.atMostOnce elseUse)
    (h_exclusive : thenUse = .zero ∨ elseUse = .zero) :
    ResumeUse.atMostOnce (ResumeUse.combine thenUse elseUse) := by
  exact resume_combine_preserves_atMostOnce_of_exclusive
    thenUse elseUse h_then h_else h_exclusive

/--
Loop legality bridge for clause-level reasoning:
if a loop-carried clause summary is legal, the body must be zero-resume.
-/
theorem loop_linearity_requires_zero
    (u : ResumeUse)
    (h_loop : ResumeUse.loopLegal u) :
    u = .zero := by
  exact resume_loop_forbids_resuming_body u h_loop

/-- Abstract handler contract as a finite collection of clauses. -/
structure HandleContract where
  clauses : List HandleClauseContract

/-- Handler-level typing contract: every clause satisfies `wellTypedSlice`. -/
def handlerWellTypedSlice (h : HandleContract) : Prop :=
  ∀ c ∈ h.clauses, wellTypedSlice c

/--
Judgment-shaped relation for clause summaries inside a handler.

`handlerClauseHasResumeSummary h c u` means clause `c` belongs to handler `h`
and is assigned resume summary `u`.
-/
inductive handlerClauseHasResumeSummary
    (h : HandleContract) : HandleClauseContract → ResumeUse → Prop where
  | mk (c : HandleClauseContract) (u : ResumeUse)
      (h_mem : c ∈ h.clauses)
      (h_summary : clauseHasResumeSummary c u) :
      handlerClauseHasResumeSummary h c u

theorem handlerClauseHasResumeSummary_mem
    (h : HandleContract)
    (c : HandleClauseContract)
    (u : ResumeUse)
    (h_summary : handlerClauseHasResumeSummary h c u) :
    c ∈ h.clauses := by
  cases h_summary with
  | mk h_mem _ =>
      exact h_mem

theorem handlerClauseHasResumeSummary_clauseSummary
    (h : HandleContract)
    (c : HandleClauseContract)
    (u : ResumeUse)
    (h_summary : handlerClauseHasResumeSummary h c u) :
    clauseHasResumeSummary c u := by
  cases h_summary with
  | mk _ h_clause =>
      exact h_clause

/--
Main handler-level linearity bridge: if a handler is well-typed in the current
slice, any clause-summary judgment in that handler satisfies at-most-once.
-/
theorem handlerClauseHasResumeSummary_implies_atMostOnce_of_handlerWellTypedSlice
    (h : HandleContract)
    (c : HandleClauseContract)
    (u : ResumeUse)
    (h_typed : handlerWellTypedSlice h)
    (h_summary : handlerClauseHasResumeSummary h c u) :
    resume_at_most_once u := by
  have h_mem : c ∈ h.clauses :=
    handlerClauseHasResumeSummary_mem h c u h_summary
  have h_clause_typed : wellTypedSlice c :=
    h_typed c h_mem
  have h_clause_summary : clauseHasResumeSummary c u :=
    handlerClauseHasResumeSummary_clauseSummary h c u h_summary
  exact clauseHasResumeSummary_implies_atMostOnce_of_wellTypedSlice
    c u h_clause_typed h_clause_summary

/--
One-hop form: every clause in a well-typed handler has a canonical summary
(`resumeUse`) that satisfies at-most-once.
-/
theorem handlerWellTypedSlice_implies_clause_atMostOnce
    (h : HandleContract)
    (h_typed : handlerWellTypedSlice h) :
    ∀ c ∈ h.clauses, resume_at_most_once c.resumeUse := by
  intro c h_mem
  have h_clause_typed : wellTypedSlice c :=
    h_typed c h_mem
  exact clauseHasResumeSummary_implies_atMostOnce_of_wellTypedSlice
    c c.resumeUse h_clause_typed (clauseHasResumeSummary.mk c)

/--
Existence form over handler membership:
every clause in a well-typed handler has some summary witness that is
at-most-once.
-/
theorem handlerWellTypedSlice_has_clause_summary_atMostOnce
    (h : HandleContract)
    (h_typed : handlerWellTypedSlice h) :
    ∀ c ∈ h.clauses,
      ∃ u, handlerClauseHasResumeSummary h c u ∧ resume_at_most_once u := by
  intro c h_mem
  refine ⟨c.resumeUse, ?_, ?_⟩
  · exact handlerClauseHasResumeSummary.mk c c.resumeUse h_mem (clauseHasResumeSummary.mk c)
  · exact handlerWellTypedSlice_implies_clause_atMostOnce h h_typed c h_mem

/-- Primitive handler-level linearity premise (clause-wise). -/
def handlerLinearityOk (h : HandleContract) : Prop :=
  ∀ c ∈ h.clauses, linearityOk c

theorem handlerWellTypedSlice_implies_handlerLinearityOk
    (h : HandleContract)
    (h_typed : handlerWellTypedSlice h) :
    handlerLinearityOk h := by
  intro c h_mem
  exact wellTypedSlice_linearity c (h_typed c h_mem)

/-- Packaged handler-level resume-linearity consequences. -/
structure HandlerResumeLinearityBundle (h : HandleContract) where
  clauseAtMostOnce :
    ∀ c ∈ h.clauses,
      ∃ u, handlerClauseHasResumeSummary h c u ∧ resume_at_most_once u

/-- Explicit component alias for `HandlerResumeLinearityBundle`. -/
abbrev HandlerResumeLinearityBundleComponents
    (h : HandleContract) : Prop :=
  ∀ c ∈ h.clauses,
    ∃ u, handlerClauseHasResumeSummary h c u ∧ resume_at_most_once u

/-- `HandlerResumeLinearityBundle` is equivalent to explicit components. -/
theorem handlerResumeLinearityBundle_iff_components
    (h : HandleContract) :
    Nonempty (HandlerResumeLinearityBundle h) ↔
      HandlerResumeLinearityBundleComponents h := by
  constructor
  · intro h_bundle
    rcases h_bundle with ⟨b⟩
    exact b.clauseAtMostOnce
  · intro h_comp
    exact ⟨{ clauseAtMostOnce := h_comp }⟩

/-- Build `HandlerResumeLinearityBundle` from explicit components. -/
theorem handlerResumeLinearityBundle_of_components
    (h : HandleContract)
    (h_comp : HandlerResumeLinearityBundleComponents h) :
    Nonempty (HandlerResumeLinearityBundle h) :=
  (handlerResumeLinearityBundle_iff_components h).2 h_comp

/-- Decompose `HandlerResumeLinearityBundle` into explicit components. -/
theorem handlerResumeLinearityBundle_as_components
    (h : HandleContract)
    (b : HandlerResumeLinearityBundle h) :
    HandlerResumeLinearityBundleComponents h :=
  (handlerResumeLinearityBundle_iff_components h).1 ⟨b⟩

/-- Direct components-route decomposition for `HandlerResumeLinearityBundle`. -/
theorem handlerResumeLinearityBundle_as_components_of_components
    (h : HandleContract)
    (h_comp : HandlerResumeLinearityBundleComponents h) :
    HandlerResumeLinearityBundleComponents h :=
  (handlerResumeLinearityBundle_iff_components h).1
    ((handlerResumeLinearityBundle_iff_components h).2 h_comp)

/--
The handler-level bundle components are equivalent to the primitive
clause-wise handler linearity premise.
-/
theorem handlerResumeLinearityBundleComponents_iff_handlerLinearityOk
    (h : HandleContract) :
    HandlerResumeLinearityBundleComponents h ↔ handlerLinearityOk h := by
  constructor
  · intro h_comp
    intro c h_mem
    rcases h_comp c h_mem with ⟨u, h_summary, h_atMostOnce⟩
    have h_clause_summary : clauseHasResumeSummary c u :=
      handlerClauseHasResumeSummary_clauseSummary h c u h_summary
    have h_eq : u = c.resumeUse :=
      clauseHasResumeSummary_eq_resumeUse c u h_clause_summary
    subst h_eq
    exact h_atMostOnce
  · intro h_lin
    intro c h_mem
    refine ⟨c.resumeUse, ?_, h_lin c h_mem⟩
    exact handlerClauseHasResumeSummary.mk c c.resumeUse h_mem (clauseHasResumeSummary.mk c)

/--
Bundle existence is equivalent to primitive handler-level linearity.
-/
theorem handlerResumeLinearityBundle_iff_handlerLinearityOk
    (h : HandleContract) :
    Nonempty (HandlerResumeLinearityBundle h) ↔ handlerLinearityOk h := by
  rw [handlerResumeLinearityBundle_iff_components h]
  exact handlerResumeLinearityBundleComponents_iff_handlerLinearityOk h

/-- Build the packaged handler-level bundle from `handlerLinearityOk`. -/
def handlerResumeLinearityBundle_of_handlerLinearityOk
    (h : HandleContract)
    (h_lin : handlerLinearityOk h) :
    HandlerResumeLinearityBundle h where
  clauseAtMostOnce := by
    intro c h_mem
    refine ⟨c.resumeUse, ?_, h_lin c h_mem⟩
    exact handlerClauseHasResumeSummary.mk c c.resumeUse h_mem (clauseHasResumeSummary.mk c)

/-- Build the packaged handler-level bundle from `handlerWellTypedSlice`. -/
def handlerResumeLinearityBundle_of_handlerWellTypedSlice
    (h : HandleContract)
    (h_typed : handlerWellTypedSlice h) :
    HandlerResumeLinearityBundle h :=
  handlerResumeLinearityBundle_of_handlerLinearityOk h
    (handlerWellTypedSlice_implies_handlerLinearityOk h h_typed)

/--
One-hop handler-level projection from `handlerWellTypedSlice`: every clause
membership judgment has an at-most-once summary witness.
-/
theorem handlerResumeLinearityBundle_clause_atMostOnce_of_handlerWellTypedSlice
    (h : HandleContract)
    (h_typed : handlerWellTypedSlice h) :
    HandlerResumeLinearityBundleComponents h :=
  (handlerResumeLinearityBundle_of_handlerWellTypedSlice h h_typed).clauseAtMostOnce

/--
Direct decomposition route from `handlerWellTypedSlice` to explicit
handler-level bundle components.
-/
theorem handlerResumeLinearityBundle_as_components_of_handlerWellTypedSlice
    (h : HandleContract)
    (h_typed : handlerWellTypedSlice h) :
    HandlerResumeLinearityBundleComponents h :=
  handlerResumeLinearityBundle_as_components h
    (handlerResumeLinearityBundle_of_handlerWellTypedSlice h h_typed)

end HandleClauseContract
