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

end HandleClauseContract
