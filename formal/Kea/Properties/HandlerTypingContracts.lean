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
  resumeUse : ResumeUse

namespace HandleClauseContract

/-- Resulting effects under spec-normalized handler composition. -/
def resultEffects (c : HandleClauseContract) : EffectRow :=
  EffectRow.handleComposeNormalized c.exprEffects c.handlerEffects c.handled

/-- Resume-linearity premise for clause legality. -/
def linearityOk (c : HandleClauseContract) : Prop :=
  ResumeUse.atMostOnce c.resumeUse

/--
Effect-side premise used by the current removal theorem:
handler-body effects do not re-introduce the handled label.
-/
def noHandledReintro (c : HandleClauseContract) : Prop :=
  RowFields.has (EffectRow.fields c.handlerEffects) c.handled = false

/-- Combined Phase-2 contract (current slice). -/
def wellTypedSlice (c : HandleClauseContract) : Prop :=
  linearityOk c ∧ noHandledReintro c

theorem wellTypedSlice_linearity (c : HandleClauseContract)
    (h : wellTypedSlice c) :
    linearityOk c := h.1

theorem wellTypedSlice_noHandledReintro (c : HandleClauseContract)
    (h : wellTypedSlice c) :
    noHandledReintro c := h.2

/--
Integration theorem: from the combined slice, handled effect remains removed
in the result effect row (under current non-reintroduction premise).
-/
theorem wellTypedSlice_implies_handled_removed
    (c : HandleClauseContract)
    (h : wellTypedSlice c) :
    RowFields.has (EffectRow.fields (resultEffects c)) c.handled = false := by
  exact EffectRow.handle_removes_effect_normalized_of_handler_absent
    c.exprEffects
    c.handlerEffects
    c.handled
    h.2

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
