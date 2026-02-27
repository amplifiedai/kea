import Kea.Properties.HandlerTypingContracts
import Kea.Properties.HandlerAbsentEffectNoop

/-!
  Kea.Properties.HandlerClosedAwareContracts

  Bridge layer that lifts closed-row absent-effect no-op semantics into the
  clause-level handler contract API.
-/

namespace Kea
namespace HandlerClosedAwareContracts

/-- Closed-aware core result effects for a handler clause contract. -/
def resultEffectsCoreClosedAware (c : HandleClauseContract) : EffectRow :=
  HandlerAbsentEffectNoop.handleComposeClosedAware
    c.exprEffects
    c.handlerEffects
    c.handled

/-- Closed-aware full result effects including optional `then` effects. -/
def resultEffectsClosedAware (c : HandleClauseContract) : EffectRow :=
  HandleClauseContract.applyThenEffects
    (resultEffectsCoreClosedAware c)
    c.thenEffects

theorem resultEffectsCoreClosedAware_noop_of_handled_absent_closed
    (c : HandleClauseContract)
    (h_abs : RowFields.has (EffectRow.fields c.exprEffects) c.handled = false)
    (h_closed : EffectRow.rest c.exprEffects = none) :
    resultEffectsCoreClosedAware c = c.exprEffects := by
  unfold resultEffectsCoreClosedAware
  exact HandlerAbsentEffectNoop.handle_absent_effect_noop
    c.exprEffects c.handlerEffects c.handled h_abs h_closed

theorem resultEffectsCoreClosedAware_eq_normalized_of_present_or_open
    (c : HandleClauseContract)
    (h_case :
      RowFields.has (EffectRow.fields c.exprEffects) c.handled = true ∨
        EffectRow.rest c.exprEffects ≠ none) :
    resultEffectsCoreClosedAware c = HandleClauseContract.resultEffectsCore c := by
  unfold resultEffectsCoreClosedAware HandleClauseContract.resultEffectsCore
  exact HandlerAbsentEffectNoop.handleComposeClosedAware_eq_normalized_of_present_or_open
    c.exprEffects c.handlerEffects c.handled h_case

theorem resultEffectsClosedAware_noop_of_handled_absent_closed_then_none
    (c : HandleClauseContract)
    (h_abs : RowFields.has (EffectRow.fields c.exprEffects) c.handled = false)
    (h_closed : EffectRow.rest c.exprEffects = none)
    (h_then_none : c.thenEffects = none) :
    resultEffectsClosedAware c = c.exprEffects := by
  unfold resultEffectsClosedAware
  rw [h_then_none]
  simp [HandleClauseContract.applyThenEffects,
    resultEffectsCoreClosedAware_noop_of_handled_absent_closed c h_abs h_closed]

theorem resultEffectsClosedAware_eq_resultEffects_of_present_or_open
    (c : HandleClauseContract)
    (h_case :
      RowFields.has (EffectRow.fields c.exprEffects) c.handled = true ∨
        EffectRow.rest c.exprEffects ≠ none) :
    resultEffectsClosedAware c = HandleClauseContract.resultEffects c := by
  unfold resultEffectsClosedAware HandleClauseContract.resultEffects
  rw [resultEffectsCoreClosedAware_eq_normalized_of_present_or_open c h_case]

theorem resultEffectsClosedAware_rest_of_then_none
    (c : HandleClauseContract)
    (h_then_none : c.thenEffects = none) :
    EffectRow.rest (resultEffectsClosedAware c) =
      EffectRow.rest (resultEffectsCoreClosedAware c) := by
  unfold resultEffectsClosedAware
  rw [h_then_none]
  simp [HandleClauseContract.applyThenEffects]

theorem resultEffectsClosedAware_absent_closed_reduces_to_applyThen
    (c : HandleClauseContract)
    (h_abs : RowFields.has (EffectRow.fields c.exprEffects) c.handled = false)
    (h_closed : EffectRow.rest c.exprEffects = none) :
    resultEffectsClosedAware c =
      HandleClauseContract.applyThenEffects c.exprEffects c.thenEffects := by
  unfold resultEffectsClosedAware
  rw [resultEffectsCoreClosedAware_noop_of_handled_absent_closed c h_abs h_closed]

/--
Closed-aware final row-tail stability: the optional `then` merge keeps the
row tail from the expression effect row in all branches.
-/
theorem resultEffectsClosedAware_preserves_row_tail
    (c : HandleClauseContract) :
    EffectRow.rest (resultEffectsClosedAware c) = EffectRow.rest c.exprEffects := by
  by_cases h_abs : RowFields.has (EffectRow.fields c.exprEffects) c.handled = false
  · by_cases h_closed : EffectRow.rest c.exprEffects = none
    · rw [resultEffectsClosedAware_absent_closed_reduces_to_applyThen c h_abs h_closed]
      rw [HandleClauseContract.applyThenEffects_rest]
    · have h_case :
        RowFields.has (EffectRow.fields c.exprEffects) c.handled = true ∨
          EffectRow.rest c.exprEffects ≠ none := Or.inr h_closed
      rw [resultEffectsClosedAware_eq_resultEffects_of_present_or_open c h_case]
      unfold HandleClauseContract.resultEffects
      rw [HandleClauseContract.applyThenEffects_rest]
      unfold HandleClauseContract.resultEffectsCore
      exact EffectRow.handleComposeNormalized_preserves_row_tail
        c.exprEffects c.handlerEffects c.handled
  · have h_present : RowFields.has (EffectRow.fields c.exprEffects) c.handled = true := by
      cases h_has : RowFields.has (EffectRow.fields c.exprEffects) c.handled <;> simp [h_has] at h_abs ⊢
    have h_case :
        RowFields.has (EffectRow.fields c.exprEffects) c.handled = true ∨
          EffectRow.rest c.exprEffects ≠ none := Or.inl h_present
    rw [resultEffectsClosedAware_eq_resultEffects_of_present_or_open c h_case]
    unfold HandleClauseContract.resultEffects
    rw [HandleClauseContract.applyThenEffects_rest]
    unfold HandleClauseContract.resultEffectsCore
    exact EffectRow.handleComposeNormalized_preserves_row_tail
      c.exprEffects c.handlerEffects c.handled

/--
`wellTypedSlice` remains sufficient for handled-label removal under
closed-aware handler composition.
-/
theorem wellTypedSlice_implies_handled_removed_closedAware
    (c : HandleClauseContract)
    (h_wt : HandleClauseContract.wellTypedSlice c) :
    RowFields.has (EffectRow.fields (resultEffectsClosedAware c)) c.handled = false := by
  by_cases h_abs : RowFields.has (EffectRow.fields c.exprEffects) c.handled = false
  · by_cases h_closed : EffectRow.rest c.exprEffects = none
    · rw [resultEffectsClosedAware_absent_closed_reduces_to_applyThen c h_abs h_closed]
      cases h_then : c.thenEffects with
      | none =>
          simpa [HandleClauseContract.applyThenEffects, h_then] using h_abs
      | some te =>
          have h_then_abs :
              RowFields.has (EffectRow.fields te) c.handled = false := by
            have h_no_then := HandleClauseContract.wellTypedSlice_noHandledReintroThen c h_wt
            simpa [HandleClauseContract.noHandledReintroThen, h_then] using h_no_then
          exact HandleClauseContract.applyThenEffects_preserves_handled_absent_of_then_absent
            c.exprEffects te c.handled h_abs h_then_abs
    · have h_case :
        RowFields.has (EffectRow.fields c.exprEffects) c.handled = true ∨
          EffectRow.rest c.exprEffects ≠ none := Or.inr h_closed
      rw [resultEffectsClosedAware_eq_resultEffects_of_present_or_open c h_case]
      exact HandleClauseContract.wellTypedSlice_implies_handled_removed c h_wt
  · have h_present : RowFields.has (EffectRow.fields c.exprEffects) c.handled = true := by
      cases h_has : RowFields.has (EffectRow.fields c.exprEffects) c.handled <;> simp [h_has] at h_abs ⊢
    have h_case :
        RowFields.has (EffectRow.fields c.exprEffects) c.handled = true ∨
          EffectRow.rest c.exprEffects ≠ none := Or.inl h_present
    rw [resultEffectsClosedAware_eq_resultEffects_of_present_or_open c h_case]
    exact HandleClauseContract.wellTypedSlice_implies_handled_removed c h_wt

/--
Closed-aware branch classifier:
- absent+closed branch reduces to body effects (core no-op),
- present/open branch agrees with normalized core semantics.
-/
theorem resultEffectsCoreClosedAware_branch_classification
    (c : HandleClauseContract) :
    (∃ (_ : RowFields.has (EffectRow.fields c.exprEffects) c.handled = false)
       (_ : EffectRow.rest c.exprEffects = none),
      resultEffectsCoreClosedAware c = c.exprEffects) ∨
    (∃ (_ :
      RowFields.has (EffectRow.fields c.exprEffects) c.handled = true ∨
        EffectRow.rest c.exprEffects ≠ none),
      resultEffectsCoreClosedAware c = HandleClauseContract.resultEffectsCore c) := by
  by_cases h_abs : RowFields.has (EffectRow.fields c.exprEffects) c.handled = false
  · by_cases h_closed : EffectRow.rest c.exprEffects = none
    · left
      exact ⟨h_abs, h_closed,
        resultEffectsCoreClosedAware_noop_of_handled_absent_closed c h_abs h_closed⟩
    · right
      exact ⟨Or.inr h_closed,
        resultEffectsCoreClosedAware_eq_normalized_of_present_or_open c (Or.inr h_closed)⟩
  · right
    have h_present : RowFields.has (EffectRow.fields c.exprEffects) c.handled = true := by
      cases h_has : RowFields.has (EffectRow.fields c.exprEffects) c.handled <;> simp [h_has] at h_abs ⊢
    exact ⟨Or.inl h_present,
      resultEffectsCoreClosedAware_eq_normalized_of_present_or_open c (Or.inl h_present)⟩

structure ClosedAwareCoreBundle (c : HandleClauseContract) where
  absentClosedNoop :
    RowFields.has (EffectRow.fields c.exprEffects) c.handled = false →
    EffectRow.rest c.exprEffects = none →
      resultEffectsCoreClosedAware c = c.exprEffects
  presentOrOpenNormalized :
    (RowFields.has (EffectRow.fields c.exprEffects) c.handled = true ∨
      EffectRow.rest c.exprEffects ≠ none) →
      resultEffectsCoreClosedAware c = HandleClauseContract.resultEffectsCore c

theorem closedAwareCoreBundle_of_classification
    (c : HandleClauseContract) :
    ClosedAwareCoreBundle c := by
  refine {
    absentClosedNoop := ?_
    presentOrOpenNormalized := ?_
  }
  · intro h_abs h_closed
    exact resultEffectsCoreClosedAware_noop_of_handled_absent_closed c h_abs h_closed
  · intro h_case
    exact resultEffectsCoreClosedAware_eq_normalized_of_present_or_open c h_case

end HandlerClosedAwareContracts
end Kea
