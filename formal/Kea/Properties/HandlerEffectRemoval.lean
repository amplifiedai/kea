import Kea.WellFormed

/-!
  Kea.Properties.HandlerEffectRemoval — Phase 2 effect-row elimination core.

  This module models the handler-level effect elimination step at the row level:
  handling effect label `E` removes `E` from the handled expression effect row,
  while preserving all other labels and row-tail openness.
-/

namespace RowFields

/-- Remove every field with the target label from a row field list. -/
def removeLabel : RowFields → Label → RowFields
  | .nil, _ => .nil
  | .cons l ty rest, target =>
      if l = target then removeLabel rest target
      else .cons l ty (removeLabel rest target)

@[simp] theorem has_removeLabel_self_false :
    ∀ (rf : RowFields) (target : Label),
      RowFields.has (removeLabel rf target) target = false
  | .nil, _ => by simp [removeLabel, RowFields.has]
  | .cons l ty rest, target => by
      by_cases h_hit : l = target
      · simp [removeLabel, h_hit, has_removeLabel_self_false rest target]
      · have h_beq : (l == target) = false := by simp [h_hit]
        simp [removeLabel, RowFields.has, h_hit, h_beq,
          has_removeLabel_self_false rest target]

@[simp] theorem has_removeLabel_of_ne :
    ∀ (rf : RowFields) (target other : Label),
      other ≠ target →
      RowFields.has (removeLabel rf target) other = RowFields.has rf other
  | .nil, _, _, _ => by simp [removeLabel, RowFields.has]
  | .cons l ty rest, target, other, h_ne => by
      by_cases h_hit : l = target
      · have h_not_other : l ≠ other := by
          intro h_eq
          apply h_ne
          exact h_eq.symm.trans h_hit
        have h_target_not_other : target ≠ other := by
          intro h_eq
          exact h_ne h_eq.symm
        simp [removeLabel, RowFields.has, h_hit, h_target_not_other,
          has_removeLabel_of_ne rest target other h_ne]
      · simp [removeLabel, RowFields.has, h_hit,
          has_removeLabel_of_ne rest target other h_ne]

theorem wellFormed_removeLabel :
    ∀ (kctx : KindCtx) (rctx : RowCtx) (rf : RowFields) (target : Label),
      RowFields.WellFormed kctx rctx rf →
      RowFields.WellFormed kctx rctx (removeLabel rf target)
  | kctx, rctx, .nil, target, h_wf => by
      simpa [removeLabel] using h_wf
  | kctx, rctx, .cons l ty rest, target, h_wf => by
      rcases h_wf with ⟨h_ty, h_rest⟩
      by_cases h_hit : l = target
      · simpa [removeLabel, h_hit] using
          wellFormed_removeLabel kctx rctx rest target h_rest
      · simpa [removeLabel, h_hit] using
          (show RowFields.WellFormed kctx rctx (.cons l ty (removeLabel rest target)) from
            ⟨h_ty, wellFormed_removeLabel kctx rctx rest target h_rest⟩)

@[simp] theorem removeLabel_idempotent :
    ∀ (rf : RowFields) (target : Label),
      removeLabel (removeLabel rf target) target = removeLabel rf target
  | .nil, _ => by simp [removeLabel]
  | .cons l ty rest, target => by
      by_cases h_hit : l = target
      · simp [removeLabel, h_hit, removeLabel_idempotent rest target]
      · simp [removeLabel, h_hit, removeLabel_idempotent rest target]

end RowFields

namespace EffectRow

/-- Fields of an effect row. -/
def fields : EffectRow → RowFields
  | .mk (.mk fs _) => fs

/-- Optional tail variable of an effect row. -/
def rest : EffectRow → Option RowVarId
  | .mk (.mk _ rv) => rv

/--
Core handler-elimination model:
handling `target` removes `target` from the handled effect row fields.
-/
def handleRemove (effects : EffectRow) (target : Label) : EffectRow :=
  match effects with
  | .mk (.mk fs rv) =>
      .mk (.mk (RowFields.removeLabel fs target) rv)

@[simp] theorem fields_handleRemove (effects : EffectRow) (target : Label) :
    fields (handleRemove effects target) = RowFields.removeLabel (fields effects) target := by
  cases effects with
  | mk row =>
      cases row <;> rfl

@[simp] theorem rest_handleRemove (effects : EffectRow) (target : Label) :
    rest (handleRemove effects target) = rest effects := by
  cases effects with
  | mk row =>
      cases row <;> rfl

/-- Phase-2 capstone core theorem: handling an effect removes that effect. -/
theorem handle_removes_effect (effects : EffectRow) (target : Label) :
    RowFields.has (fields (handleRemove effects target)) target = false := by
  simp [fields_handleRemove]

/-- Unhandled effects are preserved by handling a different label. -/
theorem handle_preserves_other_effects
    (effects : EffectRow) (target other : Label) (h_ne : other ≠ target) :
    RowFields.has (fields (handleRemove effects target)) other =
      RowFields.has (fields effects) other := by
  simp [fields_handleRemove, RowFields.has_removeLabel_of_ne, h_ne]

/-- Handling does not change row-tail openness. -/
theorem handle_preserves_row_tail (effects : EffectRow) (target : Label) :
    rest (handleRemove effects target) = rest effects := by
  simp [rest_handleRemove]

/-- Handling the same effect twice is equivalent to handling it once. -/
theorem handle_remove_idempotent (effects : EffectRow) (target : Label) :
    handleRemove (handleRemove effects target) target = handleRemove effects target := by
  cases effects with
  | mk row =>
      cases row with
      | mk fs rv =>
          simp [handleRemove, RowFields.removeLabel_idempotent]

theorem handleRemove_preserves_wellFormed
    (kctx : KindCtx) (rctx : RowCtx)
    (effects : EffectRow) (target : Label)
    (h_wf : EffectRow.WellFormed kctx rctx effects) :
    EffectRow.WellFormed kctx rctx (handleRemove effects target) := by
  cases effects with
  | mk row =>
      cases row with
      | mk fs rv =>
          cases rv with
          | none =>
              simpa [EffectRow.WellFormed, handleRemove, Row.WellFormed] using
                RowFields.wellFormed_removeLabel kctx rctx fs target h_wf
          | some restVar =>
              rcases h_wf with ⟨h_fields, h_rest⟩
              exact ⟨RowFields.wellFormed_removeLabel kctx rctx fs target h_fields, h_rest⟩

end EffectRow
