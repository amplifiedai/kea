import Kea.Properties.HandlerEffectRemoval

/-!
  Kea.Properties.HandlerAbsentEffectNoop

  Runtime-aligned contract surface for absent-effect handling on closed rows.

  This models the inference-side behavior where handling an effect absent from
  a closed body effect row is a semantic no-op on the resulting effect row.
-/

namespace Kea
namespace HandlerAbsentEffectNoop

/--
Closed-row-aware handler composition:
if `target` is absent from a closed effect row, return the body effects
unchanged; otherwise fall back to normalized handler composition.
-/
def handleComposeClosedAware
    (effects handlerEffects : EffectRow)
    (target : Label) : EffectRow :=
  if RowFields.has (EffectRow.fields effects) target = false ∧
      EffectRow.rest effects = none then
    effects
  else
    EffectRow.handleComposeNormalized effects handlerEffects target

theorem handle_absent_effect_noop
    (effects handlerEffects : EffectRow)
    (target : Label)
    (h_abs : RowFields.has (EffectRow.fields effects) target = false)
    (h_closed : EffectRow.rest effects = none) :
    handleComposeClosedAware effects handlerEffects target = effects := by
  unfold handleComposeClosedAware
  simp [h_abs, h_closed]

theorem handle_absent_effect_noop_fields
    (effects handlerEffects : EffectRow)
    (target : Label)
    (h_abs : RowFields.has (EffectRow.fields effects) target = false)
    (h_closed : EffectRow.rest effects = none) :
    EffectRow.fields (handleComposeClosedAware effects handlerEffects target) =
      EffectRow.fields effects := by
  simp [handle_absent_effect_noop effects handlerEffects target h_abs h_closed]

theorem handle_absent_effect_noop_row_tail
    (effects handlerEffects : EffectRow)
    (target : Label)
    (h_abs : RowFields.has (EffectRow.fields effects) target = false)
    (h_closed : EffectRow.rest effects = none) :
    EffectRow.rest (handleComposeClosedAware effects handlerEffects target) =
      EffectRow.rest effects := by
  simp [handle_absent_effect_noop effects handlerEffects target h_abs h_closed]

theorem handleComposeClosedAware_eq_normalized_of_present_or_open
    (effects handlerEffects : EffectRow)
    (target : Label)
    (h_case :
      RowFields.has (EffectRow.fields effects) target = true ∨
        EffectRow.rest effects ≠ none) :
    handleComposeClosedAware effects handlerEffects target =
      EffectRow.handleComposeNormalized effects handlerEffects target := by
  unfold handleComposeClosedAware
  rcases h_case with h_present | h_open
  · by_cases h_closed : EffectRow.rest effects = none
    · simp [h_present, h_closed]
    · simp [h_closed]
  · by_cases h_abs : RowFields.has (EffectRow.fields effects) target = false
    · have h_not_closed : EffectRow.rest effects ≠ none := h_open
      simp [h_abs, h_not_closed]
    · simp [h_abs]

end HandlerAbsentEffectNoop
end Kea
