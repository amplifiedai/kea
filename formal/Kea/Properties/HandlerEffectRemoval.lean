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

theorem removeLabel_noop_of_absent :
    ∀ (rf : RowFields) (target : Label),
      RowFields.has rf target = false →
      removeLabel rf target = rf
  | .nil, _, _ => by simp [removeLabel]
  | .cons l ty rest, target, h_abs => by
      by_cases h_hit : l = target
      · subst h_hit
        have h_impossible : RowFields.has (.cons l ty rest) l = false := h_abs
        simp [RowFields.has] at h_impossible
      · have h_head_false : (l == target) = false := by simp [h_hit]
        have h_rest_abs : RowFields.has rest target = false := by
          simpa [RowFields.has, h_head_false] using h_abs
        simp [removeLabel, h_hit, removeLabel_noop_of_absent rest target h_rest_abs]

/--
Insert a field only when its label is not already present.
This is the row-level idempotent-union primitive used by handler composition.
-/
def insertIfAbsent (base : RowFields) (label : Label) (ty : Ty) : RowFields :=
  if RowFields.has base label then base else .cons label ty base

/-- Idempotent union on row fields (label-level set semantics, type payload kept). -/
def unionIdem : RowFields → RowFields → RowFields
  | base, .nil => base
  | base, .cons l ty rest =>
      unionIdem (insertIfAbsent base l ty) rest

@[simp] theorem has_insertIfAbsent_self_true
    (base : RowFields) (label : Label) (ty : Ty) :
    RowFields.has (insertIfAbsent base label ty) label = true := by
  unfold insertIfAbsent
  by_cases h_has : RowFields.has base label
  · simp [h_has]
  · simp [h_has, RowFields.has]

@[simp] theorem has_insertIfAbsent_of_ne
    (base : RowFields) (label other : Label) (ty : Ty)
    (h_ne : other ≠ label) :
    RowFields.has (insertIfAbsent base label ty) other = RowFields.has base other := by
  unfold insertIfAbsent
  by_cases h_has : RowFields.has base label
  · simp [h_has]
  · have h_label_ne_other : label ≠ other := by
      intro h_eq
      apply h_ne
      exact h_eq.symm
    simp [h_has, RowFields.has, h_label_ne_other]

theorem has_unionIdem_of_has_left_true :
    ∀ (base extra : RowFields) (label : Label),
      RowFields.has base label = true →
      RowFields.has (unionIdem base extra) label = true
  | base, .nil, label, h_has => by simpa [unionIdem] using h_has
  | base, .cons l ty rest, label, h_has => by
      have h_step :
          RowFields.has (insertIfAbsent base l ty) label = true := by
        by_cases h_eq : label = l
        · subst h_eq
          exact has_insertIfAbsent_self_true base label ty
        · have h_same :
              RowFields.has (insertIfAbsent base l ty) label =
                RowFields.has base label :=
            has_insertIfAbsent_of_ne base l label ty h_eq
          rw [h_same]
          exact h_has
      exact has_unionIdem_of_has_left_true (insertIfAbsent base l ty) rest label h_step

theorem has_unionIdem_of_has_right_true :
    ∀ (base extra : RowFields) (label : Label),
      RowFields.has extra label = true →
      RowFields.has (unionIdem base extra) label = true
  | base, .nil, label, h_has => by simp [RowFields.has] at h_has
  | base, .cons l ty rest, label, h_has => by
      by_cases h_eq : l = label
      · subst h_eq
        exact has_unionIdem_of_has_left_true (insertIfAbsent base l ty) rest l
          (has_insertIfAbsent_self_true base l ty)
      · have h_head_false : (l == label) = false := by simp [h_eq]
        have h_rest_true : RowFields.has rest label = true := by
          simpa [RowFields.has, h_head_false] using h_has
        exact has_unionIdem_of_has_right_true (insertIfAbsent base l ty) rest label h_rest_true

theorem has_unionIdem_false_of_false_false :
    ∀ (base extra : RowFields) (label : Label),
      RowFields.has base label = false →
      RowFields.has extra label = false →
      RowFields.has (unionIdem base extra) label = false
  | base, .nil, label, h_base, _ => by simpa [unionIdem] using h_base
  | base, .cons l ty rest, label, h_base, h_extra => by
      by_cases h_eq : l = label
      · subst h_eq
        have : RowFields.has (.cons l ty rest) l = true := by
          simp [RowFields.has]
        simp [this] at h_extra
      · have h_head_false : (l == label) = false := by simp [h_eq]
        have h_rest_false : RowFields.has rest label = false := by
          simpa [RowFields.has, h_head_false] using h_extra
        have h_base_step : RowFields.has (insertIfAbsent base l ty) label = false := by
          have h_ne : label ≠ l := by
            intro h_rev
            exact h_eq h_rev.symm
          simpa [has_insertIfAbsent_of_ne base l label ty h_ne] using h_base
        exact has_unionIdem_false_of_false_false (insertIfAbsent base l ty) rest label
          h_base_step h_rest_false

theorem wellFormed_insertIfAbsent
    (kctx : KindCtx) (rctx : RowCtx)
    (base : RowFields) (label : Label) (ty : Ty)
    (h_base : RowFields.WellFormed kctx rctx base)
    (h_ty : Ty.WellFormed kctx rctx ty) :
    RowFields.WellFormed kctx rctx (insertIfAbsent base label ty) := by
  unfold insertIfAbsent
  by_cases h_has : RowFields.has base label
  · simp [h_has, h_base]
  · simp [h_has]
    exact ⟨h_ty, h_base⟩

theorem wellFormed_unionIdem :
    ∀ (kctx : KindCtx) (rctx : RowCtx) (base extra : RowFields),
      RowFields.WellFormed kctx rctx base →
      RowFields.WellFormed kctx rctx extra →
      RowFields.WellFormed kctx rctx (unionIdem base extra)
  | kctx, rctx, base, .nil, h_base, _ => by simpa [unionIdem] using h_base
  | kctx, rctx, base, .cons l ty rest, h_base, h_extra => by
      rcases h_extra with ⟨h_ty, h_rest⟩
      have h_step : RowFields.WellFormed kctx rctx (insertIfAbsent base l ty) :=
        wellFormed_insertIfAbsent kctx rctx base l ty h_base h_ty
      exact wellFormed_unionIdem kctx rctx (insertIfAbsent base l ty) rest h_step h_rest

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

/--
Spec-level normalized handler composition:
remove handled effect from the expression row, then idempotently union
handler-body effects (label-set semantics).

Note: this models spec normalization even if implementation currently emits
duplicate labels on overlap.
-/
def handleComposeNormalized
    (effects handlerEffects : EffectRow) (target : Label) : EffectRow :=
  let removed := handleRemove effects target
  .mk (.mk
    (RowFields.unionIdem (fields removed) (fields handlerEffects))
    (rest removed))

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

@[simp] theorem fields_handleComposeNormalized
    (effects handlerEffects : EffectRow) (target : Label) :
    fields (handleComposeNormalized effects handlerEffects target) =
      RowFields.unionIdem
        (fields (handleRemove effects target))
        (fields handlerEffects) := by
  cases effects with
  | mk row =>
      cases row with
      | mk fs rv =>
          cases handlerEffects with
          | mk hrow =>
              cases hrow with
              | mk hfs hrv =>
                  simp [handleComposeNormalized, fields, handleRemove]

@[simp] theorem rest_handleComposeNormalized
    (effects handlerEffects : EffectRow) (target : Label) :
    rest (handleComposeNormalized effects handlerEffects target) =
      rest (handleRemove effects target) := by
  cases effects with
  | mk row =>
      cases row with
      | mk fs rv =>
          cases handlerEffects with
          | mk hrow =>
              cases hrow with
              | mk hfs hrv =>
                  simp [handleComposeNormalized, rest, handleRemove]

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

theorem handleRemove_noop_of_absent
    (effects : EffectRow) (target : Label)
    (h_abs : RowFields.has (fields effects) target = false) :
    handleRemove effects target = effects := by
  cases effects with
  | mk row =>
      cases row with
      | mk fs rv =>
          simp [handleRemove, fields] at h_abs ⊢
          simpa [h_abs] using RowFields.removeLabel_noop_of_absent fs target h_abs

/--
Phase-2 composition theorem (spec-normalized):
all handler-body effects are present in the composed result.
-/
theorem handle_adds_handler_effects
    (effects handlerEffects : EffectRow) (target added : Label)
    (h_added : RowFields.has (fields handlerEffects) added = true) :
    RowFields.has (fields (handleComposeNormalized effects handlerEffects target)) added = true := by
  have h_union :
      RowFields.has
        (RowFields.unionIdem (fields (handleRemove effects target)) (fields handlerEffects))
        added = true :=
    RowFields.has_unionIdem_of_has_right_true
    (fields (handleRemove effects target))
    (fields handlerEffects)
    added
    h_added
  simpa [fields_handleComposeNormalized] using h_union

/--
Phase-2 composition theorem (spec-normalized):
unhandled effects from the original expression remain present after handling.
-/
theorem handle_preserves_other_effects_normalized
    (effects handlerEffects : EffectRow) (target other : Label)
    (h_ne : other ≠ target)
    (h_other : RowFields.has (fields effects) other = true) :
    RowFields.has (fields (handleComposeNormalized effects handlerEffects target)) other = true := by
  have h_removed : RowFields.has (fields (handleRemove effects target)) other = true := by
    rw [handle_preserves_other_effects effects target other h_ne]
    exact h_other
  have h_union :
      RowFields.has
        (RowFields.unionIdem (fields (handleRemove effects target)) (fields handlerEffects))
        other = true :=
    RowFields.has_unionIdem_of_has_left_true
    (fields (handleRemove effects target))
    (fields handlerEffects)
    other
    h_removed
  simpa [fields_handleComposeNormalized] using h_union

/--
Phase-2 composition theorem (spec-normalized):
handled effect remains removed if handler-body effects do not re-introduce it.
-/
theorem handle_removes_effect_normalized_of_handler_absent
    (effects handlerEffects : EffectRow) (target : Label)
    (h_handler_absent : RowFields.has (fields handlerEffects) target = false) :
    RowFields.has (fields (handleComposeNormalized effects handlerEffects target)) target = false := by
  have h_removed_absent :
      RowFields.has (fields (handleRemove effects target)) target = false :=
    handle_removes_effect effects target
  have h_union :
      RowFields.has
        (RowFields.unionIdem (fields (handleRemove effects target)) (fields handlerEffects))
        target = false :=
    RowFields.has_unionIdem_false_of_false_false
    (fields (handleRemove effects target))
    (fields handlerEffects)
    target
    h_removed_absent
    h_handler_absent
  simpa [fields_handleComposeNormalized] using h_union

theorem handleComposeNormalized_preserves_wellFormed
    (kctx : KindCtx) (rctx : RowCtx)
    (effects handlerEffects : EffectRow) (target : Label)
    (h_wf_effects : EffectRow.WellFormed kctx rctx effects)
    (h_wf_handler : EffectRow.WellFormed kctx rctx handlerEffects) :
    EffectRow.WellFormed kctx rctx (handleComposeNormalized effects handlerEffects target) := by
  cases effects with
  | mk erow =>
      cases erow with
      | mk efs erv =>
          cases handlerEffects with
          | mk hrow =>
              cases hrow with
              | mk hfs hrv =>
                  have h_efs_wf : RowFields.WellFormed kctx rctx efs := by
                    cases erv with
                    | none =>
                        simpa [EffectRow.WellFormed, Row.WellFormed] using h_wf_effects
                    | some rv =>
                        rcases h_wf_effects with ⟨h_fields, _h_rest⟩
                        exact h_fields
                  have h_hfs_wf : RowFields.WellFormed kctx rctx hfs := by
                    cases hrv with
                    | none =>
                        simpa [EffectRow.WellFormed, Row.WellFormed] using h_wf_handler
                    | some rv =>
                        rcases h_wf_handler with ⟨h_fields, _h_rest⟩
                        exact h_fields
                  have h_removed_fields_wf :
                      RowFields.WellFormed kctx rctx (RowFields.removeLabel efs target) :=
                    RowFields.wellFormed_removeLabel kctx rctx efs target h_efs_wf
                  have h_union_wf :
                      RowFields.WellFormed kctx rctx
                        (RowFields.unionIdem (RowFields.removeLabel efs target) hfs) :=
                    RowFields.wellFormed_unionIdem kctx rctx
                      (RowFields.removeLabel efs target) hfs
                      h_removed_fields_wf h_hfs_wf
                  cases erv with
                  | none =>
                      simpa [handleComposeNormalized, handleRemove, EffectRow.WellFormed, Row.WellFormed]
                        using h_union_wf
                  | some rv =>
                      rcases h_wf_effects with ⟨_h_fields, h_rest⟩
                      exact ⟨h_union_wf, h_rest⟩

theorem handleComposeNormalized_preserves_row_tail
    (effects handlerEffects : EffectRow) (target : Label) :
    rest (handleComposeNormalized effects handlerEffects target) = rest effects := by
  simp [rest_handleComposeNormalized, rest_handleRemove]

/--
Nested same-target handling: if the inner handled result already lacks `target`,
the outer same-target handling step performs no additional removal before
adding outer handler-body effects.
-/
theorem nested_same_target_outer_removal_noop_of_inner_absent
    (effects innerHandler outerHandler : EffectRow) (target : Label)
    (h_inner_abs :
      RowFields.has (fields (handleComposeNormalized effects innerHandler target)) target = false) :
    handleComposeNormalized (handleComposeNormalized effects innerHandler target) outerHandler target =
      .mk (.mk
        (RowFields.unionIdem
          (fields (handleComposeNormalized effects innerHandler target))
          (fields outerHandler))
        (rest (handleComposeNormalized effects innerHandler target))) := by
  have h_fields_noop :
      RowFields.removeLabel
          (fields (handleComposeNormalized effects innerHandler target))
          target =
        fields (handleComposeNormalized effects innerHandler target) :=
    RowFields.removeLabel_noop_of_absent
      (fields (handleComposeNormalized effects innerHandler target))
      target
      h_inner_abs
  have h_union_eq :
      RowFields.unionIdem
          (RowFields.removeLabel
            (fields (handleComposeNormalized effects innerHandler target))
            target)
          (fields outerHandler) =
        RowFields.unionIdem
          (fields (handleComposeNormalized effects innerHandler target))
          (fields outerHandler) := by
    exact congrArg
      (fun fs => RowFields.unionIdem fs (fields outerHandler))
      h_fields_noop
  simpa [handleComposeNormalized] using h_union_eq

/--
Nested same-target handling corollary:
if the outer handler-body does not emit `target`, final effects still lack
`target` (spec-normalized semantics).
-/
theorem nested_same_target_remains_absent_of_outer_absent
    (effects innerHandler outerHandler : EffectRow) (target : Label)
    (h_outer_abs : RowFields.has (fields outerHandler) target = false) :
    RowFields.has
      (fields (handleComposeNormalized
        (handleComposeNormalized effects innerHandler target)
        outerHandler
        target))
      target = false := by
  exact handle_removes_effect_normalized_of_handler_absent
    (handleComposeNormalized effects innerHandler target)
    outerHandler
    target
    h_outer_abs

end EffectRow
