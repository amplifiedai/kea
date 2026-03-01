import Kea.Properties.HandlerClosedAwareContracts

/-!
  Kea.Properties.NestedHandlerCompositionContracts

  Phase-2 nested same-target handler composition contracts.

  This module packages citable theorem surfaces for the "nested handlers
  compose" target over the normalized row model.
-/

namespace Kea
namespace NestedHandlerCompositionContracts

def nestedCompose
    (effects innerHandler outerHandler : EffectRow)
    (target : Label) : EffectRow :=
  EffectRow.handleComposeNormalized
    (EffectRow.handleComposeNormalized effects innerHandler target)
    outerHandler
    target

def nestedComposeClosedAware
    (effects innerHandler outerHandler : EffectRow)
    (target : Label) : EffectRow :=
  HandlerAbsentEffectNoop.handleComposeClosedAware
    (HandlerAbsentEffectNoop.handleComposeClosedAware effects innerHandler target)
    outerHandler
    target

theorem nested_handlers_compose
    (effects innerHandler outerHandler : EffectRow)
    (target : Label)
    (h_outer_abs :
      RowFields.has (EffectRow.fields outerHandler) target = false) :
    RowFields.has
      (EffectRow.fields (nestedCompose effects innerHandler outerHandler target))
      target = false := by
  exact EffectRow.nested_same_target_remains_absent_of_outer_absent
    effects innerHandler outerHandler target h_outer_abs

theorem nested_handlers_compose_row_tail
    (effects innerHandler outerHandler : EffectRow)
    (target : Label) :
    EffectRow.rest (nestedCompose effects innerHandler outerHandler target) =
      EffectRow.rest effects := by
  unfold nestedCompose
  have h_outer :=
    EffectRow.handleComposeNormalized_preserves_row_tail
      (EffectRow.handleComposeNormalized effects innerHandler target)
      outerHandler
      target
  have h_inner :=
    EffectRow.handleComposeNormalized_preserves_row_tail effects innerHandler target
  exact h_outer.trans h_inner

theorem nested_handlers_compose_preserves_other_effects
    (effects innerHandler outerHandler : EffectRow)
    (target other : Label)
    (h_ne : other ≠ target)
    (h_other :
      RowFields.has (EffectRow.fields effects) other = true) :
    RowFields.has
      (EffectRow.fields (nestedCompose effects innerHandler outerHandler target))
      other = true := by
  unfold nestedCompose
  have h_inner :
      RowFields.has
        (EffectRow.fields (EffectRow.handleComposeNormalized effects innerHandler target))
        other = true :=
    EffectRow.handle_preserves_other_effects_normalized
      effects innerHandler target other h_ne h_other
  exact EffectRow.handle_preserves_other_effects_normalized
    (EffectRow.handleComposeNormalized effects innerHandler target)
    outerHandler
    target
    other
    h_ne
    h_inner

theorem nested_handlers_compose_closedAware
    (effects innerHandler outerHandler : EffectRow)
    (target : Label)
    (h_outer_abs :
      RowFields.has (EffectRow.fields outerHandler) target = false) :
    RowFields.has
      (EffectRow.fields (nestedComposeClosedAware effects innerHandler outerHandler target))
      target = false := by
  unfold nestedComposeClosedAware
  exact HandlerClosedAwareContracts.handleComposeClosedAware_removes_target_of_handler_absent
    (HandlerAbsentEffectNoop.handleComposeClosedAware effects innerHandler target)
    outerHandler
    target
    h_outer_abs

theorem nested_handlers_compose_closedAware_row_tail
    (effects innerHandler outerHandler : EffectRow)
    (target : Label) :
    EffectRow.rest (nestedComposeClosedAware effects innerHandler outerHandler target) =
      EffectRow.rest effects := by
  unfold nestedComposeClosedAware
  have h_outer :=
    HandlerClosedAwareContracts.handleComposeClosedAware_preserves_row_tail
      (HandlerAbsentEffectNoop.handleComposeClosedAware effects innerHandler target)
      outerHandler
      target
  have h_inner :=
    HandlerClosedAwareContracts.handleComposeClosedAware_preserves_row_tail
      effects
      innerHandler
      target
  exact h_outer.trans h_inner

/--
Closed-aware nested composition agrees with normalized nested composition when
both composition stages are on present/open branches.
-/
theorem nestedComposeClosedAware_eq_nestedCompose_of_present_or_open
    (effects innerHandler outerHandler : EffectRow)
    (target : Label)
    (h_inner_case :
      RowFields.has (EffectRow.fields effects) target = true ∨
        EffectRow.rest effects ≠ none)
    (h_outer_case :
      RowFields.has
          (EffectRow.fields
            (HandlerAbsentEffectNoop.handleComposeClosedAware effects innerHandler target))
          target = true ∨
        EffectRow.rest
          (HandlerAbsentEffectNoop.handleComposeClosedAware effects innerHandler target) ≠ none) :
    nestedComposeClosedAware effects innerHandler outerHandler target =
      nestedCompose effects innerHandler outerHandler target := by
  unfold nestedComposeClosedAware nestedCompose
  rw [HandlerAbsentEffectNoop.handleComposeClosedAware_eq_normalized_of_present_or_open
        effects innerHandler target h_inner_case]
  have h_outer_case_normalized :
      RowFields.has
          (EffectRow.fields
            (EffectRow.handleComposeNormalized effects innerHandler target))
          target = true ∨
        EffectRow.rest
          (EffectRow.handleComposeNormalized effects innerHandler target) ≠ none := by
    simpa [HandlerAbsentEffectNoop.handleComposeClosedAware_eq_normalized_of_present_or_open
      effects innerHandler target h_inner_case] using h_outer_case
  rw [HandlerAbsentEffectNoop.handleComposeClosedAware_eq_normalized_of_present_or_open
        (EffectRow.handleComposeNormalized effects innerHandler target)
        outerHandler
        target
        h_outer_case_normalized]

/--
Open-row corollary: if the expression row is open, both closed-aware stages are
forced onto normalized branches, so nested closed-aware composition equals
normalized nested composition.
-/
theorem nestedComposeClosedAware_eq_nestedCompose_of_open_row
    (effects innerHandler outerHandler : EffectRow)
    (target : Label)
    (h_open : EffectRow.rest effects ≠ none) :
    nestedComposeClosedAware effects innerHandler outerHandler target =
      nestedCompose effects innerHandler outerHandler target := by
  apply nestedComposeClosedAware_eq_nestedCompose_of_present_or_open
    effects innerHandler outerHandler target
  · exact Or.inr h_open
  · right
    have h_mid_rest :
        EffectRow.rest
          (HandlerAbsentEffectNoop.handleComposeClosedAware effects innerHandler target) =
          EffectRow.rest effects :=
      HandlerClosedAwareContracts.handleComposeClosedAware_preserves_row_tail
        effects innerHandler target
    rw [h_mid_rest]
    exact h_open

structure NestedHandlerBundle
    (effects innerHandler outerHandler : EffectRow)
    (target : Label) where
  handledRemoved :
    RowFields.has
      (EffectRow.fields (nestedCompose effects innerHandler outerHandler target))
      target = false
  rowTailStable :
    EffectRow.rest (nestedCompose effects innerHandler outerHandler target) =
      EffectRow.rest effects

/-- Structural decomposition for normalized nested handler bundle. -/
theorem nestedHandlerBundle_iff_components
    (effects innerHandler outerHandler : EffectRow)
    (target : Label) :
    NestedHandlerBundle effects innerHandler outerHandler target
      ↔
      (RowFields.has
          (EffectRow.fields (nestedCompose effects innerHandler outerHandler target))
          target = false)
      ∧
      (EffectRow.rest (nestedCompose effects innerHandler outerHandler target) =
        EffectRow.rest effects) := by
  constructor
  · intro h_bundle
    exact ⟨h_bundle.handledRemoved, h_bundle.rowTailStable⟩
  · intro h_comp
    exact {
      handledRemoved := h_comp.1
      rowTailStable := h_comp.2
    }

/-- Constructor helper for normalized nested handler bundle decomposition. -/
theorem nestedHandlerBundle_of_components
    (effects innerHandler outerHandler : EffectRow)
    (target : Label)
    (h_comp :
      (RowFields.has
          (EffectRow.fields (nestedCompose effects innerHandler outerHandler target))
          target = false)
      ∧
      (EffectRow.rest (nestedCompose effects innerHandler outerHandler target) =
        EffectRow.rest effects)) :
    NestedHandlerBundle effects innerHandler outerHandler target :=
  (nestedHandlerBundle_iff_components effects innerHandler outerHandler target).2 h_comp

theorem nestedHandlerBundle_as_components_of_components
    (effects innerHandler outerHandler : EffectRow)
    (target : Label)
    (h_comp :
      (RowFields.has
          (EffectRow.fields (nestedCompose effects innerHandler outerHandler target))
          target = false)
      ∧
      (EffectRow.rest (nestedCompose effects innerHandler outerHandler target) =
        EffectRow.rest effects)) :
    (RowFields.has
        (EffectRow.fields (nestedCompose effects innerHandler outerHandler target))
        target = false)
    ∧
    (EffectRow.rest (nestedCompose effects innerHandler outerHandler target) =
      EffectRow.rest effects) :=
  (nestedHandlerBundle_iff_components effects innerHandler outerHandler target).1
    (nestedHandlerBundle_of_components effects innerHandler outerHandler target h_comp)

/-- One-hop decomposition of normalized nested handler bundle. -/
theorem nestedHandlerBundle_as_components
    (effects innerHandler outerHandler : EffectRow)
    (target : Label)
    (h_bundle : NestedHandlerBundle effects innerHandler outerHandler target) :
    (RowFields.has
        (EffectRow.fields (nestedCompose effects innerHandler outerHandler target))
        target = false)
    ∧
    (EffectRow.rest (nestedCompose effects innerHandler outerHandler target) =
      EffectRow.rest effects) :=
  (nestedHandlerBundle_iff_components effects innerHandler outerHandler target).1 h_bundle

structure NestedHandlerClosedAwareBundle
    (effects innerHandler outerHandler : EffectRow)
    (target : Label) where
  handledRemoved :
    RowFields.has
      (EffectRow.fields (nestedComposeClosedAware effects innerHandler outerHandler target))
      target = false
  rowTailStable :
    EffectRow.rest (nestedComposeClosedAware effects innerHandler outerHandler target) =
      EffectRow.rest effects

/-- Structural decomposition for closed-aware nested handler bundle. -/
theorem nestedHandlerClosedAwareBundle_iff_components
    (effects innerHandler outerHandler : EffectRow)
    (target : Label) :
    NestedHandlerClosedAwareBundle effects innerHandler outerHandler target
      ↔
      (RowFields.has
          (EffectRow.fields (nestedComposeClosedAware effects innerHandler outerHandler target))
          target = false)
      ∧
      (EffectRow.rest (nestedComposeClosedAware effects innerHandler outerHandler target) =
        EffectRow.rest effects) := by
  constructor
  · intro h_bundle
    exact ⟨h_bundle.handledRemoved, h_bundle.rowTailStable⟩
  · intro h_comp
    exact {
      handledRemoved := h_comp.1
      rowTailStable := h_comp.2
    }

/-- Constructor helper for closed-aware nested handler bundle decomposition. -/
theorem nestedHandlerClosedAwareBundle_of_components
    (effects innerHandler outerHandler : EffectRow)
    (target : Label)
    (h_comp :
      (RowFields.has
          (EffectRow.fields (nestedComposeClosedAware effects innerHandler outerHandler target))
          target = false)
      ∧
      (EffectRow.rest (nestedComposeClosedAware effects innerHandler outerHandler target) =
        EffectRow.rest effects)) :
    NestedHandlerClosedAwareBundle effects innerHandler outerHandler target :=
  (nestedHandlerClosedAwareBundle_iff_components effects innerHandler outerHandler target).2 h_comp

theorem nestedHandlerClosedAwareBundle_as_components_of_components
    (effects innerHandler outerHandler : EffectRow)
    (target : Label)
    (h_comp :
      (RowFields.has
          (EffectRow.fields (nestedComposeClosedAware effects innerHandler outerHandler target))
          target = false)
      ∧
      (EffectRow.rest (nestedComposeClosedAware effects innerHandler outerHandler target) =
        EffectRow.rest effects)) :
    (RowFields.has
        (EffectRow.fields (nestedComposeClosedAware effects innerHandler outerHandler target))
        target = false)
    ∧
    (EffectRow.rest (nestedComposeClosedAware effects innerHandler outerHandler target) =
      EffectRow.rest effects) :=
  (nestedHandlerClosedAwareBundle_iff_components effects innerHandler outerHandler target).1
    (nestedHandlerClosedAwareBundle_of_components effects innerHandler outerHandler target h_comp)

/-- One-hop decomposition of closed-aware nested handler bundle. -/
theorem nestedHandlerClosedAwareBundle_as_components
    (effects innerHandler outerHandler : EffectRow)
    (target : Label)
    (h_bundle : NestedHandlerClosedAwareBundle effects innerHandler outerHandler target) :
    (RowFields.has
        (EffectRow.fields (nestedComposeClosedAware effects innerHandler outerHandler target))
        target = false)
    ∧
    (EffectRow.rest (nestedComposeClosedAware effects innerHandler outerHandler target) =
      EffectRow.rest effects) :=
  (nestedHandlerClosedAwareBundle_iff_components effects innerHandler outerHandler target).1 h_bundle

theorem nested_handler_bundle_of_outer_absent
    (effects innerHandler outerHandler : EffectRow)
    (target : Label)
    (h_outer_abs :
      RowFields.has (EffectRow.fields outerHandler) target = false) :
    NestedHandlerBundle effects innerHandler outerHandler target := by
  exact {
    handledRemoved := nested_handlers_compose effects innerHandler outerHandler target h_outer_abs
    rowTailStable := nested_handlers_compose_row_tail effects innerHandler outerHandler target
  }

theorem nested_handler_closedAware_bundle_of_outer_absent
    (effects innerHandler outerHandler : EffectRow)
    (target : Label)
    (h_outer_abs :
      RowFields.has (EffectRow.fields outerHandler) target = false) :
    NestedHandlerClosedAwareBundle effects innerHandler outerHandler target := by
  exact {
    handledRemoved :=
      nested_handlers_compose_closedAware effects innerHandler outerHandler target h_outer_abs
    rowTailStable :=
      nested_handlers_compose_closedAware_row_tail effects innerHandler outerHandler target
  }

/--
Disjoint-target nested composition (`A` then `B`) routed through the shared
effect-row composition model.
-/
def nestedComposeDisjoint
    (effects handlerA handlerB : EffectRow)
    (targetA targetB : Label) : EffectRow :=
  EffectRow.handleComposeTwoTargets effects handlerA handlerB targetA targetB

/--
Disjoint-target nested composition (`B` then `A`) routed through the shared
effect-row composition model.
-/
def nestedComposeDisjointSwap
    (effects handlerA handlerB : EffectRow)
    (targetA targetB : Label) : EffectRow :=
  EffectRow.handleComposeTwoTargetsSwap effects handlerA handlerB targetA targetB

/-- Alias surface for disjoint-target nested composition coherence. -/
abbrev NestedHandlerDisjointCoherence
    (effects handlerA handlerB : EffectRow)
    (targetA targetB : Label) : Prop :=
  EffectRow.DisjointHandlerCompositionCoherence effects handlerA handlerB targetA targetB

/-- Alias components for disjoint-target nested composition coherence. -/
abbrev NestedHandlerDisjointCoherenceComponents
    (effects handlerA handlerB : EffectRow)
    (targetA targetB : Label) : Prop :=
  EffectRow.DisjointHandlerCompositionCoherenceComponents
    effects handlerA handlerB targetA targetB

theorem nestedHandlerDisjointCoherence_iff_components
    (effects handlerA handlerB : EffectRow)
    (targetA targetB : Label) :
    NestedHandlerDisjointCoherence effects handlerA handlerB targetA targetB
      ↔
      NestedHandlerDisjointCoherenceComponents effects handlerA handlerB targetA targetB :=
  EffectRow.disjointHandlerCompositionCoherence_iff_components
    effects handlerA handlerB targetA targetB

theorem nestedHandlerDisjointCoherence_of_components
    (effects handlerA handlerB : EffectRow)
    (targetA targetB : Label)
    (h_comp :
      NestedHandlerDisjointCoherenceComponents effects handlerA handlerB targetA targetB) :
    NestedHandlerDisjointCoherence effects handlerA handlerB targetA targetB :=
  EffectRow.disjointHandlerCompositionCoherence_of_components
    effects handlerA handlerB targetA targetB h_comp

theorem nestedHandlerDisjointCoherence_as_components
    (effects handlerA handlerB : EffectRow)
    (targetA targetB : Label)
    (h :
      NestedHandlerDisjointCoherence effects handlerA handlerB targetA targetB) :
    NestedHandlerDisjointCoherenceComponents effects handlerA handlerB targetA targetB :=
  EffectRow.disjointHandlerCompositionCoherence_as_components
    effects handlerA handlerB targetA targetB h

theorem nestedHandlerDisjointCoherence_as_components_of_components
    (effects handlerA handlerB : EffectRow)
    (targetA targetB : Label)
    (h_comp :
      NestedHandlerDisjointCoherenceComponents effects handlerA handlerB targetA targetB) :
    NestedHandlerDisjointCoherenceComponents effects handlerA handlerB targetA targetB :=
  EffectRow.disjointHandlerCompositionCoherence_as_components_of_components
    effects handlerA handlerB targetA targetB h_comp

/--
Disjoint-target coherence route from handler non-reintroduction premises.
-/
theorem nestedHandlerDisjointCoherence_of_handler_absence
    (effects handlerA handlerB : EffectRow)
    (targetA targetB : Label)
    (h_targets_ne : targetA ≠ targetB)
    (h_handlerA_abs_targetA : RowFields.has (EffectRow.fields handlerA) targetA = false)
    (h_handlerA_abs_targetB : RowFields.has (EffectRow.fields handlerA) targetB = false)
    (h_handlerB_abs_targetA : RowFields.has (EffectRow.fields handlerB) targetA = false)
    (h_handlerB_abs_targetB : RowFields.has (EffectRow.fields handlerB) targetB = false) :
    NestedHandlerDisjointCoherence effects handlerA handlerB targetA targetB :=
  EffectRow.disjoint_handler_composition_coherence_of_handler_absence
    effects handlerA handlerB targetA targetB
    h_targets_ne
    h_handlerA_abs_targetA
    h_handlerA_abs_targetB
    h_handlerB_abs_targetA
    h_handlerB_abs_targetB

theorem nestedHandlerDisjointCoherence_as_components_of_handler_absence
    (effects handlerA handlerB : EffectRow)
    (targetA targetB : Label)
    (h_targets_ne : targetA ≠ targetB)
    (h_handlerA_abs_targetA : RowFields.has (EffectRow.fields handlerA) targetA = false)
    (h_handlerA_abs_targetB : RowFields.has (EffectRow.fields handlerA) targetB = false)
    (h_handlerB_abs_targetA : RowFields.has (EffectRow.fields handlerB) targetA = false)
    (h_handlerB_abs_targetB : RowFields.has (EffectRow.fields handlerB) targetB = false) :
    NestedHandlerDisjointCoherenceComponents effects handlerA handlerB targetA targetB :=
  EffectRow.disjoint_handler_composition_coherence_as_components_of_handler_absence
    effects handlerA handlerB targetA targetB
    h_targets_ne
    h_handlerA_abs_targetA
    h_handlerA_abs_targetB
    h_handlerB_abs_targetA
    h_handlerB_abs_targetB

/--
Alias surface for disjoint-target nested composition commutation up to
label-observational equivalence.
-/
abbrev NestedHandlerDisjointLabelObservationalEq
    (effects handlerA handlerB : EffectRow)
    (targetA targetB : Label) : Prop :=
  EffectRow.LabelObservationalEq
    (nestedComposeDisjoint effects handlerA handlerB targetA targetB)
    (nestedComposeDisjointSwap effects handlerA handlerB targetA targetB)

theorem nestedHandlerDisjointLabelObservationalEq_of_handler_absence
    (effects handlerA handlerB : EffectRow)
    (targetA targetB : Label)
    (h_targets_ne : targetA ≠ targetB)
    (h_handlerA_abs_targetA : RowFields.has (EffectRow.fields handlerA) targetA = false)
    (h_handlerA_abs_targetB : RowFields.has (EffectRow.fields handlerA) targetB = false)
    (h_handlerB_abs_targetA : RowFields.has (EffectRow.fields handlerB) targetA = false)
    (h_handlerB_abs_targetB : RowFields.has (EffectRow.fields handlerB) targetB = false) :
    NestedHandlerDisjointLabelObservationalEq effects handlerA handlerB targetA targetB :=
  EffectRow.disjoint_handler_composition_labelObservationalEq_of_handler_absence
    effects handlerA handlerB targetA targetB
    h_targets_ne
    h_handlerA_abs_targetA
    h_handlerA_abs_targetB
    h_handlerB_abs_targetA
    h_handlerB_abs_targetB

theorem nestedHandlerDisjointLabelObservationalEq_rest_eq_of_handler_absence
    (effects handlerA handlerB : EffectRow)
    (targetA targetB : Label)
    (h_targets_ne : targetA ≠ targetB)
    (h_handlerA_abs_targetA : RowFields.has (EffectRow.fields handlerA) targetA = false)
    (h_handlerA_abs_targetB : RowFields.has (EffectRow.fields handlerA) targetB = false)
    (h_handlerB_abs_targetA : RowFields.has (EffectRow.fields handlerB) targetA = false)
    (h_handlerB_abs_targetB : RowFields.has (EffectRow.fields handlerB) targetB = false) :
    EffectRow.rest (nestedComposeDisjoint effects handlerA handlerB targetA targetB) =
      EffectRow.rest (nestedComposeDisjointSwap effects handlerA handlerB targetA targetB) :=
  (nestedHandlerDisjointLabelObservationalEq_of_handler_absence
    effects handlerA handlerB targetA targetB
    h_targets_ne
    h_handlerA_abs_targetA
    h_handlerA_abs_targetB
    h_handlerB_abs_targetA
    h_handlerB_abs_targetB).1

theorem nestedHandlerDisjointLabelObservationalEq_has_eq_of_handler_absence
    (effects handlerA handlerB : EffectRow)
    (targetA targetB : Label)
    (label : Label)
    (h_targets_ne : targetA ≠ targetB)
    (h_handlerA_abs_targetA : RowFields.has (EffectRow.fields handlerA) targetA = false)
    (h_handlerA_abs_targetB : RowFields.has (EffectRow.fields handlerA) targetB = false)
    (h_handlerB_abs_targetA : RowFields.has (EffectRow.fields handlerB) targetA = false)
    (h_handlerB_abs_targetB : RowFields.has (EffectRow.fields handlerB) targetB = false) :
    RowFields.has
      (EffectRow.fields (nestedComposeDisjoint effects handlerA handlerB targetA targetB))
      label =
    RowFields.has
      (EffectRow.fields (nestedComposeDisjointSwap effects handlerA handlerB targetA targetB))
      label :=
  (nestedHandlerDisjointLabelObservationalEq_of_handler_absence
    effects handlerA handlerB targetA targetB
    h_targets_ne
    h_handlerA_abs_targetA
    h_handlerA_abs_targetB
    h_handlerB_abs_targetA
    h_handlerB_abs_targetB).2 label

end NestedHandlerCompositionContracts
end Kea
