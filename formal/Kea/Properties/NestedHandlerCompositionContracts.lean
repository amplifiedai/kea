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

end NestedHandlerCompositionContracts
end Kea
