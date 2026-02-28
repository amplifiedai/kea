import Kea.Properties.HandlerEffectRemoval

/-!
  Kea.Properties.EffectOperationTyping

  Phase-2 scaffold for effect declarations and operation-call typing.

  This module models:
  - effect declarations with operation signatures
  - operation-call membership in declarations
  - effect-row update at operation call sites
  - direct-call soundness when no handler intercepts the called capability
-/

namespace Kea
namespace EffectOperationTyping

/-- Signature of one operation declared under an effect. -/
structure OperationSig where
  name : Label
  argTy : Ty
  retTy : Ty

/-- Effect declaration: one label plus a list of operation signatures. -/
structure EffectDecl where
  label : Label
  operations : List OperationSig

/-- Operation name appears in an effect declaration. -/
def operationDeclared
    (decl : EffectDecl)
    (opName : Label) : Prop :=
  ∃ sig, sig ∈ decl.operations ∧ sig.name = opName

/--
Typing-side operation-call witness:
the called operation exists in the declaration with matching argument/result types.
-/
def operationCallTyping
    (decl : EffectDecl)
    (opName : Label)
    (argTy retTy : Ty) : Prop :=
  ∃ sig, sig ∈ decl.operations ∧
    sig.name = opName ∧ sig.argTy = argTy ∧ sig.retTy = retTy

theorem operationCallTyping_implies_declared
    (decl : EffectDecl)
    (opName : Label)
    (argTy retTy : Ty)
    (h_call : operationCallTyping decl opName argTy retTy) :
    operationDeclared decl opName := by
  rcases h_call with ⟨sig, h_mem, h_name, _h_arg, _h_ret⟩
  exact ⟨sig, h_mem, h_name⟩

/--
Effect-row update at operation calls:
performing an operation under effect `E` ensures `E` is present in the row.
-/
def performOperationEffects
    (effects : EffectRow)
    (effectLabel : Label) : EffectRow :=
  .mk (.mk
    (RowFields.insertIfAbsent (EffectRow.fields effects) effectLabel Ty.unit)
    (EffectRow.rest effects))

@[simp] theorem fields_performOperationEffects
    (effects : EffectRow)
    (effectLabel : Label) :
    EffectRow.fields (performOperationEffects effects effectLabel) =
      RowFields.insertIfAbsent (EffectRow.fields effects) effectLabel Ty.unit := by
  cases effects with
  | mk row =>
      cases row <;> rfl

@[simp] theorem rest_performOperationEffects
    (effects : EffectRow)
    (effectLabel : Label) :
    EffectRow.rest (performOperationEffects effects effectLabel) =
      EffectRow.rest effects := by
  cases effects with
  | mk row =>
      cases row <;> rfl

theorem performOperation_adds_effect
    (effects : EffectRow)
    (effectLabel : Label) :
    RowFields.has
      (EffectRow.fields (performOperationEffects effects effectLabel))
      effectLabel = true := by
  simp [performOperationEffects]
  exact RowFields.has_insertIfAbsent_self_true
    (EffectRow.fields effects)
    effectLabel
    Ty.unit

theorem performOperation_preserves_other_labels
    (effects : EffectRow)
    (effectLabel other : Label)
    (h_ne : other ≠ effectLabel) :
    RowFields.has
      (EffectRow.fields (performOperationEffects effects effectLabel))
      other =
      RowFields.has (EffectRow.fields effects) other := by
  simp [performOperationEffects]
  exact RowFields.has_insertIfAbsent_of_ne
    (EffectRow.fields effects)
    effectLabel
    other
    Ty.unit
    h_ne

theorem performOperation_preserves_row_tail
    (effects : EffectRow)
    (effectLabel : Label) :
    EffectRow.rest (performOperationEffects effects effectLabel) =
      EffectRow.rest effects := by
  simp [rest_performOperationEffects]

theorem performOperationEffects_preserves_wellFormed
    (kctx : KindCtx) (rctx : RowCtx)
    (effects : EffectRow)
    (effectLabel : Label)
    (h_wf : EffectRow.WellFormed kctx rctx effects) :
    EffectRow.WellFormed kctx rctx (performOperationEffects effects effectLabel) := by
  cases effects with
  | mk row =>
      cases row with
      | mk fs rv =>
          cases rv with
          | none =>
              have h_fields : RowFields.WellFormed kctx rctx fs := by
                simpa [EffectRow.WellFormed, Row.WellFormed] using h_wf
              have h_insert :
                  RowFields.WellFormed kctx rctx
                    (RowFields.insertIfAbsent fs effectLabel Ty.unit) :=
                RowFields.wellFormed_insertIfAbsent
                  kctx
                  rctx
                  fs
                  effectLabel
                  Ty.unit
                  h_fields
                  (by simp [Ty.WellFormed])
              simpa [performOperationEffects, EffectRow.WellFormed, Row.WellFormed] using h_insert
          | some restVar =>
              rcases h_wf with ⟨h_fields, h_rest⟩
              have h_insert :
                  RowFields.WellFormed kctx rctx
                    (RowFields.insertIfAbsent fs effectLabel Ty.unit) :=
                RowFields.wellFormed_insertIfAbsent
                  kctx
                  rctx
                  fs
                  effectLabel
                  Ty.unit
                  h_fields
                  (by simp [Ty.WellFormed])
              exact ⟨h_insert, h_rest⟩

theorem operationCallTyping_adds_declared_effect
    (decl : EffectDecl)
    (effects : EffectRow)
    (opName : Label)
    (argTy retTy : Ty)
    (h_call : operationCallTyping decl opName argTy retTy) :
    RowFields.has
      (EffectRow.fields (performOperationEffects effects decl.label))
      decl.label = true := by
  have _h_declared : operationDeclared decl opName :=
    operationCallTyping_implies_declared decl opName argTy retTy h_call
  exact performOperation_adds_effect effects decl.label

structure OperationCallBundle
    (decl : EffectDecl)
    (effects : EffectRow)
    (opName : Label)
    (argTy retTy : Ty) where
  declared :
    operationDeclared decl opName
  callTyping :
    operationCallTyping decl opName argTy retTy
  effectAdded :
    RowFields.has
      (EffectRow.fields (performOperationEffects effects decl.label))
      decl.label = true
  rowTailStable :
    EffectRow.rest (performOperationEffects effects decl.label) =
      EffectRow.rest effects

/-- Structural decomposition for operation-call bundle. -/
theorem operationCallBundle_iff_components
    (decl : EffectDecl)
    (effects : EffectRow)
    (opName : Label)
    (argTy retTy : Ty) :
    OperationCallBundle decl effects opName argTy retTy
      ↔
      operationDeclared decl opName
      ∧ operationCallTyping decl opName argTy retTy
      ∧
      (RowFields.has
          (EffectRow.fields (performOperationEffects effects decl.label))
          decl.label = true)
      ∧
      (EffectRow.rest (performOperationEffects effects decl.label) =
        EffectRow.rest effects) := by
  constructor
  · intro h_bundle
    exact ⟨
      h_bundle.declared,
      h_bundle.callTyping,
      h_bundle.effectAdded,
      h_bundle.rowTailStable
    ⟩
  · intro h_comp
    exact {
      declared := h_comp.1
      callTyping := h_comp.2.1
      effectAdded := h_comp.2.2.1
      rowTailStable := h_comp.2.2.2
    }

/-- Constructor helper for operation-call bundle decomposition. -/
theorem operationCallBundle_of_components
    (decl : EffectDecl)
    (effects : EffectRow)
    (opName : Label)
    (argTy retTy : Ty)
    (h_comp :
      operationDeclared decl opName
      ∧ operationCallTyping decl opName argTy retTy
      ∧
      (RowFields.has
          (EffectRow.fields (performOperationEffects effects decl.label))
          decl.label = true)
      ∧
      (EffectRow.rest (performOperationEffects effects decl.label) =
        EffectRow.rest effects)) :
    OperationCallBundle decl effects opName argTy retTy :=
  (operationCallBundle_iff_components decl effects opName argTy retTy).2 h_comp

theorem operationCallBundle_as_components_of_components
    (decl : EffectDecl)
    (effects : EffectRow)
    (opName : Label)
    (argTy retTy : Ty)
    (h_comp :
      operationDeclared decl opName
      ∧ operationCallTyping decl opName argTy retTy
      ∧
      (RowFields.has
          (EffectRow.fields (performOperationEffects effects decl.label))
          decl.label = true)
      ∧
      (EffectRow.rest (performOperationEffects effects decl.label) =
        EffectRow.rest effects)) :
    operationDeclared decl opName
    ∧ operationCallTyping decl opName argTy retTy
    ∧
    (RowFields.has
        (EffectRow.fields (performOperationEffects effects decl.label))
        decl.label = true)
    ∧
    (EffectRow.rest (performOperationEffects effects decl.label) =
      EffectRow.rest effects) :=
  (operationCallBundle_iff_components decl effects opName argTy retTy).1
    (operationCallBundle_of_components decl effects opName argTy retTy h_comp)

/-- One-hop decomposition of operation-call bundle. -/
theorem operationCallBundle_as_components
    (decl : EffectDecl)
    (effects : EffectRow)
    (opName : Label)
    (argTy retTy : Ty)
    (h_bundle : OperationCallBundle decl effects opName argTy retTy) :
    operationDeclared decl opName
    ∧ operationCallTyping decl opName argTy retTy
    ∧
    (RowFields.has
        (EffectRow.fields (performOperationEffects effects decl.label))
        decl.label = true)
    ∧
    (EffectRow.rest (performOperationEffects effects decl.label) =
      EffectRow.rest effects) :=
  (operationCallBundle_iff_components decl effects opName argTy retTy).1 h_bundle

theorem operationCallBundle_of_typing
    (decl : EffectDecl)
    (effects : EffectRow)
    (opName : Label)
    (argTy retTy : Ty)
    (h_call : operationCallTyping decl opName argTy retTy) :
    OperationCallBundle decl effects opName argTy retTy := by
  exact {
    declared := operationCallTyping_implies_declared decl opName argTy retTy h_call
    callTyping := h_call
    effectAdded := operationCallTyping_adds_declared_effect decl effects opName argTy retTy h_call
    rowTailStable := performOperation_preserves_row_tail effects decl.label
  }

theorem operationCallBundle_as_components_of_typing
    (decl : EffectDecl)
    (effects : EffectRow)
    (opName : Label)
    (argTy retTy : Ty)
    (h_call : operationCallTyping decl opName argTy retTy) :
    operationDeclared decl opName
    ∧ operationCallTyping decl opName argTy retTy
    ∧
    (RowFields.has
        (EffectRow.fields (performOperationEffects effects decl.label))
        decl.label = true)
    ∧
    (EffectRow.rest (performOperationEffects effects decl.label) =
      EffectRow.rest effects) := by
  exact operationCallBundle_as_components
    decl effects opName argTy retTy
    (operationCallBundle_of_typing decl effects opName argTy retTy h_call)

theorem operationCallBundle_declared_of_typing
    (decl : EffectDecl)
    (effects : EffectRow)
    (opName : Label)
    (argTy retTy : Ty)
    (h_call : operationCallTyping decl opName argTy retTy) :
    operationDeclared decl opName :=
  (operationCallBundle_of_typing decl effects opName argTy retTy h_call).declared

theorem operationCallBundle_callTyping_of_typing
    (decl : EffectDecl)
    (effects : EffectRow)
    (opName : Label)
    (argTy retTy : Ty)
    (h_call : operationCallTyping decl opName argTy retTy) :
    operationCallTyping decl opName argTy retTy :=
  (operationCallBundle_of_typing decl effects opName argTy retTy h_call).callTyping

theorem operationCallBundle_rowTailStable_of_typing
    (decl : EffectDecl)
    (effects : EffectRow)
    (opName : Label)
    (argTy retTy : Ty)
    (h_call : operationCallTyping decl opName argTy retTy) :
    EffectRow.rest (performOperationEffects effects decl.label) =
      EffectRow.rest effects :=
  (operationCallBundle_of_typing decl effects opName argTy retTy h_call).rowTailStable

theorem operationCallBundle_effectAdded_of_typing
    (decl : EffectDecl)
    (effects : EffectRow)
    (opName : Label)
    (argTy retTy : Ty)
    (h_call : operationCallTyping decl opName argTy retTy) :
    RowFields.has
      (EffectRow.fields (performOperationEffects effects decl.label))
      decl.label = true :=
  (operationCallBundle_of_typing decl effects opName argTy retTy h_call).effectAdded

/--
Capability direct-call soundness:
if a handler targets a different effect label, a performed capability effect
remains present after normalized handler composition.
-/
theorem capability_direct_call_sound
    (effects handlerEffects : EffectRow)
    (capability handled : Label)
    (h_ne : capability ≠ handled) :
    RowFields.has
      (EffectRow.fields
        (EffectRow.handleComposeNormalized
          (performOperationEffects effects capability)
          handlerEffects
          handled))
      capability = true := by
  have h_performed :
      RowFields.has
        (EffectRow.fields (performOperationEffects effects capability))
        capability = true :=
    performOperation_adds_effect effects capability
  exact EffectRow.handle_preserves_other_effects_normalized
    (performOperationEffects effects capability)
    handlerEffects
    handled
    capability
    h_ne
    h_performed

end EffectOperationTyping
end Kea
