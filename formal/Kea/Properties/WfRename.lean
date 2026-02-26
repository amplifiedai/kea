import Kea.Generalize
import Kea.WellFormed

/-
  Kea.Properties.WfRename — WF preservation for variable renaming.

  Used as scaffolding for instantiate-WF proofs: if a renaming maps variables
  to variables that are in-scope in the target contexts, then renaming preserves
  well-formedness for types/rows/type-lists/row-fields/effect-rows.
-/

def VarMapping.RespectsCtx (m : VarMapping) (kctx : KindCtx) (rctx : RowCtx) : Prop :=
  (∀ v newV, m.lookupType v = some newV → ∃ k, (newV, k) ∈ kctx) ∧
  (∀ rv newRv, m.lookupRow rv = some newRv → newRv ∈ rctx)

mutual
  theorem renameType_preserves_wf
      (m : VarMapping) (kctx : KindCtx) (rctx : RowCtx)
      (h_respects : m.RespectsCtx kctx rctx) :
      ∀ ty, Ty.WellFormed kctx rctx ty → Ty.WellFormed kctx rctx (renameType ty m) := by
    intro ty h_wf
    cases ty with
    | var v =>
      cases h_lookup : m.lookupType v with
      | none =>
        simpa [renameType, h_lookup] using h_wf
      | some newV =>
        simpa [renameType, h_lookup] using h_respects.1 v newV h_lookup
    | int | intN _ _ | float | floatN _ | decimal _ _ | bool | string | html | markdown
      | atom | date | dateTime | unit | dynamic =>
      simpa [renameType] using h_wf
    | list inner | set inner | option inner | fixedSizeList inner _ | tensor inner _
      | dataframe inner | column inner | stream inner | task inner | actor inner | arc inner
      | groupedFrame inner _ | tagged inner _ =>
      simpa [Ty.WellFormed, renameType] using renameType_preserves_wf m kctx rctx h_respects inner h_wf
    | map k v | result k v =>
      rcases h_wf with ⟨h_k, h_v⟩
      exact ⟨
        by simpa [renameType] using renameType_preserves_wf m kctx rctx h_respects k h_k,
        by simpa [renameType] using renameType_preserves_wf m kctx rctx h_respects v h_v
      ⟩
    | sum _ args | «opaque» _ args | existential _ args | tuple args =>
      simpa [Ty.WellFormed, renameType] using
        renameTyList_preserves_wf m kctx rctx h_respects args h_wf
    | record _ r | anonRecord r | row r =>
      simpa [Ty.WellFormed, renameType] using
        renameRow_preserves_wf m kctx rctx h_respects r h_wf
    | function params ret =>
      rcases h_wf with ⟨h_params, h_ret⟩
      exact ⟨
        by simpa [renameType] using renameTyList_preserves_wf m kctx rctx h_respects params h_params,
        by simpa [renameType] using renameType_preserves_wf m kctx rctx h_respects ret h_ret
      ⟩
    | functionEff params effects ret =>
      rcases h_wf with ⟨h_params, h_eff, h_ret⟩
      exact ⟨
        by simpa [renameType] using renameTyList_preserves_wf m kctx rctx h_respects params h_params,
        by simpa [renameType] using renameEffectRow_preserves_wf m kctx rctx h_respects effects h_eff,
        by simpa [renameType] using renameType_preserves_wf m kctx rctx h_respects ret h_ret
      ⟩
    | «forall» _ body =>
      simpa [Ty.WellFormed, renameType] using renameType_preserves_wf m kctx rctx h_respects body h_wf
    | app ctor args =>
      rcases h_wf with ⟨h_ctor, h_args⟩
      exact ⟨
        by simpa [renameType] using renameType_preserves_wf m kctx rctx h_respects ctor h_ctor,
        by simpa [renameType] using renameTyList_preserves_wf m kctx rctx h_respects args h_args
      ⟩
    | constructor _ fixedArgs _ =>
      simpa [Ty.WellFormed, renameType] using
        renameTyList_preserves_wf m kctx rctx h_respects fixedArgs h_wf

  theorem renameRow_preserves_wf
      (m : VarMapping) (kctx : KindCtx) (rctx : RowCtx)
      (h_respects : m.RespectsCtx kctx rctx) :
      ∀ r, Row.WellFormed kctx rctx r → Row.WellFormed kctx rctx (renameRow r m) := by
    intro r h_wf
    cases r with
    | mk fields rest =>
      cases rest with
      | none =>
        have h_fields : RowFields.WellFormed kctx rctx (renameRowFields fields m) :=
          renameRowFields_preserves_wf m kctx rctx h_respects fields (by simpa [Row.WellFormed] using h_wf)
        simpa [Row.WellFormed, renameRow] using h_fields
      | some rv =>
        rcases h_wf with ⟨h_fields_wf, h_rv⟩
        have h_fields : RowFields.WellFormed kctx rctx (renameRowFields fields m) :=
          renameRowFields_preserves_wf m kctx rctx h_respects fields h_fields_wf
        cases h_lookup : m.lookupRow rv with
        | none =>
          simpa [Row.WellFormed, renameRow, h_lookup] using And.intro h_fields h_rv
        | some newRv =>
          have h_new : newRv ∈ rctx := h_respects.2 rv newRv h_lookup
          simpa [Row.WellFormed, renameRow, h_lookup] using And.intro h_fields h_new

  theorem renameTyList_preserves_wf
      (m : VarMapping) (kctx : KindCtx) (rctx : RowCtx)
      (h_respects : m.RespectsCtx kctx rctx) :
      ∀ tl, TyList.WellFormed kctx rctx tl → TyList.WellFormed kctx rctx (renameTyList tl m) := by
    intro tl h_wf
    cases tl with
    | nil =>
      simp [TyList.WellFormed, renameTyList]
    | cons t rest =>
      rcases h_wf with ⟨h_t, h_rest⟩
      exact ⟨
        by simpa [renameTyList] using renameType_preserves_wf m kctx rctx h_respects t h_t,
        by simpa [renameTyList] using renameTyList_preserves_wf m kctx rctx h_respects rest h_rest
      ⟩

  theorem renameRowFields_preserves_wf
      (m : VarMapping) (kctx : KindCtx) (rctx : RowCtx)
      (h_respects : m.RespectsCtx kctx rctx) :
      ∀ rf, RowFields.WellFormed kctx rctx rf → RowFields.WellFormed kctx rctx (renameRowFields rf m) := by
    intro rf h_wf
    cases rf with
    | nil =>
      simp [RowFields.WellFormed, renameRowFields]
    | cons l ty rest =>
      rcases h_wf with ⟨h_ty, h_rest⟩
      exact ⟨
        by simpa [renameRowFields] using renameType_preserves_wf m kctx rctx h_respects ty h_ty,
        by simpa [renameRowFields] using renameRowFields_preserves_wf m kctx rctx h_respects rest h_rest
      ⟩

  theorem renameEffectRow_preserves_wf
      (m : VarMapping) (kctx : KindCtx) (rctx : RowCtx)
      (h_respects : m.RespectsCtx kctx rctx) :
      ∀ effects, EffectRow.WellFormed kctx rctx effects →
        EffectRow.WellFormed kctx rctx (renameEffectRow effects m) := by
    intro effects h_wf
    cases effects with
    | mk row =>
      simpa [EffectRow.WellFormed, renameEffectRow] using
        renameRow_preserves_wf m kctx rctx h_respects row h_wf
end
