import Kea.Generalize
import Kea.WellFormed
import Kea.Properties.SubstIdempotent
import Kea.Properties.WfRename

/-
  Kea.Properties.WfGeneralize — WF lemmas for generalize/instantiate.

  Phase-1 baseline contracts:
  - generalization preserves WF when substitution is a no-op on the type
  - empty-substitution generalization preserves WF
  - monomorphic instantiation preserves WF
-/

theorem generalize_preserves_wf_of_no_domain_vars
    (ty : Ty) (env : TypeEnv) (s : Subst) (lc : Lacks) (traitBounds : TraitBounds) (fuel : Nat)
    (kctx : KindCtx) (rctx : RowCtx)
    (h_wf : Ty.WellFormed kctx rctx ty)
    (htv : ∀ v ∈ freeTypeVars ty, s.typeMap v = none)
    (hrv : ∀ v ∈ freeRowVars ty, s.rowMap v = none) :
    Ty.WellFormed kctx rctx (generalize ty env s lc traitBounds fuel).ty := by
  unfold generalize
  rw [(applySubst_noop s fuel).1 ty htv hrv]
  exact h_wf

theorem generalize_empty_preserves_wf
    (ty : Ty) (env : TypeEnv) (lc : Lacks) (traitBounds : TraitBounds) (fuel : Nat)
    (kctx : KindCtx) (rctx : RowCtx)
    (h_wf : Ty.WellFormed kctx rctx ty) :
    Ty.WellFormed kctx rctx (generalize ty env Subst.empty lc traitBounds fuel).ty := by
  apply generalize_preserves_wf_of_no_domain_vars ty env Subst.empty lc traitBounds fuel kctx rctx h_wf
  · intro _ _; rfl
  · intro _ _; rfl

theorem generalize_functionEff_preserves_wf_of_component_no_domain_vars
    (env : TypeEnv) (s : Subst) (lc : Lacks) (traitBounds : TraitBounds) (fuel : Nat)
    (kctx : KindCtx) (rctx : RowCtx)
    (params : TyList) (effects : EffectRow) (ret : Ty)
    (h_wf_params : TyList.WellFormed kctx rctx params)
    (h_wf_effects : EffectRow.WellFormed kctx rctx effects)
    (h_wf_ret : Ty.WellFormed kctx rctx ret)
    (htv_params : ∀ v ∈ freeTypeVarsTyList params, s.typeMap v = none)
    (hrv_params : ∀ v ∈ freeRowVarsTyList params, s.rowMap v = none)
    (htv_effects : ∀ v ∈ freeTypeVarsEffectRow effects, s.typeMap v = none)
    (hrv_effects : ∀ v ∈ freeRowVarsEffectRow effects, s.rowMap v = none)
    (htv_ret : ∀ v ∈ freeTypeVars ret, s.typeMap v = none)
    (hrv_ret : ∀ v ∈ freeRowVars ret, s.rowMap v = none) :
    Ty.WellFormed kctx rctx
      (generalize (.functionEff params effects ret) env s lc traitBounds fuel).ty := by
  exact generalize_preserves_wf_of_no_domain_vars
    (.functionEff params effects ret) env s lc traitBounds fuel kctx rctx
    ⟨h_wf_params, h_wf_effects, h_wf_ret⟩
    (fun v hv => by
      rcases (by simpa [freeTypeVars, List.mem_append] using hv) with h_params | h_rest
      · exact htv_params v h_params
      · rcases (by simpa [List.mem_append] using h_rest) with h_eff | h_r
        · exact htv_effects v h_eff
        · exact htv_ret v h_r)
    (fun v hv => by
      rcases (by simpa [freeRowVars, List.mem_append] using hv) with h_params | h_rest
      · exact hrv_params v h_params
      · rcases (by simpa [List.mem_append] using h_rest) with h_eff | h_r
        · exact hrv_effects v h_eff
        · exact hrv_ret v h_r)

theorem instantiate_mono_eq
    (scheme : TypeScheme) (st : UnifyState)
    (h_mono : scheme.isMono = true) :
    instantiate scheme st = (scheme.ty, st) := by
  unfold instantiate
  simp [h_mono]

theorem instantiate_mono_preserves_wf
    (scheme : TypeScheme) (st : UnifyState) (kctx : KindCtx) (rctx : RowCtx)
    (h_mono : scheme.isMono = true)
    (h_wf : Ty.WellFormed kctx rctx scheme.ty) :
    Ty.WellFormed kctx rctx (instantiate scheme st).1 := by
  rw [instantiate_mono_eq scheme st h_mono]
  simpa using h_wf

/-- Type-variable instantiation fold used by `instantiate`. -/
def instantiateTypeFold (scheme : TypeScheme) (st : UnifyState) :
    List (TypeVarId × TypeVarId) × UnifyState :=
  scheme.typeVars.foldl
    (fun (acc, st) tv =>
      let (fresh, st') := st.freshTypeVar
      ((tv, fresh) :: acc, st'))
    ([], st)

/-- Row-variable instantiation fold used by `instantiate`. -/
def instantiateRowFold (scheme : TypeScheme) (st : UnifyState) :
    List (RowVarId × RowVarId) × UnifyState :=
  scheme.rowVars.foldl
    (fun (acc, st) rv =>
      let (fresh, st') := st.freshRowVar
      ((rv, fresh) :: acc, st'))
    ([], (instantiateTypeFold scheme st).2)

/-- Variable renaming map induced by instantiation folds. -/
def instantiateVarMapping (scheme : TypeScheme) (st : UnifyState) : VarMapping :=
  { typeMap := (instantiateTypeFold scheme st).1
    rowMap := (instantiateRowFold scheme st).1 }

theorem instantiate_preserves_wf_of_instantiateVarMapping_respects_ctx
    (scheme : TypeScheme) (st : UnifyState) (kctx : KindCtx) (rctx : RowCtx)
    (h_wf : Ty.WellFormed kctx rctx scheme.ty)
    (h_respects : (instantiateVarMapping scheme st).RespectsCtx kctx rctx) :
    Ty.WellFormed kctx rctx (instantiate scheme st).1 := by
  unfold instantiate
  by_cases h_mono : scheme.isMono
  · simp [h_mono] at *
    simpa using h_wf
  · simp [h_mono]
    exact renameType_preserves_wf (instantiateVarMapping scheme st) kctx rctx h_respects scheme.ty h_wf

theorem instantiate_preserves_wf_of_mapping_respects_ctx
    (scheme : TypeScheme) (st : UnifyState) (kctx : KindCtx) (rctx : RowCtx)
    (h_wf : Ty.WellFormed kctx rctx scheme.ty)
    (h_respects :
      let typeMapping :=
        (scheme.typeVars.foldl
          (fun (acc, st) tv =>
            let (fresh, st') := st.freshTypeVar
            ((tv, fresh) :: acc, st'))
          ([], st)).1
      let stAfterType :=
        (scheme.typeVars.foldl
          (fun (acc, st) tv =>
            let (fresh, st') := st.freshTypeVar
            ((tv, fresh) :: acc, st'))
          ([], st)).2
      let rowMapping :=
        (scheme.rowVars.foldl
          (fun (acc, st) rv =>
            let (fresh, st') := st.freshRowVar
            ((rv, fresh) :: acc, st'))
          ([], stAfterType)).1
      ({ typeMap := typeMapping, rowMap := rowMapping } : VarMapping).RespectsCtx kctx rctx) :
    Ty.WellFormed kctx rctx (instantiate scheme st).1 := by
  simpa [instantiateVarMapping, instantiateTypeFold, instantiateRowFold] using
    instantiate_preserves_wf_of_instantiateVarMapping_respects_ctx
      scheme st kctx rctx h_wf h_respects

theorem instantiate_preserves_wf
    (scheme : TypeScheme) (st : UnifyState) (kctx : KindCtx) (rctx : RowCtx)
    (h_wf : Ty.WellFormed kctx rctx scheme.ty)
    (h_assume : scheme.isMono = true ∨ (instantiateVarMapping scheme st).RespectsCtx kctx rctx) :
    Ty.WellFormed kctx rctx (instantiate scheme st).1 := by
  rcases h_assume with h_mono | h_respects
  · exact instantiate_mono_preserves_wf scheme st kctx rctx h_mono h_wf
  · exact instantiate_preserves_wf_of_instantiateVarMapping_respects_ctx
      scheme st kctx rctx h_wf h_respects
