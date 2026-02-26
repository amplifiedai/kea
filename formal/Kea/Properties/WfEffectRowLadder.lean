import Kea.WellFormed
import Kea.Properties.WfSubstitution
import Kea.Properties.WfGeneralize

/-!
  Kea.Properties.WfEffectRowLadder — packaged WF ladder for `Ty.functionEff`.

  This module provides compact theorem surfaces that bundle the existing
  component-wise effect-row WF results across:
  - substitution (`applySubst` / `applySubstWF` / compat)
  - generalize
  - instantiate
-/

/-- Packaged substitution-level WF obligations for `Ty.functionEff`. -/
def FunctionEffSubstWfSlice
    (s : Subst) (h_ac : Subst.Acyclic s) (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat)
    (params : TyList) (effects : EffectRow) (ret : Ty) : Prop :=
  Ty.WellFormed kctx rctx (applySubst s fuel (.functionEff params effects ret))
  ∧ Ty.WellFormed kctx rctx (applySubstWF s h_ac (.functionEff params effects ret))
  ∧ Ty.WellFormed kctx rctx (applySubstCompat s fuel (.functionEff params effects ret))

theorem functionEff_subst_wf_slice_of_component_no_domain_vars
    (s : Subst) (h_ac : Subst.Acyclic s) (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat)
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
    FunctionEffSubstWfSlice s h_ac kctx rctx fuel params effects ret := by
  refine ⟨?_, ?_, ?_⟩
  · exact applySubst_functionEff_preserves_wf_of_component_no_domain_vars
      s kctx rctx fuel params effects ret
      h_wf_params h_wf_effects h_wf_ret
      htv_params hrv_params htv_effects hrv_effects htv_ret hrv_ret
  · exact applySubstWF_functionEff_preserves_wf_of_component_no_domain_vars
      s h_ac kctx rctx params effects ret
      h_wf_params h_wf_effects h_wf_ret
      htv_params hrv_params htv_effects hrv_effects htv_ret hrv_ret
  · exact applySubstCompat_functionEff_preserves_wf_of_component_no_domain_vars
      s kctx rctx fuel params effects ret
      h_wf_params h_wf_effects h_wf_ret
      htv_params hrv_params htv_effects hrv_effects htv_ret hrv_ret

theorem functionEff_subst_wf_slice_empty
    (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat)
    (params : TyList) (effects : EffectRow) (ret : Ty)
    (h_wf_params : TyList.WellFormed kctx rctx params)
    (h_wf_effects : EffectRow.WellFormed kctx rctx effects)
    (h_wf_ret : Ty.WellFormed kctx rctx ret) :
    FunctionEffSubstWfSlice
      Subst.empty Subst.emptyAcyclic kctx rctx fuel params effects ret := by
  exact functionEff_subst_wf_slice_of_component_no_domain_vars
    Subst.empty Subst.emptyAcyclic kctx rctx fuel params effects ret
    h_wf_params h_wf_effects h_wf_ret
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- Packaged generalize/instantiate WF obligations for `Ty.functionEff`. -/
def FunctionEffGenInstWfSlice
    (scheme : TypeScheme) (env : TypeEnv) (st : UnifyState)
    (s : Subst) (lc : Lacks) (traitBounds : TraitBounds)
    (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat)
    (params : TyList) (effects : EffectRow) (ret : Ty) : Prop :=
  Ty.WellFormed kctx rctx
    (generalize (.functionEff params effects ret) env s lc traitBounds fuel).ty
  ∧ Ty.WellFormed kctx rctx (instantiate scheme st).1

theorem functionEff_gen_inst_wf_slice
    (scheme : TypeScheme) (env : TypeEnv) (st : UnifyState)
    (s : Subst) (lc : Lacks) (traitBounds : TraitBounds)
    (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat)
    (params : TyList) (effects : EffectRow) (ret : Ty)
    (h_scheme : scheme.ty = .functionEff params effects ret)
    (h_wf_params : TyList.WellFormed kctx rctx params)
    (h_wf_effects : EffectRow.WellFormed kctx rctx effects)
    (h_wf_ret : Ty.WellFormed kctx rctx ret)
    (htv_params : ∀ v ∈ freeTypeVarsTyList params, s.typeMap v = none)
    (hrv_params : ∀ v ∈ freeRowVarsTyList params, s.rowMap v = none)
    (htv_effects : ∀ v ∈ freeTypeVarsEffectRow effects, s.typeMap v = none)
    (hrv_effects : ∀ v ∈ freeRowVarsEffectRow effects, s.rowMap v = none)
    (htv_ret : ∀ v ∈ freeTypeVars ret, s.typeMap v = none)
    (hrv_ret : ∀ v ∈ freeRowVars ret, s.rowMap v = none)
    (h_inst : scheme.isMono = true ∨ (instantiateVarMapping scheme st).RespectsCtx kctx rctx) :
    FunctionEffGenInstWfSlice
      scheme env st s lc traitBounds kctx rctx fuel params effects ret := by
  refine ⟨?_, ?_⟩
  · exact generalize_functionEff_preserves_wf_of_component_no_domain_vars
      env s lc traitBounds fuel kctx rctx params effects ret
      h_wf_params h_wf_effects h_wf_ret
      htv_params hrv_params htv_effects hrv_effects htv_ret hrv_ret
  · exact instantiate_functionEff_preserves_wf
      scheme st kctx rctx params effects ret h_scheme
      h_wf_params h_wf_effects h_wf_ret h_inst

theorem functionEff_gen_inst_wf_slice_mono
    (scheme : TypeScheme) (env : TypeEnv) (st : UnifyState)
    (s : Subst) (lc : Lacks) (traitBounds : TraitBounds)
    (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat)
    (params : TyList) (effects : EffectRow) (ret : Ty)
    (h_scheme : scheme.ty = .functionEff params effects ret)
    (h_wf_params : TyList.WellFormed kctx rctx params)
    (h_wf_effects : EffectRow.WellFormed kctx rctx effects)
    (h_wf_ret : Ty.WellFormed kctx rctx ret)
    (htv_params : ∀ v ∈ freeTypeVarsTyList params, s.typeMap v = none)
    (hrv_params : ∀ v ∈ freeRowVarsTyList params, s.rowMap v = none)
    (htv_effects : ∀ v ∈ freeTypeVarsEffectRow effects, s.typeMap v = none)
    (hrv_effects : ∀ v ∈ freeRowVarsEffectRow effects, s.rowMap v = none)
    (htv_ret : ∀ v ∈ freeTypeVars ret, s.typeMap v = none)
    (hrv_ret : ∀ v ∈ freeRowVars ret, s.rowMap v = none)
    (h_mono : scheme.isMono = true) :
    FunctionEffGenInstWfSlice
      scheme env st s lc traitBounds kctx rctx fuel params effects ret := by
  exact functionEff_gen_inst_wf_slice
    scheme env st s lc traitBounds kctx rctx fuel params effects ret
    h_scheme h_wf_params h_wf_effects h_wf_ret
    htv_params hrv_params htv_effects hrv_effects htv_ret hrv_ret
    (Or.inl h_mono)
