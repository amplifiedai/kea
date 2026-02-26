import Kea.WellFormed
import Kea.Properties.WfSubstitution
import Kea.Properties.WfGeneralize
import Kea.Properties.WfUnifyExtends

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

/-- Packaged `bindTypeVar` contract obligations for `Ty.functionEff`. -/
def FunctionEffBindTypeVarContractSlice
    (st stNext : UnifyState) (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat)
    (h_idemp_next : stNext.subst.Idempotent) : Prop :=
  ExtendsAndWfRange st stNext kctx rctx
  ∧ (let h_ac := Subst.acyclicOfIdempotent h_idemp_next
     CompatWFAgreeOnDomainLookupsAcyclic stNext fuel h_ac)

/-- Full-state packaged `bindTypeVar` contract obligations for `Ty.functionEff`
    with arbitrary non-`subst` field updates. -/
def FunctionEffBindTypeVarFullStateContractSlice
    (st stNext : UnifyState) (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat)
    (h_idemp_next : stNext.subst.Idempotent) : Prop :=
  ExtendsAndWfRange st stNext kctx rctx
  ∧ (let h_ac := Subst.acyclicOfIdempotent h_idemp_next
     CompatWFAgreeOnDomainLookupsAcyclic stNext fuel h_ac)

theorem functionEff_bindTypeVar_full_state_slice_to_base
    (st stNext : UnifyState) (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat)
    (h_idemp_next : stNext.subst.Idempotent)
    (h_slice :
      FunctionEffBindTypeVarFullStateContractSlice st stNext kctx rctx fuel h_idemp_next) :
    FunctionEffBindTypeVarContractSlice st stNext kctx rctx fuel h_idemp_next := by
  exact h_slice

theorem functionEff_bindTypeVar_base_slice_to_full_state
    (st stNext : UnifyState) (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat)
    (h_idemp_next : stNext.subst.Idempotent)
    (h_slice :
      FunctionEffBindTypeVarContractSlice st stNext kctx rctx fuel h_idemp_next) :
    FunctionEffBindTypeVarFullStateContractSlice st stNext kctx rctx fuel h_idemp_next := by
  exact h_slice

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

theorem functionEff_bindTypeVar_contract_slice
    (st stNext : UnifyState) (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat)
    (v : TypeVarId) (params : TyList) (effects : EffectRow) (ret : Ty)
    (h_bind : bindTypeVar st v (.functionEff params effects ret) fuel = .ok stNext)
    (h_wf_state : UnifyState.SubstWellFormedRange st kctx rctx)
    (h_wf_params : TyList.WellFormed kctx rctx params)
    (h_wf_effects : EffectRow.WellFormed kctx rctx effects)
    (h_wf_ret : Ty.WellFormed kctx rctx ret)
    (h_idemp_next : stNext.subst.Idempotent) :
    ExtendsAndWfRange st stNext kctx rctx
    ∧ (let h_ac := Subst.acyclicOfIdempotent h_idemp_next
       CompatWFAgreeOnDomainLookupsAcyclic stNext fuel h_ac) := by
  exact bindTypeVar_ok_contract_full_wf
    st stNext kctx rctx v (.functionEff params effects ret) fuel
    h_bind h_wf_state ⟨h_wf_params, h_wf_effects, h_wf_ret⟩ h_idemp_next

theorem functionEff_bindTypeVar_contract_slice_of_success
    (st stNext : UnifyState) (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat)
    (v : TypeVarId) (params : TyList) (effects : EffectRow) (ret : Ty)
    (h_bind : bindTypeVar st v (.functionEff params effects ret) fuel = .ok stNext)
    (h_wf_state : UnifyState.SubstWellFormedRange st kctx rctx)
    (h_wf_params : TyList.WellFormed kctx rctx params)
    (h_wf_effects : EffectRow.WellFormed kctx rctx effects)
    (h_wf_ret : Ty.WellFormed kctx rctx ret)
    (h_idemp_next : stNext.subst.Idempotent) :
    FunctionEffBindTypeVarContractSlice st stNext kctx rctx fuel h_idemp_next := by
  exact functionEff_bindTypeVar_contract_slice
    st stNext kctx rctx fuel v params effects ret
    h_bind h_wf_state h_wf_params h_wf_effects h_wf_ret h_idemp_next

theorem functionEff_bindTypeVar_extends_of_contract_slice
    (st stNext : UnifyState) (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat)
    (h_idemp_next : stNext.subst.Idempotent)
    (h_slice : FunctionEffBindTypeVarContractSlice st stNext kctx rctx fuel h_idemp_next) :
    ExtendsRowBindings st stNext := by
  exact h_slice.1.1

theorem functionEff_bindTypeVar_substWellFormedRange_of_contract_slice
    (st stNext : UnifyState) (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat)
    (h_idemp_next : stNext.subst.Idempotent)
    (h_slice : FunctionEffBindTypeVarContractSlice st stNext kctx rctx fuel h_idemp_next) :
    UnifyState.SubstWellFormedRange stNext kctx rctx := by
  exact h_slice.1.2

theorem functionEff_bindTypeVar_compatWFAgreeOnDomainLookupsAcyclic_of_contract_slice
    (st stNext : UnifyState) (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat)
    (h_idemp_next : stNext.subst.Idempotent)
    (h_slice : FunctionEffBindTypeVarContractSlice st stNext kctx rctx fuel h_idemp_next) :
    let h_ac := Subst.acyclicOfIdempotent h_idemp_next
    CompatWFAgreeOnDomainLookupsAcyclic stNext fuel h_ac := by
  exact h_slice.2

theorem functionEff_bindTypeVar_full_state_contract_slice
    (st st' : UnifyState) (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat)
    (v : TypeVarId) (params : TyList) (effects : EffectRow) (ret : Ty)
    (lacks' : Lacks) (bounds' : TraitBounds) (nextType' nextRow' : Nat)
    (h_bind : bindTypeVar st v (.functionEff params effects ret) fuel = .ok st')
    (h_wf_state : UnifyState.SubstWellFormedRange st kctx rctx)
    (h_wf_params : TyList.WellFormed kctx rctx params)
    (h_wf_effects : EffectRow.WellFormed kctx rctx effects)
    (h_wf_ret : Ty.WellFormed kctx rctx ret)
    (h_idemp_next :
      ({ st' with
          lacks := lacks',
          traitBounds := bounds',
          nextTypeVar := nextType',
          nextRowVar := nextRow' }).subst.Idempotent) :
    let stNext : UnifyState :=
      { st' with
          lacks := lacks',
          traitBounds := bounds',
          nextTypeVar := nextType',
          nextRowVar := nextRow' }
    ExtendsAndWfRange st stNext kctx rctx
    ∧ (let h_ac := Subst.acyclicOfIdempotent h_idemp_next
       CompatWFAgreeOnDomainLookupsAcyclic stNext fuel h_ac) := by
  simpa using bindTypeVar_ok_with_non_subst_fields_contract_full_wf
    st st' kctx rctx v (.functionEff params effects ret) fuel
    lacks' bounds' nextType' nextRow'
    h_bind h_wf_state ⟨h_wf_params, h_wf_effects, h_wf_ret⟩ h_idemp_next

theorem functionEff_bindTypeVar_full_state_contract_slice_of_success
    (st st' : UnifyState) (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat)
    (v : TypeVarId) (params : TyList) (effects : EffectRow) (ret : Ty)
    (lacks' : Lacks) (bounds' : TraitBounds) (nextType' nextRow' : Nat)
    (h_bind : bindTypeVar st v (.functionEff params effects ret) fuel = .ok st')
    (h_wf_state : UnifyState.SubstWellFormedRange st kctx rctx)
    (h_wf_params : TyList.WellFormed kctx rctx params)
    (h_wf_effects : EffectRow.WellFormed kctx rctx effects)
    (h_wf_ret : Ty.WellFormed kctx rctx ret)
    (h_idemp_next :
      ({ st' with
          lacks := lacks',
          traitBounds := bounds',
          nextTypeVar := nextType',
          nextRowVar := nextRow' }).subst.Idempotent) :
    let stNext : UnifyState :=
      { st' with
          lacks := lacks',
          traitBounds := bounds',
          nextTypeVar := nextType',
          nextRowVar := nextRow' }
    FunctionEffBindTypeVarFullStateContractSlice st stNext kctx rctx fuel h_idemp_next := by
  dsimp [FunctionEffBindTypeVarFullStateContractSlice]
  exact functionEff_bindTypeVar_full_state_contract_slice
    st st' kctx rctx fuel v params effects ret
    lacks' bounds' nextType' nextRow'
    h_bind h_wf_state h_wf_params h_wf_effects h_wf_ret h_idemp_next

theorem functionEff_bindTypeVar_full_state_extends_of_contract_slice
    (st stNext : UnifyState) (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat)
    (h_idemp_next : stNext.subst.Idempotent)
    (h_slice : FunctionEffBindTypeVarFullStateContractSlice st stNext kctx rctx fuel h_idemp_next) :
    ExtendsRowBindings st stNext := by
  exact functionEff_bindTypeVar_extends_of_contract_slice
    st stNext kctx rctx fuel h_idemp_next
    (functionEff_bindTypeVar_full_state_slice_to_base
      st stNext kctx rctx fuel h_idemp_next h_slice)

theorem functionEff_bindTypeVar_full_state_substWellFormedRange_of_contract_slice
    (st stNext : UnifyState) (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat)
    (h_idemp_next : stNext.subst.Idempotent)
    (h_slice : FunctionEffBindTypeVarFullStateContractSlice st stNext kctx rctx fuel h_idemp_next) :
    UnifyState.SubstWellFormedRange stNext kctx rctx := by
  exact functionEff_bindTypeVar_substWellFormedRange_of_contract_slice
    st stNext kctx rctx fuel h_idemp_next
    (functionEff_bindTypeVar_full_state_slice_to_base
      st stNext kctx rctx fuel h_idemp_next h_slice)

theorem functionEff_bindTypeVar_full_state_compatWFAgreeOnDomainLookupsAcyclic_of_contract_slice
    (st stNext : UnifyState) (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat)
    (h_idemp_next : stNext.subst.Idempotent)
    (h_slice : FunctionEffBindTypeVarFullStateContractSlice st stNext kctx rctx fuel h_idemp_next) :
    let h_ac := Subst.acyclicOfIdempotent h_idemp_next
    CompatWFAgreeOnDomainLookupsAcyclic stNext fuel h_ac := by
  exact functionEff_bindTypeVar_compatWFAgreeOnDomainLookupsAcyclic_of_contract_slice
    st stNext kctx rctx fuel h_idemp_next
    (functionEff_bindTypeVar_full_state_slice_to_base
      st stNext kctx rctx fuel h_idemp_next h_slice)
