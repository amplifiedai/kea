import Kea.WellFormed
import Kea.Properties.SubstBridge

/-
  Kea.Properties.WfSubstitution — WF preservation lemmas for substitution.

  Phase-1 baseline: when substitution is known to be a no-op over all free vars
  of a term, applying either fuel-based or WF substitution preserves that
  term's well-formedness immediately.
-/

theorem applySubst_preserves_wf_of_no_domain_vars
    (s : Subst) (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat) (ty : Ty)
    (h_wf : Ty.WellFormed kctx rctx ty)
    (htv : ∀ v ∈ freeTypeVars ty, s.typeMap v = none)
    (hrv : ∀ v ∈ freeRowVars ty, s.rowMap v = none) :
    Ty.WellFormed kctx rctx (applySubst s fuel ty) := by
  rw [(applySubst_noop s fuel).1 ty htv hrv]
  exact h_wf

theorem applySubstRow_preserves_wf_of_no_domain_vars
    (s : Subst) (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat) (r : Row)
    (h_wf : Row.WellFormed kctx rctx r)
    (htv : ∀ v ∈ freeTypeVarsRow r, s.typeMap v = none)
    (hrv : ∀ v ∈ freeRowVarsRow r, s.rowMap v = none) :
    Row.WellFormed kctx rctx (applySubstRow s fuel r) := by
  rw [(applySubst_noop s fuel).2.1 r htv hrv]
  exact h_wf

theorem applySubstEffectRow_preserves_wf_of_no_domain_vars
    (s : Subst) (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat) (effects : EffectRow)
    (h_wf : EffectRow.WellFormed kctx rctx effects)
    (htv : ∀ v ∈ freeTypeVarsEffectRow effects, s.typeMap v = none)
    (hrv : ∀ v ∈ freeRowVarsEffectRow effects, s.rowMap v = none) :
    EffectRow.WellFormed kctx rctx (applySubstEffectRow s fuel effects) := by
  cases effects with
  | mk row =>
    simpa [applySubstEffectRow, EffectRow.WellFormed, freeTypeVarsEffectRow, freeRowVarsEffectRow] using
      applySubstRow_preserves_wf_of_no_domain_vars s kctx rctx fuel row h_wf htv hrv

theorem applySubstWF_preserves_wf_of_no_domain_vars
    (s : Subst) (h : Subst.Acyclic s) (kctx : KindCtx) (rctx : RowCtx) (ty : Ty)
    (h_wf : Ty.WellFormed kctx rctx ty)
    (htv : ∀ v ∈ freeTypeVars ty, s.typeMap v = none)
    (hrv : ∀ v ∈ freeRowVars ty, s.rowMap v = none) :
    Ty.WellFormed kctx rctx (applySubstWF s h ty) := by
  rw [applySubstWF_noop s h ty htv hrv]
  exact h_wf

theorem applySubstRowWF_preserves_wf_of_no_domain_vars
    (s : Subst) (h : Subst.Acyclic s) (kctx : KindCtx) (rctx : RowCtx) (r : Row)
    (h_wf : Row.WellFormed kctx rctx r)
    (htv : ∀ v ∈ freeTypeVarsRow r, s.typeMap v = none)
    (hrv : ∀ v ∈ freeRowVarsRow r, s.rowMap v = none) :
    Row.WellFormed kctx rctx (applySubstRowWF s h r) := by
  rw [applySubstRowWF_noop s h r htv hrv]
  exact h_wf

theorem applySubstEffectRowWF_preserves_wf_of_no_domain_vars
    (s : Subst) (h : Subst.Acyclic s) (kctx : KindCtx) (rctx : RowCtx) (effects : EffectRow)
    (h_wf : EffectRow.WellFormed kctx rctx effects)
    (htv : ∀ v ∈ freeTypeVarsEffectRow effects, s.typeMap v = none)
    (hrv : ∀ v ∈ freeRowVarsEffectRow effects, s.rowMap v = none) :
    EffectRow.WellFormed kctx rctx (applySubstEffectRowWF s h effects) := by
  rw [applySubstEffectRowWF_noop s h effects htv hrv]
  exact h_wf

theorem applySubstWF_empty_preserves_wf
    (kctx : KindCtx) (rctx : RowCtx) (ty : Ty)
    (h_wf : Ty.WellFormed kctx rctx ty) :
    Ty.WellFormed kctx rctx (applySubstWF Subst.empty Subst.emptyAcyclic ty) := by
  rw [applySubstWF_empty ty]
  exact h_wf

theorem applySubstCompat_functionEff_preserves_wf_of_component_no_domain_vars
    (s : Subst) (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat)
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
    Ty.WellFormed kctx rctx (applySubstCompat s fuel (.functionEff params effects ret)) := by
  simpa [applySubstCompat] using
    applySubst_preserves_wf_of_no_domain_vars s kctx rctx fuel (.functionEff params effects ret)
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

theorem applySubst_empty_preserves_wf
    (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat) (ty : Ty)
    (h_wf : Ty.WellFormed kctx rctx ty) :
    Ty.WellFormed kctx rctx (applySubst Subst.empty fuel ty) := by
  rw [(applySubst_noop Subst.empty fuel).1 ty (fun _ _ => rfl) (fun _ _ => rfl)]
  exact h_wf

theorem applySubstCompat_preserves_wf_of_no_domain_vars
    (s : Subst) (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat) (ty : Ty)
    (h_wf : Ty.WellFormed kctx rctx ty)
    (htv : ∀ v ∈ freeTypeVars ty, s.typeMap v = none)
    (hrv : ∀ v ∈ freeRowVars ty, s.rowMap v = none) :
    Ty.WellFormed kctx rctx (applySubstCompat s fuel ty) := by
  simpa [applySubstCompat] using
    applySubst_preserves_wf_of_no_domain_vars s kctx rctx fuel ty h_wf htv hrv

theorem applySubstRow_empty_preserves_wf
    (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat) (r : Row)
    (h_wf : Row.WellFormed kctx rctx r) :
    Row.WellFormed kctx rctx (applySubstRow Subst.empty fuel r) := by
  rw [(applySubst_noop Subst.empty fuel).2.1 r (fun _ _ => rfl) (fun _ _ => rfl)]
  exact h_wf

theorem applySubstRowCompat_preserves_wf_of_no_domain_vars
    (s : Subst) (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat) (r : Row)
    (h_wf : Row.WellFormed kctx rctx r)
    (htv : ∀ v ∈ freeTypeVarsRow r, s.typeMap v = none)
    (hrv : ∀ v ∈ freeRowVarsRow r, s.rowMap v = none) :
    Row.WellFormed kctx rctx (applySubstRowCompat s fuel r) := by
  simpa [applySubstRowCompat] using
    applySubstRow_preserves_wf_of_no_domain_vars s kctx rctx fuel r h_wf htv hrv

theorem applySubstEffectRow_empty_preserves_wf
    (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat) (effects : EffectRow)
    (h_wf : EffectRow.WellFormed kctx rctx effects) :
    EffectRow.WellFormed kctx rctx (applySubstEffectRow Subst.empty fuel effects) := by
  cases effects with
  | mk row =>
    simpa [applySubstEffectRow, EffectRow.WellFormed] using
      applySubstRow_empty_preserves_wf kctx rctx fuel row h_wf
