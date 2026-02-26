import Kea.WellFormed
import Kea.Properties.SubstBridge
import Kea.Properties.SubstCompose

/-
  Kea.Properties.WfSubstitution — WF preservation lemmas for substitution.

  Phase-1 baseline: when substitution is known to be a no-op over all free vars
  of a term, applying either fuel-based or WF substitution preserves that
  term's well-formedness immediately.
-/

namespace Subst

/--
Every binding currently present in the substitution maps to a well-formed term.
-/
def WellFormedRange (s : Subst) (kctx : KindCtx) (rctx : RowCtx) : Prop :=
  (∀ v ty, s.typeMap v = some ty → Ty.WellFormed kctx rctx ty) ∧
  (∀ rv row, s.rowMap rv = some row → Row.WellFormed kctx rctx row)

theorem wellFormedRange_empty
    (kctx : KindCtx) (rctx : RowCtx) :
    WellFormedRange Subst.empty kctx rctx := by
  constructor <;> intro _ _ h_lookup
  · simp [Subst.empty] at h_lookup
  · simp [Subst.empty] at h_lookup

theorem wellFormedRange_bindType
    (s : Subst) (kctx : KindCtx) (rctx : RowCtx) (v : TypeVarId) (ty : Ty)
    (h_range : WellFormedRange s kctx rctx)
    (h_ty : Ty.WellFormed kctx rctx ty) :
    WellFormedRange (s.bindType v ty) kctx rctx := by
  constructor
  · intro w t h_lookup
    unfold Subst.bindType at h_lookup
    by_cases h_eq : w == v
    · simp [h_eq] at h_lookup
      cases h_lookup
      exact h_ty
    · have h_prev : s.typeMap w = some t := by
        simpa [h_eq] using h_lookup
      exact h_range.1 w t h_prev
  · intro rv row h_lookup
    unfold Subst.bindType at h_lookup
    exact h_range.2 rv row h_lookup

theorem wellFormedRange_bindRow
    (s : Subst) (kctx : KindCtx) (rctx : RowCtx) (rv : RowVarId) (row : Row)
    (h_range : WellFormedRange s kctx rctx)
    (h_row : Row.WellFormed kctx rctx row) :
    WellFormedRange (s.bindRow rv row) kctx rctx := by
  constructor
  · intro w t h_lookup
    unfold Subst.bindRow at h_lookup
    exact h_range.1 w t h_lookup
  · intro rv' row' h_lookup
    unfold Subst.bindRow at h_lookup
    by_cases h_eq : rv' == rv
    · simp [h_eq] at h_lookup
      cases h_lookup
      exact h_row
    · have h_prev : s.rowMap rv' = some row' := by
        simpa [h_eq] using h_lookup
      exact h_range.2 rv' row' h_prev

theorem wellFormedRange_bindRow_bindRow
    (s : Subst) (kctx : KindCtx) (rctx : RowCtx)
    (rv1 rv2 : RowVarId) (row1 row2 : Row)
    (h_range : WellFormedRange s kctx rctx)
    (h_row1 : Row.WellFormed kctx rctx row1)
    (h_row2 : Row.WellFormed kctx rctx row2) :
    WellFormedRange (Subst.bindRow (Subst.bindRow s rv1 row1) rv2 row2) kctx rctx := by
  exact wellFormedRange_bindRow
    (Subst.bindRow s rv1 row1) kctx rctx rv2 row2
    (wellFormedRange_bindRow s kctx rctx rv1 row1 h_range h_row1)
    h_row2

theorem wellFormedRange_of_extends
    (s s' : Subst) (kctx : KindCtx) (rctx : RowCtx)
    (h_ext : Subst.Extends s s')
    (h_range : WellFormedRange s' kctx rctx) :
    WellFormedRange s kctx rctx := by
  constructor
  · intro v ty h_lookup
    exact h_range.1 v ty (h_ext.typeExt v ty h_lookup)
  · intro rv row h_lookup
    exact h_range.2 rv row (h_ext.rowExt rv row h_lookup)

theorem extends_bindType_if_unbound
    (s : Subst) (v : TypeVarId) (ty : Ty)
    (h_unbound : s.typeMap v = none) :
    Subst.Extends s (s.bindType v ty) := by
  refine ⟨?_, ?_⟩
  · intro w t h_lookup
    unfold Subst.bindType
    by_cases h_eq : w == v
    · have h_wv : w = v := by simpa [BEq.beq] using h_eq
      rw [h_wv] at h_lookup
      simp [h_unbound] at h_lookup
    · simpa [h_eq] using h_lookup
  · intro rv row h_lookup
    unfold Subst.bindType
    exact h_lookup

theorem extends_bindRow_if_unbound
    (s : Subst) (rv : RowVarId) (row : Row)
    (h_unbound : s.rowMap rv = none) :
    Subst.Extends s (s.bindRow rv row) := by
  refine ⟨?_, ?_⟩
  · intro v ty h_lookup
    unfold Subst.bindRow
    exact h_lookup
  · intro rv' row' h_lookup
    unfold Subst.bindRow
    by_cases h_eq : rv' == rv
    · have h_rv : rv' = rv := by simpa [BEq.beq] using h_eq
      rw [h_rv] at h_lookup
      simp [h_unbound] at h_lookup
    · simpa [h_eq] using h_lookup

end Subst

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

theorem applySubstTyList_preserves_wf_of_no_domain_vars
    (s : Subst) (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat) (tl : TyList)
    (h_wf : TyList.WellFormed kctx rctx tl)
    (htv : ∀ v ∈ freeTypeVarsTyList tl, s.typeMap v = none)
    (hrv : ∀ v ∈ freeRowVarsTyList tl, s.rowMap v = none) :
    TyList.WellFormed kctx rctx (applySubstTyList s fuel tl) := by
  rw [(applySubst_noop s fuel).2.2.1 tl htv hrv]
  exact h_wf

theorem applySubstRowFields_preserves_wf_of_no_domain_vars
    (s : Subst) (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat) (rf : RowFields)
    (h_wf : RowFields.WellFormed kctx rctx rf)
    (htv : ∀ v ∈ freeTypeVarsRowFields rf, s.typeMap v = none)
    (hrv : ∀ v ∈ freeRowVarsRowFields rf, s.rowMap v = none) :
    RowFields.WellFormed kctx rctx (applySubstRowFields s fuel rf) := by
  rw [(applySubst_noop s fuel).2.2.2 rf htv hrv]
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

theorem applySubst_functionEff_preserves_wf_of_component_no_domain_vars
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
    Ty.WellFormed kctx rctx (applySubst s fuel (.functionEff params effects ret)) := by
  exact applySubst_preserves_wf_of_no_domain_vars s kctx rctx fuel (.functionEff params effects ret)
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

theorem applySubstWF_functionEff_preserves_wf_of_component_no_domain_vars
    (s : Subst) (h : Subst.Acyclic s) (kctx : KindCtx) (rctx : RowCtx)
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
    Ty.WellFormed kctx rctx (applySubstWF s h (.functionEff params effects ret)) := by
  exact applySubstWF_preserves_wf_of_no_domain_vars s h kctx rctx (.functionEff params effects ret)
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

theorem applySubstWF_empty_preserves_wf
    (kctx : KindCtx) (rctx : RowCtx) (ty : Ty)
    (h_wf : Ty.WellFormed kctx rctx ty) :
    Ty.WellFormed kctx rctx (applySubstWF Subst.empty Subst.emptyAcyclic ty) := by
  rw [applySubstWF_empty ty]
  exact h_wf

theorem applySubstRowWF_empty_preserves_wf
    (kctx : KindCtx) (rctx : RowCtx) (r : Row)
    (h_wf : Row.WellFormed kctx rctx r) :
    Row.WellFormed kctx rctx (applySubstRowWF Subst.empty Subst.emptyAcyclic r) := by
  rw [applySubstRowWF_empty r]
  exact h_wf

theorem applySubstEffectRowWF_empty_preserves_wf
    (kctx : KindCtx) (rctx : RowCtx) (effects : EffectRow)
    (h_wf : EffectRow.WellFormed kctx rctx effects) :
    EffectRow.WellFormed kctx rctx (applySubstEffectRowWF Subst.empty Subst.emptyAcyclic effects) := by
  rw [applySubstEffectRowWF_empty effects]
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

theorem applySubstTyList_empty_preserves_wf
    (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat) (tl : TyList)
    (h_wf : TyList.WellFormed kctx rctx tl) :
    TyList.WellFormed kctx rctx (applySubstTyList Subst.empty fuel tl) := by
  rw [(applySubst_noop Subst.empty fuel).2.2.1 tl (fun _ _ => rfl) (fun _ _ => rfl)]
  exact h_wf

theorem applySubstRowFields_empty_preserves_wf
    (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat) (rf : RowFields)
    (h_wf : RowFields.WellFormed kctx rctx rf) :
    RowFields.WellFormed kctx rctx (applySubstRowFields Subst.empty fuel rf) := by
  rw [(applySubst_noop Subst.empty fuel).2.2.2 rf (fun _ _ => rfl) (fun _ _ => rfl)]
  exact h_wf

theorem applySubstRowCompat_preserves_wf_of_no_domain_vars
    (s : Subst) (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat) (r : Row)
    (h_wf : Row.WellFormed kctx rctx r)
    (htv : ∀ v ∈ freeTypeVarsRow r, s.typeMap v = none)
    (hrv : ∀ v ∈ freeRowVarsRow r, s.rowMap v = none) :
    Row.WellFormed kctx rctx (applySubstRowCompat s fuel r) := by
  simpa [applySubstRowCompat] using
    applySubstRow_preserves_wf_of_no_domain_vars s kctx rctx fuel r h_wf htv hrv

theorem applySubstTyListCompat_preserves_wf_of_no_domain_vars
    (s : Subst) (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat) (tl : TyList)
    (h_wf : TyList.WellFormed kctx rctx tl)
    (htv : ∀ v ∈ freeTypeVarsTyList tl, s.typeMap v = none)
    (hrv : ∀ v ∈ freeRowVarsTyList tl, s.rowMap v = none) :
    TyList.WellFormed kctx rctx (applySubstTyListCompat s fuel tl) := by
  simpa [applySubstTyListCompat] using
    applySubstTyList_preserves_wf_of_no_domain_vars s kctx rctx fuel tl h_wf htv hrv

theorem applySubstRowFieldsCompat_preserves_wf_of_no_domain_vars
    (s : Subst) (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat) (rf : RowFields)
    (h_wf : RowFields.WellFormed kctx rctx rf)
    (htv : ∀ v ∈ freeTypeVarsRowFields rf, s.typeMap v = none)
    (hrv : ∀ v ∈ freeRowVarsRowFields rf, s.rowMap v = none) :
    RowFields.WellFormed kctx rctx (applySubstRowFieldsCompat s fuel rf) := by
  simpa [applySubstRowFieldsCompat] using
    applySubstRowFields_preserves_wf_of_no_domain_vars s kctx rctx fuel rf h_wf htv hrv

theorem applySubstEffectRow_empty_preserves_wf
    (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat) (effects : EffectRow)
    (h_wf : EffectRow.WellFormed kctx rctx effects) :
    EffectRow.WellFormed kctx rctx (applySubstEffectRow Subst.empty fuel effects) := by
  cases effects with
  | mk row =>
    simpa [applySubstEffectRow, EffectRow.WellFormed] using
      applySubstRow_empty_preserves_wf kctx rctx fuel row h_wf

theorem applySubstTyListCompat_empty_preserves_wf
    (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat) (tl : TyList)
    (h_wf : TyList.WellFormed kctx rctx tl) :
    TyList.WellFormed kctx rctx (applySubstTyListCompat Subst.empty fuel tl) := by
  simpa [applySubstTyListCompat] using
    applySubstTyList_empty_preserves_wf kctx rctx fuel tl h_wf

theorem applySubstRowFieldsCompat_empty_preserves_wf
    (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat) (rf : RowFields)
    (h_wf : RowFields.WellFormed kctx rctx rf) :
    RowFields.WellFormed kctx rctx (applySubstRowFieldsCompat Subst.empty fuel rf) := by
  simpa [applySubstRowFieldsCompat] using
    applySubstRowFields_empty_preserves_wf kctx rctx fuel rf h_wf

theorem applySubstEffectRowCompat_preserves_wf_of_no_domain_vars
    (s : Subst) (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat) (effects : EffectRow)
    (h_wf : EffectRow.WellFormed kctx rctx effects)
    (htv : ∀ v ∈ freeTypeVarsEffectRow effects, s.typeMap v = none)
    (hrv : ∀ v ∈ freeRowVarsEffectRow effects, s.rowMap v = none) :
    EffectRow.WellFormed kctx rctx (applySubstEffectRowCompat s fuel effects) := by
  simpa [applySubstEffectRowCompat] using
    applySubstEffectRow_preserves_wf_of_no_domain_vars s kctx rctx fuel effects h_wf htv hrv

theorem applySubstEffectRowCompat_empty_preserves_wf
    (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat) (effects : EffectRow)
    (h_wf : EffectRow.WellFormed kctx rctx effects) :
    EffectRow.WellFormed kctx rctx (applySubstEffectRowCompat Subst.empty fuel effects) := by
  simpa [applySubstEffectRowCompat] using
    applySubstEffectRow_empty_preserves_wf kctx rctx fuel effects h_wf
