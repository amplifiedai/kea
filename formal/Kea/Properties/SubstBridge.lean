/-
  Kea.Properties.SubstBridge — Bridge lemmas between fuel and WF substitution.

  This module provides conservative compatibility results to support incremental
  migration from `applySubst` (fuel-based) to `applySubstWF` (rank-bounded WF).

  Initial bridge scope:
  - Construct an acyclicity witness for `Subst.empty`
  - Prove WF substitution is identity on `Subst.empty`
  - Show fuel and WF APIs agree on `Subst.empty`
-/

import Kea.Substitution
import Kea.Properties.SubstIdempotent

namespace Subst

/--
Construct an `Acyclic` witness from `Idempotent`.

Ranking strategy:
- rank 1 for variables in the substitution domain
- rank 0 for variables outside the domain

Idempotence guarantees that free vars in any mapped range term are outside
the domain, so every lookup step strictly decreases rank.
-/
def acyclicOfIdempotent {s : Subst} (h : s.Idempotent) : Subst.Acyclic s where
  typeRank := fun v => match s.typeMap v with | some _ => 1 | none => 0
  rowRank := fun rv => match s.rowMap rv with | some _ => 1 | none => 0
  type_decreases := by
    intro v ty w h_map hw
    rcases h.typeRange v ty h_map with ⟨h_ty_none, _⟩
    have h_w_none : s.typeMap w = none := h_ty_none w hw
    simp [h_map, h_w_none]
  row_decreases := by
    intro rv r rv' h_map hw
    rcases h.rowRange rv r h_map with ⟨_, h_row_none⟩
    have h_rv_none : s.rowMap rv' = none := h_row_none rv' hw
    simp [h_map, h_rv_none]

/-- `Subst.empty` is acyclic: there are no bindings to violate rank decrease. -/
def emptyAcyclic : Subst.Acyclic Subst.empty where
  typeRank := fun _ => 0
  rowRank := fun _ => 0
  type_decreases := by
    intro v ty w h_map _
    simp [Subst.empty] at h_map
  row_decreases := by
    intro rv r rv' h_map _
    simp [Subst.empty] at h_map

end Subst

mutual
  private theorem applySubstBounded_empty_ty :
      ∀ tlim rlim ty,
        applySubstBounded Subst.empty Subst.emptyAcyclic tlim rlim ty = ty := by
    intro tlim rlim ty
    match ty with
    | .var v =>
      simp [applySubstBounded, Subst.empty]
    | .int | .intN _ _ | .float | .floatN _ | .decimal _ _ | .bool | .string | .html | .markdown | .atom | .date | .dateTime | .unit | .dynamic =>
      simp [applySubstBounded]
    | .list inner =>
      simp [applySubstBounded, applySubstBounded_empty_ty tlim rlim inner]
    | .map k v =>
      simp [applySubstBounded, applySubstBounded_empty_ty tlim rlim k,
        applySubstBounded_empty_ty tlim rlim v]
    | .set inner =>
      simp [applySubstBounded, applySubstBounded_empty_ty tlim rlim inner]
    | .option inner =>
      simp [applySubstBounded, applySubstBounded_empty_ty tlim rlim inner]
    | .result ok err =>
      simp [applySubstBounded, applySubstBounded_empty_ty tlim rlim ok,
        applySubstBounded_empty_ty tlim rlim err]
    | .existential bounds assoc =>
      simp [applySubstBounded, applySubstBounded_empty_tyList tlim rlim assoc]
    | .fixedSizeList inner d =>
      simp [applySubstBounded, applySubstBounded_empty_ty tlim rlim inner]
    | .tensor inner shape =>
      simp [applySubstBounded, applySubstBounded_empty_ty tlim rlim inner]
    | .sum name args =>
      simp [applySubstBounded, applySubstBounded_empty_tyList tlim rlim args]
    | .opaque name params =>
      simp [applySubstBounded, applySubstBounded_empty_tyList tlim rlim params]
    | .record name r =>
      simp [applySubstBounded, applySubstBounded_empty_row tlim rlim r]
    | .anonRecord r =>
      simp [applySubstBounded, applySubstBounded_empty_row tlim rlim r]
    | .dataframe inner =>
      simp [applySubstBounded, applySubstBounded_empty_ty tlim rlim inner]
    | .column inner =>
      simp [applySubstBounded, applySubstBounded_empty_ty tlim rlim inner]
    | .stream inner =>
      simp [applySubstBounded, applySubstBounded_empty_ty tlim rlim inner]
    | .groupedFrame inner keys =>
      simp [applySubstBounded, applySubstBounded_empty_ty tlim rlim inner]
    | .tagged inner tags =>
      simp [applySubstBounded, applySubstBounded_empty_ty tlim rlim inner]
    | .task inner =>
      simp [applySubstBounded, applySubstBounded_empty_ty tlim rlim inner]
    | .actor inner =>
      simp [applySubstBounded, applySubstBounded_empty_ty tlim rlim inner]
    | .arc inner =>
      simp [applySubstBounded, applySubstBounded_empty_ty tlim rlim inner]
    | .function params ret =>
      simp [applySubstBounded, applySubstBounded_empty_tyList tlim rlim params,
        applySubstBounded_empty_ty tlim rlim ret]
    | .functionEff params effects ret =>
      cases effects with
      | mk effectRow =>
        simp [applySubstBounded, applySubstBounded_empty_tyList tlim rlim params,
          applySubstBounded_empty_row tlim rlim effectRow,
          applySubstBounded_empty_ty tlim rlim ret]
    | .forall vars body =>
      simp [applySubstBounded, applySubstBounded_empty_ty tlim rlim body]
    | .app ctor args =>
      simp [applySubstBounded, applySubstBounded_empty_ty tlim rlim ctor,
        applySubstBounded_empty_tyList tlim rlim args]
    | .constructor name fixedArgs arity =>
      simp [applySubstBounded, applySubstBounded_empty_tyList tlim rlim fixedArgs]
    | .row r =>
      simp [applySubstBounded, applySubstBounded_empty_row tlim rlim r]
    | .tuple elems =>
      simp [applySubstBounded, applySubstBounded_empty_tyList tlim rlim elems]

  private theorem applySubstBounded_empty_row :
      ∀ tlim rlim r,
        applySubstRowBounded Subst.empty Subst.emptyAcyclic tlim rlim r = r := by
    intro tlim rlim r
    match r with
    | .mk fields rest =>
      cases rest with
      | none =>
        simp [applySubstRowBounded, applySubstBounded_empty_rowFields tlim rlim fields]
      | some rv =>
        have h_fields :
            applySubstRowFieldsBounded
                { typeMap := fun _ => none, rowMap := fun _ => none }
                Subst.emptyAcyclic tlim rlim fields = fields := by
          simpa [Subst.empty] using (applySubstBounded_empty_rowFields tlim rlim fields)
        simp [applySubstRowBounded, Subst.empty, h_fields]

  private theorem applySubstBounded_empty_tyList :
      ∀ tlim rlim tl,
        applySubstTyListBounded Subst.empty Subst.emptyAcyclic tlim rlim tl = tl := by
    intro tlim rlim tl
    match tl with
    | .nil =>
      simp [applySubstTyListBounded]
    | .cons t rest =>
      simp [applySubstTyListBounded, applySubstBounded_empty_ty tlim rlim t,
        applySubstBounded_empty_tyList tlim rlim rest]

  private theorem applySubstBounded_empty_rowFields :
      ∀ tlim rlim rf,
        applySubstRowFieldsBounded Subst.empty Subst.emptyAcyclic tlim rlim rf = rf := by
    intro tlim rlim rf
    match rf with
    | .nil =>
      simp [applySubstRowFieldsBounded]
    | .cons l ty rest =>
      simp [applySubstRowFieldsBounded, applySubstBounded_empty_ty tlim rlim ty,
        applySubstBounded_empty_rowFields tlim rlim rest]
end

mutual
  private theorem applySubstBounded_noop_ty (s : Subst) (h : Subst.Acyclic s) (tlim rlim : Nat) :
      ∀ ty, (∀ v ∈ freeTypeVars ty, s.typeMap v = none) →
            (∀ v ∈ freeRowVars ty, s.rowMap v = none) →
            applySubstBounded s h tlim rlim ty = ty := by
    intro ty htv hrv
    match ty with
    | .var v =>
      have hv : s.typeMap v = none := htv v (by simp [freeTypeVars])
      simp [applySubstBounded, hv]
    | .int | .intN _ _ | .float | .floatN _ | .decimal _ _ | .bool | .string | .html | .markdown | .atom | .date | .dateTime | .unit | .dynamic =>
      simp [applySubstBounded]
    | .list inner =>
      simp [applySubstBounded]
      exact applySubstBounded_noop_ty s h tlim rlim inner
        (fun v hv => htv v (by simp [freeTypeVars]; exact hv))
        (fun v hv => hrv v (by simp [freeRowVars]; exact hv))
    | .set inner =>
      simp [applySubstBounded]
      exact applySubstBounded_noop_ty s h tlim rlim inner
        (fun v hv => htv v (by simp [freeTypeVars]; exact hv))
        (fun v hv => hrv v (by simp [freeRowVars]; exact hv))
    | .option inner =>
      simp [applySubstBounded]
      exact applySubstBounded_noop_ty s h tlim rlim inner
        (fun v hv => htv v (by simp [freeTypeVars]; exact hv))
        (fun v hv => hrv v (by simp [freeRowVars]; exact hv))
    | .fixedSizeList inner d =>
      simp [applySubstBounded]
      exact applySubstBounded_noop_ty s h tlim rlim inner
        (fun v hv => htv v (by simp [freeTypeVars]; exact hv))
        (fun v hv => hrv v (by simp [freeRowVars]; exact hv))
    | .tensor inner shape =>
      simp [applySubstBounded]
      exact applySubstBounded_noop_ty s h tlim rlim inner
        (fun v hv => htv v (by simp [freeTypeVars]; exact hv))
        (fun v hv => hrv v (by simp [freeRowVars]; exact hv))
    | .sum name args =>
      simp [applySubstBounded]
      exact applySubstBounded_noop_tyList s h tlim rlim args
        (fun v hv => htv v (by simp [freeTypeVars]; exact hv))
        (fun v hv => hrv v (by simp [freeRowVars]; exact hv))
    | .existential bounds assoc =>
      simp [applySubstBounded]
      exact applySubstBounded_noop_tyList s h tlim rlim assoc
        (fun v hv => htv v (by simp [freeTypeVars]; exact hv))
        (fun v hv => hrv v (by simp [freeRowVars]; exact hv))
    | .opaque name params =>
      simp [applySubstBounded]
      exact applySubstBounded_noop_tyList s h tlim rlim params
        (fun v hv => htv v (by simp [freeTypeVars]; exact hv))
        (fun v hv => hrv v (by simp [freeRowVars]; exact hv))
    | .dataframe inner =>
      simp [applySubstBounded]
      exact applySubstBounded_noop_ty s h tlim rlim inner
        (fun v hv => htv v (by simp [freeTypeVars]; exact hv))
        (fun v hv => hrv v (by simp [freeRowVars]; exact hv))
    | .column inner =>
      simp [applySubstBounded]
      exact applySubstBounded_noop_ty s h tlim rlim inner
        (fun v hv => htv v (by simp [freeTypeVars]; exact hv))
        (fun v hv => hrv v (by simp [freeRowVars]; exact hv))
    | .stream inner =>
      simp [applySubstBounded]
      exact applySubstBounded_noop_ty s h tlim rlim inner
        (fun v hv => htv v (by simp [freeTypeVars]; exact hv))
        (fun v hv => hrv v (by simp [freeRowVars]; exact hv))
    | .groupedFrame inner keys =>
      simp [applySubstBounded]
      exact applySubstBounded_noop_ty s h tlim rlim inner
        (fun v hv => htv v (by simp [freeTypeVars]; exact hv))
        (fun v hv => hrv v (by simp [freeRowVars]; exact hv))
    | .tagged inner tags =>
      simp [applySubstBounded]
      exact applySubstBounded_noop_ty s h tlim rlim inner
        (fun v hv => htv v (by simp [freeTypeVars]; exact hv))
        (fun v hv => hrv v (by simp [freeRowVars]; exact hv))
    | .task inner =>
      simp [applySubstBounded]
      exact applySubstBounded_noop_ty s h tlim rlim inner
        (fun v hv => htv v (by simp [freeTypeVars]; exact hv))
        (fun v hv => hrv v (by simp [freeRowVars]; exact hv))
    | .actor inner =>
      simp [applySubstBounded]
      exact applySubstBounded_noop_ty s h tlim rlim inner
        (fun v hv => htv v (by simp [freeTypeVars]; exact hv))
        (fun v hv => hrv v (by simp [freeRowVars]; exact hv))
    | .arc inner =>
      simp [applySubstBounded]
      exact applySubstBounded_noop_ty s h tlim rlim inner
        (fun v hv => htv v (by simp [freeTypeVars]; exact hv))
        (fun v hv => hrv v (by simp [freeRowVars]; exact hv))
    | .map k v =>
      simp [applySubstBounded]
      constructor
      · exact applySubstBounded_noop_ty s h tlim rlim k
          (fun w hw => htv w (by simp [freeTypeVars, List.mem_append]; left; exact hw))
          (fun w hw => hrv w (by simp [freeRowVars, List.mem_append]; left; exact hw))
      · exact applySubstBounded_noop_ty s h tlim rlim v
          (fun w hw => htv w (by simp [freeTypeVars, List.mem_append]; right; exact hw))
          (fun w hw => hrv w (by simp [freeRowVars, List.mem_append]; right; exact hw))
    | .result ok err =>
      simp [applySubstBounded]
      constructor
      · exact applySubstBounded_noop_ty s h tlim rlim ok
          (fun w hw => htv w (by simp [freeTypeVars, List.mem_append]; left; exact hw))
          (fun w hw => hrv w (by simp [freeRowVars, List.mem_append]; left; exact hw))
      · exact applySubstBounded_noop_ty s h tlim rlim err
          (fun w hw => htv w (by simp [freeTypeVars, List.mem_append]; right; exact hw))
          (fun w hw => hrv w (by simp [freeRowVars, List.mem_append]; right; exact hw))
    | .record name r =>
      simp [applySubstBounded]
      exact applySubstBounded_noop_row s h tlim rlim r
        (fun v hv => htv v (by simp [freeTypeVars]; exact hv))
        (fun v hv => hrv v (by simp [freeRowVars]; exact hv))
    | .anonRecord r =>
      simp [applySubstBounded]
      exact applySubstBounded_noop_row s h tlim rlim r
        (fun v hv => htv v (by simp [freeTypeVars]; exact hv))
        (fun v hv => hrv v (by simp [freeRowVars]; exact hv))
    | .row r =>
      simp [applySubstBounded]
      exact applySubstBounded_noop_row s h tlim rlim r
        (fun v hv => htv v (by simp [freeTypeVars]; exact hv))
        (fun v hv => hrv v (by simp [freeRowVars]; exact hv))
    | .function params ret =>
      simp [applySubstBounded]
      constructor
      · exact applySubstBounded_noop_tyList s h tlim rlim params
          (fun w hw => htv w (by simp [freeTypeVars, List.mem_append]; left; exact hw))
          (fun w hw => hrv w (by simp [freeRowVars, List.mem_append]; left; exact hw))
      · exact applySubstBounded_noop_ty s h tlim rlim ret
          (fun w hw => htv w (by simp [freeTypeVars, List.mem_append]; right; exact hw))
          (fun w hw => hrv w (by simp [freeRowVars, List.mem_append]; right; exact hw))
    | .functionEff params effects ret =>
      cases effects with
      | mk effectRow =>
        simp [applySubstBounded]
        constructor
        · exact applySubstBounded_noop_tyList s h tlim rlim params
            (fun w hw => htv w (by simp [freeTypeVars, freeTypeVarsEffectRow, List.mem_append, hw]))
            (fun w hw => hrv w (by simp [freeRowVars, freeRowVarsEffectRow, List.mem_append, hw]))
        · constructor
          · exact applySubstBounded_noop_row s h tlim rlim effectRow
              (fun w hw => htv w (by simp [freeTypeVars, freeTypeVarsEffectRow, List.mem_append, hw]))
              (fun w hw => hrv w (by simp [freeRowVars, freeRowVarsEffectRow, List.mem_append, hw]))
          · exact applySubstBounded_noop_ty s h tlim rlim ret
              (fun w hw => htv w (by simp [freeTypeVars, freeTypeVarsEffectRow, List.mem_append, hw]))
              (fun w hw => hrv w (by simp [freeRowVars, freeRowVarsEffectRow, List.mem_append, hw]))
    | .forall vars body =>
      simp [applySubstBounded]
      exact applySubstBounded_noop_ty s h tlim rlim body
        (fun v hv => htv v (by simp [freeTypeVars]; exact hv))
        (fun v hv => hrv v (by simp [freeRowVars]; exact hv))
    | .app ctor args =>
      simp [applySubstBounded]
      constructor
      · exact applySubstBounded_noop_ty s h tlim rlim ctor
          (fun w hw => htv w (by simp [freeTypeVars, List.mem_append]; left; exact hw))
          (fun w hw => hrv w (by simp [freeRowVars, List.mem_append]; left; exact hw))
      · exact applySubstBounded_noop_tyList s h tlim rlim args
          (fun w hw => htv w (by simp [freeTypeVars, List.mem_append]; right; exact hw))
          (fun w hw => hrv w (by simp [freeRowVars, List.mem_append]; right; exact hw))
    | .constructor name fixedArgs arity =>
      simp [applySubstBounded]
      exact applySubstBounded_noop_tyList s h tlim rlim fixedArgs
        (fun v hv => htv v (by simp [freeTypeVars]; exact hv))
        (fun v hv => hrv v (by simp [freeRowVars]; exact hv))
    | .tuple elems =>
      simp [applySubstBounded]
      exact applySubstBounded_noop_tyList s h tlim rlim elems
        (fun v hv => htv v (by simp [freeTypeVars]; exact hv))
        (fun v hv => hrv v (by simp [freeRowVars]; exact hv))

  private theorem applySubstBounded_noop_row (s : Subst) (h : Subst.Acyclic s) (tlim rlim : Nat) :
      ∀ r, (∀ v ∈ freeTypeVarsRow r, s.typeMap v = none) →
           (∀ v ∈ freeRowVarsRow r, s.rowMap v = none) →
           applySubstRowBounded s h tlim rlim r = r := by
    intro r htv hrv
    match r with
    | .mk fields rest =>
      have hrf :
          applySubstRowFieldsBounded s h tlim rlim fields = fields :=
        applySubstBounded_noop_rowFields s h tlim rlim fields
          (fun v hv => htv v (by simp [freeTypeVarsRow]; exact hv))
          (fun v hv => by
            apply hrv v
            simp only [freeRowVarsRow]
            cases rest with
            | none => exact hv
            | some _ => exact List.mem_cons_of_mem _ hv)
      cases rest with
      | none =>
        simp [applySubstRowBounded, hrf]
      | some rv =>
        have hrm : s.rowMap rv = none := hrv rv (by simp [freeRowVarsRow])
        simp [applySubstRowBounded, hrf, hrm]

  private theorem applySubstBounded_noop_tyList (s : Subst) (h : Subst.Acyclic s) (tlim rlim : Nat) :
      ∀ tl, (∀ v ∈ freeTypeVarsTyList tl, s.typeMap v = none) →
            (∀ v ∈ freeRowVarsTyList tl, s.rowMap v = none) →
            applySubstTyListBounded s h tlim rlim tl = tl := by
    intro tl htv hrv
    match tl with
    | .nil =>
      simp [applySubstTyListBounded]
    | .cons t rest =>
      simp [applySubstTyListBounded]
      constructor
      · exact applySubstBounded_noop_ty s h tlim rlim t
          (fun v hv => htv v (by simp [freeTypeVarsTyList, List.mem_append]; left; exact hv))
          (fun v hv => hrv v (by simp [freeRowVarsTyList, List.mem_append]; left; exact hv))
      · exact applySubstBounded_noop_tyList s h tlim rlim rest
          (fun v hv => htv v (by simp [freeTypeVarsTyList, List.mem_append]; right; exact hv))
          (fun v hv => hrv v (by simp [freeRowVarsTyList, List.mem_append]; right; exact hv))

  private theorem applySubstBounded_noop_rowFields (s : Subst) (h : Subst.Acyclic s) (tlim rlim : Nat) :
      ∀ rf, (∀ v ∈ freeTypeVarsRowFields rf, s.typeMap v = none) →
            (∀ v ∈ freeRowVarsRowFields rf, s.rowMap v = none) →
            applySubstRowFieldsBounded s h tlim rlim rf = rf := by
    intro rf htv hrv
    match rf with
    | .nil =>
      simp [applySubstRowFieldsBounded]
    | .cons l ty rest =>
      simp [applySubstRowFieldsBounded]
      constructor
      · exact applySubstBounded_noop_ty s h tlim rlim ty
          (fun v hv => htv v (by simp [freeTypeVarsRowFields, List.mem_append]; left; exact hv))
          (fun v hv => hrv v (by simp [freeRowVarsRowFields, List.mem_append]; left; exact hv))
      · exact applySubstBounded_noop_rowFields s h tlim rlim rest
          (fun v hv => htv v (by simp [freeTypeVarsRowFields, List.mem_append]; right; exact hv))
          (fun v hv => hrv v (by simp [freeRowVarsRowFields, List.mem_append]; right; exact hv))
end

/-- WF substitution is no-op when the type has no vars in substitution domain. -/
theorem applySubstWF_noop (s : Subst) (h : Subst.Acyclic s) (ty : Ty)
    (htv : ∀ v ∈ freeTypeVars ty, s.typeMap v = none)
    (hrv : ∀ v ∈ freeRowVars ty, s.rowMap v = none) :
    applySubstWF s h ty = ty := by
  unfold applySubstWF
  exact applySubstBounded_noop_ty s h _ _ ty htv hrv

/-- WF row substitution is no-op when the row has no vars in substitution domain. -/
theorem applySubstRowWF_noop (s : Subst) (h : Subst.Acyclic s) (r : Row)
    (htv : ∀ v ∈ freeTypeVarsRow r, s.typeMap v = none)
    (hrv : ∀ v ∈ freeRowVarsRow r, s.rowMap v = none) :
    applySubstRowWF s h r = r := by
  unfold applySubstRowWF
  exact applySubstBounded_noop_row s h _ _ r htv hrv

/-- Idempotent range terms are WF fixed points (type side). -/
theorem applySubstWF_range_noop_of_idempotent
    (s : Subst) (h_idemp : s.Idempotent) (v : TypeVarId) (ty : Ty)
    (h_lookup : s.typeMap v = some ty) :
    let ac := Subst.acyclicOfIdempotent h_idemp
    applySubstWF s ac ty = ty := by
  let ac : Subst.Acyclic s := Subst.acyclicOfIdempotent h_idemp
  have h_range := h_idemp.typeRange v ty h_lookup
  exact applySubstWF_noop s ac ty h_range.1 h_range.2

/-- Idempotent range terms are WF fixed points (row side). -/
theorem applySubstRowWF_range_noop_of_idempotent
    (s : Subst) (h_idemp : s.Idempotent) (v : RowVarId) (r : Row)
    (h_lookup : s.rowMap v = some r) :
    let ac := Subst.acyclicOfIdempotent h_idemp
    applySubstRowWF s ac r = r := by
  let ac : Subst.Acyclic s := Subst.acyclicOfIdempotent h_idemp
  have h_range := h_idemp.rowRange v r h_lookup
  exact applySubstRowWF_noop s ac r h_range.1 h_range.2

/-- Under idempotence, binding `v ↦ ty` is consistent in bounded WF substitution. -/
theorem applySubstBounded_bindType_consistent_of_idempotent
    (s : Subst) (v : TypeVarId) (ty : Ty)
    (h_idemp : (s.bindType v ty).Idempotent) :
    let sb := s.bindType v ty
    let ac := Subst.acyclicOfIdempotent h_idemp
    applySubstBounded sb ac 2 1 (.var v) = applySubstBounded sb ac 2 1 ty := by
  let sb : Subst := s.bindType v ty
  have h_lookup : sb.typeMap v = some ty := by
    unfold sb Subst.bindType
    simp [BEq.beq]
  have h_range := h_idemp.typeRange v ty h_lookup
  let ac : Subst.Acyclic sb := Subst.acyclicOfIdempotent h_idemp
  have h_var : applySubstBounded sb ac 2 1 (.var v) = applySubstBounded sb ac 1 1 ty := by
    dsimp [sb, ac]
    simp [Subst.bindType, Subst.acyclicOfIdempotent, applySubstBounded, BEq.beq]
  have h_ty_1 : applySubstBounded sb ac 1 1 ty = ty :=
    applySubstBounded_noop_ty sb ac 1 1 ty h_range.1 h_range.2
  have h_ty_2 : applySubstBounded sb ac 2 1 ty = ty :=
    applySubstBounded_noop_ty sb ac 2 1 ty h_range.1 h_range.2
  dsimp [sb, ac]
  calc
    applySubstBounded (s.bindType v ty) (Subst.acyclicOfIdempotent h_idemp) 2 1 (.var v)
        = applySubstBounded (s.bindType v ty) (Subst.acyclicOfIdempotent h_idemp) 1 1 ty := h_var
    _ = ty := h_ty_1
    _ = applySubstBounded (s.bindType v ty) (Subst.acyclicOfIdempotent h_idemp) 2 1 ty := by
        symm
        exact h_ty_2

/-- Under idempotence, binding `v ↦ ty` is consistent in full WF substitution. -/
theorem applySubstWF_bindType_consistent_of_idempotent
    (s : Subst) (v : TypeVarId) (ty : Ty)
    (h_idemp : (s.bindType v ty).Idempotent) :
    let sb := s.bindType v ty
    let ac := Subst.acyclicOfIdempotent h_idemp
    applySubstWF sb ac (.var v) = applySubstWF sb ac ty := by
  let sb : Subst := s.bindType v ty
  have h_lookup : sb.typeMap v = some ty := by
    unfold sb Subst.bindType
    simp [BEq.beq]
  let ac : Subst.Acyclic sb := Subst.acyclicOfIdempotent h_idemp
  have h_range := h_idemp.typeRange v ty h_lookup
  have h_lhs : applySubstWF sb ac (.var v) = ty := by
    calc
      applySubstWF sb ac (.var v)
          = applySubstBounded sb ac (ac.typeRank v) 1 ty :=
            applySubstWF_var_lookup sb ac v ty h_lookup
      _ = ty :=
        applySubstBounded_noop_ty sb ac (ac.typeRank v) 1 ty h_range.1 h_range.2
  have h_rhs : applySubstWF sb ac ty = ty :=
    applySubstWF_noop sb ac ty h_range.1 h_range.2
  dsimp [sb, ac]
  rw [h_lhs, h_rhs]

/-- Under idempotence, binding `rv ↦ r` is consistent on an open tail row in bounded WF substitution. -/
theorem applySubstRowBounded_bindRow_consistent_of_idempotent
    (s : Subst) (rv : RowVarId) (r : Row)
    (h_idemp : (s.bindRow rv r).Idempotent) :
    let sb := s.bindRow rv r
    let ac := Subst.acyclicOfIdempotent h_idemp
    applySubstRowBounded sb ac 1 (ac.rowRank rv + 1) (Row.mk .nil (some rv)) =
      applySubstRowBounded sb ac 1 (ac.rowRank rv) r := by
  let sb : Subst := s.bindRow rv r
  let ac : Subst.Acyclic sb := Subst.acyclicOfIdempotent h_idemp
  dsimp [sb, ac]
  simp [applySubstRowBounded, applySubstRowFieldsBounded, Subst.bindRow, BEq.beq, RowFields.append]
  let tailResolved :=
      applySubstRowBounded
        { typeMap := s.typeMap, rowMap := fun w => if decide (w = rv) = true then some r else s.rowMap w }
        (Subst.acyclicOfIdempotent h_idemp) 1 ((Subst.acyclicOfIdempotent h_idemp).rowRank rv) r
  change (match tailResolved with | Row.mk tailFields tailRest => Row.mk tailFields tailRest) = tailResolved
  cases tailResolved <;> rfl

/-- Under idempotence, binding `rv ↦ r` is consistent on an open tail row in full WF substitution. -/
theorem applySubstRowWF_bindRow_consistent_of_idempotent
    (s : Subst) (rv : RowVarId) (r : Row)
    (h_idemp : (s.bindRow rv r).Idempotent) :
    let sb := s.bindRow rv r
    let ac := Subst.acyclicOfIdempotent h_idemp
    applySubstRowWF sb ac (Row.mk .nil (some rv)) = applySubstRowWF sb ac r := by
  let sb : Subst := s.bindRow rv r
  have h_lookup : sb.rowMap rv = some r := by
    unfold sb Subst.bindRow
    simp [BEq.beq]
  let ac : Subst.Acyclic sb := Subst.acyclicOfIdempotent h_idemp
  have h_range := h_idemp.rowRange rv r h_lookup
  have h_lhs :
      applySubstRowWF sb ac (Row.mk .nil (some rv))
        = applySubstRowBounded sb ac 1 (ac.rowRank rv) r :=
    applySubstRowWF_empty_open_lookup sb ac rv r h_lookup
  have h_rhs : applySubstRowWF sb ac r = r :=
    applySubstRowWF_noop sb ac r h_range.1 h_range.2
  have h_mid : applySubstRowBounded sb ac 1 (ac.rowRank rv) r = r :=
    applySubstBounded_noop_row sb ac 1 (ac.rowRank rv) r h_range.1 h_range.2
  dsimp [sb, ac]
  rw [h_lhs, h_mid, h_rhs]

/-- WF substitution is identity for `Subst.empty` (types). -/
theorem applySubstWF_empty (ty : Ty) :
    applySubstWF Subst.empty Subst.emptyAcyclic ty = ty := by
  unfold applySubstWF
  exact applySubstBounded_empty_ty _ _ ty

/-- WF substitution is identity for `Subst.empty` (rows). -/
theorem applySubstRowWF_empty (r : Row) :
    applySubstRowWF Subst.empty Subst.emptyAcyclic r = r := by
  unfold applySubstRowWF
  exact applySubstBounded_empty_row _ _ r

/-- Fuel and WF substitution agree on `Subst.empty` (types). -/
theorem applySubst_empty_eq_applySubstWF_empty (fuel : Nat) (ty : Ty) :
    applySubst Subst.empty fuel ty = applySubstWF Subst.empty Subst.emptyAcyclic ty := by
  rw [applySubstWF_empty]
  exact (applySubst_noop Subst.empty fuel).1 ty (fun _ _ => rfl) (fun _ _ => rfl)

/-- Fuel and WF substitution agree on `Subst.empty` (rows). -/
theorem applySubstRow_empty_eq_applySubstRowWF_empty (fuel : Nat) (r : Row) :
    applySubstRow Subst.empty fuel r = applySubstRowWF Subst.empty Subst.emptyAcyclic r := by
  rw [applySubstRowWF_empty]
  exact (applySubst_noop Subst.empty fuel).2.1 r (fun _ _ => rfl) (fun _ _ => rfl)

/--
Fuel-compat and WF substitution agree on a bound type variable when the
substitution is idempotent and fuel is non-zero.
-/
theorem applySubstCompat_var_eq_applySubstWF_of_idempotent
    (s : Subst) (fuel : Nat) (v : TypeVarId) (ty : Ty)
    (h_pos : 0 < fuel)
    (h_idemp : s.Idempotent)
    (h_lookup : s.typeMap v = some ty) :
    let ac := Subst.acyclicOfIdempotent h_idemp
    applySubstCompat s fuel (.var v) = applySubstWF s ac (.var v) := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt h_pos) with ⟨n, rfl⟩
  let ac : Subst.Acyclic s := Subst.acyclicOfIdempotent h_idemp
  have h_range := h_idemp.typeRange v ty h_lookup
  have h_fuel_noop : applySubst s n ty = ty :=
    (applySubst_noop s n).1 ty h_range.1 h_range.2
  have h_fuel_var : applySubst s (Nat.succ n) (.var v) = ty := by
    simp [applySubst, h_lookup, h_fuel_noop]
  have h_wf_var : applySubstWF s ac (.var v) = ty := by
    calc
      applySubstWF s ac (.var v)
          = applySubstBounded s ac (ac.typeRank v) 1 ty :=
            applySubstWF_var_lookup s ac v ty h_lookup
      _ = ty :=
        applySubstBounded_noop_ty s ac (ac.typeRank v) 1 ty h_range.1 h_range.2
  dsimp [applySubstCompat]
  rw [h_fuel_var, h_wf_var]

/--
Fuel-compat and WF substitution agree on the canonical open-row tail lookup
shape when the row binding substitution is idempotent and fuel is non-zero.
-/
theorem applySubstRowCompat_empty_open_eq_applySubstRowWF_of_idempotent
    (s : Subst) (fuel : Nat) (rv : RowVarId) (row : Row)
    (h_pos : 0 < fuel)
    (h_idemp : (s.bindRow rv row).Idempotent) :
    let sb := s.bindRow rv row
    let ac := Subst.acyclicOfIdempotent h_idemp
    applySubstRowCompat sb fuel (Row.mk .nil (some rv)) =
      applySubstRowWF sb ac (Row.mk .nil (some rv)) := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt h_pos) with ⟨n, rfl⟩
  let sb : Subst := s.bindRow rv row
  let ac : Subst.Acyclic sb := Subst.acyclicOfIdempotent h_idemp
  have h_lookup : sb.rowMap rv = some row := by
    unfold sb Subst.bindRow
    simp [BEq.beq]
  have h_range := h_idemp.rowRange rv row h_lookup
  have h_fuel_noop : applySubstRow sb n row = row :=
    (applySubst_noop sb n).2.1 row h_range.1 h_range.2
  have h_fuel_open : applySubstRow sb (Nat.succ n) (Row.mk .nil (some rv)) = row := by
    cases row with
    | mk tailFields tailRest =>
      have h_nil : applySubstRowFields sb n .nil = .nil := by
        cases n <;> rfl
      simp [applySubstRow, h_lookup, h_fuel_noop, h_nil, RowFields.append]
  have h_wf_open : applySubstRowWF sb ac (Row.mk .nil (some rv)) = row := by
    calc
      applySubstRowWF sb ac (Row.mk .nil (some rv))
          = applySubstRowWF sb ac row :=
            applySubstRowWF_bindRow_consistent_of_idempotent s rv row h_idemp
      _ = row :=
            applySubstRowWF_noop sb ac row h_range.1 h_range.2
  dsimp [applySubstRowCompat, sb, ac]
  rw [h_fuel_open, h_wf_open]

/--
Fuel-compat and WF row substitution agree on the canonical open-row tail lookup
for any bound row variable in an idempotent substitution, with positive fuel.
-/
theorem applySubstRowCompat_empty_open_eq_applySubstRowWF_of_row_lookup_idempotent
    (s : Subst) (fuel : Nat) (rv : RowVarId) (row : Row)
    (h_pos : 0 < fuel)
    (h_idemp : s.Idempotent)
    (h_lookup : s.rowMap rv = some row) :
    let ac := Subst.acyclicOfIdempotent h_idemp
    applySubstRowCompat s fuel (Row.mk .nil (some rv)) =
      applySubstRowWF s ac (Row.mk .nil (some rv)) := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt h_pos) with ⟨n, rfl⟩
  let ac : Subst.Acyclic s := Subst.acyclicOfIdempotent h_idemp
  have h_range := h_idemp.rowRange rv row h_lookup
  have h_fuel_noop : applySubstRow s n row = row :=
    (applySubst_noop s n).2.1 row h_range.1 h_range.2
  have h_fuel_open : applySubstRow s (Nat.succ n) (Row.mk .nil (some rv)) = row := by
    cases row with
    | mk tailFields tailRest =>
      have h_nil : applySubstRowFields s n .nil = .nil := by
        cases n <;> rfl
      simp [applySubstRow, h_lookup, h_fuel_noop, h_nil, RowFields.append]
  have h_wf_open : applySubstRowWF s ac (Row.mk .nil (some rv)) = row := by
    calc
      applySubstRowWF s ac (Row.mk .nil (some rv))
          = applySubstRowBounded s ac 1 (ac.rowRank rv) row :=
            applySubstRowWF_empty_open_lookup s ac rv row h_lookup
      _ = row :=
            applySubstBounded_noop_row s ac 1 (ac.rowRank rv) row h_range.1 h_range.2
  dsimp [applySubstRowCompat, ac]
  rw [h_fuel_open, h_wf_open]

/--
Generic compat/WF bridge: if a type has no free vars in substitution domain,
both fueled compat substitution and WF substitution are identity on it.
-/
theorem applySubstCompat_eq_applySubstWF_of_no_domain_vars
    (s : Subst) (h : Subst.Acyclic s) (fuel : Nat) (ty : Ty)
    (htv : ∀ v ∈ freeTypeVars ty, s.typeMap v = none)
    (hrv : ∀ v ∈ freeRowVars ty, s.rowMap v = none) :
    applySubstCompat s fuel ty = applySubstWF s h ty := by
  dsimp [applySubstCompat]
  rw [(applySubst_noop s fuel).1 ty htv hrv, applySubstWF_noop s h ty htv hrv]

/--
Generic row compat/WF bridge: if a row has no free vars in substitution domain,
both fueled compat row substitution and WF row substitution are identity on it.
-/
theorem applySubstRowCompat_eq_applySubstRowWF_of_no_domain_vars
    (s : Subst) (h : Subst.Acyclic s) (fuel : Nat) (r : Row)
    (htv : ∀ v ∈ freeTypeVarsRow r, s.typeMap v = none)
    (hrv : ∀ v ∈ freeRowVarsRow r, s.rowMap v = none) :
    applySubstRowCompat s fuel r = applySubstRowWF s h r := by
  dsimp [applySubstRowCompat]
  rw [(applySubst_noop s fuel).2.1 r htv hrv, applySubstRowWF_noop s h r htv hrv]

/-- Constructor corollary for `Ty.list` under no-domain-vars assumptions. -/
theorem applySubstCompat_list_eq_applySubstWF_of_no_domain_vars
    (s : Subst) (h : Subst.Acyclic s) (fuel : Nat) (inner : Ty)
    (htv : ∀ v ∈ freeTypeVars inner, s.typeMap v = none)
    (hrv : ∀ v ∈ freeRowVars inner, s.rowMap v = none) :
    applySubstCompat s fuel (.list inner) = applySubstWF s h (.list inner) := by
  apply applySubstCompat_eq_applySubstWF_of_no_domain_vars s h fuel (.list inner)
  · intro v hv
    exact htv v (by simpa [freeTypeVars] using hv)
  · intro v hv
    exact hrv v (by simpa [freeRowVars] using hv)

/-- Constructor corollary for `Ty.map` under no-domain-vars assumptions. -/
theorem applySubstCompat_map_eq_applySubstWF_of_no_domain_vars
    (s : Subst) (h : Subst.Acyclic s) (fuel : Nat) (k v : Ty)
    (htk : ∀ w ∈ freeTypeVars k, s.typeMap w = none)
    (hrk : ∀ w ∈ freeRowVars k, s.rowMap w = none)
    (htv : ∀ w ∈ freeTypeVars v, s.typeMap w = none)
    (hrv : ∀ w ∈ freeRowVars v, s.rowMap w = none) :
    applySubstCompat s fuel (.map k v) = applySubstWF s h (.map k v) := by
  apply applySubstCompat_eq_applySubstWF_of_no_domain_vars s h fuel (.map k v)
  · intro w hw
    rcases (by simpa [freeTypeVars, List.mem_append] using hw) with hk | hv
    · exact htk w hk
    · exact htv w hv
  · intro w hw
    rcases (by simpa [freeRowVars, List.mem_append] using hw) with hk | hv
    · exact hrk w hk
    · exact hrv w hv

/-- Constructor corollary for anonymous record typing under no-domain-vars assumptions. -/
theorem applySubstCompat_anonRecord_eq_applySubstWF_of_no_domain_vars
    (s : Subst) (h : Subst.Acyclic s) (fuel : Nat) (r : Row)
    (htv : ∀ v ∈ freeTypeVarsRow r, s.typeMap v = none)
    (hrv : ∀ v ∈ freeRowVarsRow r, s.rowMap v = none) :
    applySubstCompat s fuel (.anonRecord r) = applySubstWF s h (.anonRecord r) := by
  apply applySubstCompat_eq_applySubstWF_of_no_domain_vars s h fuel (.anonRecord r)
  · intro v hv
    exact htv v (by simpa [freeTypeVars] using hv)
  · intro v hv
    exact hrv v (by simpa [freeRowVars] using hv)

/-- Constructor corollary for tuples under no-domain-vars assumptions. -/
theorem applySubstCompat_tuple_eq_applySubstWF_of_no_domain_vars
    (s : Subst) (h : Subst.Acyclic s) (fuel : Nat) (tl : TyList)
    (htv : ∀ v ∈ freeTypeVarsTyList tl, s.typeMap v = none)
    (hrv : ∀ v ∈ freeRowVarsTyList tl, s.rowMap v = none) :
    applySubstCompat s fuel (.tuple tl) = applySubstWF s h (.tuple tl) := by
  apply applySubstCompat_eq_applySubstWF_of_no_domain_vars s h fuel (.tuple tl)
  · intro v hv
    exact htv v (by simpa [freeTypeVars] using hv)
  · intro v hv
    exact hrv v (by simpa [freeRowVars] using hv)
