/-
  Kea.Properties.NominalAdtParity - Nominal ADT constructor parity slice.

  Current scope: nominal `Sum` and `Opaque` constructors in the Lean type model
  with constructor-local substitution decomposition, reflexive unification, and
  nominal-name mismatch witnesses.
-/

import Kea.Properties.UnifyReflexive

private theorem string_beq_false_of_ne {a b : String} (h : a = b -> False) : (a == b) = false := by
  cases h_beq : (a == b) with
  | false => rfl
  | true =>
    have hab : a = b := by simpa using h_beq
    exact (h hab).elim

private theorem applySubst_int (s : Subst) : ∀ fuel, applySubst s fuel .int = .int
  | 0 => rfl
  | _ + 1 => rfl

private theorem applySubstTyList_nil (s : Subst) : ∀ fuel, applySubstTyList s fuel .nil = .nil
  | 0 => rfl
  | _ + 1 => rfl

private theorem applySubstTyList_int_singleton (s : Subst) :
    ∀ fuel, applySubstTyList s fuel (.cons .int .nil) = (.cons .int .nil)
  | 0 => rfl
  | fuel + 1 => by
    simp [applySubstTyList, applySubst_int s fuel, applySubstTyList_nil s fuel]

/-- One substitution step over `Sum` rewrites only instantiated type arguments. -/
theorem sum_subst_step (s : Subst) (fuel : Nat) (name : String) (args : TyList) :
    applySubst s (fuel + 1) (.sum name args) = .sum name (applySubstTyList s fuel args) := by
  simp [applySubst]

/-- One substitution step over `Opaque` rewrites only instantiated type arguments. -/
theorem opaque_subst_step (s : Subst) (fuel : Nat) (name : String) (params : TyList) :
    applySubst s (fuel + 1) (.opaque name params) = .opaque name (applySubstTyList s fuel params) := by
  simp [applySubst]

/-- Packaged nominal-ADT substitution-step slice across `Sum` and `Opaque`. -/
theorem nominal_adt_subst_step_slice
    (s : Subst) (fuel : Nat) (sumName opaqueName : String) (args params : TyList) :
    applySubst s (fuel + 1) (.sum sumName args) =
      .sum sumName (applySubstTyList s fuel args)
    ∧
    applySubst s (fuel + 1) (.opaque opaqueName params) =
      .opaque opaqueName (applySubstTyList s fuel params) := by
  refine ⟨?_, ?_⟩
  · exact sum_subst_step s fuel sumName args
  · exact opaque_subst_step s fuel opaqueName params

/-- On normalized sum forms, failed constructor BEq short-circuit and equal
    nominal names reduce unification to argument-list unification. -/
theorem sum_unify_branch_decision_of_normalized
    (st : UnifyState) (fuel : Nat)
    (name1 name2 name1' name2' : String) (args1 args2 args1' args2' : TyList)
    (hleft :
      applySubst st.subst fuel (.sum name1 args1) =
        .sum name1' args1')
    (hright :
      applySubst st.subst fuel (.sum name2 args2) =
        .sum name2' args2')
    (h_ctor_neq :
      (applySubst st.subst fuel (.sum name1 args1) ==
        applySubst st.subst fuel (.sum name2 args2)) = false) :
    unify st (fuel + 1) (.sum name1 args1) (.sum name2 args2) =
      (if name1' == name2' then unifyTyList st fuel args1' args2' else .err "type mismatch") := by
  have h_ctor_neq' :
      (Ty.sum name1' args1' == Ty.sum name2' args2') = false := by
    simpa [hleft, hright] using h_ctor_neq
  simp [unify, applySubstCompat, hleft, hright, h_ctor_neq']

/-- On normalized sum forms, failed constructor BEq short-circuit and equal
    nominal names reduce unification to argument-list unification. -/
theorem sum_unify_reduces_to_args_of_normalized
    (st : UnifyState) (fuel : Nat)
    (name1 name2 name1' name2' : String) (args1 args2 args1' args2' : TyList)
    (hleft :
      applySubst st.subst fuel (.sum name1 args1) =
        .sum name1' args1')
    (hright :
      applySubst st.subst fuel (.sum name2 args2) =
        .sum name2' args2')
    (h_ctor_neq :
      (applySubst st.subst fuel (.sum name1 args1) ==
        applySubst st.subst fuel (.sum name2 args2)) = false)
    (h_name : (name1' == name2') = true) :
    unify st (fuel + 1) (.sum name1 args1) (.sum name2 args2) =
      unifyTyList st fuel args1' args2' := by
  rw [sum_unify_branch_decision_of_normalized st fuel name1 name2 name1' name2' args1 args2 args1' args2'
        hleft hright h_ctor_neq]
  simp [h_name]

/-- If the normalized sum-argument branch succeeds, the outer normalized sum
    unifier succeeds with the same resulting state. -/
theorem sum_unify_accepts_of_normalized_args_ok
    (st st' : UnifyState) (fuel : Nat)
    (name1 name2 name1' name2' : String) (args1 args2 args1' args2' : TyList)
    (hleft :
      applySubst st.subst fuel (.sum name1 args1) =
        .sum name1' args1')
    (hright :
      applySubst st.subst fuel (.sum name2 args2) =
        .sum name2' args2')
    (h_ctor_neq :
      (applySubst st.subst fuel (.sum name1 args1) ==
        applySubst st.subst fuel (.sum name2 args2)) = false)
    (h_name : (name1' == name2') = true)
    (h_args : unifyTyList st fuel args1' args2' = .ok st') :
    unify st (fuel + 1) (.sum name1 args1) (.sum name2 args2) = .ok st' := by
  rw [sum_unify_reduces_to_args_of_normalized st fuel name1 name2 name1' name2' args1 args2 args1' args2'
        hleft hright h_ctor_neq h_name]
  exact h_args

/-- If the normalized sum-argument branch rejects with arity mismatch, the
    outer normalized sum unifier rejects with the same error. -/
theorem sum_unify_rejects_args_err_of_normalized
    (st : UnifyState) (fuel : Nat)
    (name1 name2 name1' name2' : String) (args1 args2 args1' args2' : TyList)
    (hleft :
      applySubst st.subst fuel (.sum name1 args1) =
        .sum name1' args1')
    (hright :
      applySubst st.subst fuel (.sum name2 args2) =
        .sum name2' args2')
    (h_ctor_neq :
      (applySubst st.subst fuel (.sum name1 args1) ==
        applySubst st.subst fuel (.sum name2 args2)) = false)
    (h_name : (name1' == name2') = true)
    (e : String)
    (h_args : unifyTyList st fuel args1' args2' = .err e) :
    unify st (fuel + 1) (.sum name1 args1) (.sum name2 args2) =
      .err e := by
  rw [sum_unify_reduces_to_args_of_normalized st fuel name1 name2 name1' name2' args1 args2 args1' args2'
        hleft hright h_ctor_neq h_name]
  exact h_args

/-- If the normalized sum-argument branch rejects with arity mismatch, the
    outer normalized sum unifier rejects with the same error. -/
theorem sum_unify_rejects_arity_mismatch_of_normalized
    (st : UnifyState) (fuel : Nat)
    (name1 name2 name1' name2' : String) (args1 args2 args1' args2' : TyList)
    (hleft :
      applySubst st.subst fuel (.sum name1 args1) =
        .sum name1' args1')
    (hright :
      applySubst st.subst fuel (.sum name2 args2) =
        .sum name2' args2')
    (h_ctor_neq :
      (applySubst st.subst fuel (.sum name1 args1) ==
        applySubst st.subst fuel (.sum name2 args2)) = false)
    (h_name : (name1' == name2') = true)
    (h_args : unifyTyList st fuel args1' args2' = .err "type list length mismatch") :
    unify st (fuel + 1) (.sum name1 args1) (.sum name2 args2) =
      .err "type list length mismatch" := by
  exact sum_unify_rejects_args_err_of_normalized st fuel
    name1 name2 name1' name2' args1 args2 args1' args2'
    hleft hright h_ctor_neq h_name
    "type list length mismatch" h_args

/-- On normalized sum forms, failed constructor BEq short-circuit and distinct
    nominal names force mismatch. -/
theorem sum_unify_rejects_of_normalized
    (st : UnifyState) (fuel : Nat)
    (name1 name2 name1' name2' : String) (args1 args2 args1' args2' : TyList)
    (hleft :
      applySubst st.subst fuel (.sum name1 args1) =
        .sum name1' args1')
    (hright :
      applySubst st.subst fuel (.sum name2 args2) =
        .sum name2' args2')
    (h_ctor_neq :
      (applySubst st.subst fuel (.sum name1 args1) ==
        applySubst st.subst fuel (.sum name2 args2)) = false)
    (h_name : (name1' == name2') = false) :
    unify st (fuel + 1) (.sum name1 args1) (.sum name2 args2) =
      .err "type mismatch" := by
  have h_ctor_neq' :
      (Ty.sum name1' args1' == Ty.sum name2' args2') = false := by
    simpa [hleft, hright] using h_ctor_neq
  simp [unify, applySubstCompat, hleft, hright, h_ctor_neq', h_name]

/-- On normalized opaque forms, failed constructor BEq short-circuit and equal
    nominal names reduce unification to parameter-list unification. -/
theorem opaque_unify_branch_decision_of_normalized
    (st : UnifyState) (fuel : Nat)
    (name1 name2 name1' name2' : String) (params1 params2 params1' params2' : TyList)
    (hleft :
      applySubst st.subst fuel (.opaque name1 params1) =
        .opaque name1' params1')
    (hright :
      applySubst st.subst fuel (.opaque name2 params2) =
        .opaque name2' params2')
    (h_ctor_neq :
      (applySubst st.subst fuel (.opaque name1 params1) ==
        applySubst st.subst fuel (.opaque name2 params2)) = false) :
    unify st (fuel + 1) (.opaque name1 params1) (.opaque name2 params2) =
      (if name1' == name2' then unifyTyList st fuel params1' params2' else .err "type mismatch") := by
  have h_ctor_neq' :
      (Ty.opaque name1' params1' == Ty.opaque name2' params2') = false := by
    simpa [hleft, hright] using h_ctor_neq
  simp [unify, applySubstCompat, hleft, hright, h_ctor_neq']

/-- Packaged normalized branch-decision slice across nominal ADT constructors:
    with failed constructor BEq short-circuit, `Sum`/`Opaque` unification each
    reduce to name-gated list unification branches. -/
theorem nominal_adt_unify_branch_decision_slice_of_normalized
    (st : UnifyState) (fuel : Nat)
    (sumName1 sumName2 sumName1' sumName2' : String)
    (sumArgs1 sumArgs2 sumArgs1' sumArgs2' : TyList)
    (opaqueName1 opaqueName2 opaqueName1' opaqueName2' : String)
    (opaqueParams1 opaqueParams2 opaqueParams1' opaqueParams2' : TyList)
    (h_sum_left :
      applySubst st.subst fuel (.sum sumName1 sumArgs1) =
        .sum sumName1' sumArgs1')
    (h_sum_right :
      applySubst st.subst fuel (.sum sumName2 sumArgs2) =
        .sum sumName2' sumArgs2')
    (h_sum_ctor_neq :
      (applySubst st.subst fuel (.sum sumName1 sumArgs1) ==
        applySubst st.subst fuel (.sum sumName2 sumArgs2)) = false)
    (h_opaque_left :
      applySubst st.subst fuel (.opaque opaqueName1 opaqueParams1) =
        .opaque opaqueName1' opaqueParams1')
    (h_opaque_right :
      applySubst st.subst fuel (.opaque opaqueName2 opaqueParams2) =
        .opaque opaqueName2' opaqueParams2')
    (h_opaque_ctor_neq :
      (applySubst st.subst fuel (.opaque opaqueName1 opaqueParams1) ==
        applySubst st.subst fuel (.opaque opaqueName2 opaqueParams2)) = false) :
    (unify st (fuel + 1) (.sum sumName1 sumArgs1) (.sum sumName2 sumArgs2) =
      (if sumName1' == sumName2' then unifyTyList st fuel sumArgs1' sumArgs2' else .err "type mismatch"))
    ∧
    (unify st (fuel + 1) (.opaque opaqueName1 opaqueParams1) (.opaque opaqueName2 opaqueParams2) =
      (if opaqueName1' == opaqueName2' then
        unifyTyList st fuel opaqueParams1' opaqueParams2' else .err "type mismatch")) := by
  refine ⟨?_, ?_⟩
  · exact sum_unify_branch_decision_of_normalized
      st fuel sumName1 sumName2 sumName1' sumName2' sumArgs1 sumArgs2 sumArgs1' sumArgs2'
      h_sum_left h_sum_right h_sum_ctor_neq
  · exact opaque_unify_branch_decision_of_normalized
      st fuel
      opaqueName1 opaqueName2 opaqueName1' opaqueName2'
      opaqueParams1 opaqueParams2 opaqueParams1' opaqueParams2'
      h_opaque_left h_opaque_right h_opaque_ctor_neq

/-- On normalized opaque forms, failed constructor BEq short-circuit and equal
    nominal names reduce unification to parameter-list unification. -/
theorem opaque_unify_reduces_to_params_of_normalized
    (st : UnifyState) (fuel : Nat)
    (name1 name2 name1' name2' : String) (params1 params2 params1' params2' : TyList)
    (hleft :
      applySubst st.subst fuel (.opaque name1 params1) =
        .opaque name1' params1')
    (hright :
      applySubst st.subst fuel (.opaque name2 params2) =
        .opaque name2' params2')
    (h_ctor_neq :
      (applySubst st.subst fuel (.opaque name1 params1) ==
        applySubst st.subst fuel (.opaque name2 params2)) = false)
    (h_name : (name1' == name2') = true) :
    unify st (fuel + 1) (.opaque name1 params1) (.opaque name2 params2) =
      unifyTyList st fuel params1' params2' := by
  rw [opaque_unify_branch_decision_of_normalized st fuel name1 name2 name1' name2' params1 params2 params1' params2'
        hleft hright h_ctor_neq]
  simp [h_name]

/-- If the normalized opaque-parameter branch succeeds, the outer normalized
    opaque unifier succeeds with the same resulting state. -/
theorem opaque_unify_accepts_of_normalized_params_ok
    (st st' : UnifyState) (fuel : Nat)
    (name1 name2 name1' name2' : String) (params1 params2 params1' params2' : TyList)
    (hleft :
      applySubst st.subst fuel (.opaque name1 params1) =
        .opaque name1' params1')
    (hright :
      applySubst st.subst fuel (.opaque name2 params2) =
        .opaque name2' params2')
    (h_ctor_neq :
      (applySubst st.subst fuel (.opaque name1 params1) ==
        applySubst st.subst fuel (.opaque name2 params2)) = false)
    (h_name : (name1' == name2') = true)
    (h_params : unifyTyList st fuel params1' params2' = .ok st') :
    unify st (fuel + 1) (.opaque name1 params1) (.opaque name2 params2) = .ok st' := by
  rw [opaque_unify_reduces_to_params_of_normalized st fuel name1 name2 name1' name2' params1 params2 params1' params2'
        hleft hright h_ctor_neq h_name]
  exact h_params

/-- If the normalized opaque-parameter branch rejects with arity mismatch, the
    outer normalized opaque unifier rejects with the same error. -/
theorem opaque_unify_rejects_params_err_of_normalized
    (st : UnifyState) (fuel : Nat)
    (name1 name2 name1' name2' : String) (params1 params2 params1' params2' : TyList)
    (hleft :
      applySubst st.subst fuel (.opaque name1 params1) =
        .opaque name1' params1')
    (hright :
      applySubst st.subst fuel (.opaque name2 params2) =
        .opaque name2' params2')
    (h_ctor_neq :
      (applySubst st.subst fuel (.opaque name1 params1) ==
        applySubst st.subst fuel (.opaque name2 params2)) = false)
    (h_name : (name1' == name2') = true)
    (e : String)
    (h_params : unifyTyList st fuel params1' params2' = .err e) :
    unify st (fuel + 1) (.opaque name1 params1) (.opaque name2 params2) =
      .err e := by
  rw [opaque_unify_reduces_to_params_of_normalized st fuel name1 name2 name1' name2' params1 params2 params1' params2'
        hleft hright h_ctor_neq h_name]
  exact h_params

/-- If the normalized opaque-parameter branch rejects with arity mismatch, the
    outer normalized opaque unifier rejects with the same error. -/
theorem opaque_unify_rejects_arity_mismatch_of_normalized
    (st : UnifyState) (fuel : Nat)
    (name1 name2 name1' name2' : String) (params1 params2 params1' params2' : TyList)
    (hleft :
      applySubst st.subst fuel (.opaque name1 params1) =
        .opaque name1' params1')
    (hright :
      applySubst st.subst fuel (.opaque name2 params2) =
        .opaque name2' params2')
    (h_ctor_neq :
      (applySubst st.subst fuel (.opaque name1 params1) ==
        applySubst st.subst fuel (.opaque name2 params2)) = false)
    (h_name : (name1' == name2') = true)
    (h_params : unifyTyList st fuel params1' params2' = .err "type list length mismatch") :
    unify st (fuel + 1) (.opaque name1 params1) (.opaque name2 params2) =
      .err "type list length mismatch" := by
  exact opaque_unify_rejects_params_err_of_normalized st fuel
    name1 name2 name1' name2' params1 params2 params1' params2'
    hleft hright h_ctor_neq h_name
    "type list length mismatch" h_params

/-- On normalized opaque forms, failed constructor BEq short-circuit and
    distinct nominal names force mismatch. -/
theorem opaque_unify_rejects_of_normalized
    (st : UnifyState) (fuel : Nat)
    (name1 name2 name1' name2' : String) (params1 params2 params1' params2' : TyList)
    (hleft :
      applySubst st.subst fuel (.opaque name1 params1) =
        .opaque name1' params1')
    (hright :
      applySubst st.subst fuel (.opaque name2 params2) =
        .opaque name2' params2')
    (h_ctor_neq :
      (applySubst st.subst fuel (.opaque name1 params1) ==
        applySubst st.subst fuel (.opaque name2 params2)) = false)
    (h_name : (name1' == name2') = false) :
    unify st (fuel + 1) (.opaque name1 params1) (.opaque name2 params2) =
      .err "type mismatch" := by
  have h_ctor_neq' :
      (Ty.opaque name1' params1' == Ty.opaque name2' params2') = false := by
    simpa [hleft, hright] using h_ctor_neq
  simp [unify, applySubstCompat, hleft, hright, h_ctor_neq', h_name]

/-- Normalized `Sum` unification rejects immediately on normalized nominal-name
    inequality (constructor-BEq guard failure is derivable from the name
    inequality). -/
theorem sum_unify_rejects_of_normalized_name_ne
    (st : UnifyState) (fuel : Nat)
    (name1 name2 name1' name2' : String) (args1 args2 args1' args2' : TyList)
    (hleft :
      applySubst st.subst fuel (.sum name1 args1) =
        .sum name1' args1')
    (hright :
      applySubst st.subst fuel (.sum name2 args2) =
        .sum name2' args2')
    (h_name : (name1' == name2') = false) :
    unify st (fuel + 1) (.sum name1 args1) (.sum name2 args2) =
      .err "type mismatch" := by
  have h_ctor_neq :
      (applySubst st.subst fuel (.sum name1 args1) ==
        applySubst st.subst fuel (.sum name2 args2)) = false := by
    rw [hleft, hright]
    show beqTy (Ty.sum name1' args1') (Ty.sum name2' args2') = false
    simp [beqTy, h_name]
  exact sum_unify_rejects_of_normalized st fuel
    name1 name2 name1' name2' args1 args2 args1' args2'
    hleft hright h_ctor_neq h_name

/-- Normalized `Opaque` unification rejects immediately on normalized
    nominal-name inequality (constructor-BEq guard failure is derivable from
    the name inequality). -/
theorem opaque_unify_rejects_of_normalized_name_ne
    (st : UnifyState) (fuel : Nat)
    (name1 name2 name1' name2' : String) (params1 params2 params1' params2' : TyList)
    (hleft :
      applySubst st.subst fuel (.opaque name1 params1) =
        .opaque name1' params1')
    (hright :
      applySubst st.subst fuel (.opaque name2 params2) =
        .opaque name2' params2')
    (h_name : (name1' == name2') = false) :
    unify st (fuel + 1) (.opaque name1 params1) (.opaque name2 params2) =
      .err "type mismatch" := by
  have h_ctor_neq :
      (applySubst st.subst fuel (.opaque name1 params1) ==
        applySubst st.subst fuel (.opaque name2 params2)) = false := by
    rw [hleft, hright]
    show beqTy (Ty.opaque name1' params1') (Ty.opaque name2' params2') = false
    simp [beqTy, h_name]
  exact opaque_unify_rejects_of_normalized st fuel
    name1 name2 name1' name2' params1 params2 params1' params2'
    hleft hright h_ctor_neq h_name

/-- Packaged normalized nominal-name inequality rejection across both nominal
    ADT constructors (`Sum`/`Opaque`). -/
theorem nominal_adt_unify_rejects_of_normalized_name_ne_slice
    (st : UnifyState) (fuel : Nat)
    (sumName1 sumName2 sumName1' sumName2' : String)
    (args1 args2 args1' args2' : TyList)
    (opaqueName1 opaqueName2 opaqueName1' opaqueName2' : String)
    (params1 params2 params1' params2' : TyList)
    (h_sum_left :
      applySubst st.subst fuel (.sum sumName1 args1) =
        .sum sumName1' args1')
    (h_sum_right :
      applySubst st.subst fuel (.sum sumName2 args2) =
        .sum sumName2' args2')
    (h_sum_name_ne : (sumName1' == sumName2') = false)
    (h_opaque_left :
      applySubst st.subst fuel (.opaque opaqueName1 params1) =
        .opaque opaqueName1' params1')
    (h_opaque_right :
      applySubst st.subst fuel (.opaque opaqueName2 params2) =
        .opaque opaqueName2' params2')
    (h_opaque_name_ne : (opaqueName1' == opaqueName2') = false) :
    unify st (fuel + 1) (.sum sumName1 args1) (.sum sumName2 args2) =
      .err "type mismatch"
    ∧
    unify st (fuel + 1) (.opaque opaqueName1 params1) (.opaque opaqueName2 params2) =
      .err "type mismatch" := by
  refine ⟨?_, ?_⟩
  · exact sum_unify_rejects_of_normalized_name_ne st fuel
      sumName1 sumName2 sumName1' sumName2' args1 args2 args1' args2'
      h_sum_left h_sum_right h_sum_name_ne
  · exact opaque_unify_rejects_of_normalized_name_ne st fuel
      opaqueName1 opaqueName2 opaqueName1' opaqueName2' params1 params2 params1' params2'
      h_opaque_left h_opaque_right h_opaque_name_ne

/-- At any outer successor+1 fuel, normalized sum-argument-list errors
    propagate through sum unification unchanged when nominal names match. -/
theorem sum_args_error_propagates_any_fuel
    (st : UnifyState) (fuel : Nat)
    (name1 name2 : String) (args1 args2 : TyList)
    (e : String)
    (hbeq :
      (Ty.sum name1 (applySubstTyList st.subst fuel args1) ==
        Ty.sum name2 (applySubstTyList st.subst fuel args2)) = false)
    (h_name : (name1 == name2) = true)
    (h_args :
      unifyTyList st (fuel + 1)
        (applySubstTyList st.subst fuel args1)
        (applySubstTyList st.subst fuel args2) = .err e) :
    unify st (fuel + 2) (.sum name1 args1) (.sum name2 args2) = .err e := by
  have hleft :
      applySubst st.subst (fuel + 1) (.sum name1 args1) =
        .sum name1 (applySubstTyList st.subst fuel args1) := by
    simp [applySubst]
  have hright :
      applySubst st.subst (fuel + 1) (.sum name2 args2) =
        .sum name2 (applySubstTyList st.subst fuel args2) := by
    simp [applySubst]
  have h_ctor_neq :
      (applySubst st.subst (fuel + 1) (.sum name1 args1) ==
        applySubst st.subst (fuel + 1) (.sum name2 args2)) = false := by
    simpa [hleft, hright] using hbeq
  exact sum_unify_rejects_args_err_of_normalized st (fuel + 1)
    name1 name2 name1 name2
    args1 args2
    (applySubstTyList st.subst fuel args1)
    (applySubstTyList st.subst fuel args2)
    hleft hright h_ctor_neq h_name e h_args

/-- At any outer successor+1 fuel, normalized sum-argument-list success
    propagates through sum unification with the same resulting state when
    nominal names match. -/
theorem sum_args_success_propagates_any_fuel
    (st st' : UnifyState) (fuel : Nat)
    (name1 name2 : String) (args1 args2 : TyList)
    (hbeq :
      (Ty.sum name1 (applySubstTyList st.subst fuel args1) ==
        Ty.sum name2 (applySubstTyList st.subst fuel args2)) = false)
    (h_name : (name1 == name2) = true)
    (h_args :
      unifyTyList st (fuel + 1)
        (applySubstTyList st.subst fuel args1)
        (applySubstTyList st.subst fuel args2) = .ok st') :
    unify st (fuel + 2) (.sum name1 args1) (.sum name2 args2) = .ok st' := by
  have hleft :
      applySubst st.subst (fuel + 1) (.sum name1 args1) =
        .sum name1 (applySubstTyList st.subst fuel args1) := by
    simp [applySubst]
  have hright :
      applySubst st.subst (fuel + 1) (.sum name2 args2) =
        .sum name2 (applySubstTyList st.subst fuel args2) := by
    simp [applySubst]
  have h_ctor_neq :
      (applySubst st.subst (fuel + 1) (.sum name1 args1) ==
        applySubst st.subst (fuel + 1) (.sum name2 args2)) = false := by
    simpa [hleft, hright] using hbeq
  exact sum_unify_accepts_of_normalized_args_ok st st' (fuel + 1)
    name1 name2 name1 name2
    args1 args2
    (applySubstTyList st.subst fuel args1)
    (applySubstTyList st.subst fuel args2)
    hleft hright h_ctor_neq h_name h_args

/-- At any outer successor+1 fuel, normalized sum-argument-list arity mismatch
    propagates through sum unification when nominal names match. -/
theorem sum_args_arity_mismatch_propagates_any_fuel
    (st : UnifyState) (fuel : Nat)
    (name1 name2 : String) (args1 args2 : TyList)
    (hbeq :
      (Ty.sum name1 (applySubstTyList st.subst fuel args1) ==
        Ty.sum name2 (applySubstTyList st.subst fuel args2)) = false)
    (h_name : (name1 == name2) = true)
    (h_args :
      unifyTyList st (fuel + 1)
        (applySubstTyList st.subst fuel args1)
        (applySubstTyList st.subst fuel args2) = .err "type list length mismatch") :
    unify st (fuel + 2) (.sum name1 args1) (.sum name2 args2) =
      .err "type list length mismatch" := by
  exact sum_args_error_propagates_any_fuel st fuel
    name1 name2 args1 args2
    "type list length mismatch"
    hbeq h_name h_args

/-- At any outer successor+1 fuel, normalized opaque-parameter-list errors
    propagate through opaque unification unchanged when nominal names match. -/
theorem opaque_params_error_propagates_any_fuel
    (st : UnifyState) (fuel : Nat)
    (name1 name2 : String) (params1 params2 : TyList)
    (e : String)
    (hbeq :
      (Ty.opaque name1 (applySubstTyList st.subst fuel params1) ==
        Ty.opaque name2 (applySubstTyList st.subst fuel params2)) = false)
    (h_name : (name1 == name2) = true)
    (h_params :
      unifyTyList st (fuel + 1)
        (applySubstTyList st.subst fuel params1)
        (applySubstTyList st.subst fuel params2) = .err e) :
    unify st (fuel + 2) (.opaque name1 params1) (.opaque name2 params2) = .err e := by
  have hleft :
      applySubst st.subst (fuel + 1) (.opaque name1 params1) =
        .opaque name1 (applySubstTyList st.subst fuel params1) := by
    simp [applySubst]
  have hright :
      applySubst st.subst (fuel + 1) (.opaque name2 params2) =
        .opaque name2 (applySubstTyList st.subst fuel params2) := by
    simp [applySubst]
  have h_ctor_neq :
      (applySubst st.subst (fuel + 1) (.opaque name1 params1) ==
        applySubst st.subst (fuel + 1) (.opaque name2 params2)) = false := by
    simpa [hleft, hright] using hbeq
  exact opaque_unify_rejects_params_err_of_normalized st (fuel + 1)
    name1 name2 name1 name2
    params1 params2
    (applySubstTyList st.subst fuel params1)
    (applySubstTyList st.subst fuel params2)
    hleft hright h_ctor_neq h_name e h_params

/-- At any outer successor+1 fuel, normalized opaque-parameter-list success
    propagates through opaque unification with the same resulting state when
    nominal names match. -/
theorem opaque_params_success_propagates_any_fuel
    (st st' : UnifyState) (fuel : Nat)
    (name1 name2 : String) (params1 params2 : TyList)
    (hbeq :
      (Ty.opaque name1 (applySubstTyList st.subst fuel params1) ==
        Ty.opaque name2 (applySubstTyList st.subst fuel params2)) = false)
    (h_name : (name1 == name2) = true)
    (h_params :
      unifyTyList st (fuel + 1)
        (applySubstTyList st.subst fuel params1)
        (applySubstTyList st.subst fuel params2) = .ok st') :
    unify st (fuel + 2) (.opaque name1 params1) (.opaque name2 params2) = .ok st' := by
  have hleft :
      applySubst st.subst (fuel + 1) (.opaque name1 params1) =
        .opaque name1 (applySubstTyList st.subst fuel params1) := by
    simp [applySubst]
  have hright :
      applySubst st.subst (fuel + 1) (.opaque name2 params2) =
        .opaque name2 (applySubstTyList st.subst fuel params2) := by
    simp [applySubst]
  have h_ctor_neq :
      (applySubst st.subst (fuel + 1) (.opaque name1 params1) ==
        applySubst st.subst (fuel + 1) (.opaque name2 params2)) = false := by
    simpa [hleft, hright] using hbeq
  exact opaque_unify_accepts_of_normalized_params_ok st st' (fuel + 1)
    name1 name2 name1 name2
    params1 params2
    (applySubstTyList st.subst fuel params1)
    (applySubstTyList st.subst fuel params2)
    hleft hright h_ctor_neq h_name h_params

/-- At any outer successor+1 fuel, normalized opaque-parameter-list arity
    mismatch propagates through opaque unification when nominal names match. -/
theorem opaque_params_arity_mismatch_propagates_any_fuel
    (st : UnifyState) (fuel : Nat)
    (name1 name2 : String) (params1 params2 : TyList)
    (hbeq :
      (Ty.opaque name1 (applySubstTyList st.subst fuel params1) ==
        Ty.opaque name2 (applySubstTyList st.subst fuel params2)) = false)
    (h_name : (name1 == name2) = true)
    (h_params :
      unifyTyList st (fuel + 1)
        (applySubstTyList st.subst fuel params1)
        (applySubstTyList st.subst fuel params2) = .err "type list length mismatch") :
    unify st (fuel + 2) (.opaque name1 params1) (.opaque name2 params2) =
      .err "type list length mismatch" := by
  exact opaque_params_error_propagates_any_fuel st fuel
    name1 name2 params1 params2
    "type list length mismatch"
    hbeq h_name h_params

/-- `Sum` unifies with itself. -/
theorem sum_unifies_with_self
    (st : UnifyState) (fuel : Nat) (name : String) (args : TyList) :
    unify st (fuel + 1) (.sum name args) (.sum name args) = .ok st := by
  simpa using (unifyReflexive' st fuel (.sum name args))

/-- `Opaque` unifies with itself. -/
theorem opaque_unifies_with_self
    (st : UnifyState) (fuel : Nat) (name : String) (params : TyList) :
    unify st (fuel + 1) (.opaque name params) (.opaque name params) = .ok st := by
  simpa using (unifyReflexive' st fuel (.opaque name params))

/-- Packaged nominal-ADT reflexive-unification slice across `Sum` and `Opaque`. -/
theorem nominal_adt_unifies_with_self_slice
    (st : UnifyState) (fuel : Nat)
    (sumName opaqueName : String) (args params : TyList) :
    unify st (fuel + 1) (.sum sumName args) (.sum sumName args) = .ok st
    ∧
    unify st (fuel + 1) (.opaque opaqueName params) (.opaque opaqueName params) = .ok st := by
  refine ⟨?_, ?_⟩
  · exact sum_unifies_with_self st fuel sumName args
  · exact opaque_unifies_with_self st fuel opaqueName params

/-- `Sum` constructor names are nominal: mismatched names do not unify. -/
theorem sum_name_mismatch
    (st : UnifyState) (n1 n2 : String) (h : n1 = n2 -> False) :
    unify st 1 (.sum n1 .nil) (.sum n2 .nil) = .err "type mismatch" := by
  have h_name : (n1 == n2) = false := string_beq_false_of_ne h
  have h_neq : ((Ty.sum n1 .nil) == (Ty.sum n2 .nil)) = false := by
    show beqTy (Ty.sum n1 .nil) (Ty.sum n2 .nil) = false
    simp [beqTy, h_name]
  unfold unify
  simp [applySubstCompat, applySubst, h_neq, h_name]

/-- `Sum` nominal name mismatch rejects at any successor fuel. -/
theorem sum_name_mismatch_any_fuel
    (st : UnifyState) (fuel : Nat) (n1 n2 : String) (h : n1 = n2 -> False) :
    unify st (fuel + 1) (.sum n1 .nil) (.sum n2 .nil) = .err "type mismatch" := by
  have h_name : (n1 == n2) = false := string_beq_false_of_ne h
  have h_neq : ((Ty.sum n1 .nil) == (Ty.sum n2 .nil)) = false := by
    show beqTy (Ty.sum n1 .nil) (Ty.sum n2 .nil) = false
    simp [beqTy, h_name]
  have h_left : applySubst st.subst fuel (.sum n1 .nil) = .sum n1 .nil := by
    cases fuel with
    | zero => rfl
    | succ n => simp [applySubst, applySubstTyList_nil st.subst n]
  have h_right : applySubst st.subst fuel (.sum n2 .nil) = .sum n2 .nil := by
    cases fuel with
    | zero => rfl
    | succ n => simp [applySubst, applySubstTyList_nil st.subst n]
  unfold unify
  simp [applySubstCompat, h_left, h_right, h_neq, h_name]

/-- `Sum` nominal name mismatch rejects at any successor fuel for arbitrary
    argument lists. -/
theorem sum_name_mismatch_any_args_any_fuel
    (st : UnifyState) (fuel : Nat) (n1 n2 : String) (args1 args2 : TyList)
    (h : n1 = n2 -> False) :
    unify st (fuel + 1) (.sum n1 args1) (.sum n2 args2) = .err "type mismatch" := by
  have h_name : (n1 == n2) = false := string_beq_false_of_ne h
  cases fuel with
  | zero =>
    have hleft : applySubst st.subst 0 (.sum n1 args1) = .sum n1 args1 := rfl
    have hright : applySubst st.subst 0 (.sum n2 args2) = .sum n2 args2 := rfl
    have h_ctor_neq :
        (applySubst st.subst 0 (.sum n1 args1) ==
          applySubst st.subst 0 (.sum n2 args2)) = false := by
      show beqTy (Ty.sum n1 args1) (Ty.sum n2 args2) = false
      simp [beqTy, h_name]
    exact sum_unify_rejects_of_normalized st 0 n1 n2 n1 n2 args1 args2 args1 args2
      hleft hright h_ctor_neq h_name
  | succ n =>
    have hleft :
        applySubst st.subst (n + 1) (.sum n1 args1) =
          .sum n1 (applySubstTyList st.subst n args1) := by
      simp [applySubst]
    have hright :
        applySubst st.subst (n + 1) (.sum n2 args2) =
          .sum n2 (applySubstTyList st.subst n args2) := by
      simp [applySubst]
    have h_ctor_neq :
        (applySubst st.subst (n + 1) (.sum n1 args1) ==
          applySubst st.subst (n + 1) (.sum n2 args2)) = false := by
      show
        beqTy (Ty.sum n1 (applySubstTyList st.subst n args1))
          (Ty.sum n2 (applySubstTyList st.subst n args2)) = false
      simp [beqTy, h_name]
    exact sum_unify_rejects_of_normalized st (n + 1) n1 n2 n1 n2 args1 args2
      (applySubstTyList st.subst n args1) (applySubstTyList st.subst n args2)
      hleft hright h_ctor_neq h_name

/-- `Opaque` constructor names are nominal: mismatched names do not unify. -/
theorem opaque_name_mismatch
    (st : UnifyState) (n1 n2 : String) (h : n1 = n2 -> False) :
    unify st 1 (.opaque n1 .nil) (.opaque n2 .nil) = .err "type mismatch" := by
  have h_name : (n1 == n2) = false := string_beq_false_of_ne h
  have h_neq : ((Ty.opaque n1 .nil) == (Ty.opaque n2 .nil)) = false := by
    show beqTy (Ty.opaque n1 .nil) (Ty.opaque n2 .nil) = false
    simp [beqTy, h_name]
  unfold unify
  simp [applySubstCompat, applySubst, h_neq, h_name]

/-- `Opaque` nominal name mismatch rejects at any successor fuel. -/
theorem opaque_name_mismatch_any_fuel
    (st : UnifyState) (fuel : Nat) (n1 n2 : String) (h : n1 = n2 -> False) :
    unify st (fuel + 1) (.opaque n1 .nil) (.opaque n2 .nil) = .err "type mismatch" := by
  have h_name : (n1 == n2) = false := string_beq_false_of_ne h
  have h_neq : ((Ty.opaque n1 .nil) == (Ty.opaque n2 .nil)) = false := by
    show beqTy (Ty.opaque n1 .nil) (Ty.opaque n2 .nil) = false
    simp [beqTy, h_name]
  have h_left : applySubst st.subst fuel (.opaque n1 .nil) = .opaque n1 .nil := by
    cases fuel with
    | zero => rfl
    | succ n => simp [applySubst, applySubstTyList_nil st.subst n]
  have h_right : applySubst st.subst fuel (.opaque n2 .nil) = .opaque n2 .nil := by
    cases fuel with
    | zero => rfl
    | succ n => simp [applySubst, applySubstTyList_nil st.subst n]
  unfold unify
  simp [applySubstCompat, h_left, h_right, h_neq, h_name]

/-- `Opaque` nominal name mismatch rejects at any successor fuel for arbitrary
    parameter lists. -/
theorem opaque_name_mismatch_any_params_any_fuel
    (st : UnifyState) (fuel : Nat) (n1 n2 : String) (params1 params2 : TyList)
    (h : n1 = n2 -> False) :
    unify st (fuel + 1) (.opaque n1 params1) (.opaque n2 params2) = .err "type mismatch" := by
  have h_name : (n1 == n2) = false := string_beq_false_of_ne h
  cases fuel with
  | zero =>
    have hleft : applySubst st.subst 0 (.opaque n1 params1) = .opaque n1 params1 := rfl
    have hright : applySubst st.subst 0 (.opaque n2 params2) = .opaque n2 params2 := rfl
    have h_ctor_neq :
        (applySubst st.subst 0 (.opaque n1 params1) ==
          applySubst st.subst 0 (.opaque n2 params2)) = false := by
      show beqTy (Ty.opaque n1 params1) (Ty.opaque n2 params2) = false
      simp [beqTy, h_name]
    exact opaque_unify_rejects_of_normalized st 0 n1 n2 n1 n2 params1 params2 params1 params2
      hleft hright h_ctor_neq h_name
  | succ n =>
    have hleft :
        applySubst st.subst (n + 1) (.opaque n1 params1) =
          .opaque n1 (applySubstTyList st.subst n params1) := by
      simp [applySubst]
    have hright :
        applySubst st.subst (n + 1) (.opaque n2 params2) =
          .opaque n2 (applySubstTyList st.subst n params2) := by
      simp [applySubst]
    have h_ctor_neq :
        (applySubst st.subst (n + 1) (.opaque n1 params1) ==
          applySubst st.subst (n + 1) (.opaque n2 params2)) = false := by
      show
        beqTy (Ty.opaque n1 (applySubstTyList st.subst n params1))
          (Ty.opaque n2 (applySubstTyList st.subst n params2)) = false
      simp [beqTy, h_name]
    exact opaque_unify_rejects_of_normalized st (n + 1) n1 n2 n1 n2 params1 params2
      (applySubstTyList st.subst n params1) (applySubstTyList st.subst n params2)
      hleft hright h_ctor_neq h_name

/-- `Sum` argument arity is structural: mismatched arity does not unify. -/
theorem sum_arity_mismatch
    (st : UnifyState) (name : String) :
    unify st 2 (.sum name (.cons .int .nil)) (.sum name .nil) =
      .err "type list length mismatch" := by
  have h_neq :
      ((Ty.sum name (.cons .int .nil)) == (Ty.sum name .nil)) = false := by
    simp [BEq.beq, beqTy, beqTyList]
  unfold unify
  simp [applySubstCompat, applySubst, applySubstTyList, h_neq, unifyTyList]

/-- `Sum` argument arity mismatch rejects at any successor+1 fuel. -/
theorem sum_arity_mismatch_any_fuel
    (st : UnifyState) (fuel : Nat) (name : String) :
    unify st (fuel + 2) (.sum name (.cons .int .nil)) (.sum name .nil) =
      .err "type list length mismatch" := by
  have h_neq : ((Ty.sum name (.cons .int .nil)) == (Ty.sum name .nil)) = false := by
    simp [BEq.beq, beqTy, beqTyList]
  have h_args_left : applySubstTyList st.subst fuel (.cons .int .nil) = (.cons .int .nil) := by
    exact applySubstTyList_int_singleton st.subst fuel
  have h_args_right : applySubstTyList st.subst fuel .nil = .nil := by
    exact applySubstTyList_nil st.subst fuel
  unfold unify
  simp [applySubstCompat, applySubst, h_args_left, h_args_right, h_neq, unifyTyList]

/-- `Sum` argument arity mismatch rejects at any successor+1 fuel for arbitrary
    non-empty argument lists vs empty. -/
theorem sum_arity_mismatch_any_nonempty_args_any_fuel
    (st : UnifyState) (fuel : Nat) (name : String) (arg : Ty) (argsTail : TyList) :
    unify st (fuel + 2) (.sum name (.cons arg argsTail)) (.sum name .nil) =
      .err "type list length mismatch" := by
  have h_neq_zero :
      ((Ty.sum name (.cons arg argsTail)) == (Ty.sum name .nil)) = false := by
    simp [BEq.beq, beqTy, beqTyList]
  unfold unify
  cases fuel with
  | zero =>
    simp [applySubstCompat, applySubst, applySubstTyList, h_neq_zero, unifyTyList]
  | succ n =>
    have h_neq_succ :
        ((Ty.sum name (.cons (applySubst st.subst n arg) (applySubstTyList st.subst n argsTail)) ==
          Ty.sum name .nil)) = false := by
      simp [BEq.beq, beqTy, beqTyList]
    simp [applySubstCompat, applySubst, applySubstTyList, h_neq_succ, unifyTyList]

/-- `Sum` argument arity mismatch rejects at any successor+1 fuel for
    empty vs arbitrary non-empty argument lists. -/
theorem sum_arity_mismatch_empty_vs_nonempty_any_fuel
    (st : UnifyState) (fuel : Nat) (name : String) (arg : Ty) (argsTail : TyList) :
    unify st (fuel + 2) (.sum name .nil) (.sum name (.cons arg argsTail)) =
      .err "type list length mismatch" := by
  have h_neq_zero :
      ((Ty.sum name .nil) == (Ty.sum name (.cons arg argsTail))) = false := by
    simp [BEq.beq, beqTy, beqTyList]
  unfold unify
  cases fuel with
  | zero =>
    simp [applySubstCompat, applySubst, applySubstTyList, h_neq_zero, unifyTyList]
  | succ n =>
    have h_neq_succ :
        ((Ty.sum name .nil ==
          Ty.sum name (.cons (applySubst st.subst n arg) (applySubstTyList st.subst n argsTail)))) = false := by
      simp [BEq.beq, beqTy, beqTyList]
    simp [applySubstCompat, applySubst, applySubstTyList, h_neq_succ, unifyTyList]

/-- `Opaque` parameter arity is structural: mismatched arity does not unify. -/
theorem opaque_arity_mismatch
    (st : UnifyState) (name : String) :
    unify st 2 (.opaque name (.cons .int .nil)) (.opaque name .nil) =
      .err "type list length mismatch" := by
  have h_neq :
      ((Ty.opaque name (.cons .int .nil)) == (Ty.opaque name .nil)) = false := by
    simp [BEq.beq, beqTy, beqTyList]
  unfold unify
  simp [applySubstCompat, applySubst, applySubstTyList, h_neq, unifyTyList]

/-- `Opaque` parameter arity mismatch rejects at any successor+1 fuel. -/
theorem opaque_arity_mismatch_any_fuel
    (st : UnifyState) (fuel : Nat) (name : String) :
    unify st (fuel + 2) (.opaque name (.cons .int .nil)) (.opaque name .nil) =
      .err "type list length mismatch" := by
  have h_neq : ((Ty.opaque name (.cons .int .nil)) == (Ty.opaque name .nil)) = false := by
    simp [BEq.beq, beqTy, beqTyList]
  have h_params_left : applySubstTyList st.subst fuel (.cons .int .nil) = (.cons .int .nil) := by
    exact applySubstTyList_int_singleton st.subst fuel
  have h_params_right : applySubstTyList st.subst fuel .nil = .nil := by
    exact applySubstTyList_nil st.subst fuel
  unfold unify
  simp [applySubstCompat, applySubst, h_params_left, h_params_right, h_neq, unifyTyList]

/-- `Opaque` parameter arity mismatch rejects at any successor+1 fuel for
    arbitrary non-empty parameter lists vs empty. -/
theorem opaque_arity_mismatch_any_nonempty_params_any_fuel
    (st : UnifyState) (fuel : Nat) (name : String) (param : Ty) (paramsTail : TyList) :
    unify st (fuel + 2) (.opaque name (.cons param paramsTail)) (.opaque name .nil) =
      .err "type list length mismatch" := by
  have h_neq_zero :
      ((Ty.opaque name (.cons param paramsTail)) == (Ty.opaque name .nil)) = false := by
    simp [BEq.beq, beqTy, beqTyList]
  unfold unify
  cases fuel with
  | zero =>
    simp [applySubstCompat, applySubst, applySubstTyList, h_neq_zero, unifyTyList]
  | succ n =>
    have h_neq_succ :
        ((Ty.opaque name (.cons (applySubst st.subst n param) (applySubstTyList st.subst n paramsTail)) ==
          Ty.opaque name .nil)) = false := by
      simp [BEq.beq, beqTy, beqTyList]
    simp [applySubstCompat, applySubst, applySubstTyList, h_neq_succ, unifyTyList]

/-- `Opaque` parameter arity mismatch rejects at any successor+1 fuel for
    empty vs arbitrary non-empty parameter lists. -/
theorem opaque_arity_mismatch_empty_vs_nonempty_any_fuel
    (st : UnifyState) (fuel : Nat) (name : String) (param : Ty) (paramsTail : TyList) :
    unify st (fuel + 2) (.opaque name .nil) (.opaque name (.cons param paramsTail)) =
      .err "type list length mismatch" := by
  have h_neq_zero :
      ((Ty.opaque name .nil) == (Ty.opaque name (.cons param paramsTail))) = false := by
    simp [BEq.beq, beqTy, beqTyList]
  unfold unify
  cases fuel with
  | zero =>
    simp [applySubstCompat, applySubst, applySubstTyList, h_neq_zero, unifyTyList]
  | succ n =>
    have h_neq_succ :
        ((Ty.opaque name .nil ==
          Ty.opaque name (.cons (applySubst st.subst n param) (applySubstTyList st.subst n paramsTail)))) = false := by
      simp [BEq.beq, beqTy, beqTyList]
    simp [applySubstCompat, applySubst, applySubstTyList, h_neq_succ, unifyTyList]

/-- Packaged nominal-name mismatch slice: distinct names reject both `Sum` and
    `Opaque` unification at any successor fuel for arbitrary argument/parameter
    lists. -/
theorem nominal_adt_name_mismatch_slice_any_lists_any_fuel
    (st : UnifyState) (fuel : Nat)
    (n1 n2 : String) (args1 args2 params1 params2 : TyList) (h_name : n1 ≠ n2) :
    unify st (fuel + 1) (.sum n1 args1) (.sum n2 args2) = .err "type mismatch"
    ∧
    unify st (fuel + 1) (.opaque n1 params1) (.opaque n2 params2) = .err "type mismatch" := by
  refine ⟨?_, ?_⟩
  · exact sum_name_mismatch_any_args_any_fuel st fuel n1 n2 args1 args2 h_name
  · exact opaque_name_mismatch_any_params_any_fuel st fuel n1 n2 params1 params2 h_name

/-- Packaged nominal-ADT arity mismatch slice: non-empty/empty and
    empty/non-empty mismatches reject in both `Sum` and `Opaque` constructors
    at any successor+1 fuel. -/
theorem nominal_adt_arity_mismatch_slice_any_fuel
    (st : UnifyState) (fuel : Nat) (name : String)
    (arg : Ty) (argsTail : TyList) (param : Ty) (paramsTail : TyList) :
    unify st (fuel + 2) (.sum name (.cons arg argsTail)) (.sum name .nil) =
      .err "type list length mismatch"
    ∧
    unify st (fuel + 2) (.sum name .nil) (.sum name (.cons arg argsTail)) =
      .err "type list length mismatch"
    ∧
    unify st (fuel + 2) (.opaque name (.cons param paramsTail)) (.opaque name .nil) =
      .err "type list length mismatch"
    ∧
    unify st (fuel + 2) (.opaque name .nil) (.opaque name (.cons param paramsTail)) =
      .err "type list length mismatch" := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact sum_arity_mismatch_any_nonempty_args_any_fuel st fuel name arg argsTail
  · exact sum_arity_mismatch_empty_vs_nonempty_any_fuel st fuel name arg argsTail
  · exact opaque_arity_mismatch_any_nonempty_params_any_fuel st fuel name param paramsTail
  · exact opaque_arity_mismatch_empty_vs_nonempty_any_fuel st fuel name param paramsTail

/-- Packaged nominal mismatch suite combining distinct-name rejection and
    constructor-arity rejection surfaces across `Sum` and `Opaque`. -/
theorem nominal_adt_mismatch_suite_any_fuel
    (st : UnifyState) (fuel : Nat)
    (n1 n2 : String) (args1 args2 params1 params2 : TyList) (h_name : n1 ≠ n2)
    (name : String) (arg : Ty) (argsTail : TyList) (param : Ty) (paramsTail : TyList) :
    (unify st (fuel + 1) (.sum n1 args1) (.sum n2 args2) = .err "type mismatch"
      ∧
      unify st (fuel + 1) (.opaque n1 params1) (.opaque n2 params2) = .err "type mismatch")
    ∧
    (unify st (fuel + 2) (.sum name (.cons arg argsTail)) (.sum name .nil) =
      .err "type list length mismatch"
      ∧
      unify st (fuel + 2) (.sum name .nil) (.sum name (.cons arg argsTail)) =
        .err "type list length mismatch"
      ∧
      unify st (fuel + 2) (.opaque name (.cons param paramsTail)) (.opaque name .nil) =
        .err "type list length mismatch"
      ∧
      unify st (fuel + 2) (.opaque name .nil) (.opaque name (.cons param paramsTail)) =
        .err "type list length mismatch") := by
  refine ⟨?_, ?_⟩
  · exact nominal_adt_name_mismatch_slice_any_lists_any_fuel
      st fuel n1 n2 args1 args2 params1 params2 h_name
  · exact nominal_adt_arity_mismatch_slice_any_fuel
      st fuel name arg argsTail param paramsTail

/-- Boundary-sensitive sites where nominal ADT checks are enforced. -/
inductive NominalAdtBoundarySite : Type where
  | letAnnotation
  | callArgument
  | returnAnnotation
  | ascription

/-- Site-level nominal ADT boundary policy.
    Current scope: nominal name equality is required for `Sum`/`Opaque`
    constructor compatibility; non-nominal actuals are rejected when a nominal
    constructor is expected. -/
def nominalAdtBoundaryAllows (expected actual : Ty) : Bool :=
  match expected, actual with
  | .sum expectedName _, .sum actualName _ => expectedName == actualName
  | .opaque expectedName _, .opaque actualName _ => expectedName == actualName
  | .sum _ _, _ => false
  | .opaque _ _, _ => false
  | _, _ => true

/-- Site-level wrapper for nominal ADT boundary checks. -/
def nominalAdtBoundaryAllowsAtSite
    (_site : NominalAdtBoundarySite) (expected actual : Ty) : Bool :=
  nominalAdtBoundaryAllows expected actual

/-- Nominal ADT boundary policy is currently site-invariant. -/
theorem nominal_adt_boundary_policy_site_invariant
    (site1 site2 : NominalAdtBoundarySite) (expected actual : Ty) :
    nominalAdtBoundaryAllowsAtSite site1 expected actual =
      nominalAdtBoundaryAllowsAtSite site2 expected actual := by
  cases site1 <;> cases site2 <;> rfl

/-- Distinct nominal sum names are rejected by boundary policy. -/
theorem nominal_adt_boundary_rejects_sum_name_mismatch :
    nominalAdtBoundaryAllows
      (.sum "A" .nil)
      (.sum "B" .nil)
      = false := by
  native_decide

/-- Distinct nominal opaque names are rejected by boundary policy. -/
theorem nominal_adt_boundary_rejects_opaque_name_mismatch :
    nominalAdtBoundaryAllows
      (.opaque "UserId" .nil)
      (.opaque "OrderId" .nil)
      = false := by
  native_decide

/-- Non-nominal actuals are rejected when a nominal sum is expected. -/
theorem nominal_adt_boundary_rejects_non_nominal_actual :
    nominalAdtBoundaryAllows
      (.sum "A" .nil)
      .int
      = false := by
  native_decide

/-- Packaged nominal ADT boundary surface slice:
    site invariance + nominal-name rejection and non-nominal rejection, with
    closure to concrete unifier mismatch/reflexive witnesses. -/
theorem nominal_adt_boundary_surface_slice
    (st : UnifyState) (site : NominalAdtBoundarySite) :
    (nominalAdtBoundaryAllowsAtSite site (.sum "A" .nil) (.sum "B" .nil) = false)
    ∧
    (nominalAdtBoundaryAllowsAtSite site (.opaque "UserId" .nil) (.opaque "OrderId" .nil) = false)
    ∧
    (nominalAdtBoundaryAllowsAtSite site (.sum "A" .nil) .int = false)
    ∧
    (unify st 1 (.sum "A" .nil) (.sum "B" .nil) = .err "type mismatch")
    ∧
    (unify st 1 (.opaque "UserId" .nil) (.opaque "OrderId" .nil) = .err "type mismatch")
    ∧
    (unify st 2 (.sum "A" (.cons .int .nil)) (.sum "A" (.cons .int .nil)) = .ok st) := by
  have h_sum_name_ne : "A" = "B" → False := by decide
  have h_opaque_name_ne : "UserId" = "OrderId" → False := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases site <;> exact nominal_adt_boundary_rejects_sum_name_mismatch
  · cases site <;> exact nominal_adt_boundary_rejects_opaque_name_mismatch
  · cases site <;> exact nominal_adt_boundary_rejects_non_nominal_actual
  · exact sum_name_mismatch st "A" "B" h_sum_name_ne
  · exact opaque_name_mismatch st "UserId" "OrderId" h_opaque_name_ne
  · exact sum_unifies_with_self st 1 "A" (.cons .int .nil)

/-- `Sum` free vars are exactly its parameter free vars. -/
theorem sum_free_vars (name : String) (args : TyList) :
    freeTypeVars (.sum name args) = freeTypeVarsTyList args /\
      freeRowVars (.sum name args) = freeRowVarsTyList args := by
  simp [freeTypeVars, freeRowVars]

/-- `Opaque` free vars are exactly its parameter free vars. -/
theorem opaque_free_vars (name : String) (params : TyList) :
    freeTypeVars (.opaque name params) = freeTypeVarsTyList params /\
      freeRowVars (.opaque name params) = freeRowVarsTyList params := by
  simp [freeTypeVars, freeRowVars]

/-- Packaged nominal-ADT free-variable slice across `Sum` and `Opaque`. -/
theorem nominal_adt_free_vars_slice
    (sumName opaqueName : String) (args params : TyList) :
    (freeTypeVars (.sum sumName args) = freeTypeVarsTyList args
      ∧ freeRowVars (.sum sumName args) = freeRowVarsTyList args)
    ∧
    (freeTypeVars (.opaque opaqueName params) = freeTypeVarsTyList params
      ∧ freeRowVars (.opaque opaqueName params) = freeRowVarsTyList params) := by
  refine ⟨?_, ?_⟩
  · exact sum_free_vars sumName args
  · exact opaque_free_vars opaqueName params
