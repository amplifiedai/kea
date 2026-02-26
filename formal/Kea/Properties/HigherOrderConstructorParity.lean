/- 
  Kea.Properties.HigherOrderConstructorParity - Constructor-app parity slice.

  Current scope: internal higher-order constructor terms (`app`, `constructor`)
  are modeled in `Ty`, propagated through substitution/unification, and covered
  with constructor-local parity theorems.
-/

import Kea.Properties.UnifyReflexive

private theorem string_beq_false_of_ne {a b : String} (h : a = b → False) : (a == b) = false := by
  cases h_beq : (a == b) with
  | false => rfl
  | true =>
    have hab : a = b := by simpa using h_beq
    exact (h hab).elim

private theorem nat_beq_false_of_ne {a b : Nat} (h : a = b → False) : (a == b) = false := by
  cases h_beq : (a == b) with
  | false => rfl
  | true =>
    have hab : a = b := by simpa using h_beq
    exact (h hab).elim

/-- One substitution step over `app` rewrites both constructor and arguments. -/
theorem app_subst_step (s : Subst) (fuel : Nat) (ctor : Ty) (args : TyList) :
    applySubst s (fuel + 1) (.app ctor args) =
      .app (applySubst s fuel ctor) (applySubstTyList s fuel args) := by
  simp [applySubst]

/-- One substitution step over `constructor` rewrites fixed arguments only. -/
theorem constructor_subst_step
    (s : Subst) (fuel : Nat) (name : String) (fixedArgs : TyList) (arity : Nat) :
    applySubst s (fuel + 1) (.constructor name fixedArgs arity) =
      .constructor name (applySubstTyList s fuel fixedArgs) arity := by
  simp [applySubst]

/-- Packaged constructor-app substitution-step slice across `app` and
    `constructor`. -/
theorem constructor_app_subst_step_slice
    (s : Subst) (fuel : Nat)
    (ctor : Ty) (args : TyList)
    (name : String) (fixedArgs : TyList) (arity : Nat) :
    applySubst s (fuel + 1) (.app ctor args) =
      .app (applySubst s fuel ctor) (applySubstTyList s fuel args)
    ∧
    applySubst s (fuel + 1) (.constructor name fixedArgs arity) =
      .constructor name (applySubstTyList s fuel fixedArgs) arity := by
  refine ⟨?_, ?_⟩
  · exact app_subst_step s fuel ctor args
  · exact constructor_subst_step s fuel name fixedArgs arity

/-- On normalized `app` forms, failed constructor BEq short-circuit reduces
    unification to the app-branch constructor/argument sequence. -/
theorem app_unify_branch_of_normalized
    (st : UnifyState) (fuel : Nat)
    (ctor1 ctor2 ctor1' ctor2' : Ty) (args1 args2 args1' args2' : TyList)
    (hleft :
      applySubst st.subst fuel (.app ctor1 args1) =
        .app ctor1' args1')
    (hright :
      applySubst st.subst fuel (.app ctor2 args2) =
        .app ctor2' args2')
    (h_ctor_neq :
      (applySubst st.subst fuel (.app ctor1 args1) ==
        applySubst st.subst fuel (.app ctor2 args2)) = false) :
    unify st (fuel + 1) (.app ctor1 args1) (.app ctor2 args2) =
      (match unify st fuel ctor1' ctor2' with
        | .ok st' => unifyTyList st' fuel args1' args2'
        | e => e) := by
  have h_ctor_neq' : (Ty.app ctor1' args1' == Ty.app ctor2' args2') = false := by
    simpa [hleft, hright] using h_ctor_neq
  simp [unify, applySubstCompat, hleft, hright, h_ctor_neq']
  rfl

/-- If normalized app unification fails in the constructor sub-branch, the
    outer app unifier returns that same constructor error. -/
theorem app_unify_rejects_ctor_err_of_normalized
    (st : UnifyState) (fuel : Nat)
    (ctor1 ctor2 ctor1' ctor2' : Ty) (args1 args2 args1' args2' : TyList)
    (hleft :
      applySubst st.subst fuel (.app ctor1 args1) =
        .app ctor1' args1')
    (hright :
      applySubst st.subst fuel (.app ctor2 args2) =
        .app ctor2' args2')
    (h_ctor_neq :
      (applySubst st.subst fuel (.app ctor1 args1) ==
        applySubst st.subst fuel (.app ctor2 args2)) = false)
    (e : String)
    (h_ctor : unify st fuel ctor1' ctor2' = .err e) :
    unify st (fuel + 1) (.app ctor1 args1) (.app ctor2 args2) = .err e := by
  rw [app_unify_branch_of_normalized st fuel ctor1 ctor2 ctor1' ctor2' args1 args2 args1' args2'
        hleft hright h_ctor_neq]
  simp [h_ctor]

/-- If normalized app unification succeeds in both constructor and argument
    sub-branches, the outer app unifier succeeds with the argument-branch state. -/
theorem app_unify_accepts_of_normalized_ctor_ok_args_ok
    (st stCtor st' : UnifyState) (fuel : Nat)
    (ctor1 ctor2 ctor1' ctor2' : Ty) (args1 args2 args1' args2' : TyList)
    (hleft :
      applySubst st.subst fuel (.app ctor1 args1) =
        .app ctor1' args1')
    (hright :
      applySubst st.subst fuel (.app ctor2 args2) =
        .app ctor2' args2')
    (h_ctor_neq :
      (applySubst st.subst fuel (.app ctor1 args1) ==
        applySubst st.subst fuel (.app ctor2 args2)) = false)
    (h_ctor : unify st fuel ctor1' ctor2' = .ok stCtor)
    (h_args : unifyTyList stCtor fuel args1' args2' = .ok st') :
    unify st (fuel + 1) (.app ctor1 args1) (.app ctor2 args2) = .ok st' := by
  rw [app_unify_branch_of_normalized st fuel ctor1 ctor2 ctor1' ctor2' args1 args2 args1' args2'
        hleft hright h_ctor_neq]
  simp [h_ctor, h_args]

/-- If normalized app unification succeeds in the constructor sub-branch but
    fails in the argument sub-branch, the outer app unifier returns that
    argument-branch error. -/
theorem app_unify_rejects_args_err_of_normalized_ctor_ok
    (st stCtor : UnifyState) (fuel : Nat)
    (ctor1 ctor2 ctor1' ctor2' : Ty) (args1 args2 args1' args2' : TyList)
    (hleft :
      applySubst st.subst fuel (.app ctor1 args1) =
        .app ctor1' args1')
    (hright :
      applySubst st.subst fuel (.app ctor2 args2) =
        .app ctor2' args2')
    (h_ctor_neq :
      (applySubst st.subst fuel (.app ctor1 args1) ==
        applySubst st.subst fuel (.app ctor2 args2)) = false)
    (h_ctor : unify st fuel ctor1' ctor2' = .ok stCtor)
    (e : String)
    (h_args : unifyTyList stCtor fuel args1' args2' = .err e) :
    unify st (fuel + 1) (.app ctor1 args1) (.app ctor2 args2) = .err e := by
  rw [app_unify_branch_of_normalized st fuel ctor1 ctor2 ctor1' ctor2' args1 args2 args1' args2'
        hleft hright h_ctor_neq]
  simp [h_ctor, h_args]

/-- If normalized app unification succeeds in the constructor sub-branch but
    argument unification rejects with arity mismatch, the outer app unifier
    rejects with the same arity-mismatch error. -/
theorem app_unify_rejects_args_arity_mismatch_of_normalized_ctor_ok
    (st stCtor : UnifyState) (fuel : Nat)
    (ctor1 ctor2 ctor1' ctor2' : Ty) (args1 args2 args1' args2' : TyList)
    (hleft :
      applySubst st.subst fuel (.app ctor1 args1) =
        .app ctor1' args1')
    (hright :
      applySubst st.subst fuel (.app ctor2 args2) =
        .app ctor2' args2')
    (h_ctor_neq :
      (applySubst st.subst fuel (.app ctor1 args1) ==
        applySubst st.subst fuel (.app ctor2 args2)) = false)
    (h_ctor : unify st fuel ctor1' ctor2' = .ok stCtor)
    (h_args : unifyTyList stCtor fuel args1' args2' = .err "type list length mismatch") :
    unify st (fuel + 1) (.app ctor1 args1) (.app ctor2 args2) =
      .err "type list length mismatch" := by
  exact app_unify_rejects_args_err_of_normalized_ctor_ok st stCtor fuel
    ctor1 ctor2 ctor1' ctor2' args1 args2 args1' args2'
    hleft hright h_ctor_neq h_ctor
    "type list length mismatch" h_args

/-- At any outer successor+1 fuel, normalized constructor-branch errors
    propagate through app unification unchanged. -/
theorem app_ctor_error_propagates_any_fuel
    (st : UnifyState) (fuel : Nat)
    (ctor1 ctor2 : Ty) (args1 args2 : TyList)
    (e : String)
    (hbeq :
      (Ty.app (applySubst st.subst fuel ctor1) (applySubstTyList st.subst fuel args1) ==
        Ty.app (applySubst st.subst fuel ctor2) (applySubstTyList st.subst fuel args2)) = false)
    (h_ctor :
      unify st (fuel + 1)
        (applySubst st.subst fuel ctor1)
        (applySubst st.subst fuel ctor2) = .err e) :
    unify st (fuel + 2) (.app ctor1 args1) (.app ctor2 args2) = .err e := by
  have hleft :
      applySubst st.subst (fuel + 1) (.app ctor1 args1) =
        .app (applySubst st.subst fuel ctor1) (applySubstTyList st.subst fuel args1) := by
    simp [applySubst]
  have hright :
      applySubst st.subst (fuel + 1) (.app ctor2 args2) =
        .app (applySubst st.subst fuel ctor2) (applySubstTyList st.subst fuel args2) := by
    simp [applySubst]
  have h_ctor_neq :
      (applySubst st.subst (fuel + 1) (.app ctor1 args1) ==
        applySubst st.subst (fuel + 1) (.app ctor2 args2)) = false := by
    simpa [hleft, hright] using hbeq
  exact app_unify_rejects_ctor_err_of_normalized st (fuel + 1)
    ctor1 ctor2
    (applySubst st.subst fuel ctor1)
    (applySubst st.subst fuel ctor2)
    args1 args2
    (applySubstTyList st.subst fuel args1)
    (applySubstTyList st.subst fuel args2)
    hleft hright h_ctor_neq e h_ctor

/-- At any outer successor+1 fuel, normalized constructor+argument branch
    success propagates through app unification with the same resulting state. -/
theorem app_ctor_args_success_propagates_any_fuel
    (st stCtor st' : UnifyState) (fuel : Nat)
    (ctor1 ctor2 : Ty) (args1 args2 : TyList)
    (hbeq :
      (Ty.app (applySubst st.subst fuel ctor1) (applySubstTyList st.subst fuel args1) ==
        Ty.app (applySubst st.subst fuel ctor2) (applySubstTyList st.subst fuel args2)) = false)
    (h_ctor :
      unify st (fuel + 1)
        (applySubst st.subst fuel ctor1)
        (applySubst st.subst fuel ctor2) = .ok stCtor)
    (h_args :
      unifyTyList stCtor (fuel + 1)
        (applySubstTyList st.subst fuel args1)
        (applySubstTyList st.subst fuel args2) = .ok st') :
    unify st (fuel + 2) (.app ctor1 args1) (.app ctor2 args2) = .ok st' := by
  have hleft :
      applySubst st.subst (fuel + 1) (.app ctor1 args1) =
        .app (applySubst st.subst fuel ctor1) (applySubstTyList st.subst fuel args1) := by
    simp [applySubst]
  have hright :
      applySubst st.subst (fuel + 1) (.app ctor2 args2) =
        .app (applySubst st.subst fuel ctor2) (applySubstTyList st.subst fuel args2) := by
    simp [applySubst]
  have h_ctor_neq :
      (applySubst st.subst (fuel + 1) (.app ctor1 args1) ==
        applySubst st.subst (fuel + 1) (.app ctor2 args2)) = false := by
    simpa [hleft, hright] using hbeq
  exact app_unify_accepts_of_normalized_ctor_ok_args_ok st stCtor st' (fuel + 1)
    ctor1 ctor2
    (applySubst st.subst fuel ctor1)
    (applySubst st.subst fuel ctor2)
    args1 args2
    (applySubstTyList st.subst fuel args1)
    (applySubstTyList st.subst fuel args2)
    hleft hright h_ctor_neq h_ctor h_args

/-- At any outer successor+1 fuel, normalized argument-branch errors propagate
    through app unification unchanged when the constructor branch succeeds. -/
theorem app_args_error_propagates_any_fuel
    (st stCtor : UnifyState) (fuel : Nat)
    (ctor1 ctor2 : Ty) (args1 args2 : TyList)
    (e : String)
    (hbeq :
      (Ty.app (applySubst st.subst fuel ctor1) (applySubstTyList st.subst fuel args1) ==
        Ty.app (applySubst st.subst fuel ctor2) (applySubstTyList st.subst fuel args2)) = false)
    (h_ctor :
      unify st (fuel + 1)
        (applySubst st.subst fuel ctor1)
        (applySubst st.subst fuel ctor2) = .ok stCtor)
    (h_args :
      unifyTyList stCtor (fuel + 1)
        (applySubstTyList st.subst fuel args1)
        (applySubstTyList st.subst fuel args2) = .err e) :
    unify st (fuel + 2) (.app ctor1 args1) (.app ctor2 args2) = .err e := by
  have hleft :
      applySubst st.subst (fuel + 1) (.app ctor1 args1) =
        .app (applySubst st.subst fuel ctor1) (applySubstTyList st.subst fuel args1) := by
    simp [applySubst]
  have hright :
      applySubst st.subst (fuel + 1) (.app ctor2 args2) =
        .app (applySubst st.subst fuel ctor2) (applySubstTyList st.subst fuel args2) := by
    simp [applySubst]
  have h_ctor_neq :
      (applySubst st.subst (fuel + 1) (.app ctor1 args1) ==
        applySubst st.subst (fuel + 1) (.app ctor2 args2)) = false := by
    simpa [hleft, hright] using hbeq
  exact app_unify_rejects_args_err_of_normalized_ctor_ok st stCtor (fuel + 1)
    ctor1 ctor2
    (applySubst st.subst fuel ctor1)
    (applySubst st.subst fuel ctor2)
    args1 args2
    (applySubstTyList st.subst fuel args1)
    (applySubstTyList st.subst fuel args2)
    hleft hright h_ctor_neq h_ctor e h_args

/-- At any outer successor+1 fuel, normalized argument-branch arity mismatch
    propagates through app unification when the constructor branch succeeds. -/
theorem app_args_arity_mismatch_propagates_any_fuel
    (st stCtor : UnifyState) (fuel : Nat)
    (ctor1 ctor2 : Ty) (args1 args2 : TyList)
    (hbeq :
      (Ty.app (applySubst st.subst fuel ctor1) (applySubstTyList st.subst fuel args1) ==
        Ty.app (applySubst st.subst fuel ctor2) (applySubstTyList st.subst fuel args2)) = false)
    (h_ctor :
      unify st (fuel + 1)
        (applySubst st.subst fuel ctor1)
        (applySubst st.subst fuel ctor2) = .ok stCtor)
    (h_args :
      unifyTyList stCtor (fuel + 1)
        (applySubstTyList st.subst fuel args1)
        (applySubstTyList st.subst fuel args2) = .err "type list length mismatch") :
    unify st (fuel + 2) (.app ctor1 args1) (.app ctor2 args2)
      = .err "type list length mismatch" := by
  exact app_args_error_propagates_any_fuel st stCtor fuel
    ctor1 ctor2 args1 args2
    "type list length mismatch"
    hbeq h_ctor h_args

/-- On normalized `constructor` forms, failed constructor BEq short-circuit and
    matching name/arity reduce unification to fixed-argument unification. -/
theorem constructor_unify_reduces_to_fixed_args_of_normalized
    (st : UnifyState) (fuel : Nat)
    (name1 name2 name1' name2' : String)
    (fixed1 fixed2 fixed1' fixed2' : TyList)
    (arity1 arity2 arity1' arity2' : Nat)
    (hleft :
      applySubst st.subst fuel (.constructor name1 fixed1 arity1) =
        .constructor name1' fixed1' arity1')
    (hright :
      applySubst st.subst fuel (.constructor name2 fixed2 arity2) =
        .constructor name2' fixed2' arity2')
    (h_ctor_neq :
      (applySubst st.subst fuel (.constructor name1 fixed1 arity1) ==
        applySubst st.subst fuel (.constructor name2 fixed2 arity2)) = false)
    (h_guard : name1' = name2' ∧ arity1' = arity2') :
    unify st (fuel + 1) (.constructor name1 fixed1 arity1) (.constructor name2 fixed2 arity2) =
      unifyTyList st fuel fixed1' fixed2' := by
  have h_ctor_neq' :
      (Ty.constructor name1' fixed1' arity1' == Ty.constructor name2' fixed2' arity2') = false := by
    simpa [hleft, hright] using h_ctor_neq
  have h_ctor_neq'' :
      (Ty.constructor name2' fixed1' arity2' == Ty.constructor name2' fixed2' arity2') = false := by
    rcases h_guard with ⟨hname, harity⟩
    simpa [hname, harity] using h_ctor_neq'
  simp [unify, applySubstCompat, hleft, hright, h_guard, h_ctor_neq'']

/-- If the normalized constructor fixed-arg branch succeeds under matching
    name/arity guard, the outer constructor unifier succeeds with the same state. -/
theorem constructor_unify_accepts_of_normalized_fixed_args_ok
    (st st' : UnifyState) (fuel : Nat)
    (name1 name2 name1' name2' : String)
    (fixed1 fixed2 fixed1' fixed2' : TyList)
    (arity1 arity2 arity1' arity2' : Nat)
    (hleft :
      applySubst st.subst fuel (.constructor name1 fixed1 arity1) =
        .constructor name1' fixed1' arity1')
    (hright :
      applySubst st.subst fuel (.constructor name2 fixed2 arity2) =
        .constructor name2' fixed2' arity2')
    (h_ctor_neq :
      (applySubst st.subst fuel (.constructor name1 fixed1 arity1) ==
        applySubst st.subst fuel (.constructor name2 fixed2 arity2)) = false)
    (h_guard : name1' = name2' ∧ arity1' = arity2')
    (h_fixed : unifyTyList st fuel fixed1' fixed2' = .ok st') :
    unify st (fuel + 1) (.constructor name1 fixed1 arity1) (.constructor name2 fixed2 arity2) =
      .ok st' := by
  rw [constructor_unify_reduces_to_fixed_args_of_normalized st fuel
        name1 name2 name1' name2' fixed1 fixed2 fixed1' fixed2'
        arity1 arity2 arity1' arity2' hleft hright h_ctor_neq h_guard]
  exact h_fixed

/-- If the normalized constructor fixed-arg branch rejects under matching
    name/arity guard, the outer constructor unifier returns the same error. -/
theorem constructor_unify_rejects_fixed_args_err_of_normalized
    (st : UnifyState) (fuel : Nat)
    (name1 name2 name1' name2' : String)
    (fixed1 fixed2 fixed1' fixed2' : TyList)
    (arity1 arity2 arity1' arity2' : Nat)
    (hleft :
      applySubst st.subst fuel (.constructor name1 fixed1 arity1) =
        .constructor name1' fixed1' arity1')
    (hright :
      applySubst st.subst fuel (.constructor name2 fixed2 arity2) =
        .constructor name2' fixed2' arity2')
    (h_ctor_neq :
      (applySubst st.subst fuel (.constructor name1 fixed1 arity1) ==
        applySubst st.subst fuel (.constructor name2 fixed2 arity2)) = false)
    (h_guard : name1' = name2' ∧ arity1' = arity2')
    (e : String)
    (h_fixed : unifyTyList st fuel fixed1' fixed2' = .err e) :
    unify st (fuel + 1) (.constructor name1 fixed1 arity1) (.constructor name2 fixed2 arity2) =
      .err e := by
  rw [constructor_unify_reduces_to_fixed_args_of_normalized st fuel
        name1 name2 name1' name2' fixed1 fixed2 fixed1' fixed2'
        arity1 arity2 arity1' arity2' hleft hright h_ctor_neq h_guard]
  exact h_fixed

/-- If the normalized constructor fixed-arg branch rejects with arity mismatch
    under matching name/arity guard, the outer constructor unifier rejects with
    the same arity-mismatch error. -/
theorem constructor_unify_rejects_fixed_args_arity_mismatch_of_normalized
    (st : UnifyState) (fuel : Nat)
    (name1 name2 name1' name2' : String)
    (fixed1 fixed2 fixed1' fixed2' : TyList)
    (arity1 arity2 arity1' arity2' : Nat)
    (hleft :
      applySubst st.subst fuel (.constructor name1 fixed1 arity1) =
        .constructor name1' fixed1' arity1')
    (hright :
      applySubst st.subst fuel (.constructor name2 fixed2 arity2) =
        .constructor name2' fixed2' arity2')
    (h_ctor_neq :
      (applySubst st.subst fuel (.constructor name1 fixed1 arity1) ==
        applySubst st.subst fuel (.constructor name2 fixed2 arity2)) = false)
    (h_guard : name1' = name2' ∧ arity1' = arity2')
    (h_fixed : unifyTyList st fuel fixed1' fixed2' = .err "type list length mismatch") :
    unify st (fuel + 1) (.constructor name1 fixed1 arity1) (.constructor name2 fixed2 arity2) =
      .err "type list length mismatch" := by
  exact constructor_unify_rejects_fixed_args_err_of_normalized st fuel
    name1 name2 name1' name2' fixed1 fixed2 fixed1' fixed2'
    arity1 arity2 arity1' arity2'
    hleft hright h_ctor_neq h_guard
    "type list length mismatch" h_fixed

/-- At any outer successor+1 fuel, normalized fixed-argument errors propagate
    through constructor unification unchanged when name/arity guard matches. -/
theorem constructor_fixed_args_error_propagates_any_fuel
    (st : UnifyState) (fuel : Nat)
    (name1 name2 : String) (fixed1 fixed2 : TyList) (arity1 arity2 : Nat)
    (e : String)
    (hbeq :
      (Ty.constructor name1 (applySubstTyList st.subst fuel fixed1) arity1 ==
        Ty.constructor name2 (applySubstTyList st.subst fuel fixed2) arity2) = false)
    (h_guard : name1 = name2 ∧ arity1 = arity2)
    (h_fixed :
      unifyTyList st (fuel + 1)
        (applySubstTyList st.subst fuel fixed1)
        (applySubstTyList st.subst fuel fixed2) = .err e) :
    unify st (fuel + 2)
      (.constructor name1 fixed1 arity1)
      (.constructor name2 fixed2 arity2)
      = .err e := by
  have hleft :
      applySubst st.subst (fuel + 1) (.constructor name1 fixed1 arity1) =
        .constructor name1 (applySubstTyList st.subst fuel fixed1) arity1 := by
    simp [applySubst]
  have hright :
      applySubst st.subst (fuel + 1) (.constructor name2 fixed2 arity2) =
        .constructor name2 (applySubstTyList st.subst fuel fixed2) arity2 := by
    simp [applySubst]
  have h_ctor_neq :
      (applySubst st.subst (fuel + 1) (.constructor name1 fixed1 arity1) ==
        applySubst st.subst (fuel + 1) (.constructor name2 fixed2 arity2)) = false := by
    simpa [hleft, hright] using hbeq
  exact constructor_unify_rejects_fixed_args_err_of_normalized st (fuel + 1)
    name1 name2 name1 name2
    fixed1 fixed2
    (applySubstTyList st.subst fuel fixed1)
    (applySubstTyList st.subst fuel fixed2)
    arity1 arity2 arity1 arity2
    hleft hright h_ctor_neq h_guard
    e h_fixed

/-- At any outer successor+1 fuel, normalized fixed-argument success propagates
    through constructor unification with the same resulting state when
    name/arity guard matches. -/
theorem constructor_fixed_args_success_propagates_any_fuel
    (st st' : UnifyState) (fuel : Nat)
    (name1 name2 : String) (fixed1 fixed2 : TyList) (arity1 arity2 : Nat)
    (hbeq :
      (Ty.constructor name1 (applySubstTyList st.subst fuel fixed1) arity1 ==
        Ty.constructor name2 (applySubstTyList st.subst fuel fixed2) arity2) = false)
    (h_guard : name1 = name2 ∧ arity1 = arity2)
    (h_fixed :
      unifyTyList st (fuel + 1)
        (applySubstTyList st.subst fuel fixed1)
        (applySubstTyList st.subst fuel fixed2) = .ok st') :
    unify st (fuel + 2)
      (.constructor name1 fixed1 arity1)
      (.constructor name2 fixed2 arity2)
      = .ok st' := by
  have hleft :
      applySubst st.subst (fuel + 1) (.constructor name1 fixed1 arity1) =
        .constructor name1 (applySubstTyList st.subst fuel fixed1) arity1 := by
    simp [applySubst]
  have hright :
      applySubst st.subst (fuel + 1) (.constructor name2 fixed2 arity2) =
        .constructor name2 (applySubstTyList st.subst fuel fixed2) arity2 := by
    simp [applySubst]
  have h_ctor_neq :
      (applySubst st.subst (fuel + 1) (.constructor name1 fixed1 arity1) ==
        applySubst st.subst (fuel + 1) (.constructor name2 fixed2 arity2)) = false := by
    simpa [hleft, hright] using hbeq
  exact constructor_unify_accepts_of_normalized_fixed_args_ok st st' (fuel + 1)
    name1 name2 name1 name2
    fixed1 fixed2
    (applySubstTyList st.subst fuel fixed1)
    (applySubstTyList st.subst fuel fixed2)
    arity1 arity2 arity1 arity2
    hleft hright h_ctor_neq h_guard h_fixed

/-- On normalized `constructor` forms, failed constructor BEq short-circuit and
    mismatched name/arity guard force mismatch. -/
theorem constructor_unify_rejects_of_normalized_guard_false
    (st : UnifyState) (fuel : Nat)
    (name1 name2 name1' name2' : String)
    (fixed1 fixed2 fixed1' fixed2' : TyList)
    (arity1 arity2 arity1' arity2' : Nat)
    (hleft :
      applySubst st.subst fuel (.constructor name1 fixed1 arity1) =
        .constructor name1' fixed1' arity1')
    (hright :
      applySubst st.subst fuel (.constructor name2 fixed2 arity2) =
        .constructor name2' fixed2' arity2')
    (h_ctor_neq :
      (applySubst st.subst fuel (.constructor name1 fixed1 arity1) ==
        applySubst st.subst fuel (.constructor name2 fixed2 arity2)) = false)
    (h_guard : ¬ (name1' = name2' ∧ arity1' = arity2')) :
    unify st (fuel + 1) (.constructor name1 fixed1 arity1) (.constructor name2 fixed2 arity2) =
      .err "type mismatch" := by
  have h_ctor_neq' :
      (Ty.constructor name1' fixed1' arity1' == Ty.constructor name2' fixed2' arity2') = false := by
    simpa [hleft, hright] using h_ctor_neq
  simp [unify, applySubstCompat, hleft, hright, h_ctor_neq', h_guard]

/-- `app` unifies with itself. -/
theorem app_unifies_with_self
    (st : UnifyState) (fuel : Nat) (ctor : Ty) (args : TyList) :
    unify st (fuel + 1) (.app ctor args) (.app ctor args) = .ok st := by
  simpa using (unifyReflexive' st fuel (.app ctor args))

/-- `constructor` unifies with itself. -/
theorem constructor_unifies_with_self
    (st : UnifyState) (fuel : Nat) (name : String) (fixedArgs : TyList) (arity : Nat) :
    unify st (fuel + 1) (.constructor name fixedArgs arity) (.constructor name fixedArgs arity) = .ok st := by
  simpa using (unifyReflexive' st fuel (.constructor name fixedArgs arity))

/-- Packaged constructor-app reflexive-unification slice across `app` and
    `constructor`. -/
theorem constructor_app_unifies_with_self_slice
    (st : UnifyState) (fuel : Nat)
    (ctor : Ty) (args : TyList)
    (name : String) (fixedArgs : TyList) (arity : Nat) :
    unify st (fuel + 1) (.app ctor args) (.app ctor args) = .ok st
    ∧
    unify st (fuel + 1)
      (.constructor name fixedArgs arity)
      (.constructor name fixedArgs arity) = .ok st := by
  refine ⟨?_, ?_⟩
  · exact app_unifies_with_self st fuel ctor args
  · exact constructor_unifies_with_self st fuel name fixedArgs arity

/-- Constructor names are nominal at unification boundaries. -/
theorem constructor_name_mismatch (st : UnifyState) :
    unify st 1
      (.constructor "Foo" (.cons .int .nil) 1)
      (.constructor "Bar" (.cons .int .nil) 1)
      = .err "type mismatch" := by
  have h_neq :
      (Ty.constructor "Foo" (.cons .int .nil) 1 ==
        Ty.constructor "Bar" (.cons .int .nil) 1) = false := by
    native_decide
  simp [unify, applySubstCompat, applySubst, h_neq]

/-- Constructor arity mismatches reject unification. -/
theorem constructor_arity_mismatch (st : UnifyState) :
    unify st 1
      (.constructor "Foo" (.cons .int .nil) 1)
      (.constructor "Foo" (.cons .int .nil) 2)
      = .err "type mismatch" := by
  have h_neq :
      (Ty.constructor "Foo" (.cons .int .nil) 1 ==
        Ty.constructor "Foo" (.cons .int .nil) 2) = false := by
    native_decide
  simp [unify, applySubstCompat, applySubst, h_neq]

/-- Constructor-name mismatch rejects unification at any successor fuel, for
    arbitrary fixed arguments and arities. -/
theorem constructor_name_mismatch_any_fixed_any_fuel
    (st : UnifyState) (fuel : Nat)
    (name1 name2 : String) (fixed1 fixed2 : TyList) (arity1 arity2 : Nat)
    (hname : name1 = name2 → False) :
    unify st (fuel + 1)
      (.constructor name1 fixed1 arity1)
      (.constructor name2 fixed2 arity2)
      = .err "type mismatch" := by
  have h_name_beq : (name1 == name2) = false := string_beq_false_of_ne hname
  have h_guard : ¬ (name1 = name2 ∧ arity1 = arity2) := by
    intro hpair
    exact hname hpair.1
  cases fuel with
  | zero =>
    have hleft :
        applySubst st.subst 0 (.constructor name1 fixed1 arity1) =
          .constructor name1 fixed1 arity1 := rfl
    have hright :
        applySubst st.subst 0 (.constructor name2 fixed2 arity2) =
          .constructor name2 fixed2 arity2 := rfl
    have h_ctor_neq :
        (applySubst st.subst 0 (.constructor name1 fixed1 arity1) ==
          applySubst st.subst 0 (.constructor name2 fixed2 arity2)) = false := by
      show beqTy (Ty.constructor name1 fixed1 arity1) (Ty.constructor name2 fixed2 arity2) = false
      simp [beqTy, h_name_beq]
    exact constructor_unify_rejects_of_normalized_guard_false st 0
      name1 name2 name1 name2 fixed1 fixed2 fixed1 fixed2 arity1 arity2 arity1 arity2
      hleft hright h_ctor_neq h_guard
  | succ n =>
    have hleft :
        applySubst st.subst (n + 1) (.constructor name1 fixed1 arity1) =
          .constructor name1 (applySubstTyList st.subst n fixed1) arity1 := by
      simp [applySubst]
    have hright :
        applySubst st.subst (n + 1) (.constructor name2 fixed2 arity2) =
          .constructor name2 (applySubstTyList st.subst n fixed2) arity2 := by
      simp [applySubst]
    have h_ctor_neq :
        (applySubst st.subst (n + 1) (.constructor name1 fixed1 arity1) ==
          applySubst st.subst (n + 1) (.constructor name2 fixed2 arity2)) = false := by
      show
        beqTy (Ty.constructor name1 (applySubstTyList st.subst n fixed1) arity1)
          (Ty.constructor name2 (applySubstTyList st.subst n fixed2) arity2) = false
      simp [beqTy, h_name_beq]
    exact constructor_unify_rejects_of_normalized_guard_false st (n + 1)
      name1 name2 name1 name2 fixed1 fixed2
      (applySubstTyList st.subst n fixed1) (applySubstTyList st.subst n fixed2)
      arity1 arity2 arity1 arity2 hleft hright h_ctor_neq h_guard

/-- Constructor-arity mismatch rejects unification at any successor fuel, for
    arbitrary fixed arguments. -/
theorem constructor_arity_mismatch_any_fixed_any_fuel
    (st : UnifyState) (fuel : Nat)
    (name : String) (fixed1 fixed2 : TyList) (arity1 arity2 : Nat)
    (harity : arity1 = arity2 → False) :
    unify st (fuel + 1)
      (.constructor name fixed1 arity1)
      (.constructor name fixed2 arity2)
      = .err "type mismatch" := by
  have h_arity_beq : (arity1 == arity2) = false := nat_beq_false_of_ne harity
  have h_guard : ¬ (name = name ∧ arity1 = arity2) := by
    intro hpair
    exact harity hpair.2
  cases fuel with
  | zero =>
    have hleft :
        applySubst st.subst 0 (.constructor name fixed1 arity1) =
          .constructor name fixed1 arity1 := rfl
    have hright :
        applySubst st.subst 0 (.constructor name fixed2 arity2) =
          .constructor name fixed2 arity2 := rfl
    have h_ctor_neq :
        (applySubst st.subst 0 (.constructor name fixed1 arity1) ==
          applySubst st.subst 0 (.constructor name fixed2 arity2)) = false := by
      show beqTy (Ty.constructor name fixed1 arity1) (Ty.constructor name fixed2 arity2) = false
      simp [beqTy, h_arity_beq]
    exact constructor_unify_rejects_of_normalized_guard_false st 0
      name name name name fixed1 fixed2 fixed1 fixed2 arity1 arity2 arity1 arity2
      hleft hright h_ctor_neq h_guard
  | succ n =>
    have hleft :
        applySubst st.subst (n + 1) (.constructor name fixed1 arity1) =
          .constructor name (applySubstTyList st.subst n fixed1) arity1 := by
      simp [applySubst]
    have hright :
        applySubst st.subst (n + 1) (.constructor name fixed2 arity2) =
          .constructor name (applySubstTyList st.subst n fixed2) arity2 := by
      simp [applySubst]
    have h_ctor_neq :
        (applySubst st.subst (n + 1) (.constructor name fixed1 arity1) ==
          applySubst st.subst (n + 1) (.constructor name fixed2 arity2)) = false := by
      show
        beqTy (Ty.constructor name (applySubstTyList st.subst n fixed1) arity1)
          (Ty.constructor name (applySubstTyList st.subst n fixed2) arity2) = false
      simp [beqTy, h_arity_beq]
    exact constructor_unify_rejects_of_normalized_guard_false st (n + 1)
      name name name name fixed1 fixed2
      (applySubstTyList st.subst n fixed1) (applySubstTyList st.subst n fixed2)
      arity1 arity2 arity1 arity2 hleft hright h_ctor_neq h_guard

/-- Constructor guard mismatch (name mismatch or arity mismatch) rejects
    unification at any successor fuel, for arbitrary fixed arguments. -/
theorem constructor_guard_mismatch_any_fixed_any_fuel
    (st : UnifyState) (fuel : Nat)
    (name1 name2 : String) (fixed1 fixed2 : TyList) (arity1 arity2 : Nat)
    (h_guard : ¬ (name1 = name2 ∧ arity1 = arity2)) :
    unify st (fuel + 1)
      (.constructor name1 fixed1 arity1)
      (.constructor name2 fixed2 arity2)
      = .err "type mismatch" := by
  by_cases hname : name1 = name2
  · subst hname
    have harity : arity1 = arity2 → False := by
      intro h
      exact h_guard ⟨rfl, h⟩
    exact constructor_arity_mismatch_any_fixed_any_fuel st fuel
      name1 fixed1 fixed2 arity1 arity2 harity
  · have hname' : name1 = name2 → False := by
      intro h
      exact hname h
    exact constructor_name_mismatch_any_fixed_any_fuel st fuel
      name1 name2 fixed1 fixed2 arity1 arity2 hname'

/-- At successor fuel on the normalized app path (`fuel+2` outer), if the
    normalized constructor guard fails (name or arity mismatch), app
    unification rejects with constructor mismatch. -/
theorem app_unify_rejects_ctor_guard_false_of_normalized_succ
    (st : UnifyState) (fuel : Nat)
    (ctor1 ctor2 : Ty) (args1 args2 args1' args2' : TyList)
    (name1 name2 : String) (fixed1 fixed2 : TyList) (arity1 arity2 : Nat)
    (hleft :
      applySubst st.subst (fuel + 1) (.app ctor1 args1) =
        .app (.constructor name1 fixed1 arity1) args1')
    (hright :
      applySubst st.subst (fuel + 1) (.app ctor2 args2) =
        .app (.constructor name2 fixed2 arity2) args2')
    (h_ctor_neq :
      (applySubst st.subst (fuel + 1) (.app ctor1 args1) ==
        applySubst st.subst (fuel + 1) (.app ctor2 args2)) = false)
    (h_guard : ¬ (name1 = name2 ∧ arity1 = arity2)) :
    unify st (fuel + 2) (.app ctor1 args1) (.app ctor2 args2) =
      .err "type mismatch" := by
  have h_ctor :
      unify st (fuel + 1) (.constructor name1 fixed1 arity1) (.constructor name2 fixed2 arity2) =
        .err "type mismatch" := by
    by_cases hname : name1 = name2
    · have harity : arity1 = arity2 → False := by
        intro h
        exact h_guard ⟨hname, h⟩
      simpa [hname] using
        (constructor_arity_mismatch_any_fixed_any_fuel st fuel name1 fixed1 fixed2 arity1 arity2 harity)
    · have hname' : name1 = name2 → False := by
        intro h
        exact hname h
      exact constructor_name_mismatch_any_fixed_any_fuel
        st fuel name1 name2 fixed1 fixed2 arity1 arity2 hname'
  exact app_unify_rejects_ctor_err_of_normalized st (fuel + 1) ctor1 ctor2
    (.constructor name1 fixed1 arity1) (.constructor name2 fixed2 arity2)
    args1 args2 args1' args2' hleft hright h_ctor_neq "type mismatch" h_ctor

/-- App unification rejects at any outer successor+1 fuel when constructor names
    mismatch (constructor-headed app forms). -/
theorem app_constructor_name_mismatch_any_fuel
    (st : UnifyState) (fuel : Nat)
    (name1 name2 : String) (fixed1 fixed2 : TyList) (arity1 arity2 : Nat)
    (args1 args2 : TyList)
    (hname : name1 = name2 → False) :
    unify st (fuel + 2)
      (.app (.constructor name1 fixed1 arity1) args1)
      (.app (.constructor name2 fixed2 arity2) args2)
      = .err "type mismatch" := by
  have h_name_beq : (name1 == name2) = false := string_beq_false_of_ne hname
  have h_guard :
      ¬ (name1 = name2 ∧ arity1 = arity2) := by
    intro hpair
    exact hname hpair.1
  cases fuel with
  | zero =>
    have hleft :
        applySubst st.subst (0 + 1) (.app (.constructor name1 fixed1 arity1) args1) =
          .app (.constructor name1 fixed1 arity1) (applySubstTyList st.subst 0 args1) := by
      simp [applySubst]
    have hright :
        applySubst st.subst (0 + 1) (.app (.constructor name2 fixed2 arity2) args2) =
          .app (.constructor name2 fixed2 arity2) (applySubstTyList st.subst 0 args2) := by
      simp [applySubst]
    have h_ctor_neq :
        (applySubst st.subst (0 + 1) (.app (.constructor name1 fixed1 arity1) args1) ==
          applySubst st.subst (0 + 1) (.app (.constructor name2 fixed2 arity2) args2)) = false := by
      rw [hleft, hright]
      show
        beqTy (Ty.app (.constructor name1 fixed1 arity1) (applySubstTyList st.subst 0 args1))
          (Ty.app (.constructor name2 fixed2 arity2) (applySubstTyList st.subst 0 args2)) = false
      simp [beqTy, h_name_beq]
    simpa using app_unify_rejects_ctor_guard_false_of_normalized_succ st 0
      (.constructor name1 fixed1 arity1) (.constructor name2 fixed2 arity2)
      args1 args2 (applySubstTyList st.subst 0 args1) (applySubstTyList st.subst 0 args2)
      name1 name2 fixed1 fixed2 arity1 arity2
      hleft hright h_ctor_neq h_guard
  | succ n =>
    have hleft :
        applySubst st.subst ((n + 1) + 1) (.app (.constructor name1 fixed1 arity1) args1) =
          .app (.constructor name1 (applySubstTyList st.subst n fixed1) arity1)
               (applySubstTyList st.subst (n + 1) args1) := by
      simp [applySubst]
    have hright :
        applySubst st.subst ((n + 1) + 1) (.app (.constructor name2 fixed2 arity2) args2) =
          .app (.constructor name2 (applySubstTyList st.subst n fixed2) arity2)
               (applySubstTyList st.subst (n + 1) args2) := by
      simp [applySubst]
    have h_ctor_neq :
        (applySubst st.subst ((n + 1) + 1) (.app (.constructor name1 fixed1 arity1) args1) ==
          applySubst st.subst ((n + 1) + 1) (.app (.constructor name2 fixed2 arity2) args2)) = false := by
      rw [hleft, hright]
      show
        beqTy
          (Ty.app (.constructor name1 (applySubstTyList st.subst n fixed1) arity1)
            (applySubstTyList st.subst (n + 1) args1))
          (Ty.app (.constructor name2 (applySubstTyList st.subst n fixed2) arity2)
            (applySubstTyList st.subst (n + 1) args2)) = false
      simp [beqTy, h_name_beq]
    simpa [Nat.add_assoc] using app_unify_rejects_ctor_guard_false_of_normalized_succ st (n + 1)
      (.constructor name1 fixed1 arity1) (.constructor name2 fixed2 arity2)
      args1 args2
      (applySubstTyList st.subst (n + 1) args1)
      (applySubstTyList st.subst (n + 1) args2)
      name1 name2
      (applySubstTyList st.subst n fixed1)
      (applySubstTyList st.subst n fixed2)
      arity1 arity2
      hleft hright h_ctor_neq h_guard

/-- App unification rejects at any outer successor+1 fuel when constructor
    arities mismatch (constructor-headed app forms, equal constructor names). -/
theorem app_constructor_arity_mismatch_any_fuel
    (st : UnifyState) (fuel : Nat)
    (name : String) (fixed1 fixed2 : TyList) (arity1 arity2 : Nat)
    (args1 args2 : TyList)
    (harity : arity1 = arity2 → False) :
    unify st (fuel + 2)
      (.app (.constructor name fixed1 arity1) args1)
      (.app (.constructor name fixed2 arity2) args2)
      = .err "type mismatch" := by
  have h_arity_beq : (arity1 == arity2) = false := nat_beq_false_of_ne harity
  have h_guard :
      ¬ (name = name ∧ arity1 = arity2) := by
    intro hpair
    exact harity hpair.2
  cases fuel with
  | zero =>
    have hleft :
        applySubst st.subst (0 + 1) (.app (.constructor name fixed1 arity1) args1) =
          .app (.constructor name fixed1 arity1) (applySubstTyList st.subst 0 args1) := by
      simp [applySubst]
    have hright :
        applySubst st.subst (0 + 1) (.app (.constructor name fixed2 arity2) args2) =
          .app (.constructor name fixed2 arity2) (applySubstTyList st.subst 0 args2) := by
      simp [applySubst]
    have h_ctor_neq :
        (applySubst st.subst (0 + 1) (.app (.constructor name fixed1 arity1) args1) ==
          applySubst st.subst (0 + 1) (.app (.constructor name fixed2 arity2) args2)) = false := by
      rw [hleft, hright]
      show
        beqTy (Ty.app (.constructor name fixed1 arity1) (applySubstTyList st.subst 0 args1))
          (Ty.app (.constructor name fixed2 arity2) (applySubstTyList st.subst 0 args2)) = false
      simp [beqTy, h_arity_beq]
    simpa using app_unify_rejects_ctor_guard_false_of_normalized_succ st 0
      (.constructor name fixed1 arity1) (.constructor name fixed2 arity2)
      args1 args2 (applySubstTyList st.subst 0 args1) (applySubstTyList st.subst 0 args2)
      name name fixed1 fixed2 arity1 arity2
      hleft hright h_ctor_neq h_guard
  | succ n =>
    have hleft :
        applySubst st.subst ((n + 1) + 1) (.app (.constructor name fixed1 arity1) args1) =
          .app (.constructor name (applySubstTyList st.subst n fixed1) arity1)
               (applySubstTyList st.subst (n + 1) args1) := by
      simp [applySubst]
    have hright :
        applySubst st.subst ((n + 1) + 1) (.app (.constructor name fixed2 arity2) args2) =
          .app (.constructor name (applySubstTyList st.subst n fixed2) arity2)
               (applySubstTyList st.subst (n + 1) args2) := by
      simp [applySubst]
    have h_ctor_neq :
        (applySubst st.subst ((n + 1) + 1) (.app (.constructor name fixed1 arity1) args1) ==
          applySubst st.subst ((n + 1) + 1) (.app (.constructor name fixed2 arity2) args2)) = false := by
      rw [hleft, hright]
      show
        beqTy
          (Ty.app (.constructor name (applySubstTyList st.subst n fixed1) arity1)
            (applySubstTyList st.subst (n + 1) args1))
          (Ty.app (.constructor name (applySubstTyList st.subst n fixed2) arity2)
            (applySubstTyList st.subst (n + 1) args2)) = false
      simp [beqTy, h_arity_beq]
    simpa [Nat.add_assoc] using app_unify_rejects_ctor_guard_false_of_normalized_succ st (n + 1)
      (.constructor name fixed1 arity1) (.constructor name fixed2 arity2)
      args1 args2
      (applySubstTyList st.subst (n + 1) args1)
      (applySubstTyList st.subst (n + 1) args2)
      name name
      (applySubstTyList st.subst n fixed1)
      (applySubstTyList st.subst n fixed2)
      arity1 arity2
      hleft hright h_ctor_neq h_guard

/-- App unification rejects at any outer successor+1 fuel when the normalized
    constructor guard fails (constructor-headed app forms). -/
theorem app_constructor_guard_mismatch_any_fuel
    (st : UnifyState) (fuel : Nat)
    (name1 name2 : String) (fixed1 fixed2 : TyList) (arity1 arity2 : Nat)
    (args1 args2 : TyList)
    (h_guard : ¬ (name1 = name2 ∧ arity1 = arity2)) :
    unify st (fuel + 2)
      (.app (.constructor name1 fixed1 arity1) args1)
      (.app (.constructor name2 fixed2 arity2) args2)
      = .err "type mismatch" := by
  by_cases hname : name1 = name2
  · subst hname
    have harity : arity1 = arity2 → False := by
      intro h
      exact h_guard ⟨rfl, h⟩
    exact app_constructor_arity_mismatch_any_fuel st fuel
      name1 fixed1 fixed2 arity1 arity2 args1 args2 harity
  · have hname' : name1 = name2 → False := by
      intro h
      exact hname h
    exact app_constructor_name_mismatch_any_fuel st fuel
      name1 name2 fixed1 fixed2 arity1 arity2 args1 args2 hname'

/-- Packaged constructor-guard mismatch suite across constructor and
    constructor-headed app unification: both distinct-name and equal-name
    arity-mismatch paths reject at any outer successor fuel. -/
theorem constructor_guard_mismatch_suite_any_fuel
    (st : UnifyState) (fuel : Nat)
    (name1 name2 name : String) (fixed1 fixed2 : TyList) (arity1 arity2 : Nat)
    (args1 args2 : TyList)
    (hname : name1 = name2 → False)
    (harity : arity1 = arity2 → False) :
    (unify st (fuel + 1)
      (.constructor name1 fixed1 arity1)
      (.constructor name2 fixed2 arity2) = .err "type mismatch")
    ∧
    (unify st (fuel + 2)
      (.app (.constructor name1 fixed1 arity1) args1)
      (.app (.constructor name2 fixed2 arity2) args2) = .err "type mismatch")
    ∧
    (unify st (fuel + 1)
      (.constructor name fixed1 arity1)
      (.constructor name fixed2 arity2) = .err "type mismatch")
    ∧
    (unify st (fuel + 2)
      (.app (.constructor name fixed1 arity1) args1)
      (.app (.constructor name fixed2 arity2) args2) = .err "type mismatch") := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact constructor_name_mismatch_any_fixed_any_fuel
      st fuel name1 name2 fixed1 fixed2 arity1 arity2 hname
  · exact app_constructor_name_mismatch_any_fuel
      st fuel name1 name2 fixed1 fixed2 arity1 arity2 args1 args2 hname
  · exact constructor_arity_mismatch_any_fixed_any_fuel
      st fuel name fixed1 fixed2 arity1 arity2 harity
  · exact app_constructor_arity_mismatch_any_fuel
      st fuel name fixed1 fixed2 arity1 arity2 args1 args2 harity

/-- Packaged concrete surface witness for constructor guard behavior:
    constructor-name mismatch rejects, equal-name arity mismatch rejects, and
    constructor-headed app name mismatch rejects. -/
theorem constructor_guard_surface_slice (st : UnifyState) :
    (unify st 2
      (.constructor "List" (.cons .int .nil) 1)
      (.constructor "Map" (.cons .bool .nil) 1)
      = .err "type mismatch")
    ∧
    (unify st 2
      (.constructor "Map" (.cons .int .nil) 1)
      (.constructor "Map" .nil 2)
      = .err "type mismatch")
    ∧
    (unify st 2
      (.app (.constructor "List" (.cons .int .nil) 1) .nil)
      (.app (.constructor "Map" (.cons .int .nil) 1) .nil)
      = .err "type mismatch") := by
  have hname : "List" = "Map" → False := by
    decide
  have harity : 1 = 2 → False := by
    decide
  refine ⟨?_, ?_, ?_⟩
  · simpa using constructor_name_mismatch_any_fixed_any_fuel
      st 1 "List" "Map"
      (.cons .int .nil) (.cons .bool .nil)
      1 1 hname
  · simpa using constructor_arity_mismatch_any_fixed_any_fuel
      st 1 "Map"
      (.cons .int .nil) .nil
      1 2 harity
  · simpa using app_constructor_name_mismatch_any_fuel
      st 0 "List" "Map"
      (.cons .int .nil) (.cons .int .nil)
      1 1 .nil .nil hname

/-- Boundary-sensitive sites where constructor-head guard checks are enforced. -/
inductive ConstructorGuardBoundarySite : Type where
  | letAnnotation
  | callArgument
  | returnAnnotation
  | ascription

/-- Site-level constructor-guard boundary policy.
    Current scope: when expected/actual are constructor-headed, head name/arity
    must match; non-constructor actuals are rejected when constructor-headed
    expected forms are present. -/
def constructorGuardBoundaryAllows (expected actual : Ty) : Bool :=
  match expected, actual with
  | .constructor expectedName _ expectedArity, .constructor actualName _ actualArity =>
      (expectedName == actualName) && (expectedArity == actualArity)
  | .constructor _ _ _, _ => false
  | .app (.constructor expectedName _ expectedArity) _, .app (.constructor actualName _ actualArity) _ =>
      (expectedName == actualName) && (expectedArity == actualArity)
  | .app (.constructor _ _ _) _, _ => false
  | _, _ => true

/-- Site-level wrapper for constructor-head guard boundary checks. -/
def constructorGuardBoundaryAllowsAtSite
    (_site : ConstructorGuardBoundarySite) (expected actual : Ty) : Bool :=
  constructorGuardBoundaryAllows expected actual

/-- Constructor-head guard boundary policy is currently site-invariant. -/
theorem constructor_guard_boundary_policy_site_invariant
    (site1 site2 : ConstructorGuardBoundarySite) (expected actual : Ty) :
    constructorGuardBoundaryAllowsAtSite site1 expected actual =
      constructorGuardBoundaryAllowsAtSite site2 expected actual := by
  cases site1 <;> cases site2 <;> rfl

/-- Distinct constructor names are rejected by constructor-head boundary policy. -/
theorem constructor_guard_boundary_rejects_name_mismatch :
    constructorGuardBoundaryAllows
      (.constructor "List" (.cons .int .nil) 1)
      (.constructor "Map" (.cons .int .nil) 1)
      = false := by
  native_decide

/-- Equal constructor names with mismatched arities are rejected by boundary policy. -/
theorem constructor_guard_boundary_rejects_arity_mismatch :
    constructorGuardBoundaryAllows
      (.constructor "Map" (.cons .int .nil) 1)
      (.constructor "Map" .nil 2)
      = false := by
  native_decide

/-- Non-constructor actuals are rejected when constructor-headed types are expected. -/
theorem constructor_guard_boundary_rejects_non_constructor_actual :
    constructorGuardBoundaryAllows
      (.constructor "List" (.cons .int .nil) 1)
      .int
      = false := by
  native_decide

/-- Packaged constructor-guard boundary surface slice:
    site invariance + boundary rejection witnesses with closure to concrete
    unifier mismatch witnesses. -/
theorem constructor_guard_boundary_surface_slice
    (st : UnifyState) (site : ConstructorGuardBoundarySite) :
    (constructorGuardBoundaryAllowsAtSite site
      (.constructor "List" (.cons .int .nil) 1)
      (.constructor "Map" (.cons .int .nil) 1)
      = false)
    ∧
    (constructorGuardBoundaryAllowsAtSite site
      (.constructor "Map" (.cons .int .nil) 1)
      (.constructor "Map" .nil 2)
      = false)
    ∧
    (constructorGuardBoundaryAllowsAtSite site
      (.constructor "List" (.cons .int .nil) 1)
      .int
      = false)
    ∧
    (unify st 2
      (.constructor "List" (.cons .int .nil) 1)
      (.constructor "Map" (.cons .bool .nil) 1)
      = .err "type mismatch")
    ∧
    (unify st 2
      (.constructor "Map" (.cons .int .nil) 1)
      (.constructor "Map" .nil 2)
      = .err "type mismatch")
    ∧
    (unify st 2
      (.app (.constructor "List" (.cons .int .nil) 1) .nil)
      (.app (.constructor "Map" (.cons .int .nil) 1) .nil)
      = .err "type mismatch") := by
  have h_surface := constructor_guard_surface_slice st
  rcases h_surface with ⟨h_name_unify, h_arity_unify, h_app_name_unify⟩
  refine ⟨?_, ?_, ?_, h_name_unify, h_arity_unify, h_app_name_unify⟩
  · cases site <;> exact constructor_guard_boundary_rejects_name_mismatch
  · cases site <;> exact constructor_guard_boundary_rejects_arity_mismatch
  · cases site <;> exact constructor_guard_boundary_rejects_non_constructor_actual

/-- `app` free vars are constructor free vars plus argument free vars. -/
theorem app_free_vars (ctor : Ty) (args : TyList) :
    freeTypeVars (.app ctor args) = freeTypeVars ctor ++ freeTypeVarsTyList args /\
      freeRowVars (.app ctor args) = freeRowVars ctor ++ freeRowVarsTyList args := by
  simp [freeTypeVars, freeRowVars]

/-- `constructor` free vars are exactly its fixed-argument free vars. -/
theorem constructor_free_vars (name : String) (fixedArgs : TyList) (arity : Nat) :
    freeTypeVars (.constructor name fixedArgs arity) = freeTypeVarsTyList fixedArgs /\
      freeRowVars (.constructor name fixedArgs arity) = freeRowVarsTyList fixedArgs := by
  simp [freeTypeVars, freeRowVars]

/-- Packaged constructor-app free-variable slice across `app` and
    `constructor`. -/
theorem constructor_app_free_vars_slice
    (ctor : Ty) (args : TyList) (name : String) (fixedArgs : TyList) (arity : Nat) :
    (freeTypeVars (.app ctor args) = freeTypeVars ctor ++ freeTypeVarsTyList args
      ∧ freeRowVars (.app ctor args) = freeRowVars ctor ++ freeRowVarsTyList args)
    ∧
    (freeTypeVars (.constructor name fixedArgs arity) = freeTypeVarsTyList fixedArgs
      ∧ freeRowVars (.constructor name fixedArgs arity) = freeRowVarsTyList fixedArgs) := by
  refine ⟨?_, ?_⟩
  · exact app_free_vars ctor args
  · exact constructor_free_vars name fixedArgs arity
