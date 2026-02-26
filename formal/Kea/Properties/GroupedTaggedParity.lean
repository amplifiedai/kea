/- 
  Kea.Properties.GroupedTaggedParity - GroupedFrame/Tagged parity slice.

  Current scope: `GroupedFrame` and `Tagged` are modeled in `Ty`, propagated
  through substitution/unification, and covered with constructor-local parity
  lemmas (substitution, reflexive unification, mismatch witnesses, free vars).
-/

import Kea.Properties.UnifyReflexive

private theorem applySubst_int (s : Subst) : ∀ fuel, applySubst s fuel .int = .int
  | 0 => rfl
  | _ + 1 => rfl

/-- One substitution step over `GroupedFrame` rewrites only the row type. -/
theorem groupedFrame_subst_step (s : Subst) (fuel : Nat) (rowTy : Ty) (keys : List Label) :
    applySubst s (fuel + 1) (.groupedFrame rowTy keys) =
      .groupedFrame (applySubst s fuel rowTy) keys := by
  simp [applySubst]

/-- One substitution step over `Tagged` rewrites only the inner type. -/
theorem tagged_subst_step (s : Subst) (fuel : Nat) (inner : Ty) (tags : List (String × Int)) :
    applySubst s (fuel + 1) (.tagged inner tags) =
      .tagged (applySubst s fuel inner) tags := by
  simp [applySubst]

/-- On normalized grouped-frame forms, failed constructor BEq short-circuit and
    equal key sets reduce unification to inner-type unification. -/
theorem groupedFrame_unify_reduces_to_inner_of_normalized
    (st : UnifyState) (fuel : Nat)
    (row1 row2 row1' row2' : Ty) (keys1 keys2 keys1' keys2' : List Label)
    (hleft :
      applySubst st.subst fuel (.groupedFrame row1 keys1) =
        .groupedFrame row1' keys1')
    (hright :
      applySubst st.subst fuel (.groupedFrame row2 keys2) =
        .groupedFrame row2' keys2')
    (h_ctor_neq :
      (applySubst st.subst fuel (.groupedFrame row1 keys1) ==
        applySubst st.subst fuel (.groupedFrame row2 keys2)) = false)
    (h_keys : keys1' = keys2') :
    unify st (fuel + 1) (.groupedFrame row1 keys1) (.groupedFrame row2 keys2) =
      unify st fuel row1' row2' := by
  have h_ctor_neq' :
      (Ty.groupedFrame row1' keys1' == Ty.groupedFrame row2' keys2') = false := by
    simpa [hleft, hright] using h_ctor_neq
  have h_ctor_neq'' :
      (Ty.groupedFrame row1' keys2' == Ty.groupedFrame row2' keys2') = false := by
    simpa [h_keys] using h_ctor_neq'
  simp [unify, applySubstCompat, hleft, hright, h_ctor_neq'', h_keys]

/-- On normalized grouped-frame forms, failed constructor BEq short-circuit and
    distinct key sets force mismatch. -/
theorem groupedFrame_unify_rejects_of_normalized
    (st : UnifyState) (fuel : Nat)
    (row1 row2 row1' row2' : Ty) (keys1 keys2 keys1' keys2' : List Label)
    (hleft :
      applySubst st.subst fuel (.groupedFrame row1 keys1) =
        .groupedFrame row1' keys1')
    (hright :
      applySubst st.subst fuel (.groupedFrame row2 keys2) =
        .groupedFrame row2' keys2')
    (h_ctor_neq :
      (applySubst st.subst fuel (.groupedFrame row1 keys1) ==
        applySubst st.subst fuel (.groupedFrame row2 keys2)) = false)
    (h_keys : keys1' ≠ keys2') :
    unify st (fuel + 1) (.groupedFrame row1 keys1) (.groupedFrame row2 keys2) =
      .err "type mismatch" := by
  have h_ctor_neq' :
      (Ty.groupedFrame row1' keys1' == Ty.groupedFrame row2' keys2') = false := by
    simpa [hleft, hright] using h_ctor_neq
  simp [unify, applySubstCompat, hleft, hright, h_ctor_neq', h_keys]

/-- On normalized tagged forms, failed constructor BEq short-circuit and equal
    metadata reduce unification to inner-type unification. -/
theorem tagged_unify_reduces_to_inner_of_normalized
    (st : UnifyState) (fuel : Nat)
    (inner1 inner2 inner1' inner2' : Ty)
    (tags1 tags2 tags1' tags2' : List (String × Int))
    (hleft :
      applySubst st.subst fuel (.tagged inner1 tags1) =
        .tagged inner1' tags1')
    (hright :
      applySubst st.subst fuel (.tagged inner2 tags2) =
        .tagged inner2' tags2')
    (h_ctor_neq :
      (applySubst st.subst fuel (.tagged inner1 tags1) ==
        applySubst st.subst fuel (.tagged inner2 tags2)) = false)
    (h_tags : tags1' = tags2') :
    unify st (fuel + 1) (.tagged inner1 tags1) (.tagged inner2 tags2) =
      unify st fuel inner1' inner2' := by
  have h_ctor_neq' :
      (Ty.tagged inner1' tags1' == Ty.tagged inner2' tags2') = false := by
    simpa [hleft, hright] using h_ctor_neq
  have h_ctor_neq'' :
      (Ty.tagged inner1' tags2' == Ty.tagged inner2' tags2') = false := by
    simpa [h_tags] using h_ctor_neq'
  simp [unify, applySubstCompat, hleft, hright, h_ctor_neq'', h_tags]

/-- On normalized tagged forms, failed constructor BEq short-circuit and
    distinct metadata force mismatch. -/
theorem tagged_unify_rejects_of_normalized
    (st : UnifyState) (fuel : Nat)
    (inner1 inner2 inner1' inner2' : Ty)
    (tags1 tags2 tags1' tags2' : List (String × Int))
    (hleft :
      applySubst st.subst fuel (.tagged inner1 tags1) =
        .tagged inner1' tags1')
    (hright :
      applySubst st.subst fuel (.tagged inner2 tags2) =
        .tagged inner2' tags2')
    (h_ctor_neq :
      (applySubst st.subst fuel (.tagged inner1 tags1) ==
        applySubst st.subst fuel (.tagged inner2 tags2)) = false)
    (h_tags : tags1' ≠ tags2') :
    unify st (fuel + 1) (.tagged inner1 tags1) (.tagged inner2 tags2) =
      .err "type mismatch" := by
  have h_ctor_neq' :
      (Ty.tagged inner1' tags1' == Ty.tagged inner2' tags2') = false := by
    simpa [hleft, hright] using h_ctor_neq
  simp [unify, applySubstCompat, hleft, hright, h_ctor_neq', h_tags]

/-- At any outer successor+1 fuel, normalized grouped-frame inner-type errors
    propagate through grouped-frame unification unchanged when key sets match. -/
theorem groupedFrame_inner_error_propagates_any_fuel
    (st : UnifyState) (fuel : Nat)
    (row1 row2 : Ty) (keys1 keys2 : List Label)
    (e : String)
    (hbeq :
      (Ty.groupedFrame (applySubst st.subst fuel row1) keys1 ==
        Ty.groupedFrame (applySubst st.subst fuel row2) keys2) = false)
    (h_keys : keys1 = keys2)
    (h_inner :
      unify st (fuel + 1)
        (applySubst st.subst fuel row1)
        (applySubst st.subst fuel row2) = .err e) :
    unify st (fuel + 2)
      (.groupedFrame row1 keys1)
      (.groupedFrame row2 keys2) = .err e := by
  have hleft :
      applySubst st.subst (fuel + 1) (.groupedFrame row1 keys1) =
        .groupedFrame (applySubst st.subst fuel row1) keys1 := by
    simp [applySubst]
  have hright :
      applySubst st.subst (fuel + 1) (.groupedFrame row2 keys2) =
        .groupedFrame (applySubst st.subst fuel row2) keys2 := by
    simp [applySubst]
  have h_ctor_neq :
      (applySubst st.subst (fuel + 1) (.groupedFrame row1 keys1) ==
        applySubst st.subst (fuel + 1) (.groupedFrame row2 keys2)) = false := by
    simpa [hleft, hright] using hbeq
  have h_reduce :
      unify st (fuel + 2)
        (.groupedFrame row1 keys1)
        (.groupedFrame row2 keys2) =
      unify st (fuel + 1)
        (applySubst st.subst fuel row1)
        (applySubst st.subst fuel row2) := by
    exact groupedFrame_unify_reduces_to_inner_of_normalized st (fuel + 1)
      row1 row2
      (applySubst st.subst fuel row1)
      (applySubst st.subst fuel row2)
      keys1 keys2 keys1 keys2
      hleft hright h_ctor_neq h_keys
  rw [h_reduce]
  exact h_inner

/-- At any outer successor+1 fuel, normalized grouped-frame inner-type success
    propagates through grouped-frame unification with the same resulting state
    when key sets match. -/
theorem groupedFrame_inner_success_propagates_any_fuel
    (st st' : UnifyState) (fuel : Nat)
    (row1 row2 : Ty) (keys1 keys2 : List Label)
    (hbeq :
      (Ty.groupedFrame (applySubst st.subst fuel row1) keys1 ==
        Ty.groupedFrame (applySubst st.subst fuel row2) keys2) = false)
    (h_keys : keys1 = keys2)
    (h_inner :
      unify st (fuel + 1)
        (applySubst st.subst fuel row1)
        (applySubst st.subst fuel row2) = .ok st') :
    unify st (fuel + 2)
      (.groupedFrame row1 keys1)
      (.groupedFrame row2 keys2) = .ok st' := by
  have hleft :
      applySubst st.subst (fuel + 1) (.groupedFrame row1 keys1) =
        .groupedFrame (applySubst st.subst fuel row1) keys1 := by
    simp [applySubst]
  have hright :
      applySubst st.subst (fuel + 1) (.groupedFrame row2 keys2) =
        .groupedFrame (applySubst st.subst fuel row2) keys2 := by
    simp [applySubst]
  have h_ctor_neq :
      (applySubst st.subst (fuel + 1) (.groupedFrame row1 keys1) ==
        applySubst st.subst (fuel + 1) (.groupedFrame row2 keys2)) = false := by
    simpa [hleft, hright] using hbeq
  have h_reduce :
      unify st (fuel + 2)
        (.groupedFrame row1 keys1)
        (.groupedFrame row2 keys2) =
      unify st (fuel + 1)
        (applySubst st.subst fuel row1)
        (applySubst st.subst fuel row2) := by
    exact groupedFrame_unify_reduces_to_inner_of_normalized st (fuel + 1)
      row1 row2
      (applySubst st.subst fuel row1)
      (applySubst st.subst fuel row2)
      keys1 keys2 keys1 keys2
      hleft hright h_ctor_neq h_keys
  rw [h_reduce]
  exact h_inner

/-- At any outer successor+1 fuel, normalized tagged-inner errors propagate
    through tagged unification unchanged when metadata matches. -/
theorem tagged_inner_error_propagates_any_fuel
    (st : UnifyState) (fuel : Nat)
    (inner1 inner2 : Ty) (tags1 tags2 : List (String × Int))
    (e : String)
    (hbeq :
      (Ty.tagged (applySubst st.subst fuel inner1) tags1 ==
        Ty.tagged (applySubst st.subst fuel inner2) tags2) = false)
    (h_tags : tags1 = tags2)
    (h_inner :
      unify st (fuel + 1)
        (applySubst st.subst fuel inner1)
        (applySubst st.subst fuel inner2) = .err e) :
    unify st (fuel + 2)
      (.tagged inner1 tags1)
      (.tagged inner2 tags2) = .err e := by
  have hleft :
      applySubst st.subst (fuel + 1) (.tagged inner1 tags1) =
        .tagged (applySubst st.subst fuel inner1) tags1 := by
    simp [applySubst]
  have hright :
      applySubst st.subst (fuel + 1) (.tagged inner2 tags2) =
        .tagged (applySubst st.subst fuel inner2) tags2 := by
    simp [applySubst]
  have h_ctor_neq :
      (applySubst st.subst (fuel + 1) (.tagged inner1 tags1) ==
        applySubst st.subst (fuel + 1) (.tagged inner2 tags2)) = false := by
    simpa [hleft, hright] using hbeq
  have h_reduce :
      unify st (fuel + 2)
        (.tagged inner1 tags1)
        (.tagged inner2 tags2) =
      unify st (fuel + 1)
        (applySubst st.subst fuel inner1)
        (applySubst st.subst fuel inner2) := by
    exact tagged_unify_reduces_to_inner_of_normalized st (fuel + 1)
      inner1 inner2
      (applySubst st.subst fuel inner1)
      (applySubst st.subst fuel inner2)
      tags1 tags2 tags1 tags2
      hleft hright h_ctor_neq h_tags
  rw [h_reduce]
  exact h_inner

/-- At any outer successor+1 fuel, normalized tagged-inner success propagates
    through tagged unification with the same resulting state when metadata
    matches. -/
theorem tagged_inner_success_propagates_any_fuel
    (st st' : UnifyState) (fuel : Nat)
    (inner1 inner2 : Ty) (tags1 tags2 : List (String × Int))
    (hbeq :
      (Ty.tagged (applySubst st.subst fuel inner1) tags1 ==
        Ty.tagged (applySubst st.subst fuel inner2) tags2) = false)
    (h_tags : tags1 = tags2)
    (h_inner :
      unify st (fuel + 1)
        (applySubst st.subst fuel inner1)
        (applySubst st.subst fuel inner2) = .ok st') :
    unify st (fuel + 2)
      (.tagged inner1 tags1)
      (.tagged inner2 tags2) = .ok st' := by
  have hleft :
      applySubst st.subst (fuel + 1) (.tagged inner1 tags1) =
        .tagged (applySubst st.subst fuel inner1) tags1 := by
    simp [applySubst]
  have hright :
      applySubst st.subst (fuel + 1) (.tagged inner2 tags2) =
        .tagged (applySubst st.subst fuel inner2) tags2 := by
    simp [applySubst]
  have h_ctor_neq :
      (applySubst st.subst (fuel + 1) (.tagged inner1 tags1) ==
        applySubst st.subst (fuel + 1) (.tagged inner2 tags2)) = false := by
    simpa [hleft, hright] using hbeq
  have h_reduce :
      unify st (fuel + 2)
        (.tagged inner1 tags1)
        (.tagged inner2 tags2) =
      unify st (fuel + 1)
        (applySubst st.subst fuel inner1)
        (applySubst st.subst fuel inner2) := by
    exact tagged_unify_reduces_to_inner_of_normalized st (fuel + 1)
      inner1 inner2
      (applySubst st.subst fuel inner1)
      (applySubst st.subst fuel inner2)
      tags1 tags2 tags1 tags2
      hleft hright h_ctor_neq h_tags
  rw [h_reduce]
  exact h_inner

/-- `GroupedFrame` unifies with itself. -/
theorem groupedFrame_unifies_with_self
    (st : UnifyState) (fuel : Nat) (rowTy : Ty) (keys : List Label) :
    unify st (fuel + 1) (.groupedFrame rowTy keys) (.groupedFrame rowTy keys) = .ok st := by
  simpa using (unifyReflexive' st fuel (.groupedFrame rowTy keys))

/-- `Tagged` unifies with itself. -/
theorem tagged_unifies_with_self
    (st : UnifyState) (fuel : Nat) (inner : Ty) (tags : List (String × Int)) :
    unify st (fuel + 1) (.tagged inner tags) (.tagged inner tags) = .ok st := by
  simpa using (unifyReflexive' st fuel (.tagged inner tags))

/-- GroupedFrame key-set mismatch rejects unification. -/
theorem groupedFrame_keys_mismatch (st : UnifyState) :
    unify st 1
      (.groupedFrame (.row (.mk (.cons "a" .int .nil) none)) ["a"])
      (.groupedFrame (.row (.mk (.cons "a" .int .nil) none)) ["b"])
      = .err "type mismatch" := by
  have h_neq :
      (Ty.groupedFrame (.row (.mk (.cons "a" .int .nil) none)) ["a"] ==
        Ty.groupedFrame (.row (.mk (.cons "a" .int .nil) none)) ["b"]) = false := by
    native_decide
  simp [unify, applySubstCompat, applySubst, h_neq]

/-- GroupedFrame key-set mismatch rejects unification at any successor fuel. -/
theorem groupedFrame_keys_mismatch_any_fuel (st : UnifyState) (fuel : Nat) :
    unify st (fuel + 1)
      (.groupedFrame .int ["a"])
      (.groupedFrame .int ["b"])
      = .err "type mismatch" := by
  have h_neq :
      (Ty.groupedFrame .int ["a"] == Ty.groupedFrame .int ["b"]) = false := by
    native_decide
  cases fuel with
  | zero =>
      unfold unify
      simp [applySubstCompat, applySubst, h_neq]
  | succ fuel' =>
      have h_int : applySubst st.subst fuel' .int = .int := applySubst_int st.subst fuel'
      unfold unify
      simp [applySubstCompat, applySubst, h_int, h_neq]

/-- GroupedFrame key-set mismatch rejects unification at any successor fuel,
    for arbitrary inner row types. -/
theorem groupedFrame_keys_mismatch_any_inner_any_fuel
    (st : UnifyState) (fuel : Nat)
    (row1 row2 : Ty) (keys1 keys2 : List Label)
    (h_keys_ne : keys1 ≠ keys2) :
    unify st (fuel + 1)
      (.groupedFrame row1 keys1)
      (.groupedFrame row2 keys2)
      = .err "type mismatch" := by
  have h_keys_beq : (keys1 == keys2) = false := by
    cases hbeq : (keys1 == keys2) with
    | false => rfl
    | true =>
      have h_eq : keys1 = keys2 := by simpa using hbeq
      exact (h_keys_ne h_eq).elim
  cases fuel with
  | zero =>
    have hleft :
        applySubst st.subst 0 (.groupedFrame row1 keys1) =
          .groupedFrame row1 keys1 := rfl
    have hright :
        applySubst st.subst 0 (.groupedFrame row2 keys2) =
          .groupedFrame row2 keys2 := rfl
    have h_ctor_neq :
        (applySubst st.subst 0 (.groupedFrame row1 keys1) ==
          applySubst st.subst 0 (.groupedFrame row2 keys2)) = false := by
      show beqTy (Ty.groupedFrame row1 keys1) (Ty.groupedFrame row2 keys2) = false
      simp [beqTy, h_keys_beq]
    exact groupedFrame_unify_rejects_of_normalized st 0
      row1 row2 row1 row2
      keys1 keys2 keys1 keys2
      hleft hright h_ctor_neq h_keys_ne
  | succ n =>
    have hleft :
        applySubst st.subst (n + 1) (.groupedFrame row1 keys1) =
          .groupedFrame (applySubst st.subst n row1) keys1 := by
      simp [applySubst]
    have hright :
        applySubst st.subst (n + 1) (.groupedFrame row2 keys2) =
          .groupedFrame (applySubst st.subst n row2) keys2 := by
      simp [applySubst]
    have h_ctor_neq :
        (applySubst st.subst (n + 1) (.groupedFrame row1 keys1) ==
          applySubst st.subst (n + 1) (.groupedFrame row2 keys2)) = false := by
      show
        beqTy
          (Ty.groupedFrame (applySubst st.subst n row1) keys1)
          (Ty.groupedFrame (applySubst st.subst n row2) keys2) = false
      simp [beqTy, h_keys_beq]
    exact groupedFrame_unify_rejects_of_normalized st (n + 1)
      row1 row2
      (applySubst st.subst n row1)
      (applySubst st.subst n row2)
      keys1 keys2 keys1 keys2
      hleft hright h_ctor_neq h_keys_ne

/-- Tagged metadata mismatch rejects unification. -/
theorem tagged_metadata_mismatch (st : UnifyState) :
    unify st 1
      (.tagged .int [("unit", 1)])
      (.tagged .int [("unit", 2)])
      = .err "type mismatch" := by
  have h_neq :
      (Ty.tagged .int [("unit", 1)] == Ty.tagged .int [("unit", 2)]) = false := by
    native_decide
  simp [unify, applySubstCompat, applySubst, h_neq]

/-- Tagged metadata mismatch rejects unification at any successor fuel. -/
theorem tagged_metadata_mismatch_any_fuel (st : UnifyState) (fuel : Nat) :
    unify st (fuel + 1)
      (.tagged .int [("unit", 1)])
      (.tagged .int [("unit", 2)])
      = .err "type mismatch" := by
  have h_neq :
      (Ty.tagged .int [("unit", 1)] == Ty.tagged .int [("unit", 2)]) = false := by
    native_decide
  cases fuel with
  | zero =>
      unfold unify
      simp [applySubstCompat, applySubst, h_neq]
  | succ fuel' =>
      have h_int : applySubst st.subst fuel' .int = .int := applySubst_int st.subst fuel'
      unfold unify
      simp [applySubstCompat, applySubst, h_int, h_neq]

/-- Tagged metadata mismatch rejects unification at any successor fuel, for
    arbitrary inner types. -/
theorem tagged_metadata_mismatch_any_inner_any_fuel
    (st : UnifyState) (fuel : Nat)
    (inner1 inner2 : Ty) (tags1 tags2 : List (String × Int))
    (h_tags_ne : tags1 ≠ tags2) :
    unify st (fuel + 1)
      (.tagged inner1 tags1)
      (.tagged inner2 tags2)
      = .err "type mismatch" := by
  have h_tags_beq : (tags1 == tags2) = false := by
    cases hbeq : (tags1 == tags2) with
    | false => rfl
    | true =>
      have h_eq : tags1 = tags2 := by simpa using hbeq
      exact (h_tags_ne h_eq).elim
  cases fuel with
  | zero =>
    have hleft :
        applySubst st.subst 0 (.tagged inner1 tags1) =
          .tagged inner1 tags1 := rfl
    have hright :
        applySubst st.subst 0 (.tagged inner2 tags2) =
          .tagged inner2 tags2 := rfl
    have h_ctor_neq :
        (applySubst st.subst 0 (.tagged inner1 tags1) ==
          applySubst st.subst 0 (.tagged inner2 tags2)) = false := by
      show beqTy (Ty.tagged inner1 tags1) (Ty.tagged inner2 tags2) = false
      simp [beqTy, h_tags_beq]
    exact tagged_unify_rejects_of_normalized st 0
      inner1 inner2 inner1 inner2
      tags1 tags2 tags1 tags2
      hleft hright h_ctor_neq h_tags_ne
  | succ n =>
    have hleft :
        applySubst st.subst (n + 1) (.tagged inner1 tags1) =
          .tagged (applySubst st.subst n inner1) tags1 := by
      simp [applySubst]
    have hright :
        applySubst st.subst (n + 1) (.tagged inner2 tags2) =
          .tagged (applySubst st.subst n inner2) tags2 := by
      simp [applySubst]
    have h_ctor_neq :
        (applySubst st.subst (n + 1) (.tagged inner1 tags1) ==
          applySubst st.subst (n + 1) (.tagged inner2 tags2)) = false := by
      show
        beqTy
          (Ty.tagged (applySubst st.subst n inner1) tags1)
          (Ty.tagged (applySubst st.subst n inner2) tags2) = false
      simp [beqTy, h_tags_beq]
    exact tagged_unify_rejects_of_normalized st (n + 1)
      inner1 inner2
      (applySubst st.subst n inner1)
      (applySubst st.subst n inner2)
      tags1 tags2 tags1 tags2
      hleft hright h_ctor_neq h_tags_ne

/-- GroupedFrame inner-type mismatch rejects unification when keys match. -/
theorem groupedFrame_inner_mismatch (st : UnifyState) :
    unify st 2
      (.groupedFrame .int ["a"])
      (.groupedFrame .bool ["a"])
      = .err "type mismatch" := by
  have h_neq :
      (Ty.groupedFrame .int ["a"] == Ty.groupedFrame .bool ["a"]) = false := by
    native_decide
  have h_int_bool_beq : (Ty.int == Ty.bool) = false := by
    simp [BEq.beq, beqTy]
  have h_inner : unify st 1 .int .bool = .err "type mismatch" := by
    simp [unify, applySubstCompat, applySubst, h_int_bool_beq]
  unfold unify
  simp [applySubstCompat, applySubst, h_neq, h_inner]

/-- Tagged inner-type mismatch rejects unification when metadata matches. -/
theorem tagged_inner_mismatch (st : UnifyState) :
    unify st 2
      (.tagged .int [("unit", 1)])
      (.tagged .bool [("unit", 1)])
      = .err "type mismatch" := by
  have h_neq :
      (Ty.tagged .int [("unit", 1)] == Ty.tagged .bool [("unit", 1)]) = false := by
    native_decide
  have h_int_bool_beq : (Ty.int == Ty.bool) = false := by
    simp [BEq.beq, beqTy]
  have h_inner : unify st 1 .int .bool = .err "type mismatch" := by
    simp [unify, applySubstCompat, applySubst, h_int_bool_beq]
  unfold unify
  simp [applySubstCompat, applySubst, h_neq, h_inner]

/-- GroupedFrame and non-grouped types do not unify. -/
theorem groupedFrame_non_grouped_mismatch (st : UnifyState) :
    unify st 1
      (.groupedFrame .int ["a"])
      .int
      = .err "type mismatch" := by
  have h_neq : (Ty.groupedFrame .int ["a"] == Ty.int) = false := by
    native_decide
  unfold unify
  simp [applySubstCompat, applySubst, h_neq]

/-- Tagged and non-tagged types do not unify. -/
theorem tagged_non_tagged_mismatch (st : UnifyState) :
    unify st 1
      (.tagged .int [("unit", 1)])
      .int
      = .err "type mismatch" := by
  have h_neq : (Ty.tagged .int [("unit", 1)] == Ty.int) = false := by
    native_decide
  unfold unify
  simp [applySubstCompat, applySubst, h_neq]

/-- Boundary-sensitive sites where grouped/tagged metadata checks are enforced. -/
inductive GroupedTaggedBoundarySite : Type where
  | letAnnotation
  | callArgument
  | returnAnnotation
  | ascription

/-- Site-level grouped/tagged boundary policy.
    Current scope:
    - grouped keys must match when grouped wrappers are expected/actual
    - tagged metadata must match when tagged wrappers are expected/actual
    - non-wrapper actuals are rejected when grouped/tagged wrappers are expected
    - otherwise allowed (outside this boundary surface) -/
def groupedTaggedBoundaryAllows (expected actual : Ty) : Bool :=
  match expected, actual with
  | .groupedFrame _ expectedKeys, .groupedFrame _ actualKeys =>
      expectedKeys == actualKeys
  | .groupedFrame _ _, _ => false
  | .tagged _ expectedTags, .tagged _ actualTags =>
      expectedTags == actualTags
  | .tagged _ _, _ => false
  | _, _ => true

/-- Site-level wrapper for grouped/tagged boundary checks. -/
def groupedTaggedBoundaryAllowsAtSite
    (_site : GroupedTaggedBoundarySite) (expected actual : Ty) : Bool :=
  groupedTaggedBoundaryAllows expected actual

/-- Grouped/tagged boundary policy is currently site-invariant. -/
theorem grouped_tagged_boundary_policy_site_invariant
    (site1 site2 : GroupedTaggedBoundarySite) (expected actual : Ty) :
    groupedTaggedBoundaryAllowsAtSite site1 expected actual =
      groupedTaggedBoundaryAllowsAtSite site2 expected actual := by
  cases site1 <;> cases site2 <;> rfl

/-- Distinct grouped key lists are rejected by boundary policy. -/
theorem grouped_tagged_boundary_rejects_grouped_key_mismatch :
    groupedTaggedBoundaryAllows
      (.groupedFrame .int ["a"])
      (.groupedFrame .int ["b"])
      = false := by
  native_decide

/-- Distinct tagged metadata lists are rejected by boundary policy. -/
theorem grouped_tagged_boundary_rejects_tagged_metadata_mismatch :
    groupedTaggedBoundaryAllows
      (.tagged .int [("unit", 1)])
      (.tagged .int [("unit", 2)])
      = false := by
  native_decide

/-- Non-wrapper actuals are rejected when grouped wrappers are expected. -/
theorem grouped_tagged_boundary_rejects_non_wrapper_actual :
    groupedTaggedBoundaryAllows
      (.groupedFrame .int ["a"])
      .int
      = false := by
  native_decide

/-- Packaged grouped/tagged boundary surface slice:
    site invariance + grouped/tagged metadata rejection and non-wrapper
    rejection, with closure to concrete mismatch/reflexive unifier witnesses. -/
theorem grouped_tagged_boundary_surface_slice
    (st : UnifyState) (site : GroupedTaggedBoundarySite) :
    (groupedTaggedBoundaryAllowsAtSite site
      (.groupedFrame .int ["a"])
      (.groupedFrame .int ["b"]) = false)
    ∧
    (groupedTaggedBoundaryAllowsAtSite site
      (.tagged .int [("unit", 1)])
      (.tagged .int [("unit", 2)]) = false)
    ∧
    (groupedTaggedBoundaryAllowsAtSite site
      (.groupedFrame .int ["a"])
      .int = false)
    ∧
    (unify st 1
      (.groupedFrame (.row (.mk (.cons "a" .int .nil) none)) ["a"])
      (.groupedFrame (.row (.mk (.cons "a" .int .nil) none)) ["b"])
      = .err "type mismatch")
    ∧
    (unify st 1
      (.tagged .int [("unit", 1)])
      (.tagged .int [("unit", 2)])
      = .err "type mismatch")
    ∧
    (unify st 1
      (.groupedFrame .int ["a"])
      .int
      = .err "type mismatch")
    ∧
    (unify st 2
      (.groupedFrame .int ["a"])
      (.groupedFrame .int ["a"])
      = .ok st)
    ∧
    (unify st 2
      (.tagged .int [("unit", 1)])
      (.tagged .int [("unit", 1)])
      = .ok st) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases site <;> exact grouped_tagged_boundary_rejects_grouped_key_mismatch
  · cases site <;> exact grouped_tagged_boundary_rejects_tagged_metadata_mismatch
  · cases site <;> exact grouped_tagged_boundary_rejects_non_wrapper_actual
  · exact groupedFrame_keys_mismatch st
  · exact tagged_metadata_mismatch st
  · exact groupedFrame_non_grouped_mismatch st
  · exact groupedFrame_unifies_with_self st 1 .int ["a"]
  · exact tagged_unifies_with_self st 1 .int [("unit", 1)]

/-- `GroupedFrame` free vars are exactly the row type free vars. -/
theorem groupedFrame_free_vars (rowTy : Ty) (keys : List Label) :
    freeTypeVars (.groupedFrame rowTy keys) = freeTypeVars rowTy /\
      freeRowVars (.groupedFrame rowTy keys) = freeRowVars rowTy := by
  simp [freeTypeVars, freeRowVars]

/-- `Tagged` free vars are exactly the inner type free vars. -/
theorem tagged_free_vars (inner : Ty) (tags : List (String × Int)) :
    freeTypeVars (.tagged inner tags) = freeTypeVars inner /\
      freeRowVars (.tagged inner tags) = freeRowVars inner := by
  simp [freeTypeVars, freeRowVars]
