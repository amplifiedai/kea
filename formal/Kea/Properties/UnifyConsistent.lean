/-
  Kea.Properties.UnifyConsistent — Unification consistency.

  Maps to Rust proptests:
    - `unify_consistent_substitution` (prop_tests.rs:203)
    - `unify_rows_consistent` (prop_tests.rs:224)

  This module currently proves the BEq fast-path consistency core:
  when unify succeeds via the equality shortcut, both sides resolve equally.

  IMPORTANT: The original full statement used the same `fuel` parameter for both
  the unification call (`fuel + 1`) and the conclusion (`fuel`), which is
  FALSE in the fuel model — counterexample:
    a = List(Var(0)), b = List(Int), st.subst = empty, fuel = 1
    unify st 2 a b succeeds (binds 0 → Int)
    applySubst st'.subst 1 a = List(Var(0))  (fuel 0 on inner var, identity!)
    applySubst st'.subst 1 b = List(Int)
    List(Var(0)) ≠ List(Int)

  Full non-BEq consistency over arbitrary substitution states is also
  non-robust in the fuel model (especially with cyclic row substitutions).
  This module keeps the proved BEq-fast-path theorem, which is the stable core.
-/

import Kea.Unify
import Kea.Properties.UnifyReflexive
import Kea.Properties.SubstIdempotent
import Kea.Properties.SubstBridge

/-- BEq-shortcut consistency: when unify succeeds via the equality fast-path,
    both sides are definitionally equal after substitution at that fuel.

    This is the proved core needed by the broader consistency theorem.
    Full consistency for all non-BEq success arms is deferred to
    substitution-composition lemmas in `SubstCompose`. -/
theorem unifyConsistentBeq (st : UnifyState) (fuel : Nat) (a b : Ty) (st' : UnifyState)
    (h_beq : (applySubst st.subst fuel a == applySubst st.subst fuel b) = true) :
    unify st (fuel + 1) a b = .ok st' →
    ∃ fuel', applySubst st'.subst fuel' a = applySubst st'.subst fuel' b := by
  intro h
  -- unify takes the BEq branch and returns `.ok st`
  simp [unify, h_beq] at h
  have h_types_eq := beqTy_sound _ _ h_beq
  rw [← h]
  exact ⟨fuel, h_types_eq⟩

/-- Variable-binding consistency under an idempotent result substitution.
    This gives a stable non-BEq branch theorem when the resulting substitution
    is fully resolved on its range. -/
theorem bindTypeVarConsistentIdempotent
    (st : UnifyState) (v : TypeVarId) (ty : Ty) (fuel : Nat) (st' : UnifyState)
    (h_bind : bindTypeVar st v ty fuel = .ok st')
    (h_idemp : st'.subst.Idempotent) :
    applySubst st'.subst (fuel + 1) (.var v) = applySubst st'.subst (fuel + 1) ty := by
  unfold bindTypeVar at h_bind
  split at h_bind
  · -- no-op branch: ty == var v
    simp [UnifyResult.ok.injEq] at h_bind
    rw [← h_bind]
    have h_eq : ty = .var v := beqTy_sound _ _ ‹_›
    simp [h_eq]
  · split at h_bind
    · -- occurs check failure can't produce .ok
      exact absurd h_bind (by intro h'; exact UnifyResult.noConfusion h')
    · -- real binding branch
      simp [UnifyResult.ok.injEq] at h_bind
      have h_subst : st'.subst = st.subst.bindType v ty := by
        cases h_bind
        rfl
      have h_idemp' : (st.subst.bindType v ty).Idempotent := by
        rw [← h_subst]
        exact h_idemp
      have h_lookup : (st.subst.bindType v ty).typeMap v = some ty := by
        unfold Subst.bindType; simp [BEq.beq]
      have h_range := h_idemp'.typeRange v ty h_lookup
      have h_noop_fuel :=
        (applySubst_noop (st.subst.bindType v ty) fuel).1 ty h_range.1 h_range.2
      have h_noop_succ :=
        (applySubst_noop (st.subst.bindType v ty) (fuel + 1)).1 ty h_range.1 h_range.2
      rw [h_subst]
      calc
        applySubst (st.subst.bindType v ty) (fuel + 1) (.var v)
            = applySubst (st.subst.bindType v ty) fuel ty := by
                simp [applySubst, Subst.bindType, BEq.beq]
        _ = ty := h_noop_fuel
        _ = applySubst (st.subst.bindType v ty) (fuel + 1) ty := by
                symm; exact h_noop_succ

/-- WF variant of `bindTypeVarConsistentIdempotent`.
    This removes fuel from the conclusion by using bounded WF substitution. -/
theorem bindTypeVarConsistentWFBoundedIdempotent
    (st : UnifyState) (v : TypeVarId) (ty : Ty) (fuel : Nat) (st' : UnifyState)
    (h_bind : bindTypeVar st v ty fuel = .ok st')
    (h_idemp : st'.subst.Idempotent) :
    let ac := Subst.acyclicOfIdempotent h_idemp
    applySubstBounded st'.subst ac 2 1 (.var v) = applySubstBounded st'.subst ac 2 1 ty := by
  unfold bindTypeVar at h_bind
  split at h_bind
  · -- no-op branch: ty == var v
    simp [UnifyResult.ok.injEq] at h_bind
    cases h_bind
    have h_eq : ty = .var v := beqTy_sound _ _ ‹_›
    simp [h_eq]
  · split at h_bind
    · -- occurs check failure can't produce .ok
      exact absurd h_bind (by intro h'; exact UnifyResult.noConfusion h')
    · -- real binding branch
      simp [UnifyResult.ok.injEq] at h_bind
      cases h_bind
      simpa using applySubstBounded_bindType_consistent_of_idempotent st.subst v ty h_idemp

/-- Full WF variant of `bindTypeVarConsistentIdempotent`. -/
theorem bindTypeVarConsistentWFIdempotent
    (st : UnifyState) (v : TypeVarId) (ty : Ty) (fuel : Nat) (st' : UnifyState)
    (h_bind : bindTypeVar st v ty fuel = .ok st')
    (h_idemp : st'.subst.Idempotent) :
    let ac := Subst.acyclicOfIdempotent h_idemp
    applySubstWF st'.subst ac (.var v) = applySubstWF st'.subst ac ty := by
  unfold bindTypeVar at h_bind
  split at h_bind
  · -- no-op branch: ty == var v
    simp [UnifyResult.ok.injEq] at h_bind
    cases h_bind
    have h_eq : ty = .var v := beqTy_sound _ _ ‹_›
    simp [h_eq]
  · split at h_bind
    · -- occurs check failure can't produce .ok
      exact absurd h_bind (by intro h'; exact UnifyResult.noConfusion h')
    · -- real binding branch
      simp [UnifyResult.ok.injEq] at h_bind
      cases h_bind
      simpa using applySubstWF_bindType_consistent_of_idempotent st.subst v ty h_idemp

-- Bounded witness: a successful non-BEq unification can fail to reach a
-- common normal form within large fuel windows under cyclic row substitutions.
private def unifyConsistentCounterexample : Bool :=
  let s : Subst :=
    { typeMap := fun _ => none
      rowMap := fun v =>
        if v == 0 then some (Row.mk (.cons "a" .int .nil) (some 1))
        else if v == 1 then some (Row.mk .nil (some 0))
        else none }
  let st : UnifyState :=
    { subst := s, lacks := Lacks.empty, traitBounds := [], nextTypeVar := 2, nextRowVar := 2 }
  let a : Ty := Ty.var 0
  let b : Ty := Ty.anonRecord (Row.mk .nil (some 0))
  match unify st 4 a b with
  | .err _ => false
  | .ok st' =>
    -- No witness up to 200 fuel steps.
    !((List.range 201).any (fun f => applySubst st'.subst f a == applySubst st'.subst f b))

private theorem unifyConsistentCounterexample_true :
    unifyConsistentCounterexample = true := by
  native_decide

-- Positive bounded evidence: on a small acyclic substitution sample,
-- successful unification remains consistency-preserving (within bounded fuel).
private def unifyConsistentAcyclicSample : Bool :=
  let concatMap := fun {α β} (xs : List α) (f : α → List β) =>
    xs.foldr (fun x acc => f x ++ acc) []
  let tys : List Ty :=
    [Ty.int, Ty.bool, Ty.var 0, Ty.var 1, Ty.list Ty.int, Ty.list (Ty.var 0)]
  let s0 : Subst := Subst.empty
  let s1 : Subst :=
    { typeMap := fun _ => none
      rowMap := fun v => if v == 0 then some (Row.mk .nil (some 1)) else none }
  let s2 : Subst :=
    { typeMap := fun _ => none
      rowMap := fun v => if v == 1 then some (Row.mk (.cons "a" .int .nil) none) else none }
  let substs : List Subst := [s0, s1, s2]
  let mkState := fun s =>
    ({ subst := s, lacks := Lacks.empty, traitBounds := [], nextTypeVar := 2, nextRowVar := 2 } : UnifyState)
  let consistentUpTo := fun (st' : UnifyState) (a b : Ty) (n : Nat) =>
    (List.range (n + 1)).any (fun f => applySubst st'.subst f a == applySubst st'.subst f b)
  let checkOne := fun (s : Subst) (fuel : Nat) (a b : Ty) =>
    match unify (mkState s) (fuel + 1) a b with
    | .err _ => true
    | .ok st' => consistentUpTo st' a b 10
  (concatMap substs fun s =>
    (concatMap [0, 1, 2, 3] fun fuel =>
      (concatMap tys fun a => tys.map fun b => checkOne s fuel a b))).all id

private theorem unifyConsistentAcyclicSample_true :
    unifyConsistentAcyclicSample = true := by
  native_decide
