/-
  Kea.Unify — Unification algorithm.

  Mirrors: rill-infer/src/lib.rs:200-487
    - Unifier struct (substitution + lacks + errors + fresh vars)
    - unify: structural type unification
    - unify_rows: Rémy-style row unification

  Design: Returns Either (success with updated state) or error.
  The Rust code mutates in place and accumulates errors;
  the Lean model uses a pure state-passing style.
-/

import Kea.Ty
import Kea.Substitution
import Kea.OccursCheck
import Kea.LacksConstraints

-- =========================================================================
-- Unification state
-- =========================================================================

/-- Trait bounds on type variables: (TypeVarId, trait name) pairs.
    Accumulated during instantiation, checked after inference resolves types. -/
abbrev TraitBounds := List (TypeVarId × String)

/-- Unification state threaded through the algorithm. -/
structure UnifyState where
  /-- Type and row variable substitution. -/
  subst : Subst
  /-- Lacks constraints on row variables. -/
  lacks : Lacks
  /-- Trait bounds accumulated during instantiation. -/
  traitBounds : TraitBounds
  /-- Next fresh type variable ID. -/
  nextTypeVar : Nat
  /-- Next fresh row variable ID. -/
  nextRowVar : Nat

namespace UnifyState

/-- Initial empty state. -/
def empty : UnifyState where
  subst := Subst.empty
  lacks := Lacks.empty
  traitBounds := []
  nextTypeVar := 0
  nextRowVar := 0

/-- Add a trait bound on a type variable. -/
def addTraitBound (st : UnifyState) (tv : TypeVarId) (traitName : String) : UnifyState :=
  { st with traitBounds := (tv, traitName) :: st.traitBounds }

/-- Generate a fresh type variable. -/
def freshTypeVar (s : UnifyState) : TypeVarId × UnifyState :=
  (s.nextTypeVar, { s with nextTypeVar := s.nextTypeVar + 1 })

/-- Generate a fresh row variable. -/
def freshRowVar (s : UnifyState) : RowVarId × UnifyState :=
  (s.nextRowVar, { s with nextRowVar := s.nextRowVar + 1 })

end UnifyState

/-- Result of a unification step. -/
inductive UnifyResult where
  | ok  : UnifyState → UnifyResult
  | err : String → UnifyResult

-- =========================================================================
-- Row field decomposition (merge-style on sorted fields)
-- =========================================================================

/-- Decompose two sorted field lists into (common, only-left, only-right).
    Helper: accumulate into lists, reverse common at the end. -/
def decomposeFieldsGo
    : RowFields → RowFields → List (Label × Ty × Ty) → RowFields → RowFields
    → List (Label × Ty × Ty) × RowFields × RowFields
  | .nil, .nil, common, onlyL, onlyR => (common.reverse, onlyL, onlyR)
  | .nil, .cons l ty rest, common, onlyL, onlyR =>
    decomposeFieldsGo .nil rest common onlyL (.cons l ty onlyR)
  | .cons l ty rest, .nil, common, onlyL, onlyR =>
    decomposeFieldsGo rest .nil common (.cons l ty onlyL) onlyR
  | .cons l1 ty1 rest1, .cons l2 ty2 rest2, common, onlyL, onlyR =>
    if l1 < l2 then
      decomposeFieldsGo rest1 (.cons l2 ty2 rest2) common (.cons l1 ty1 onlyL) onlyR
    else if l2 < l1 then
      decomposeFieldsGo (.cons l1 ty1 rest1) rest2 common onlyL (.cons l2 ty2 onlyR)
    else -- l1 == l2
      decomposeFieldsGo rest1 rest2 ((l1, ty1, ty2) :: common) onlyL onlyR

/-- Decompose two sorted field lists into (common, only-left, only-right). -/
def decomposeFields (left right : RowFields)
    : List (Label × Ty × Ty) × RowFields × RowFields :=
  decomposeFieldsGo left right [] .nil .nil

/-- Check if any field in `fields` violates a lacks constraint on `rv`. -/
def lacksViolation (lc : Lacks) (rv : RowVarId) (fields : RowFields) : Bool :=
  match fields with
  | .nil => false
  | .cons l _ rest => Lacks.lacksLabel lc rv l || lacksViolation lc rv rest

-- =========================================================================
-- Bind a type variable (with occurs check)
-- =========================================================================

/-- Bind a type variable to a type, checking for occurs (infinite types). -/
def bindTypeVar (st : UnifyState) (v : TypeVarId) (ty : Ty) (fuel : Nat) : UnifyResult :=
  -- Binding v to itself is a no-op
  if ty == .var v then .ok st
  else if occursIn v (applySubstCompat st.subst fuel ty) then
    .err s!"infinite type: variable {v} occurs in type"
  else
    .ok { st with subst := st.subst.bindType v ty }

-- =========================================================================
-- Unify (fuel-based)
-- =========================================================================

mutual
  /--
  Unify two types. Returns updated state on success, error on failure.
  Uses fuel to ensure termination.
  -/
  def unify (st : UnifyState) (fuel : Nat) (a b : Ty) : UnifyResult :=
    match fuel with
    | 0 => .err "out of fuel during unification"
    | fuel + 1 =>
      let a' := applySubstCompat st.subst fuel a
      let b' := applySubstCompat st.subst fuel b
      if a' == b' then .ok st
      else match a', b' with
      | .var v, _ => bindTypeVar st v b' fuel
      | _, .var v => bindTypeVar st v a' fuel
      | .dynamic, _ | _, .dynamic => .ok st
      | .list x, .list y => unify st fuel x y
      | .set x, .set y => unify st fuel x y
      | .option x, .option y => unify st fuel x y
      | .map k1 v1, .map k2 v2 =>
        match unify st fuel k1 k2 with
        | .ok st' => unify st' fuel v1 v2
        | e => e
      | .result ok1 err1, .result ok2 err2 =>
        match unify st fuel ok1 ok2 with
        | .ok st' => unify st' fuel err1 err2
        | e => e
      | .existential b1 a1, .existential b2 a2 =>
        if b1 == b2 then unifyTyList st fuel a1 a2
        else .err "type mismatch"
      | .fixedSizeList e1 d1, .fixedSizeList e2 d2 =>
        if d1 == d2 then unify st fuel e1 e2
        else .err "type mismatch"
      | .tensor e1 sh1, .tensor e2 sh2 =>
        if sh1 == sh2 then unify st fuel e1 e2
        else .err "type mismatch"
      | .sum n1 args1, .sum n2 args2 =>
        if n1 == n2 then unifyTyList st fuel args1 args2
        else .err "type mismatch"
      | .opaque n1 params1, .opaque n2 params2 =>
        if n1 == n2 then unifyTyList st fuel params1 params2
        else .err "type mismatch"
      | .function params1 ret1, .function params2 ret2 =>
        match unifyTyList st fuel params1 params2 with
        | .ok st' => unify st' fuel ret1 ret2
        | e => e
      | .forall _ body1, .forall _ body2 =>
        -- Runtime behavior canonicalizes quantified binders (alpha-equivalent
        -- names and vacuous binders do not block compatibility), so the
        -- simplified model unifies on quantified bodies directly.
        unify st fuel body1 body2
      | .app f1 args1, .app f2 args2 =>
        match unify st fuel f1 f2 with
        | .ok st' => unifyTyList st' fuel args1 args2
        | e => e
      | .constructor n1 fixed1 arity1, .constructor n2 fixed2 arity2 =>
        if n1 == n2 && arity1 == arity2 then unifyTyList st fuel fixed1 fixed2
        else .err "type mismatch"
      | .tuple elems1, .tuple elems2 =>
        unifyTyList st fuel elems1 elems2
      | .row r1, .row r2 => unifyRows st fuel r1 r2
      | .anonRecord r1, .anonRecord r2 => unifyRows st fuel r1 r2
      -- Phase 2: named records unify if same name and rows unify
      | .record n1 r1, .record n2 r2 =>
        if n1 == n2 then unifyRows st fuel r1 r2
        else .err s!"record type mismatch: {n1} vs {n2}"
      -- Phase 2: named record unifies with anonymous record (structural projection)
      | .record _ r1, .anonRecord r2 => unifyRows st fuel r1 r2
      | .anonRecord r1, .record _ r2 => unifyRows st fuel r1 r2
      -- Phase 2: DataFrame(S1) unifies if inner types unify
      | .dataframe s1, .dataframe s2 => unify st fuel s1 s2
      | .groupedFrame r1 k1, .groupedFrame r2 k2 =>
        if k1 == k2 then unify st fuel r1 r2
        else .err "type mismatch"
      | .tagged inner1 tags1, .tagged inner2 tags2 =>
        if tags1 == tags2 then unify st fuel inner1 inner2
        else .err "type mismatch"
      -- Phase 3: Column(T) unifies if inner types unify
      | .column a, .column b => unify st fuel a b
      -- Phase 5: Stream(T) unifies if element types unify
      | .stream a, .stream b => unify st fuel a b
      | .task a, .task b => unify st fuel a b
      | .actor a, .actor b => unify st fuel a b
      | .arc a, .arc b => unify st fuel a b
      | _, _ => .err "type mismatch"
  termination_by fuel
  decreasing_by all_goals omega

  /-- Unify two type lists element-wise. -/
  def unifyTyList (st : UnifyState) (fuel : Nat) (a b : TyList) : UnifyResult :=
    match fuel with
    | 0 => .err "out of fuel"
    | fuel + 1 =>
      match a, b with
      | .nil, .nil => .ok st
      | .cons x xs, .cons y ys =>
        match unify st fuel x y with
        | .ok st' => unifyTyList st' fuel xs ys
        | e => e
      | _, _ => .err "type list length mismatch"
  termination_by fuel
  decreasing_by all_goals omega

  /--
  Rémy-style row unification (KERNEL §2.2).
  -/
  def unifyRows (st : UnifyState) (fuel : Nat) (r1 r2 : Row) : UnifyResult :=
    match fuel with
    | 0 => .err "out of fuel"
    | fuel + 1 =>
      let r1' := applySubstRowCompat st.subst fuel r1
      let r2' := applySubstRowCompat st.subst fuel r2
      let (common, onlyLeft, onlyRight) := decomposeFields r1'.fields r2'.fields
      match unifyCommonFields st fuel common with
      | .err e => .err e
      | .ok st' =>
        match r1'.rest, r2'.rest with
        | none, none =>
          if RowFields.length onlyLeft > 0 || RowFields.length onlyRight > 0 then
            .err "row mismatch: extra fields in closed rows"
          else .ok st'
        | some rv, none =>
          if RowFields.length onlyLeft > 0 then
            .err "row mismatch: closed row missing fields"
          else if lacksViolation st'.lacks rv onlyRight then
            .err "lacks constraint violation"
          else
            .ok { st' with subst := st'.subst.bindRow rv (Row.closed onlyRight) }
        | none, some rv =>
          if RowFields.length onlyRight > 0 then
            .err "row mismatch: closed row has extra fields"
          else if lacksViolation st'.lacks rv onlyLeft then
            .err "lacks constraint violation"
          else
            .ok { st' with subst := st'.subst.bindRow rv (Row.closed onlyLeft) }
        | some rv1, some rv2 =>
          if rv1 == rv2 then
            if RowFields.length onlyLeft > 0 || RowFields.length onlyRight > 0 then
              .err "row mismatch: same variable but different extra fields"
            else .ok st'
          else
            if lacksViolation st'.lacks rv1 onlyRight then
              .err "lacks constraint violation on row var 1"
            else if lacksViolation st'.lacks rv2 onlyLeft then
              .err "lacks constraint violation on row var 2"
            else
              let (r3, st'') := st'.freshRowVar
              let lacks' := Lacks.transfer st''.lacks rv1 r3 |> (fun l => Lacks.transfer l rv2 r3)
              let allLabels := RowFields.labels r1'.fields ++ RowFields.labels r2'.fields
              let lacks'' := allLabels.foldl (fun acc l => Lacks.addLacks acc r3 l) lacks'
              let subst' := Subst.bindRow (Subst.bindRow st''.subst rv1 (Row.mkOpen onlyRight r3)) rv2 (Row.mkOpen onlyLeft r3)
              .ok { st'' with subst := subst', lacks := lacks'' }
  termination_by fuel
  decreasing_by all_goals omega

  /-- Unify common fields (fields with matching labels). -/
  def unifyCommonFields (st : UnifyState) (fuel : Nat)
      (common : List (Label × Ty × Ty)) : UnifyResult :=
    match fuel with
    | 0 => .err "out of fuel"
    | fuel + 1 =>
      match common with
      | [] => .ok st
      | (_, ty1, ty2) :: rest =>
        match unify st fuel ty1 ty2 with
        | .ok st' => unifyCommonFields st' fuel rest
        | e => e
  termination_by fuel
  decreasing_by all_goals omega
end
