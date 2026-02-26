/-
  Kea.Substitution — Substitution definition and application.

  Mirrors: rill-types/src/lib.rs:506-608 (Substitution, apply, apply_row)

  Design: Function-based substitution rather than BTreeMap for simpler proofs.
  A substitution maps type variable IDs to optional types and row variable IDs
  to optional rows.
-/

import Kea.Ty
import Kea.FreeVars

/-- A substitution maps type variables and row variables to their resolved types/rows. -/
structure Subst where
  /-- Map type variable to its resolved type, or `none` if unresolved. -/
  typeMap : TypeVarId → Option Ty
  /-- Map row variable to its resolved row, or `none` if unresolved. -/
  rowMap  : RowVarId → Option Row

namespace Subst

/-- The empty substitution (all variables unresolved). -/
def empty : Subst where
  typeMap := fun _ => none
  rowMap  := fun _ => none

/-- Bind a type variable to a type. -/
def bindType (s : Subst) (v : TypeVarId) (ty : Ty) : Subst where
  typeMap := fun w => if w == v then some ty else s.typeMap w
  rowMap  := s.rowMap

/-- Bind a row variable to a row. -/
def bindRow (s : Subst) (v : RowVarId) (r : Row) : Subst where
  typeMap := s.typeMap
  rowMap  := fun w => if w == v then some r else s.rowMap w

end Subst

-- =========================================================================
-- Apply substitution (fuel-based to handle transitive chains)
-- =========================================================================

/-- Fuel for termination of transitive substitution application. -/
def defaultFuel : Nat := 100

mutual
  /-- Apply a substitution to a type, resolving all bound variables transitively. -/
  def applySubst (s : Subst) (fuel : Nat) (ty : Ty) : Ty :=
    match fuel with
    | 0 => ty  -- out of fuel, return as-is
    | fuel + 1 =>
      match ty with
      | .var v =>
        match s.typeMap v with
        | some resolved => applySubst s fuel resolved  -- transitive resolution
        | none => .var v
      | .int => .int
      | .intN w sgn => .intN w sgn
      | .float => .float
      | .floatN w => .floatN w
      | .decimal p sc => .decimal p sc
      | .bool => .bool
      | .string => .string
      | .html => .html
      | .markdown => .markdown
      | .atom => .atom
      | .date => .date
      | .dateTime => .dateTime
      | .unit => .unit
      | .list inner => .list (applySubst s fuel inner)
      | .map k v => .map (applySubst s fuel k) (applySubst s fuel v)
      | .set inner => .set (applySubst s fuel inner)
      | .option inner => .option (applySubst s fuel inner)
      | .result ok err => .result (applySubst s fuel ok) (applySubst s fuel err)
      | .existential bounds assoc => .existential bounds (applySubstTyList s fuel assoc)
      | .fixedSizeList inner d => .fixedSizeList (applySubst s fuel inner) d
      | .tensor inner shape => .tensor (applySubst s fuel inner) shape
      | .sum name args => .sum name (applySubstTyList s fuel args)
      | .opaque name params => .opaque name (applySubstTyList s fuel params)
      | .record name r => .record name (applySubstRow s fuel r)
      | .anonRecord r => .anonRecord (applySubstRow s fuel r)
      | .dataframe inner => .dataframe (applySubst s fuel inner)
      | .dynamic => .dynamic
      | .groupedFrame inner keys => .groupedFrame (applySubst s fuel inner) keys
      | .tagged inner tags => .tagged (applySubst s fuel inner) tags
      | .column inner => .column (applySubst s fuel inner)
      | .stream inner => .stream (applySubst s fuel inner)
      | .task inner => .task (applySubst s fuel inner)
      | .actor inner => .actor (applySubst s fuel inner)
      | .arc inner => .arc (applySubst s fuel inner)
      | .function params ret => .function (applySubstTyList s fuel params) (applySubst s fuel ret)
      | .functionEff params (.mk row) ret =>
        let effects' := .mk (applySubstRow s fuel row)
        .functionEff (applySubstTyList s fuel params) effects' (applySubst s fuel ret)
      | .forall vars body => .forall vars (applySubst s fuel body)
      | .app ctor args => .app (applySubst s fuel ctor) (applySubstTyList s fuel args)
      | .constructor name fixedArgs arity => .constructor name (applySubstTyList s fuel fixedArgs) arity
      | .row r => .row (applySubstRow s fuel r)
      | .tuple elems => .tuple (applySubstTyList s fuel elems)

  /-- Apply a substitution to a row type. -/
  def applySubstRow (s : Subst) (fuel : Nat) (r : Row) : Row :=
    match fuel with
    | 0 => r
    | fuel + 1 =>
      match r with
      | .mk fields rest =>
        let resolvedFields := applySubstRowFields s fuel fields
        match rest with
        | none => .mk resolvedFields none
        | some var =>
          match s.rowMap var with
          | none => .mk resolvedFields (some var)
          | some resolvedRow =>
            -- Merge: append our fields with the resolved row's fields
            let tail := applySubstRow s fuel resolvedRow
            match tail with
            | .mk tailFields tailRest =>
              .mk (resolvedFields.append tailFields) tailRest

  /-- Apply a substitution to a list of types. -/
  def applySubstTyList (s : Subst) (fuel : Nat) (tl : TyList) : TyList :=
    match fuel with
    | 0 => tl
    | fuel + 1 =>
      match tl with
      | .nil => .nil
      | .cons t rest => .cons (applySubst s fuel t) (applySubstTyList s fuel rest)

  /-- Apply a substitution to row fields. -/
  def applySubstRowFields (s : Subst) (fuel : Nat) (rf : RowFields) : RowFields :=
    match fuel with
    | 0 => rf
    | fuel + 1 =>
      match rf with
      | .nil => .nil
      | .cons l ty rest => .cons l (applySubst s fuel ty) (applySubstRowFields s fuel rest)

end

/-- Apply a substitution to an effect row. -/
def applySubstEffectRow (s : Subst) (fuel : Nat) (effects : EffectRow) : EffectRow :=
  match effects with
  | .mk row => .mk (applySubstRow s fuel row)

-- Convenience wrappers with default fuel.

/-- Apply substitution with default fuel. -/
def Subst.apply (s : Subst) (ty : Ty) : Ty :=
  applySubst s defaultFuel ty

/-- Apply substitution to a row with default fuel. -/
def Subst.applyRow (s : Subst) (r : Row) : Row :=
  applySubstRow s defaultFuel r

/--
Compatibility wrapper used by unification and inference.
Currently aliases the legacy fuel-based substitution, and can later be
retargeted to WF substitution once bridge lemmas are in place.
-/
abbrev applySubstCompat (s : Subst) (fuel : Nat) (ty : Ty) : Ty :=
  applySubst s fuel ty

/-- Compatibility wrapper for row substitution (see `applySubstCompat`). -/
abbrev applySubstRowCompat (s : Subst) (fuel : Nat) (r : Row) : Row :=
  applySubstRow s fuel r

/-- Compatibility wrapper for effect-row substitution (see `applySubstCompat`). -/
abbrev applySubstEffectRowCompat (s : Subst) (fuel : Nat) (effects : EffectRow) : EffectRow :=
  applySubstEffectRow s fuel effects

@[simp] theorem applySubstCompat_eq (s : Subst) (fuel : Nat) (ty : Ty) :
    applySubstCompat s fuel ty = applySubst s fuel ty := rfl

@[simp] theorem applySubstRowCompat_eq (s : Subst) (fuel : Nat) (r : Row) :
    applySubstRowCompat s fuel r = applySubstRow s fuel r := rfl

@[simp] theorem applySubstEffectRowCompat_eq (s : Subst) (fuel : Nat) (effects : EffectRow) :
    applySubstEffectRowCompat s fuel effects = applySubstEffectRow s fuel effects := rfl

-- =========================================================================
-- Well-founded substitution (rank-bounded recursion; no external fuel)
-- =========================================================================

mutual
  /-- Structural size used in well-founded recursion measures. -/
  private def tySize : Ty → Nat
    | .var _ | .int | .intN _ _ | .float | .floatN _ | .decimal _ _ | .bool | .string | .html | .markdown | .atom | .date | .dateTime | .unit | .dynamic => 1
    | .list inner | .set inner | .option inner | .dataframe inner | .column inner | .stream inner
      | .task inner | .actor inner | .arc inner | .groupedFrame inner _ | .tagged inner _
      | .fixedSizeList inner _ | .tensor inner _ =>
      1 + tySize inner
    | .sum _ args | .opaque _ args => 1 + tyListSize args
    | .existential _ assoc => 1 + tyListSize assoc
    | .map k v | .result k v => 1 + tySize k + tySize v
    | .record _ r | .anonRecord r | .row r => 1 + rowSize r
    | .function params ret => 1 + tyListSize params + tySize ret
    | .functionEff params (.mk row) ret => 2 + tyListSize params + rowSize row + tySize ret
    | .forall _ body => 1 + tySize body
    | .app ctor args => 1 + tySize ctor + tyListSize args
    | .constructor _ fixedArgs _ => 1 + tyListSize fixedArgs
    | .tuple elems => 1 + tyListSize elems

  /-- Structural size used in well-founded recursion measures. -/
  private def rowSize : Row → Nat
    | .mk fields _ => 1 + rowFieldsSize fields

  /-- Structural size used in well-founded recursion measures. -/
  private def tyListSize : TyList → Nat
    | .nil => 1
    | .cons ty rest => 1 + tySize ty + tyListSize rest

  /-- Structural size used in well-founded recursion measures. -/
  private def rowFieldsSize : RowFields → Nat
    | .nil => 1
    | .cons _ ty rest => 1 + tySize ty + rowFieldsSize rest

end

namespace Subst

/--
Acyclicity/ranking invariant for substitution chains.
Each lookup must move to strictly smaller-ranked variables of the same kind.
-/
structure Acyclic (s : Subst) : Type where
  typeRank : TypeVarId → Nat
  rowRank : RowVarId → Nat
  type_decreases :
    ∀ v ty w,
      s.typeMap v = some ty →
      w ∈ freeTypeVars ty →
      typeRank w < typeRank v
  row_decreases :
    ∀ rv r rv',
      s.rowMap rv = some r →
      rv' ∈ freeRowVarsRow r →
      rowRank rv' < rowRank rv

end Subst

private def maxNatList : List Nat → Nat
  | [] => 0
  | x :: xs => max x (maxNatList xs)

private def typeRankBoundTy {s : Subst} (h : Subst.Acyclic s) (ty : Ty) : Nat :=
  maxNatList ((freeTypeVars ty).map h.typeRank)

private def rowRankBoundTy {s : Subst} (h : Subst.Acyclic s) (ty : Ty) : Nat :=
  maxNatList ((freeRowVars ty).map h.rowRank)

private def typeRankBoundRow {s : Subst} (h : Subst.Acyclic s) (r : Row) : Nat :=
  maxNatList ((freeTypeVarsRow r).map h.typeRank)

private def rowRankBoundRow {s : Subst} (h : Subst.Acyclic s) (r : Row) : Nat :=
  maxNatList ((freeRowVarsRow r).map h.rowRank)

private def typeRankBoundTyList {s : Subst} (h : Subst.Acyclic s) (tl : TyList) : Nat :=
  maxNatList ((freeTypeVarsTyList tl).map h.typeRank)

private def rowRankBoundTyList {s : Subst} (h : Subst.Acyclic s) (tl : TyList) : Nat :=
  maxNatList ((freeRowVarsTyList tl).map h.rowRank)

private def typeRankBoundRowFields {s : Subst} (h : Subst.Acyclic s) (rf : RowFields) : Nat :=
  maxNatList ((freeTypeVarsRowFields rf).map h.typeRank)

private def rowRankBoundRowFields {s : Subst} (h : Subst.Acyclic s) (rf : RowFields) : Nat :=
  maxNatList ((freeRowVarsRowFields rf).map h.rowRank)

mutual
  /--
  Well-founded substitution application with rank limits.
  `tlim` and `rlim` bound lookup depth for type/row variable chains.
  -/
  def applySubstBounded (s : Subst) (h : Subst.Acyclic s) (tlim rlim : Nat) (ty : Ty) : Ty :=
    match ty with
    | .var v =>
      if _ : h.typeRank v < tlim then
        match s.typeMap v with
        | some resolved => applySubstBounded s h (h.typeRank v) rlim resolved
        | none => .var v
      else
        .var v
    | .int => .int
    | .intN w sgn => .intN w sgn
    | .float => .float
    | .floatN w => .floatN w
    | .decimal p sc => .decimal p sc
    | .bool => .bool
    | .string => .string
    | .html => .html
    | .markdown => .markdown
    | .atom => .atom
    | .date => .date
    | .dateTime => .dateTime
    | .unit => .unit
    | .list inner => .list (applySubstBounded s h tlim rlim inner)
    | .map k v => .map (applySubstBounded s h tlim rlim k) (applySubstBounded s h tlim rlim v)
    | .set inner => .set (applySubstBounded s h tlim rlim inner)
    | .option inner => .option (applySubstBounded s h tlim rlim inner)
    | .result ok err => .result (applySubstBounded s h tlim rlim ok) (applySubstBounded s h tlim rlim err)
    | .existential bounds assoc => .existential bounds (applySubstTyListBounded s h tlim rlim assoc)
    | .fixedSizeList inner d => .fixedSizeList (applySubstBounded s h tlim rlim inner) d
    | .tensor inner shape => .tensor (applySubstBounded s h tlim rlim inner) shape
    | .sum name args => .sum name (applySubstTyListBounded s h tlim rlim args)
    | .opaque name params => .opaque name (applySubstTyListBounded s h tlim rlim params)
    | .record name r => .record name (applySubstRowBounded s h tlim rlim r)
    | .anonRecord r => .anonRecord (applySubstRowBounded s h tlim rlim r)
    | .dataframe inner => .dataframe (applySubstBounded s h tlim rlim inner)
    | .dynamic => .dynamic
    | .groupedFrame inner keys => .groupedFrame (applySubstBounded s h tlim rlim inner) keys
    | .tagged inner tags => .tagged (applySubstBounded s h tlim rlim inner) tags
    | .column inner => .column (applySubstBounded s h tlim rlim inner)
    | .stream inner => .stream (applySubstBounded s h tlim rlim inner)
    | .task inner => .task (applySubstBounded s h tlim rlim inner)
    | .actor inner => .actor (applySubstBounded s h tlim rlim inner)
    | .arc inner => .arc (applySubstBounded s h tlim rlim inner)
    | .function params ret =>
      .function (applySubstTyListBounded s h tlim rlim params) (applySubstBounded s h tlim rlim ret)
    | .functionEff params (.mk row) ret =>
      let effects' := .mk (applySubstRowBounded s h tlim rlim row)
      .functionEff
        (applySubstTyListBounded s h tlim rlim params)
        effects'
        (applySubstBounded s h tlim rlim ret)
    | .forall vars body =>
      .forall vars (applySubstBounded s h tlim rlim body)
    | .app ctor args =>
      .app (applySubstBounded s h tlim rlim ctor) (applySubstTyListBounded s h tlim rlim args)
    | .constructor name fixedArgs arity =>
      .constructor name (applySubstTyListBounded s h tlim rlim fixedArgs) arity
    | .row r => .row (applySubstRowBounded s h tlim rlim r)
    | .tuple elems => .tuple (applySubstTyListBounded s h tlim rlim elems)
  termination_by (tlim + rlim, tySize ty)
  decreasing_by
    all_goals
      simp_wf
      simp [tySize]
      omega

  /-- Well-founded substitution on rows with rank limits. -/
  def applySubstRowBounded (s : Subst) (h : Subst.Acyclic s) (tlim rlim : Nat) (r : Row) : Row :=
    match r with
    | .mk fields rest =>
      let resolvedFields := applySubstRowFieldsBounded s h tlim rlim fields
      match rest with
      | none => .mk resolvedFields none
      | some rv =>
        if _ : h.rowRank rv < rlim then
          match s.rowMap rv with
          | none => .mk resolvedFields (some rv)
          | some resolvedRow =>
            let tail := applySubstRowBounded s h tlim (h.rowRank rv) resolvedRow
            match tail with
            | .mk tailFields tailRest =>
              .mk (resolvedFields.append tailFields) tailRest
        else
          .mk resolvedFields (some rv)
  termination_by (tlim + rlim, rowSize r)
  decreasing_by
    all_goals
      simp_wf
      simp [rowSize]
      omega

  /-- Well-founded substitution on type lists with rank limits. -/
  def applySubstTyListBounded
      (s : Subst) (h : Subst.Acyclic s) (tlim rlim : Nat) (tl : TyList) : TyList :=
    match tl with
    | .nil => .nil
    | .cons t rest => .cons (applySubstBounded s h tlim rlim t) (applySubstTyListBounded s h tlim rlim rest)
  termination_by (tlim + rlim, tyListSize tl)
  decreasing_by
    all_goals
      simp_wf
      simp [tyListSize]
      omega

  /-- Well-founded substitution on row fields with rank limits. -/
  def applySubstRowFieldsBounded
      (s : Subst) (h : Subst.Acyclic s) (tlim rlim : Nat) (rf : RowFields) : RowFields :=
    match rf with
    | .nil => .nil
    | .cons l ty rest =>
      .cons l (applySubstBounded s h tlim rlim ty) (applySubstRowFieldsBounded s h tlim rlim rest)
  termination_by (tlim + rlim, rowFieldsSize rf)
  decreasing_by
    all_goals
      simp_wf
      simp [rowFieldsSize]
      omega

end

/-- Well-founded substitution for types (no external fuel). -/
def applySubstWF (s : Subst) (h : Subst.Acyclic s) (ty : Ty) : Ty :=
  let tlim := typeRankBoundTy h ty + 1
  let rlim := rowRankBoundTy h ty + 1
  applySubstBounded s h tlim rlim ty

/-- Well-founded substitution for rows (no external fuel). -/
def applySubstRowWF (s : Subst) (h : Subst.Acyclic s) (r : Row) : Row :=
  let tlim := typeRankBoundRow h r + 1
  let rlim := rowRankBoundRow h r + 1
  applySubstRowBounded s h tlim rlim r

/-- Well-founded substitution for type lists (no external fuel). -/
def applySubstTyListWF (s : Subst) (h : Subst.Acyclic s) (tl : TyList) : TyList :=
  let tlim := typeRankBoundTyList h tl + 1
  let rlim := rowRankBoundTyList h tl + 1
  applySubstTyListBounded s h tlim rlim tl

/-- Well-founded substitution for row fields (no external fuel). -/
def applySubstRowFieldsWF (s : Subst) (h : Subst.Acyclic s) (rf : RowFields) : RowFields :=
  let tlim := typeRankBoundRowFields h rf + 1
  let rlim := rowRankBoundRowFields h rf + 1
  applySubstRowFieldsBounded s h tlim rlim rf

/-- Well-founded substitution for effect rows (no external fuel). -/
def applySubstEffectRowWF (s : Subst) (h : Subst.Acyclic s) (effects : EffectRow) : EffectRow :=
  match effects with
  | .mk row =>
    let tlim := typeRankBoundRow h row + 1
    let rlim := rowRankBoundRow h row + 1
    .mk (applySubstRowBounded s h tlim rlim row)

/-- On a type variable, WF substitution takes one lookup step when bound. -/
theorem applySubstWF_var_lookup
    (s : Subst) (h : Subst.Acyclic s) (v : TypeVarId) (ty : Ty)
    (h_lookup : s.typeMap v = some ty) :
    applySubstWF s h (.var v) = applySubstBounded s h (h.typeRank v) 1 ty := by
  unfold applySubstWF
  have h_tlim : h.typeRank v < typeRankBoundTy h (.var v) + 1 := by
    simp [typeRankBoundTy, freeTypeVars, maxNatList]
  have h_rlim : rowRankBoundTy h (.var v) + 1 = 1 := by
    simp [rowRankBoundTy, freeRowVars, maxNatList]
  simp [applySubstBounded, h_lookup, h_tlim, h_rlim]

/-- On an unbound type variable, WF substitution returns the same variable. -/
theorem applySubstWF_var_unbound
    (s : Subst) (h : Subst.Acyclic s) (v : TypeVarId)
    (h_lookup : s.typeMap v = none) :
    applySubstWF s h (.var v) = .var v := by
  unfold applySubstWF
  have h_tlim : h.typeRank v < typeRankBoundTy h (.var v) + 1 := by
    simp [typeRankBoundTy, freeTypeVars, maxNatList]
  have h_rlim : rowRankBoundTy h (.var v) + 1 = 1 := by
    simp [rowRankBoundTy, freeRowVars, maxNatList]
  simp [applySubstBounded, h_lookup, h_tlim, h_rlim]

/-- On an empty open row, WF row substitution takes one row-var lookup step when bound. -/
theorem applySubstRowWF_empty_open_lookup
    (s : Subst) (h : Subst.Acyclic s) (rv : RowVarId) (r : Row)
    (h_lookup : s.rowMap rv = some r) :
    applySubstRowWF s h (Row.mk .nil (some rv)) = applySubstRowBounded s h 1 (h.rowRank rv) r := by
  unfold applySubstRowWF
  have h_tlim : typeRankBoundRow h (Row.mk .nil (some rv)) + 1 = 1 := by
    simp [typeRankBoundRow, freeTypeVarsRow, freeTypeVarsRowFields, maxNatList]
  have h_rlim : rowRankBoundRow h (Row.mk .nil (some rv)) + 1 = h.rowRank rv + 1 := by
    simp [rowRankBoundRow, freeRowVarsRow, freeRowVarsRowFields, maxNatList]
  have h_lt : h.rowRank rv < h.rowRank rv + 1 := Nat.lt_succ_self _
  rw [h_tlim, h_rlim]
  simp [applySubstRowBounded, applySubstRowFieldsBounded, h_lookup, h_lt, RowFields.append]
  cases h_row : applySubstRowBounded s h 1 (h.rowRank rv) r with
  | mk tailFields tailRest =>
      rfl

/-- On an empty open row, WF row substitution is identity when the row-var is unbound. -/
theorem applySubstRowWF_empty_open_unbound
    (s : Subst) (h : Subst.Acyclic s) (rv : RowVarId)
    (h_lookup : s.rowMap rv = none) :
    applySubstRowWF s h (Row.mk .nil (some rv)) = Row.mk .nil (some rv) := by
  unfold applySubstRowWF
  have h_tlim : typeRankBoundRow h (Row.mk .nil (some rv)) + 1 = 1 := by
    simp [typeRankBoundRow, freeTypeVarsRow, freeTypeVarsRowFields, maxNatList]
  have h_rlim : rowRankBoundRow h (Row.mk .nil (some rv)) + 1 = h.rowRank rv + 1 := by
    simp [rowRankBoundRow, freeRowVarsRow, freeRowVarsRowFields, maxNatList]
  have h_lt : h.rowRank rv < h.rowRank rv + 1 := Nat.lt_succ_self _
  rw [h_tlim, h_rlim]
  simp [applySubstRowBounded, applySubstRowFieldsBounded, h_lookup, h_lt]
