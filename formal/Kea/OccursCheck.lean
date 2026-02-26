/-
  Kea.OccursCheck — Occurs check predicate.

  Mirrors: rill-infer/src/lib.rs:491-515 (Unifier.occurs_in)

  Prevents infinite types like T = List(T). If type variable `v`
  appears anywhere inside type `t`, then unifying Var(v) with t
  would create a cyclic type.
-/

import Kea.Ty
import Kea.Substitution

-- =========================================================================
-- Occurs check (without substitution — checks structural occurrence)
-- =========================================================================

mutual
  /-- Does type variable `v` occur in type `ty`? -/
  def occursIn (v : TypeVarId) (ty : Ty) : Bool :=
    match ty with
    | .var w => v == w
    | .int | .intN _ _ | .float | .floatN _ | .decimal _ _ | .bool | .string | .html | .markdown | .atom | .date | .dateTime | .unit | .dynamic => false
    | .list inner | .set inner | .option inner | .dataframe inner | .column inner | .stream inner
      | .task inner | .actor inner | .arc inner | .groupedFrame inner _ | .tagged inner _
      | .fixedSizeList inner _ | .tensor inner _ =>
      occursIn v inner
    | .sum _ args | .opaque _ args => occursInTyList v args
    | .existential _ assoc => occursInTyList v assoc
    | .map k val => occursIn v k || occursIn v val
    | .result ok err => occursIn v ok || occursIn v err
    | .record _ r | .anonRecord r | .row r => occursInRow v r
    | .function params ret => occursInTyList v params || occursIn v ret
    | .forall _ body => occursIn v body
    | .app ctor args => occursIn v ctor || occursInTyList v args
    | .constructor _ fixedArgs _ => occursInTyList v fixedArgs
    | .tuple elems => occursInTyList v elems

  /-- Does type variable `v` occur in row `r`? -/
  def occursInRow (v : TypeVarId) (r : Row) : Bool :=
    match r with
    | .mk fields _ => occursInRowFields v fields

  /-- Does type variable `v` occur in any type in the type list? -/
  def occursInTyList (v : TypeVarId) (tl : TyList) : Bool :=
    match tl with
    | .nil => false
    | .cons t rest => occursIn v t || occursInTyList v rest

  /-- Does type variable `v` occur in any type in the row fields? -/
  def occursInRowFields (v : TypeVarId) (rf : RowFields) : Bool :=
    match rf with
    | .nil => false
    | .cons _ ty rest => occursIn v ty || occursInRowFields v rest
end

-- =========================================================================
-- Occurs check with substitution application
-- =========================================================================

/-- Does `v` occur in `ty` after applying substitution `s`?
    This mirrors the Rust code which applies the substitution first. -/
def occursInResolved (s : Subst) (fuel : Nat) (v : TypeVarId) (ty : Ty) : Bool :=
  occursIn v (applySubst s fuel ty)
