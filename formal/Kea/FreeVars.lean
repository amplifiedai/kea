/-
  Kea.FreeVars — Free variable computation for types and rows.

  Mirrors: rill-types/src/lib.rs:335-437 (free_type_vars, free_row_vars)
-/

import Kea.Ty

-- =========================================================================
-- Free type variables
-- =========================================================================

mutual
  /-- Collect all free type variable IDs in a type. -/
  def freeTypeVars (ty : Ty) : List TypeVarId :=
    match ty with
    | .var v => [v]
    | .int | .intN _ _ | .float | .floatN _ | .decimal _ _ | .bool | .string | .html | .markdown | .atom | .date | .dateTime | .unit | .dynamic => []
    | .list inner | .set inner | .option inner | .dataframe inner | .column inner | .stream inner
      | .task inner | .actor inner | .arc inner | .groupedFrame inner _ | .tagged inner _
      | .fixedSizeList inner _ | .tensor inner _ =>
      freeTypeVars inner
    | .sum _ args | .opaque _ args => freeTypeVarsTyList args
    | .existential _ assoc => freeTypeVarsTyList assoc
    | .map k v | .result k v => freeTypeVars k ++ freeTypeVars v
    | .record _ r | .anonRecord r | .row r => freeTypeVarsRow r
    | .function params ret => freeTypeVarsTyList params ++ freeTypeVars ret
    | .forall _ body => freeTypeVars body
    | .app ctor args => freeTypeVars ctor ++ freeTypeVarsTyList args
    | .constructor _ fixedArgs _ => freeTypeVarsTyList fixedArgs
    | .tuple elems => freeTypeVarsTyList elems

  /-- Collect all free type variable IDs in a row. -/
  def freeTypeVarsRow (r : Row) : List TypeVarId :=
    match r with
    | .mk fields _ => freeTypeVarsRowFields fields

  /-- Collect all free type variable IDs in a type list. -/
  def freeTypeVarsTyList (tl : TyList) : List TypeVarId :=
    match tl with
    | .nil => []
    | .cons t rest => freeTypeVars t ++ freeTypeVarsTyList rest

  /-- Collect all free type variable IDs in row fields. -/
  def freeTypeVarsRowFields (rf : RowFields) : List TypeVarId :=
    match rf with
    | .nil => []
    | .cons _ ty rest => freeTypeVars ty ++ freeTypeVarsRowFields rest
end

-- =========================================================================
-- Free row variables
-- =========================================================================

mutual
  /-- Collect all free row variable IDs in a type. -/
  def freeRowVars (ty : Ty) : List RowVarId :=
    match ty with
    | .var _ | .int | .intN _ _ | .float | .floatN _ | .decimal _ _ | .bool | .string | .html | .markdown | .atom | .date | .dateTime | .unit | .dynamic => []
    | .list inner | .set inner | .option inner | .dataframe inner | .column inner | .stream inner
      | .task inner | .actor inner | .arc inner | .groupedFrame inner _ | .tagged inner _
      | .fixedSizeList inner _ | .tensor inner _ =>
      freeRowVars inner
    | .sum _ args | .opaque _ args => freeRowVarsTyList args
    | .existential _ assoc => freeRowVarsTyList assoc
    | .map k v | .result k v => freeRowVars k ++ freeRowVars v
    | .record _ r | .anonRecord r | .row r => freeRowVarsRow r
    | .function params ret => freeRowVarsTyList params ++ freeRowVars ret
    | .forall _ body => freeRowVars body
    | .app ctor args => freeRowVars ctor ++ freeRowVarsTyList args
    | .constructor _ fixedArgs _ => freeRowVarsTyList fixedArgs
    | .tuple elems => freeRowVarsTyList elems

  /-- Collect all free row variable IDs in a row. -/
  def freeRowVarsRow (r : Row) : List RowVarId :=
    match r with
    | .mk fields rest =>
      let fieldVars := freeRowVarsRowFields fields
      match rest with
      | none => fieldVars
      | some v => v :: fieldVars

  /-- Collect all free row variable IDs in a type list. -/
  def freeRowVarsTyList (tl : TyList) : List RowVarId :=
    match tl with
    | .nil => []
    | .cons t rest => freeRowVars t ++ freeRowVarsTyList rest

  /-- Collect all free row variable IDs in row fields. -/
  def freeRowVarsRowFields (rf : RowFields) : List RowVarId :=
    match rf with
    | .nil => []
    | .cons _ ty rest => freeRowVars ty ++ freeRowVarsRowFields rest
end
