/-
  Kea.DataFrame — Type-level DataFrame operations.

  Mirrors: rill-infer/src/typeck.rs:770-1091 (df_mutate, df_update, df_drop,
  resolve_atom, df_filter, df_sort, df_distinct, df_select, df_summarize,
  df_join_check)

  These operations compose row extension/decomposition with unification
  and lacks checking. They work through the unifier — they unify the input
  against an expected shape, then construct the output type.
-/

import Kea.Ty
import Kea.Unify

-- =========================================================================
-- resolvedHasColumn: check if a resolved type has a column
-- =========================================================================

/-- Check whether a resolved DataFrame type has a column with the given label.
    Extracted as a named function so both dfMutate and proofs about it
    reference the same compiled match. -/
def resolvedHasColumn (s : Subst) (fuel : Nat) (inputTy : Ty) (column : Label) : Bool :=
  match applySubst s fuel inputTy with
  | .dataframe (.anonRecord (.mk fields _)) => fields.has column
  | _ => false

-- =========================================================================
-- df_mutate: add a new column to a DataFrame
-- =========================================================================

/--
Type-level `mutate`: add a new column to a DataFrame.

Given `DataFrame(#{ a: Int | r })`, adding column `b` with type `T`
produces `DataFrame(#{ a: Int, b: T | r })`.

The column must not already exist — this is enforced by checking
the resolved input row for the label after unification.

Mirrors `df_mutate` in typeck.rs:770-811.
-/
def dfMutate (st : UnifyState) (fuel : Nat) (inputTy : Ty) (column : Label) (valueTy : Ty)
    : UnifyResult × Ty :=
  -- Input must be DataFrame(AnonRecord(row)) — unify against DataFrame(#{| r})
  let (inputRowVar, st') := st.freshRowVar
  let inputRow := Row.emptyOpen inputRowVar
  let expectedInput := Ty.dataframe (Ty.anonRecord inputRow)
  match unify st' fuel inputTy expectedInput with
  | .err e => (.err e, inputTy)
  | .ok st'' =>
    -- Check if the column already exists in the resolved input row
    if resolvedHasColumn st''.subst fuel inputTy column then
      (.err s!"cannot add column `{column}` — DataFrame already has a column named `{column}`",
       inputTy)
    else
      -- Build output row: extend with the new column
      let outputRow := Row.mkOpen (.cons column valueTy .nil) inputRowVar
      let outputTy := Ty.dataframe (Ty.anonRecord outputRow)
      (.ok st'', outputTy)

-- =========================================================================
-- df_drop: remove a column from a DataFrame
-- =========================================================================

/--
Type-level `drop`: remove a column from a DataFrame.

Given `DataFrame(#{ a: Int, b: String | r })`, dropping `:a` produces
`DataFrame(#{ b: String | r })`.

The column must exist — enforced by unifying the input against a row
that contains the column.

Mirrors `df_drop` in typeck.rs:849-872.
-/
def dfDrop (st : UnifyState) (fuel : Nat) (inputTy : Ty) (column : Label)
    : UnifyResult × Ty :=
  -- Input must have the column to drop
  let (colTyVar, st') := st.freshTypeVar
  let colTy := Ty.var colTyVar
  let (restVar, st'') := st'.freshRowVar
  let inputRow := Row.mkOpen (.cons column colTy .nil) restVar
  let expectedInput := Ty.dataframe (Ty.anonRecord inputRow)
  match unify st'' fuel inputTy expectedInput with
  | .err e => (.err e, inputTy)
  | .ok st''' =>
    -- Output is the rest (without the dropped column)
    let restRow := applySubstRow st'''.subst fuel (Row.emptyOpen restVar)
    let outputTy := Ty.dataframe (Ty.anonRecord restRow)
    (.ok st''', outputTy)

-- =========================================================================
-- df_update: change a column's values in-place (same type)
-- =========================================================================

/--
Type-level `update`: replace a column's values in-place.

Given `DataFrame(#{ a: Int | r })`, updating `:a` with `Int` succeeds.
Updating `:a` with `String` is a type error (column type must match).

The output type equals the input type (schema unchanged).

Mirrors `df_update` in typeck.rs:817-843.
-/
def dfUpdate (st : UnifyState) (fuel : Nat) (inputTy : Ty) (column : Label) (valueTy : Ty)
    : UnifyResult × Ty :=
  -- Input must be DataFrame with a row containing this column
  let (colTyVar, st') := st.freshTypeVar
  let colTy := Ty.var colTyVar
  let (restVar, st'') := st'.freshRowVar
  let inputRow := Row.mkOpen (.cons column colTy .nil) restVar
  let expectedInput := Ty.dataframe (Ty.anonRecord inputRow)
  match unify st'' fuel inputTy expectedInput with
  | .err e => (.err e, inputTy)
  | .ok st''' =>
    -- The new value must match the existing column type
    match unify st''' fuel colTy valueTy with
    | .err e => (.err e, inputTy)
    | .ok st'''' =>
      -- Output type is same as input (schema unchanged)
      let resolved := applySubst st''''.subst fuel inputTy
      (.ok st'''', resolved)

-- =========================================================================
-- resolve_atom: resolve a column name against a DataFrame's row type
-- =========================================================================

/--
Resolve an atom (`:name`) against a DataFrame's row type, returning
the column's type.

Unifies the input against `DataFrame(#{ name: T | r })` where T and r
are fresh, then returns the resolved T.

Mirrors `resolve_atom` in typeck.rs:1093-1117.
-/
def resolveAtom (st : UnifyState) (fuel : Nat) (label : Label) (inputTy : Ty)
    : UnifyResult × Ty :=
  let (colTyVar, st') := st.freshTypeVar
  let colTy := Ty.var colTyVar
  let (restVar, st'') := st'.freshRowVar
  let expectedRow := Row.mkOpen (.cons label colTy .nil) restVar
  let expectedDf := Ty.dataframe (Ty.anonRecord expectedRow)
  match unify st'' fuel inputTy expectedDf with
  | .err e => (.err e, colTy)
  | .ok st''' =>
    let resolved := applySubst st'''.subst fuel colTy
    (.ok st''', resolved)

-- =========================================================================
-- df_filter: filter rows (schema preserved)
-- =========================================================================

/--
Type-level `filter`: select rows matching a predicate.

Given `DataFrame(R)`, filter always produces `DataFrame(R)` — the schema
is preserved, only rows change. The predicate must evaluate to `Bool`,
but that constraint is on the ColExpr, not on the DataFrame type.

Mirrors `DfVerbKind::Filter` in typeck.rs:980-989.
-/
def dfFilter (inputTy : Ty) : Ty :=
  inputTy

-- =========================================================================
-- df_sort: reorder rows (schema preserved)
-- =========================================================================

/--
Type-level `sort`: reorder rows by column values.

Given `DataFrame(R)`, sort always produces `DataFrame(R)`. Column
existence is checked by `resolveAtom` on each sort key, but the
output schema is identical to the input.

Mirrors `DfVerbKind::Sort` in typeck.rs:1019-1026.
-/
def dfSort (inputTy : Ty) : Ty :=
  inputTy

-- =========================================================================
-- df_distinct: deduplicate rows (schema preserved)
-- =========================================================================

/--
Type-level `distinct`: remove duplicate rows.

Given `DataFrame(R)`, distinct always produces `DataFrame(R)`. No
columns are referenced — the operation is schema-preserving by definition.

Mirrors `DfVerbKind::Distinct` in typeck.rs:1028-1031.
-/
def dfDistinct (inputTy : Ty) : Ty :=
  inputTy

-- =========================================================================
-- df_select: restrict to a subset of columns
-- =========================================================================

/--
Select specific fields from a RowFields by label list.

Returns a new RowFields containing only the fields whose labels appear
in the selection list, preserving the order of the selection list.
Fields not found are skipped (errors are handled upstream by resolveAtom).
-/
def RowFields.select (rf : RowFields) (labels : List Label) : RowFields :=
  match labels with
  | [] => .nil
  | l :: rest =>
    match rf.get l with
    | some ty => .cons l ty (rf.select rest)
    | none => rf.select rest

/--
Type-level `select`: restrict a DataFrame to specified columns.

Given `DataFrame(#{ a: Int, b: String, c: Bool })` and `select(:a, :c)`,
produces `DataFrame(#{ a: Int, c: Bool })`. The output row is always
closed — select discards the row variable.

Mirrors `DfVerbKind::Select` in typeck.rs:991-1001.
-/
def dfSelect (st : UnifyState) (fuel : Nat) (inputTy : Ty) (columns : List Label)
    : UnifyResult × Ty :=
  -- Resolve input as DataFrame
  let (inputRowVar, st') := st.freshRowVar
  let inputRow := Row.emptyOpen inputRowVar
  let expectedInput := Ty.dataframe (Ty.anonRecord inputRow)
  match unify st' fuel inputTy expectedInput with
  | .err e => (.err e, inputTy)
  | .ok st'' =>
    -- Resolve each column via resolveAtom and build closed output row
    let rec resolveColumns (st : UnifyState) (cols : List Label) (acc : RowFields)
        : UnifyResult × RowFields :=
      match cols with
      | [] => (.ok st, acc)
      | l :: rest =>
        match resolveAtom st fuel l inputTy with
        | (.err e, _) => (.err e, acc)
        | (.ok st', colTy) =>
          resolveColumns st' rest (.cons l colTy acc)
    match resolveColumns st'' columns .nil with
    | (.err e, _) => (.err e, inputTy)
    | (.ok st''', selectedFields) =>
      let outputRow := Row.closed selectedFields
      let outputTy := Ty.dataframe (Ty.anonRecord outputRow)
      (.ok st''', outputTy)

-- =========================================================================
-- df_summarize: aggregate into new columns
-- =========================================================================

/--
Type-level `summarize`: produce a new DataFrame from aggregation expressions.

Given column expression result types, builds a new closed DataFrame row.
The input schema is discarded — the output contains only the aggregation columns.

Mirrors `DfVerbKind::Summarize` in typeck.rs:1052-1062.
-/
def dfSummarize (columns : List (Label × Ty)) : Ty :=
  let fields := columns.foldr (fun (l, ty) acc => RowFields.cons l ty acc) .nil
  Ty.dataframe (Ty.anonRecord (Row.closed fields))

-- =========================================================================
-- RecordRegistry (simplified model for formalization)
-- =========================================================================

/--
A record registry: maps record names to their row types.
Simplified from the Rust RecordRegistry which also handles params and annotations.
-/
structure RecordRegistry where
  records : List (String × Row)

namespace RecordRegistry

def empty : RecordRegistry := ⟨[]⟩

/-- Register a named record with its row. -/
def register (reg : RecordRegistry) (name : String) (row : Row) : RecordRegistry :=
  ⟨(name, row) :: reg.records⟩

/-- Look up a record by name. -/
def lookup (reg : RecordRegistry) (name : String) : Option Row :=
  match reg.records.find? (fun (n, _) => n == name) with
  | some (_, row) => some row
  | none => none

/-- Convert a record name to its nominal Ty. -/
def toType (reg : RecordRegistry) (name : String) : Option Ty :=
  match reg.lookup name with
  | some row => some (Ty.record name row)
  | none => none

end RecordRegistry

-- =========================================================================
-- TraitRegistry (simplified model for coherence property)
-- =========================================================================

/-- A trait implementation record: (trait name, implementing type name). -/
structure ImplEntry where
  traitName : String
  typeName  : String

/--
Trait registry for coherence checking.
The key property: no two impls for the same (trait, type) pair.
-/
structure TraitRegistry where
  impls : List ImplEntry

namespace TraitRegistry

def empty : TraitRegistry := ⟨[]⟩

/-- Check if an impl already exists for this (trait, type) pair. -/
def hasImpl (reg : TraitRegistry) (traitName typeName : String) : Bool :=
  reg.impls.any (fun e => e.traitName == traitName && e.typeName == typeName)

/-- Register a trait impl. Returns false if duplicate (coherence violation). -/
def registerImpl (reg : TraitRegistry) (traitName typeName : String) : Option TraitRegistry :=
  if reg.hasImpl traitName typeName then none
  else some ⟨{ traitName, typeName } :: reg.impls⟩

/-- Check if a trait is satisfied for a given type name. -/
def satisfies (reg : TraitRegistry) (traitName typeName : String) : Bool :=
  reg.hasImpl traitName typeName

end TraitRegistry

-- =========================================================================
-- Trait bound checking (post-inference)
-- =========================================================================

/-- Map a concrete type to its name for trait dispatch.
    Mirrors `type_name_for_trait_check` in rill-infer/src/lib.rs. -/
def typeNameForTraitCheck : Ty → Option String
  | .int => some "Int"
  | .intN _ _ => some "Int"
  | .float => some "Float"
  | .floatN _ => some "Float"
  | .string => some "String"
  | .bool => some "Bool"
  | .html => some "Html"
  | .markdown => some "Markdown"
  | .atom => some "Atom"
  | .date => some "Date"
  | .dateTime => some "DateTime"
  | .unit => some "Unit"
  | .record name _ => some name
  | .list _ => some "List"
  | .map _ _ => some "Map"
  | .set _ => some "Set"
  | .option _ => some "Option"
  | .result _ _ => some "Result"
  | .dataframe _ => some "DataFrame"
  | .column _ => some "Column"
  | .tuple _ => some "Tuple"
  | .anonRecord _ => some "AnonRecord"
  | _ => none  -- Var, Function, Row: can't dispatch on

/-- Check all accumulated trait bounds against the registry.
    Returns a list of unsatisfied bounds (trait name, type name).
    Mirrors `Unifier::check_trait_bounds` in rill-infer/src/lib.rs. -/
def checkTraitBounds (traitBounds : TraitBounds) (subst : Subst) (fuel : Nat)
    (registry : TraitRegistry) : List (String × String) :=
  traitBounds.filterMap fun (tv, traitName) =>
    let resolved := applySubst subst fuel (.var tv)
    match resolved with
    | .var _ => none  -- Still polymorphic, skip
    | _ =>
      match typeNameForTraitCheck resolved with
      | none => none  -- Can't dispatch
      | some typeName =>
        if registry.satisfies traitName typeName then none
        else some (traitName, typeName)
