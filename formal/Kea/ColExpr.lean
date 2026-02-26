/-
  Kea.ColExpr — Column expression AST and type inference model.

  Mirrors: rill-ast/src/lib.rs (ColExprKind) and
           rill-infer/src/typeck.rs (infer_col_expr)

  This is a simplified model: just enough AST and typing rules to state
  and prove `inferColExpr_always_returns_column` — the key theorem that
  connects VISION.md §2.1's cardinality thesis to the actual type inference.

  Design decisions:
  - No spans, no diagnostics — pure type-level reasoning
  - No UnaryOp (structurally identical to BinaryOp for the Column property)
  - No Call (aggregates are handled identically — all return Column(T))
  - Capture resolves from a simple environment (Label → Ty)
  - Binary ops: arithmetic, comparison, logical — all return Column(T)
  - Nullable propagation modeled but simplified
  - `resolveAtom` integrated (from DataFrame.lean) rather than duplicated

  The full Rust infer_col_expr is ~150 lines. This model is ~80 lines.
  What matters is the Column(T) wrapper — every arm wraps its result.
-/

import Kea.Ty
import Kea.Unify
import Kea.Properties.ColumnBoundary

-- =========================================================================
-- Part 1: ColExpr AST
-- =========================================================================

/-- Binary operation kinds for column expressions.
    Simplified from Rust BinOp — we group by typing behavior, not syntax. -/
inductive ColBinOp where
  /-- Arithmetic: +, -, *, /, %. Operands unified, result = operand type. -/
  | arith : ColBinOp
  /-- Comparison: ==, !=, <, <=, >, >=. Operands unified, result = Bool. -/
  | cmp   : ColBinOp
  /-- Logical: &&, ||. Operands must be Bool, result = Bool. -/
  | logic : ColBinOp

/-- Column expression AST. Mirrors `ColExprKind` in rill-ast/src/lib.rs.

    Every constructor corresponds to a case in `infer_col_expr` (typeck.rs:1472).
    The model omits UnaryOp (same Column-wrapping behavior) and Call
    (same pattern: infer args, compute result, wrap in Column). -/
inductive ColExpr where
  /-- Column reference: `:name`. Resolves against DataFrame schema. -/
  | atom : Label → ColExpr
  /-- Literal: `42`, `"hello"`, `true`. The Ty is the literal's ground type. -/
  | lit : Ty → ColExpr
  /-- Null literal: `nil`. Creates Column(Option(fresh_var)). -/
  | nil : ColExpr
  /-- Binary operation: `:price * :qty`, `:age > 18`. -/
  | binOp : ColBinOp → ColExpr → ColExpr → ColExpr
  /-- Value capture from Kea scope: `$threshold`. -/
  | capture : Label → ColExpr

-- =========================================================================
-- Part 2: Capture environment
-- =========================================================================

/-- A capture environment maps variable names to their types.
    Mirrors the TypeEnv lookup in infer_col_expr's Capture arm. -/
def CaptureEnv := List (Label × Ty)

namespace CaptureEnv

def lookup (env : CaptureEnv) (name : Label) : Option Ty :=
  match env with
  | [] => none
  | (l, ty) :: rest => if l == name then some ty else lookup rest name

end CaptureEnv

-- =========================================================================
-- Part 3: inferColExpr — type inference for column expressions
-- =========================================================================

/-- Infer the type of a column expression given a DataFrame input type.

    This mirrors `infer_col_expr` in typeck.rs:1472-1629. Key properties:
    1. Every result is wrapped in `Ty.column` (the Column(T) boundary)
    2. Atoms resolve against the DataFrame schema via row unification
    3. Literals produce Column(ground_type)
    4. Binary ops unify operand types and produce Column(result_type)
    5. Captures resolve from the environment and produce Column(captured_type)

    Simplifications vs Rust:
    - No unifier state threading (we model resolved types directly)
    - No nullable propagation (modeled separately if needed)
    - No error diagnostics
    - Atom resolution returns a pre-resolved type from the schema

    The function takes the DataFrame's schema row directly (not a Ty),
    because in the Rust implementation, resolveAtom has already unified
    the input to DataFrame(AnonRecord(row)) by this point. -/
def inferColExpr (schemaFields : RowFields) (captures : CaptureEnv) : ColExpr → Option Ty
  | .atom label =>
    -- Resolve column from schema. Returns Column(element_type).
    match schemaFields.get label with
    | some elemTy => some (.column elemTy)
    | none => none  -- Column not found (type error in Rust)

  | .lit ty =>
    -- Literal: wrap ground type in Column.
    some (.column ty)

  | .nil =>
    -- nil: Column(Option(Unit)) as a placeholder.
    -- In Rust this uses a fresh type variable; we use Unit as a ground stand-in.
    some (.column (.option .unit))

  | .binOp op left right =>
    -- Recursively infer both operands
    match inferColExpr schemaFields captures left,
          inferColExpr schemaFields captures right with
    | some (.column leftInner), some (.column rightInner) =>
      match op with
      | .arith =>
        -- Arithmetic: result type = left type (after unification with right).
        -- We model successful unification by assuming left = right.
        if leftInner == rightInner then some (.column leftInner) else none
      | .cmp =>
        -- Comparison: result is always Bool (operands unified).
        if leftInner == rightInner then some (.column .bool) else none
      | .logic =>
        -- Logical: both must be Bool, result is Bool.
        if leftInner == .bool && rightInner == .bool then some (.column .bool)
        else none
    | _, _ => none  -- Subexpression failed

  | .capture name =>
    -- Capture: look up in environment, wrap in Column.
    match captures.lookup name with
    | some ty => some (.column ty)
    | none => none  -- Capture not found (error in Rust)

-- =========================================================================
-- Part 4: The key theorem — inferColExpr always returns Column(T)
-- =========================================================================

/-- Helper: extract the inner type from a Column, if it is one. -/
def isColumn : Ty → Prop
  | .column _ => True
  | _ => False

/-- When inferColExpr succeeds, the result is always of the form Column(T)
    for some T. This is the central type-level invariant that makes the
    cardinality boundary work:

    - infer_col_expr always wraps in Column(T) (typeck.rs:1466-1468)
    - Verb boundaries unwrap with unwrapCol (typeck.rs:1435)
    - The round-trip (Column → unwrap → bare type) is always valid

    This theorem, combined with `force_lift_id` from ColumnBoundary.lean,
    gives us the full cardinality transition chain:

      inferColExpr produces Column(T)
      → unwrapCol extracts T
      → T is inserted into the output schema
      → The output DataFrame has the correct element type

    VISION.md §2.1: "Column(T) is a cardinality annotation, not a domain
    boundary. The same T appears at both cardinalities."

    Proof strategy: structural recursion on ColExpr. Each case unfolds
    inferColExpr and shows the result is `some (.column _)` or contradicts
    the `h : ... = some result` hypothesis. -/
theorem inferColExpr_always_returns_column
    (schema : RowFields) (env : CaptureEnv) (expr : ColExpr) (result : Ty)
    (h : inferColExpr schema env expr = some result) :
    ∃ inner, result = .column inner := by
  match expr with
  | .atom label =>
    unfold inferColExpr at h
    match hget : schema.get label with
    | some elemTy =>
      simp [hget] at h
      exact ⟨elemTy, h.symm⟩
    | none =>
      simp [hget] at h
  | .lit ty =>
    unfold inferColExpr at h
    simp at h
    exact ⟨ty, h.symm⟩
  | .nil =>
    unfold inferColExpr at h
    simp at h
    exact ⟨.option .unit, h.symm⟩
  | .binOp op left right =>
    -- Recursive: both subexprs must succeed with Column results
    have hl := inferColExpr_always_returns_column schema env left
    have hr := inferColExpr_always_returns_column schema env right
    unfold inferColExpr at h
    -- Case split on left result
    match hleft : inferColExpr schema env left with
    | none => simp [hleft] at h
    | some leftTy =>
      -- Case split on right result
      match hright : inferColExpr schema env right with
      | none => simp [hleft, hright] at h
      | some rightTy =>
        -- Both succeeded. Use recursive hypotheses to get Column form.
        have ⟨li, hli⟩ := hl leftTy hleft
        have ⟨ri, hri⟩ := hr rightTy hright
        subst hli; subst hri
        simp [hleft, hright] at h
        -- Now h is about the op match with known Column inputs
        match op with
        | .arith =>
          simp at h
          exact ⟨li, h.2.symm⟩
        | .cmp =>
          simp at h
          exact ⟨.bool, h.2.symm⟩
        | .logic =>
          simp at h
          exact ⟨.bool, h.2.symm⟩
  | .capture name =>
    unfold inferColExpr at h
    match hget : env.lookup name with
    | some ty =>
      simp [hget] at h
      exact ⟨ty, h.symm⟩
    | none =>
      simp [hget] at h

-- =========================================================================
-- Part 5: Verb boundary composition — unwrapCol ∘ inferColExpr
-- =========================================================================

/-- When inferColExpr succeeds, unwrapCol recovers the element type.
    This is the verb boundary pattern: infer in Column domain, unwrap to
    insert bare type into the output schema.

    Mirrors the pattern at every verb callsite in typeck.rs:
      let col_ty = infer_col_expr(col_expr, ...);
      let bare_ty = unwrap_col(&col_ty);
      result_ty = df_mutate(&result_ty, label, bare_ty, ...); -/
theorem verb_boundary_unwrap
    (schema : RowFields) (env : CaptureEnv) (expr : ColExpr) (result : Ty)
    (h : inferColExpr schema env expr = some result) :
    ∃ inner, result = .column inner ∧ unwrapCol result = inner := by
  have ⟨inner, heq⟩ := inferColExpr_always_returns_column schema env expr result h
  exact ⟨inner, heq, by simp [heq, unwrapCol]⟩

-- =========================================================================
-- Part 6: Atom resolution preserves schema types
-- =========================================================================

/-- When an atom resolves successfully, the element type comes directly
    from the schema. This means Column(T) wraps exactly the schema's
    field type — no transformation occurs at the type level.

    Combined with verb_boundary_unwrap, this gives:
    unwrapCol(inferColExpr(atom(label))) = schema.get(label)  -/
theorem atom_resolves_schema_type
    (schema : RowFields) (env : CaptureEnv) (label : Label) (fieldTy : Ty)
    (hget : schema.get label = some fieldTy) :
    inferColExpr schema env (.atom label) = some (.column fieldTy) := by
  simp [inferColExpr, hget]

/-- Corollary: atom resolution + unwrap recovers the schema field type. -/
theorem atom_unwrap_is_field_type
    (fieldTy : Ty) :
    unwrapCol (.column fieldTy) = fieldTy := by
  rfl

-- =========================================================================
-- Part 7: Literal typing
-- =========================================================================

/-- Literals always produce Column(ground_type). -/
theorem lit_produces_column (schema : RowFields) (env : CaptureEnv) (ty : Ty) :
    inferColExpr schema env (.lit ty) = some (.column ty) := by
  rfl

/-- Capture always produces Column(captured_type) when name exists. -/
theorem capture_produces_column
    (schema : RowFields) (env : CaptureEnv) (name : Label) (ty : Ty)
    (henv : env.lookup name = some ty) :
    inferColExpr schema env (.capture name) = some (.column ty) := by
  simp [inferColExpr, henv]

-- =========================================================================
-- Part 8: Mutate verb boundary composition
-- =========================================================================

/-- End-to-end mutate composition: given a DataFrame with schema `fields`,
    if inferColExpr produces Column(T) for a new column, then unwrapCol
    gives T, and the output schema can extend with (label, T).

    This connects the column expression typing to the DataFrame operations
    in DataFrame.lean, completing the cardinality transition chain:

    input DataFrame(#{...fields...})
    → inferColExpr → Column(T)
    → unwrapCol → T
    → dfMutate(label, T) → DataFrame(#{...fields, label: T...})

    The theorem states the type-level invariant, not the full dfMutate
    proof (which requires row unification). -/
theorem mutate_col_type_correct
    (schema : RowFields) (env : CaptureEnv) (expr : ColExpr)
    (colLabel : Label) (colResult : Ty)
    (hinfer : inferColExpr schema env expr = some colResult) :
    ∃ elemTy,
      colResult = .column elemTy ∧
      unwrapCol colResult = elemTy ∧
      -- The new column's type in the output schema would be elemTy
      RowFields.cons colLabel elemTy schema =
        .cons colLabel (unwrapCol colResult) schema := by
  have ⟨inner, heq, hunwrap⟩ := verb_boundary_unwrap schema env expr colResult hinfer
  exact ⟨inner, heq, hunwrap, by rw [hunwrap]⟩
