/-
  Kea.Properties.ColumnBoundary — Column(T) cardinality boundary.

  Formalizes KERNEL §0: "Column(T) does not unify with bare T."
  Formalizes VISION.md §2.1: the labeled row is the universal abstraction,
  with Col(T) as a cardinality annotation distinguishing records (1 value
  per field) from DataFrames (N values per field).

  Structure:
  1. Structural boundary: Column(T) ≠ T for any T (including type variables)
  2. BEq boundary: beqTy(Column(T), T) = false
  3. Cardinality model: Cardinality inductive, lift/force operations
  4. Round-trip properties: lift ∘ unwrapCol and unwrapCol ∘ lift
  5. Cardinality transition proofs: Lift goes one→many, Force goes many→one
  6. Row sharing: records and DataFrames share the same Row type

  The novel formal claim (VISION.md §2.1): same row structure at different
  cardinalities, with typed transitions between them and backend selection
  as a consequence of the type.
-/

import Kea.Unify

-- =========================================================================
-- Part 1: Structural boundary — Column(T) ≠ T
-- =========================================================================

/-- Column(T) is never equal to T. This is the fundamental cardinality
    boundary: wrapping a type in Column always produces a distinct type.

    Proof: Column(T) has strictly larger sizeOf than T, so equality
    is impossible. This holds for ALL types including type variables. -/
theorem column_ne_bare (ty : Ty) : Ty.column ty ≠ ty := by
  intro h
  have hsz := congrArg sizeOf h
  simp only [Ty.column.sizeOf_spec] at hsz
  omega

-- =========================================================================
-- Part 2: BEq boundary — beqTy(Column(T), T) = false
-- =========================================================================

/-- Column(T) is never BEq-equal to T. Proved by structural recursion:
    .column is a distinct constructor from all non-column types,
    and for .column inner, the recursive case reduces to the same property. -/
theorem column_beq_ne_bare (ty : Ty) : beqTy (Ty.column ty) ty = false := by
  match ty with
  | .int | .intN _ _ | .float | .floatN _ | .decimal _ _ | .bool | .string | .html | .markdown | .atom | .date | .dateTime | .unit | .dynamic => simp [beqTy]
  | .list _ | .set _ | .option _ | .fixedSizeList _ _ | .tensor _ _ | .sum _ _ | .opaque _ _ | .dataframe _ | .groupedFrame _ _ | .tagged _ _ | .stream _ | .task _ | .actor _ | .arc _ => simp [beqTy]
  | .map _ _ | .result _ _ => simp [beqTy]
  | .existential _ _ => simp [beqTy]
  | .record _ _ | .anonRecord _ | .row _ => simp [beqTy]
  | .function _ _ | .forall _ _ | .app _ _ | .constructor _ _ _ | .tuple _ => simp [beqTy]
  | .var _ => simp [beqTy]
  | .column inner =>
    simp [beqTy]
    exact column_beq_ne_bare inner

-- =========================================================================
-- Part 3: Cardinality model
-- =========================================================================

/-- Cardinality: the semantic axis that distinguishes records from DataFrames.

    Records have cardinality `one` (1 value per field).
    DataFrames have cardinality `many` (N values per field).
    Column(T) marks a type as being in the `many` domain.

    VISION.md §2.1: "A record and a DataFrame have the same row type;
    they differ in cardinality." -/
inductive Cardinality where
  | one  : Cardinality  -- scalar: record, closure env, REPL binding, actor state
  | many : Cardinality  -- columnar: DataFrame column, ColumnExpr result
  deriving DecidableEq, Repr

/-- Determine the cardinality of a type.

    Column(T) and DataFrame(_) are in the `many` domain.
    Everything else is `one`. -/
def cardinality : Ty → Cardinality
  | .column _    => .many
  | .dataframe _ => .many
  | _            => .one

-- =========================================================================
-- Part 4: Lift and Force — the only cardinality transitions
-- =========================================================================

/-- Lift: T → Column(T). Broadcast a scalar into the columnar domain.

    KERNEL §0: "Lift: T → Column(T)" is one of the two cardinality transitions.
    In the Rust implementation, this is the implicit wrapping that happens
    when a scalar appears in a ColumnExpr context (e.g., `filter(:price > 100)`
    wraps the literal `100` as Column(Int)). -/
def lift (ty : Ty) : Ty := .column ty

/-- Force: Column(T) → T. Unwrap a Column annotation.

    KERNEL §0: "Force: Column(T) → T" is the other cardinality transition.
    In the Rust implementation, this is `unwrap_col` at verb boundaries
    (e.g., mutate inserts the unwrapped type into the output schema). -/
def unwrapCol : Ty → Ty
  | .column inner => inner
  | other => other

-- =========================================================================
-- Part 5: Round-trip properties
-- =========================================================================

/-- Force after Lift is identity: unwrapCol(Column(T)) = T. -/
theorem force_lift_id (ty : Ty) : unwrapCol (lift ty) = ty := rfl

/-- Lift after Force recovers Column: lift(unwrapCol(Column(T))) = Column(T). -/
theorem lift_force_col (ty : Ty) : lift (unwrapCol (.column ty)) = .column ty := rfl

/-- Force on a non-Column type is identity. -/
theorem force_non_column_id (ty : Ty) (h : ∀ inner, ty ≠ .column inner) :
    unwrapCol ty = ty := by
  match ty with
  | .column inner => exact absurd rfl (h inner)
  | .int | .intN _ _ | .float | .floatN _ | .decimal _ _ | .bool | .string | .html | .markdown | .atom | .date | .dateTime | .unit | .dynamic => rfl
  | .list _ | .set _ | .option _ | .fixedSizeList _ _ | .tensor _ _ | .sum _ _ | .opaque _ _ | .dataframe _ | .groupedFrame _ _ | .tagged _ _ | .stream _ | .task _ | .actor _ | .arc _ => rfl
  | .map _ _ | .result _ _ => rfl
  | .existential _ _ => rfl
  | .record _ _ | .anonRecord _ | .row _ => rfl
  | .function _ _ | .forall _ _ | .app _ _ | .constructor _ _ _ | .tuple _ => rfl
  | .var _ => rfl

-- =========================================================================
-- Part 6: Cardinality transition theorems
-- =========================================================================

/-- Lift always produces a many-cardinality type. -/
theorem lift_cardinality (ty : Ty) : cardinality (lift ty) = .many := rfl

/-- Force on Column(T) produces a one-cardinality type, provided T itself
    is not Column or DataFrame. This is the expected case at verb boundaries:
    the ColumnExpr returns Column(Int), Force unwraps to Int (cardinality one). -/
theorem force_cardinality_ground (ty : Ty)
    (h : cardinality ty = .one) :
    cardinality (unwrapCol (.column ty)) = .one := by
  simp [unwrapCol, h]

/-- Lift changes cardinality from one to many (regardless of starting cardinality). -/
theorem lift_one_to_many (ty : Ty) :
    cardinality (lift ty) = .many := rfl

/-- Force restores cardinality: Force(Lift(T)) has the same cardinality as T. -/
theorem force_lift_preserves_cardinality (ty : Ty) :
    cardinality (unwrapCol (lift ty)) = cardinality ty := rfl

-- =========================================================================
-- Part 7: Row sharing — records and DataFrames use the same Row
-- =========================================================================

/-- Extracting the row from a named record gives back the original row.
    This is trivial by construction but states the key structural fact:
    the Row is the shared substrate across all row-based types. -/
theorem record_extracts_row (name : String) (row : Row) :
    (fun | .record _ r => some r | _ => none) (Ty.record name row) = some row := rfl

/-- Extracting the row from an anonymous record gives back the original row. -/
theorem anon_record_extracts_row (row : Row) :
    (fun | .anonRecord r => some r | _ => none) (Ty.anonRecord row) = some row := rfl

/-- Extracting the row from a DataFrame gives back the original schema row.
    DataFrame(AnonRecord(row)) wraps the same Row that a bare AnonRecord uses. -/
theorem dataframe_extracts_row (row : Row) :
    (fun | .dataframe (.anonRecord r) => some r | _ => none)
      (Ty.dataframe (Ty.anonRecord row)) = some row := rfl

-- =========================================================================
-- Part 8: Column does not unify with non-Column ground types
-- =========================================================================

/-- Column(T) does not unify with T when T is a ground type and both sides
    are already substitution-stable. This is the unifier respecting the
    cardinality boundary established structurally in column_ne_bare.

    The proof unfolds unify and uses the BEq boundary (column_beq_ne_bare)
    to show the shortcut check fails, then shows no match arm applies. -/
-- Helper: applySubst on Int always returns Int (ground type, no vars)
private theorem applySubst_int (s : Subst) : ∀ fuel, applySubst s fuel .int = .int
  | 0 => rfl
  | _ + 1 => by unfold applySubst; rfl

-- Helper: applySubst on Column(Int) always returns Column(Int)
private theorem applySubst_column_int (s : Subst) : ∀ fuel,
    applySubst s fuel (.column .int) = .column .int
  | 0 => rfl
  | fuel + 1 => by
    unfold applySubst
    exact congrArg Ty.column (applySubst_int s fuel)

private theorem applySubstCompat_int (s : Subst) : ∀ fuel, applySubstCompat s fuel .int = .int
  | fuel => by simpa [applySubstCompat] using applySubst_int s fuel

private theorem applySubstCompat_column_int (s : Subst) : ∀ fuel,
    applySubstCompat s fuel (.column .int) = .column .int
  | fuel => by simpa [applySubstCompat] using applySubst_column_int s fuel

/-- Column(Int) does not unify with Int: the cardinality boundary holds.

    The proof traces through unify: after substitution, Column(Int) and Int
    are still distinct constructors, the BEq shortcut fails, and no match
    arm applies — falling through to the "type mismatch" error.

    This generalizes to all ground types; Int is representative. -/
theorem column_unify_int_fails (st : UnifyState) (fuel : Nat) :
    unify st (fuel + 1) (Ty.column Ty.int) Ty.int = .err "type mismatch" := by
  unfold unify
  rw [applySubstCompat_column_int st.subst fuel, applySubstCompat_int st.subst fuel]
  -- Goal: if (Column(Int) == Int) then .ok st else match ... = .err "type mismatch"
  -- Bridge == to beqTy and use column_beq_ne_bare
  have hneq : (Ty.column Ty.int == Ty.int) = false := by
    show beqTy _ _ = false
    exact column_beq_ne_bare .int
  simp [hneq]

/-- Int does not unify with Column(Int): the cardinality boundary is symmetric. -/
theorem int_unify_column_int_fails (st : UnifyState) (fuel : Nat) :
    unify st (fuel + 1) Ty.int (Ty.column Ty.int) = .err "type mismatch" := by
  unfold unify
  rw [applySubstCompat_int st.subst fuel, applySubstCompat_column_int st.subst fuel]
  have hneq : (Ty.int == Ty.column Ty.int) = false := by
    native_decide
  simp [hneq]

/-- Column inner mismatch rejects unification once inner fuel is available. -/
theorem column_inner_mismatch (st : UnifyState) :
    unify st 2 (Ty.column Ty.int) (Ty.column Ty.bool) = .err "type mismatch" := by
  have h_inner_neq : (Ty.int == Ty.bool) = false := by
    native_decide
  have h_inner : unify st 1 Ty.int Ty.bool = .err "type mismatch" := by
    unfold unify
    simp [applySubstCompat, applySubst, h_inner_neq]
  have h_outer_neq : (Ty.column Ty.int == Ty.column Ty.bool) = false := by
    native_decide
  unfold unify
  simp [applySubstCompat, applySubst, h_outer_neq, h_inner]

/-- Boundary-sensitive sites where column cardinality checks are enforced. -/
inductive ColumnBoundarySite : Type where
  | letAnnotation
  | callArgument
  | returnAnnotation
  | ascription

/-- Site-level column boundary policy.
    Current scope:
    - expected `Column(T)` requires actual `Column(T')` with matching inner type
    - expected bare types reject actual `Column(_)`
    - otherwise allowed (outside this boundary surface) -/
def columnBoundaryAllows (expected actual : Ty) : Bool :=
  match expected, actual with
  | .column e, .column a => e == a
  | .column _, _ => false
  | _, .column _ => false
  | _, _ => true

/-- Site-level wrapper for column boundary checks. -/
def columnBoundaryAllowsAtSite
    (_site : ColumnBoundarySite) (expected actual : Ty) : Bool :=
  columnBoundaryAllows expected actual

/-- Column boundary policy is currently site-invariant. -/
theorem column_boundary_policy_site_invariant
    (site1 site2 : ColumnBoundarySite) (expected actual : Ty) :
    columnBoundaryAllowsAtSite site1 expected actual =
      columnBoundaryAllowsAtSite site2 expected actual := by
  cases site1 <;> cases site2 <;> rfl

/-- Column-to-bare flow is rejected by column boundary policy. -/
theorem column_boundary_rejects_column_to_bare :
    columnBoundaryAllows Ty.int (Ty.column Ty.int) = false := by
  native_decide

/-- Bare-to-column flow is rejected by column boundary policy. -/
theorem column_boundary_rejects_bare_to_column :
    columnBoundaryAllows (Ty.column Ty.int) Ty.int = false := by
  native_decide

/-- Column inner mismatch is rejected by column boundary policy. -/
theorem column_boundary_rejects_inner_mismatch :
    columnBoundaryAllows (Ty.column Ty.int) (Ty.column Ty.bool) = false := by
  native_decide

/-- Packaged column boundary surface slice:
    site invariance + both-direction cardinality rejection and inner mismatch,
    with closure to concrete mismatch/reflexive unifier witnesses. -/
theorem column_boundary_surface_slice
    (st : UnifyState) (site : ColumnBoundarySite) :
    (columnBoundaryAllowsAtSite site Ty.int (Ty.column Ty.int) = false)
    ∧
    (columnBoundaryAllowsAtSite site (Ty.column Ty.int) Ty.int = false)
    ∧
    (columnBoundaryAllowsAtSite site (Ty.column Ty.int) (Ty.column Ty.bool) = false)
    ∧
    (unify st 1 (Ty.column Ty.int) Ty.int = .err "type mismatch")
    ∧
    (unify st 1 Ty.int (Ty.column Ty.int) = .err "type mismatch")
    ∧
    (unify st 2 (Ty.column Ty.int) (Ty.column Ty.bool) = .err "type mismatch")
    ∧
    (unify st 1 (Ty.column Ty.int) (Ty.column Ty.int) = .ok st) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases site <;> exact column_boundary_rejects_column_to_bare
  · cases site <;> exact column_boundary_rejects_bare_to_column
  · cases site <;> exact column_boundary_rejects_inner_mismatch
  · exact column_unify_int_fails st 0
  · exact int_unify_column_int_fails st 0
  · exact column_inner_mismatch st
  · have h_eq : (Ty.column Ty.int == Ty.column Ty.int) = true := by
      native_decide
    unfold unify
    simp [applySubstCompat, applySubst, h_eq]

-- =========================================================================
-- Future work: ColExpr model, infer_col_expr, verb boundary composition
-- =========================================================================

/-
  What's formalized above: the structural and semantic boundary that Column(T)
  establishes, and the round-trip properties of Lift/Force.

  COMPLETED in ColExpr.lean:
  ✓ ColExpr AST model (atom, lit, nil, binOp, capture)
  ✓ inferColExpr always returns Column(T) — `inferColExpr_always_returns_column`
  ✓ Verb boundary unwrap composition — `verb_boundary_unwrap`
  ✓ End-to-end mutate correctness — `mutate_col_type_correct`

  Remaining for the full cardinality thesis (VISION.md §2.1):

  1. **Compilation target theorem**: Formalize that `cardinality ty = .one` types
     compile to the Cranelift region and `cardinality ty = .many` types compile to
     the DataFusion region. (This is a specification, not a compiler theorem —
     the compiler doesn't exist in the Lean model.)

  2. **Nullable propagation**: The Lean ColExpr model omits Option wrapping.
     Full nullable propagation would prove that `T?` inputs produce `T?` outputs.

  The core cardinality thesis is now formal: Column(T) is always produced by
  column expression inference, unwrapped at verb boundaries, and inserted
  into output schemas at the correct element type.
-/
