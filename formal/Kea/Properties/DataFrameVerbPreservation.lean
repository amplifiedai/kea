/-
  Kea.Properties.DataFrameVerbPreservation — Schema preservation and
  transformation properties for DataFrame verb operations.

  Maps to Rust unit tests in typeck_tests.rs:
    - `infer_df_verb_filter_preserves_schema` (:2999)
    - `infer_df_verb_sort_preserves_schema` (:3083)
    - `infer_df_verb_distinct_preserves_schema` (:3100)
    - `infer_df_verb_select_restricts_schema` (:3050)

  These theorems establish type-level invariants for DataFrame verbs:
  - Filter, sort, distinct preserve the schema (identity on type)
  - Select restricts to a closed subset of columns
  - Summarize produces a closed row from aggregation outputs
  - resolveAtom extracts the correct column type via row unification
-/

import Kea.DataFrame
import Kea.Properties.UnifyReflexive
import Kea.Properties.SubstIdempotent

-- =========================================================================
-- Tier 1: Schema-preserving verbs (trivial — identity on type)
-- =========================================================================

/-- Filter preserves the DataFrame schema. -/
theorem dfFilterPreservesSchema (ty : Ty) : dfFilter ty = ty := rfl

/-- Sort preserves the DataFrame schema. -/
theorem dfSortPreservesSchema (ty : Ty) : dfSort ty = ty := rfl

/-- Distinct preserves the DataFrame schema. -/
theorem dfDistinctPreservesSchema (ty : Ty) : dfDistinct ty = ty := rfl

/-- Filter on a DataFrame yields a DataFrame. -/
theorem dfFilterYieldsDataFrame (inner : Ty) :
    dfFilter (Ty.dataframe inner) = Ty.dataframe inner := rfl

/-- Sort on a DataFrame yields a DataFrame. -/
theorem dfSortYieldsDataFrame (inner : Ty) :
    dfSort (Ty.dataframe inner) = Ty.dataframe inner := rfl

/-- Distinct on a DataFrame yields a DataFrame. -/
theorem dfDistinctYieldsDataFrame (inner : Ty) :
    dfDistinct (Ty.dataframe inner) = Ty.dataframe inner := rfl

-- =========================================================================
-- Tier 1: Schema-preserving verb composition
-- =========================================================================

/-- Filter then sort preserves schema. -/
theorem dfFilterSortPreservesSchema (ty : Ty) :
    dfSort (dfFilter ty) = ty := rfl

/-- Filter then distinct preserves schema. -/
theorem dfFilterDistinctPreservesSchema (ty : Ty) :
    dfDistinct (dfFilter ty) = ty := rfl

/-- Any chain of filter/sort/distinct preserves schema. -/
theorem dfPreservingVerbsCompose (ty : Ty) :
    dfDistinct (dfSort (dfFilter ty)) = ty := rfl

-- =========================================================================
-- Tier 2: Summarize produces a closed row
-- =========================================================================

/-- Summarize always produces a DataFrame with a closed row. -/
theorem dfSummarizeProducesClosed (columns : List (Label × Ty)) :
    ∃ row, dfSummarize columns = Ty.dataframe (Ty.anonRecord row) ∧ row.isClosed = true := by
  refine ⟨Row.closed _, rfl, ?_⟩
  simp [Row.closed, Row.isClosed, Row.rest]

/-- Summarize with no columns produces an empty closed DataFrame. -/
theorem dfSummarizeEmpty :
    dfSummarize [] = Ty.dataframe (Ty.anonRecord (Row.closed .nil)) := rfl

/-- Summarize with one column produces a single-column closed DataFrame. -/
theorem dfSummarizeSingle (l : Label) (ty : Ty) :
    dfSummarize [(l, ty)] = Ty.dataframe (Ty.anonRecord (Row.closed (.cons l ty .nil))) := rfl

-- =========================================================================
-- Tier 2: Select produces a closed row
-- =========================================================================

/-- RowFields.select on empty labels returns nil. -/
theorem rowFieldsSelectEmpty (rf : RowFields) :
    rf.select [] = .nil := by
  simp [RowFields.select]

/-- RowFields.get finds the first matching label. -/
theorem rowFieldsGetHead (l : Label) (ty : Ty) (rest : RowFields) :
    RowFields.get (RowFields.cons l ty rest) l = some ty := by
  simp [RowFields.get]

/-- RowFields.select on a single present label returns that field. -/
theorem rowFieldsSelectSingle (l : Label) (ty : Ty) (rest : RowFields) :
    (RowFields.cons l ty rest).select [l] = RowFields.cons l ty .nil := by
  simp [RowFields.select, RowFields.get]

-- =========================================================================
-- Tier 3: resolveAtom structural properties
-- =========================================================================

/--
resolveAtom's return type is always determined by the fresh type variable:
  - On success (.ok): the returned type is the substitution applied to the fresh var
  - On error (.err): the returned type is the unresolved fresh var

This is the core structural property: resolveAtom creates fresh α, unifies
to discover what α should be, then returns the resolved α.
-/
theorem resolveAtom_returns_resolved_var (st : UnifyState) (fuel : Nat)
    (label : Label) (inputTy : Ty) :
    let (result, retTy) := resolveAtom st fuel label inputTy
    match result with
    | .ok st' => retTy = applySubst st'.subst fuel (Ty.var st.nextTypeVar)
    | .err _ => retTy = Ty.var st.nextTypeVar
    := by
  simp only [resolveAtom, UnifyState.freshTypeVar, UnifyState.freshRowVar]
  generalize unify _ fuel _ _ = ur
  cases ur with
  | err _ => dsimp only []
  | ok _ => dsimp only []

/-- resolveAtom returns a type (never crashes/diverges for any fuel). -/
theorem resolveAtomTotal (st : UnifyState) (fuel : Nat) (label : Label) (inputTy : Ty) :
    ∃ r ty, resolveAtom st fuel label inputTy = (r, ty) := by
  exact ⟨_, _, rfl⟩

-- =========================================================================
-- Tier 3: decomposeFields for matching single-field rows
-- =========================================================================

/-- When two single-field rows share the same label, decomposeFields puts
    them in the common list with no left-only or right-only fields. -/
theorem decomposeFields_same_single (col : Label) (ty1 ty2 : Ty) :
    decomposeFields (.cons col ty1 .nil) (.cons col ty2 .nil) =
      ([(col, ty1, ty2)], .nil, .nil) := by
  simp [decomposeFields, decomposeFieldsGo]

-- =========================================================================
-- Infrastructure for resolveAtom proof
-- =========================================================================

-- Applying the empty substitution to any type is a no-op.
private theorem applySubst_empty (fuel : Nat) (ty : Ty) :
    applySubst Subst.empty fuel ty = ty :=
  (applySubst_noop Subst.empty fuel).1 ty
    (fun _ _ => rfl) (fun _ _ => rfl)

private theorem applySubstRow_empty (fuel : Nat) (row : Row) :
    applySubstRow Subst.empty fuel row = row :=
  (applySubst_noop Subst.empty fuel).2.1 row
    (fun _ _ => rfl) (fun _ _ => rfl)

-- beqRow is false when row rests differ (none vs some).
private theorem beqRow_none_vs_some (f1 f2 : RowFields) (rv : RowVarId) :
    beqRow (Row.mk f1 none) (Row.mk f2 (some rv)) = false := by
  simp [beqRow]

-- ¬occursIn v ty implies beqTy ty (.var v) = false.
private theorem not_occurs_beq_var_false (v : TypeVarId) (ty : Ty)
    (h : ¬(occursIn v ty = true)) : beqTy ty (.var v) = false := by
  cases h_val : beqTy ty (.var v)
  · rfl
  · exfalso; have := beqTy_sound ty (.var v) h_val; subst this; simp [occursIn] at h

-- bindTypeVar v ty 0 succeeds when ty ≠ .var v and ¬occursIn v ty.
-- (fuel 0 makes applySubst = identity, so occurs check reduces to ¬occursIn v ty)
private theorem bindTypeVar_succeeds (st : UnifyState) (v : TypeVarId) (ty : Ty)
    (h_neq : (ty == Ty.var v) = false)
    (h_not_occurs : occursIn v ty = false) :
    ∃ st', bindTypeVar st v ty 0 = .ok st' := by
  unfold bindTypeVar
  simp only [h_neq, applySubst, h_not_occurs]
  exact ⟨_, rfl⟩

-- Unifying ty against a fresh variable .var v succeeds with fuel 1
-- when ¬occursIn v ty.
private theorem unify_against_fresh_var (v : TypeVarId) (ty : Ty) (st : UnifyState)
    (h_not_occurs : ¬(occursIn v ty = true)) :
    ∃ st', unify st 1 ty (.var v) = .ok st' := by
  have h_beq : beqTy ty (.var v) = false := not_occurs_beq_var_false v ty h_not_occurs
  have h_beq' : (ty == Ty.var v) = false := h_beq
  have h_occ : occursIn v ty = false := by
    cases h : occursIn v ty <;> simp_all
  unfold unify
  -- applySubst at fuel 0 is identity for any substitution
  simp only [applySubst, h_beq']
  -- Case split: ty = .var w (first match arm) vs non-var (second match arm)
  match ty with
  | .var w =>
    -- occursIn v (.var w) = (v == w), so h_occ gives (v == w) = false
    have h_vw : v ≠ w := by
      intro heq; subst heq; simp [occursIn] at h_occ
    have h_wv : w ≠ v := fun h => h_vw h.symm
    have h_neq_vw : (Ty.var v == Ty.var w) = false := by
      show beqTy (.var v) (.var w) = false
      simp [beqTy]; exact h_vw
    have h_occ_w : occursIn w (Ty.var v) = false := by
      simp [occursIn]; exact h_wv
    exact bindTypeVar_succeeds st w (.var v) h_neq_vw h_occ_w
  | .int | .intN _ _ | .float | .floatN _ | .decimal _ _ | .bool | .string | .html | .markdown | .atom | .date | .dateTime | .unit | .dynamic =>
    exact bindTypeVar_succeeds st v _ (by simp [BEq.beq, beqTy]) (by simp [occursIn])
  | .list _ | .set _ | .option _ | .fixedSizeList _ _ | .tensor _ _ | .sum _ _ | .opaque _ _ | .dataframe _ | .groupedFrame _ _ | .tagged _ _ | .column _ | .stream _ | .task _ | .actor _ | .arc _ =>
    exact bindTypeVar_succeeds st v _ (by simp [BEq.beq, beqTy]) h_occ
  | .map _ _ | .result _ _ =>
    exact bindTypeVar_succeeds st v _ (by simp [BEq.beq, beqTy]) h_occ
  | .existential _ _ =>
    exact bindTypeVar_succeeds st v _ (by simp [BEq.beq, beqTy]) h_occ
  | .function _ _ | .forall _ _ | .app _ _ | .constructor _ _ _ =>
    exact bindTypeVar_succeeds st v _ (by simp [BEq.beq, beqTy]) h_occ
  | .tuple _ =>
    exact bindTypeVar_succeeds st v _ (by simp [BEq.beq, beqTy]) h_occ
  | .record _ _ | .anonRecord _ | .row _ =>
    exact bindTypeVar_succeeds st v _ (by simp [BEq.beq, beqTy]) h_occ

-- lacksViolation on nil fields is always false.
private theorem lacksViolation_nil (lc : Lacks) (rv : RowVarId) :
    lacksViolation lc rv .nil = false := by
  unfold lacksViolation; rfl

/--
resolveAtom on a single-column DataFrame succeeds when the fresh type variable
doesn't occur in the column type.

Traces through 5 levels of mutual recursion:
  resolveAtom → unify (DataFrame) → unify (AnonRecord) → unifyRows →
  unifyCommonFields → unify (bind var)
-/
-- Helper: the specific unification in resolveAtom for a single-column DataFrame succeeds.
private theorem unify_single_col_df (col : Label) (colTy : Ty)
    (hfresh : ¬occursIn 0 colTy = true) :
    ∃ st', unify
      { subst := Subst.empty, lacks := Lacks.empty, traitBounds := [],
        nextTypeVar := 0 + 1, nextRowVar := 0 + 1 }
      5 (Ty.dataframe (Ty.anonRecord (Row.mk (.cons col colTy .nil) none)))
        (Ty.dataframe (Ty.anonRecord (Row.mk (.cons col (.var 0) .nil) (some 0))))
      = UnifyResult.ok st' := by
  -- BEq helpers: row rests differ (none vs some) → comparison is false
  have h_neq_df :
    (Ty.dataframe (Ty.anonRecord (Row.mk (.cons col colTy .nil) none)) ==
     Ty.dataframe (Ty.anonRecord (Row.mk (.cons col (.var 0) .nil) (some 0)))) = false := by
    show beqTy _ _ = false; simp [beqTy, beqRow_none_vs_some]
  have h_neq_ar :
    (Ty.anonRecord (Row.mk (.cons col colTy .nil) none) ==
     Ty.anonRecord (Row.mk (.cons col (.var 0) .nil) (some 0))) = false := by
    show beqTy _ _ = false; simp [beqTy, beqRow_none_vs_some]
  -- Unfold all mutual recursive layers at once
  unfold unify       -- Layer 1: fuel 5, .dataframe/.dataframe
  unfold unify       -- Layer 2: fuel 4, .anonRecord/.anonRecord
  unfold unifyRows   -- Layer 3: fuel 3, row decomposition
  unfold unifyCommonFields  -- Layer 4: fuel 2, single common field
  -- Reduce everything: fuel matches, structure fields, applySubst with empty subst,
  -- BEq comparisons, if-then-else, decomposeFields, pattern matching
  dsimp only []
  simp only [applySubst_empty, applySubstRow_empty, h_neq_df, h_neq_ar]
  simp (config := { decide := true }) only [ite_false]
  simp only [Row.fields, Row.rest, decomposeFields_same_single]
  -- Goal: match (match unify st 1 colTy (.var 0) with ...) with ... = .ok st'
  -- Step 1: Rewrite inner unify using helper lemma
  have h_inner := unify_against_fresh_var 0 colTy
    (UnifyState.mk Subst.empty Lacks.empty [] (0 + 1) (0 + 1)) hfresh
  obtain ⟨st_inner, h_ok⟩ := h_inner
  simp only [h_ok]
  -- Step 2: unifyCommonFields st_inner 1 [] → .ok st_inner
  unfold unifyCommonFields
  dsimp only []
  -- Step 3: Reduce RowFields.nil.length > 0 → false, lacksViolation_nil → false
  simp only [RowFields.length, lacksViolation_nil]
  simp (config := { decide := true }) only [ite_false]
  exact ⟨_, rfl⟩

theorem resolveAtom_single_col_succeeds (col : Label) (colTy : Ty)
    (hfresh : ¬occursIn 0 colTy = true) :
    match resolveAtom UnifyState.empty 5 col
      (Ty.dataframe (Ty.anonRecord (Row.closed (.cons col colTy .nil)))) with
    | (.ok _, _) => True
    | (.err _, _) => False
    := by
  -- Unfold resolveAtom and reduce all structure operations
  unfold resolveAtom
  dsimp only [UnifyState.freshTypeVar, UnifyState.freshRowVar,
              UnifyState.empty, Row.mkOpen, Row.closed]
  -- Use the helper lemma to establish the unify succeeds
  have h := unify_single_col_df col colTy hfresh
  obtain ⟨st', hok⟩ := h
  -- Rewrite the unify call in the goal; both matches reduce to True
  simp only [hok]
