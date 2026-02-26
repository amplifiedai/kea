/-
  Kea.Properties.DecomposeFields — Properties of row field decomposition.

  Key lemma: decomposing identical field lists produces all-common entries
  (with matching types) and empty only-left/only-right lists. This is the
  foundation for unifyRowsReflexive and related Rémy row properties.
-/

import Kea.Unify
import Kea.Properties.SubstIdempotent
import Kea.Properties.UnifyReflexive

-- =========================================================================
-- Label ordering properties
-- =========================================================================

/-- String < is irreflexive: no string is less than itself.
    Required because decomposeFieldsGo uses label ordering to merge fields. -/
private theorem label_lt_irrefl (l : Label) : ¬(l < l) :=
  String.lt_irrefl l

/-- Two labels that are not ordered in either direction are equal.
    Uses String.le_antisymm and String.not_lt from batteries. -/
private theorem label_eq_of_not_lt (l1 l2 : Label)
    (h1 : ¬(l1 < l2)) (h2 : ¬(l2 < l1)) : l1 = l2 :=
  String.le_antisymm (String.not_lt.mp h2) (String.not_lt.mp h1)

-- =========================================================================
-- decomposeFieldsGo on identical inputs
-- =========================================================================

/-- Decomposing identical field lists against themselves:
    - preserves the only-left and only-right accumulators unchanged
    - all entries in the result common list have matching types (t1 = t2)

    Generalizes over the common accumulator for the inductive argument.
    The precondition requires the initial common entries to already have
    matching types. Uses match instead of induction (mutual inductive). -/
theorem decomposeFieldsGo_self (rf : RowFields)
    (common : List (Label × Ty × Ty))
    (h : ∀ e ∈ common, e.2.1 = e.2.2) :
    let result := decomposeFieldsGo rf rf common .nil .nil
    result.2.1 = .nil ∧ result.2.2 = .nil ∧ (∀ e ∈ result.1, e.2.1 = e.2.2) :=
  match rf with
  | .nil => by
    unfold decomposeFieldsGo
    exact ⟨rfl, rfl, fun e he => h e (List.mem_reverse.mp he)⟩
  | .cons l ty rest => by
    unfold decomposeFieldsGo
    have hlt : ¬(l < l) := label_lt_irrefl l
    rw [if_neg hlt, if_neg hlt]
    exact decomposeFieldsGo_self rest ((l, ty, ty) :: common) (by
      intro e he
      cases he with
      | head => rfl
      | tail _ h' => exact h e h')

/-- Corollary: decomposeFields on identical field lists produces
    empty only-left and only-right, with all common entries matching. -/
theorem decomposeFields_self (rf : RowFields) :
    let (common, onlyL, onlyR) := decomposeFields rf rf
    onlyL = .nil ∧ onlyR = .nil ∧ (∀ e ∈ common, e.2.1 = e.2.2) := by
  unfold decomposeFields
  exact decomposeFieldsGo_self rf [] (fun _ h => nomatch h)

-- =========================================================================
-- decomposeFieldsGo common list length tracks field count
-- =========================================================================

/-- The common list produced by decomposeFieldsGo on identical fields
    has length = initial accumulator length + field count. -/
theorem decomposeFieldsGo_self_common_length
    (rf : RowFields) (common : List (Label × Ty × Ty))
    (onlyL onlyR : RowFields) :
    (decomposeFieldsGo rf rf common onlyL onlyR).1.length =
    common.length + RowFields.length rf := by
  match rf with
  | .nil =>
    unfold decomposeFieldsGo
    simp [List.length_reverse, RowFields.length]
  | .cons l _ty rest =>
    unfold decomposeFieldsGo
    have hlt : ¬(l < l) := label_lt_irrefl l
    rw [if_neg hlt, if_neg hlt]
    rw [decomposeFieldsGo_self_common_length rest ((l, _ty, _ty) :: common) onlyL onlyR]
    simp [List.length_cons, RowFields.length]
    omega

/-- The common list from decomposeFields on identical fields has the same
    length as the field list. -/
theorem decomposeFields_self_common_length (rf : RowFields) :
    (decomposeFields rf rf).1.length = RowFields.length rf := by
  unfold decomposeFields
  rw [decomposeFieldsGo_self_common_length rf [] .nil .nil]
  simp

-- =========================================================================
-- unifyCommonFields succeeds when all types match
-- =========================================================================

/-- When all common field entries have matching types (t1 = t2),
    unifyCommonFields succeeds given fuel proportional to the list length.

    Each entry consumes one fuel unit (for the outer match) and calls
    unify with the remaining fuel. Since unify(t, t) succeeds for any
    fuel ≥ 1 (by unifyReflexive), the total fuel needed is length + 1. -/
theorem unifyCommonFields_refl
    (st : UnifyState) (common : List (Label × Ty × Ty))
    (h : ∀ e ∈ common, e.2.1 = e.2.2) :
    ∃ st', unifyCommonFields st (common.length + 1) common = .ok st' := by
  match common with
  | [] =>
    unfold unifyCommonFields
    exact ⟨st, rfl⟩
  | (l, ty1, ty2) :: rest =>
    have heq : ty1 = ty2 := h (l, ty1, ty2) (.head _)
    subst heq
    -- Fuel = rest.length + 2 = (rest.length + 1) + 1
    simp only [List.length_cons]
    -- Reduce unifyCommonFields on the cons case
    unfold unifyCommonFields
    dsimp only
    -- Goal now has: match unify st (rest.length + 1) ty1 ty1 with ...
    -- unify st (rest.length + 1) ty1 ty1 succeeds by unifyReflexive
    have ⟨st_u, hu⟩ := unifyReflexive st rest.length ty1
    rw [hu]
    -- Now: unifyCommonFields st_u (rest.length + 1) rest
    exact unifyCommonFields_refl st_u rest (fun e he => h e (.tail _ he))

-- =========================================================================
-- unifyCommonFields_refl with generalized fuel (≥ version)
-- =========================================================================

/-- Stronger form: unifyCommonFields succeeds with any fuel ≥ common.length + 1
    when all types match. Moreover, the state is returned unchanged.

    This is the form needed by unifyRowsReflexive where the fuel is
    determined by the outer context, not the common list length. -/
theorem unifyCommonFields_refl_ge
    (st : UnifyState) (fuel : Nat) (common : List (Label × Ty × Ty))
    (h_types : ∀ e ∈ common, e.2.1 = e.2.2)
    (h_fuel : fuel ≥ common.length + 1) :
    unifyCommonFields st fuel common = .ok st := by
  match common with
  | [] =>
    match fuel, h_fuel with
    | fuel' + 1, _ =>
      unfold unifyCommonFields
      rfl
  | (l, ty1, ty2) :: rest =>
    have heq : ty1 = ty2 := h_types (l, ty1, ty2) (.head _)
    subst heq
    -- fuel ≥ rest.length + 2 ≥ 2
    have hf2 : fuel ≥ 2 := by simp [List.length_cons] at h_fuel; omega
    -- Extract f such that fuel = f + 2 (so the inner fuel after two peels is f)
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 2 := ⟨fuel - 2, by omega⟩
    -- After unfolding: match (f + 2) with (f+1) + 1 => ...
    -- Inner call: unify st (f + 1) ty1 ty1
    unfold unifyCommonFields
    dsimp only
    -- unifyReflexive' st f ty1 : unify st (f + 1) ty1 ty1 = .ok st
    rw [unifyReflexive' st f ty1]
    -- Goal: unifyCommonFields st (f + 1) rest = .ok st
    -- Need: f + 1 ≥ rest.length + 1
    exact unifyCommonFields_refl_ge st (f + 1) rest
      (fun e he => h_types e (.tail _ he))
      (by simp [List.length_cons] at h_fuel; omega)

-- =========================================================================
-- unifyRowsReflexive: row unification reflexivity
-- =========================================================================

/-- General form: unifyRows on a row with itself succeeds when we know what
    the substitution resolves the row to, and fuel is sufficient for the
    resolved field count.

    This is the workhorse for row unification reflexivity — both sides resolve
    to the same row (since the input is identical), decomposeFields produces
    all-common matching entries, and unifyCommonFields succeeds via BEq. -/
theorem unifyRows_self_via_resolution (st : UnifyState) (row resolvedRow : Row)
    (fuel : Nat) (h_fuel : fuel ≥ RowFields.length resolvedRow.fields + 2)
    (h_resolved : applySubstRow st.subst (fuel - 1) row = resolvedRow) :
    unifyRows st fuel row row = .ok st := by
  -- Extract fuel structure: fuel = f + 2
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 2 := ⟨fuel - 2, by omega⟩
  -- Simplify the hypothesis: (f + 2) - 1 = f + 1
  have h_simp : f + 2 - 1 = f + 1 := by omega
  rw [h_simp] at h_resolved
  -- Unfold unifyRows and reduce substitution applications + let-bindings
  unfold unifyRows
  simp only [h_resolved]
  -- Now goal is about decomposeFields resolvedRow.fields resolvedRow.fields
  have hds := decomposeFields_self resolvedRow.fields
  have h_clen := decomposeFields_self_common_length resolvedRow.fields
  -- Generalize the decomposition result
  generalize decomposeFields resolvedRow.fields resolvedRow.fields = d at *
  obtain ⟨common, onlyL, onlyR⟩ := d
  simp only [] at hds
  obtain ⟨hdl, hdr, hcommon⟩ := hds
  subst hdl; subst hdr
  simp only [] at h_clen
  -- unifyCommonFields succeeds since all types match
  have h_common_fuel : f + 1 ≥ common.length + 1 := by omega
  rw [unifyCommonFields_refl_ge st (f + 1) common hcommon h_common_fuel]
  -- Case split on resolvedRow.rest (both sides are the same)
  match resolvedRow.rest with
  | none => simp [RowFields.length]
  | some rv =>
    simp [RowFields.length, BEq.beq]

/-- Special case: when the row is a fixed point of substitution application. -/
theorem unifyRows_self_fixed (st : UnifyState) (row : Row)
    (fuel : Nat) (h_fuel : fuel ≥ RowFields.length row.fields + 2)
    (h_fixed : applySubstRow st.subst (fuel - 1) row = row) :
    unifyRows st fuel row row = .ok st :=
  unifyRows_self_via_resolution st row row fuel h_fuel h_fixed

-- =========================================================================
-- applySubstRow field length for closed/unbound rows
-- =========================================================================

/-- For closed rows, applySubstRow preserves the field count.
    The resolved row has fields = applySubstRowFields(...) and rest = none. -/
theorem applySubstRow_closed_fields_length (s : Subst) (fuel : Nat) (fields : RowFields) :
    RowFields.length (applySubstRow s (fuel + 1) (Row.mk fields none)).fields =
    RowFields.length fields := by
  unfold applySubstRow
  exact applySubstRowFields_preserves_length s fuel fields

/-- For open rows with unbound variable, applySubstRow preserves the field count. -/
theorem applySubstRow_open_unbound_fields_length (s : Subst) (fuel : Nat) (fields : RowFields)
    (rv : RowVarId) (h_unbound : s.rowMap rv = none) :
    RowFields.length (applySubstRow s (fuel + 1) (Row.mk fields (some rv))).fields =
    RowFields.length fields := by
  unfold applySubstRow
  simp only [h_unbound]
  exact applySubstRowFields_preserves_length s fuel fields

-- =========================================================================
-- RowFields.append preserves length
-- =========================================================================

/-- Appending two row field lists sums their lengths. -/
theorem RowFields.append_length (a b : RowFields) :
    RowFields.length (a.append b) = RowFields.length a + RowFields.length b := by
  match a with
  | .nil => simp [RowFields.append, RowFields.length]
  | .cons _ _ rest =>
    simp only [RowFields.append, RowFields.length]
    rw [RowFields.append_length rest b]
    omega

-- =========================================================================
-- applySubstRow field length for bound row variables
-- =========================================================================

/-- For open rows with a bound variable whose resolved row is a fixed point
    of substitution, applySubstRow computes to a known row. -/
private theorem applySubstRow_bound_eq
    (s : Subst) (fuel : Nat) (fields : RowFields)
    (rv : RowVarId) (rFields : RowFields) (rRest : Option RowVarId)
    (h_lookup : s.rowMap rv = some (Row.mk rFields rRest))
    (h_noop : applySubstRow s fuel (Row.mk rFields rRest) = Row.mk rFields rRest) :
    applySubstRow s (fuel + 1) (Row.mk fields (some rv)) =
    Row.mk ((applySubstRowFields s fuel fields).append rFields) rRest := by
  unfold applySubstRow
  simp only [h_lookup, h_noop]

/-- Corollary: the field count of the bound-variable resolved row. -/
private theorem applySubstRow_bound_fields_length
    (s : Subst) (fuel : Nat) (fields : RowFields)
    (rv : RowVarId) (rFields : RowFields) (rRest : Option RowVarId)
    (h_lookup : s.rowMap rv = some (Row.mk rFields rRest))
    (h_noop : applySubstRow s fuel (Row.mk rFields rRest) = Row.mk rFields rRest) :
    RowFields.length (applySubstRow s (fuel + 1) (Row.mk fields (some rv))).fields =
    RowFields.length fields + RowFields.length rFields := by
  rw [applySubstRow_bound_eq s fuel fields rv rFields rRest h_lookup h_noop]
  simp only [Row.fields]
  rw [RowFields.append_length, applySubstRowFields_preserves_length]

-- =========================================================================
-- unifyRowsReflexive: existential form
-- =========================================================================

/-- Unifying any row with itself succeeds given sufficient fuel.

    Requires an idempotent substitution (range vars disjoint from domain)
    to ensure the bound row variable case terminates — cyclic substitutions
    would expand indefinitely, making the theorem false. The Rust implementation
    maintains this invariant via the occurs check. -/
theorem unifyRowsReflexive' (st : UnifyState) (r : Row)
    (h_idemp : Subst.Idempotent st.subst) :
    ∃ fuel st', unifyRows st fuel r r = .ok st' := by
  match r with
  | .mk fields none =>
    -- Closed row: resolved fields have same length as original
    refine ⟨RowFields.length fields + 2, st, ?_⟩
    apply unifyRows_self_via_resolution st (.mk fields none)
      (applySubstRow st.subst (RowFields.length fields + 1) (.mk fields none))
      (RowFields.length fields + 2)
    · -- h_fuel: fuel ≥ resolved.fields.length + 2
      rw [applySubstRow_closed_fields_length]; omega
    · -- h_resolved: applySubstRow produces the resolved row
      simp
  | .mk fields (some rv) =>
    match h_lookup : st.subst.rowMap rv with
    | none =>
      -- Unbound row variable: same field count as original
      refine ⟨RowFields.length fields + 2, st, ?_⟩
      apply unifyRows_self_via_resolution st (.mk fields (some rv))
        (applySubstRow st.subst (RowFields.length fields + 1) (.mk fields (some rv)))
        (RowFields.length fields + 2)
      · -- h_fuel
        rw [applySubstRow_open_unbound_fields_length _ _ _ _ h_lookup]; omega
      · -- h_resolved
        simp
    | some resolvedRow =>
      -- Bound row variable: with idempotent substitution, the resolved row
      -- is a fixed point (its free vars are outside the domain), so we can
      -- compute the exact field count after one application.
      obtain ⟨rFields, rRest⟩ := resolvedRow
      have h_range := h_idemp.rowRange rv (Row.mk rFields rRest) h_lookup
      have h_noop_row : ∀ fuel, applySubstRow st.subst fuel (Row.mk rFields rRest) = Row.mk rFields rRest :=
        fun fuel => (applySubst_noop st.subst fuel).2.1 (Row.mk rFields rRest) h_range.1 h_range.2
      let N := RowFields.length fields + RowFields.length rFields
      refine ⟨N + 3, st, ?_⟩
      apply unifyRows_self_via_resolution st (Row.mk fields (some rv))
        (applySubstRow st.subst (N + 2) (Row.mk fields (some rv)))
        (N + 3)
      · -- h_fuel: N + 3 ≥ resolved.fields.length + 2
        rw [applySubstRow_bound_fields_length st.subst (N + 1) fields rv
          rFields rRest h_lookup (h_noop_row (N + 1))]
        omega
      · -- h_resolved: (N + 3) - 1 = N + 2, tautological
        simp

-- =========================================================================
-- Public version (co-located here to avoid circular imports with
-- UnifyReflexive.lean which DecomposeFields already imports)
-- =========================================================================

/-- Unifying any row with itself succeeds given sufficient fuel.
    Unlike `unifyReflexive` (which is fuel-independent thanks to the BEq
    shortcut in `unify`), `unifyRows` decomposes fields and unifies them
    pairwise, consuming fuel proportional to the field count.

    Requires an idempotent substitution to ensure the bound row variable
    case terminates. Without this, cyclic row bindings would make the
    theorem false. The Rust implementation maintains idempotency via the
    occurs check. -/
theorem unifyRowsReflexive (st : UnifyState) (r : Row)
    (h_idemp : Subst.Idempotent st.subst) :
    ∃ fuel st', unifyRows st fuel r r = .ok st' :=
  unifyRowsReflexive' st r h_idemp

-- =========================================================================
-- Decomposition coverage: labels from right end up in common or onlyRight
-- =========================================================================

/-- Helper: RowFields.has on cons distributes over BEq check. -/
private theorem RowFields.has_cons (l label : Label) (ty : Ty) (rest : RowFields) :
    RowFields.has (.cons label ty rest) l = (label == l || rest.has l) := by
  simp only [RowFields.has]

/-- Every label from the right input or the onlyR accumulator or the common
    accumulator ends up either in the result's onlyRight or result's common.

    This is the decomposition coverage property: decomposeFieldsGo faithfully
    partitions all right-side labels. -/
theorem decomposeFieldsGo_right_coverage
    (left right : RowFields)
    (common : List (Label × Ty × Ty))
    (onlyL onlyR : RowFields) (l : Label) :
    right.has l = true ∨ onlyR.has l = true ∨ (∃ ty1 ty2, (l, ty1, ty2) ∈ common) →
    let result := decomposeFieldsGo left right common onlyL onlyR
    result.2.2.has l = true ∨ (∃ ty1 ty2, (l, ty1, ty2) ∈ result.1) := by
  intro h_in
  match left, right with
  | .nil, .nil =>
    -- Base case: result = (common.reverse, onlyL, onlyR)
    unfold decomposeFieldsGo
    simp only [RowFields.has] at h_in
    cases h_in with
    | inl h => exact absurd h (by decide)
    | inr h =>
      cases h with
      | inl h_onlyR => exact .inl h_onlyR
      | inr h_common =>
        right
        obtain ⟨ty1, ty2, h_mem⟩ := h_common
        exact ⟨ty1, ty2, List.mem_reverse.mpr h_mem⟩
  | .nil, .cons l2 ty2 rest2 =>
    -- Right non-empty: l2 goes to onlyR, recurse
    unfold decomposeFieldsGo
    apply decomposeFieldsGo_right_coverage .nil rest2 common onlyL (.cons l2 ty2 onlyR) l
    -- Transform antecedent
    cases h_in with
    | inl h_right =>
      simp only [RowFields.has] at h_right
      cases h_eq : (l2 == l) with
      | true =>
        right; left
        simp only [RowFields.has, h_eq, Bool.true_or]
      | false =>
        simp only [h_eq, Bool.false_or] at h_right
        left; exact h_right
    | inr h =>
      cases h with
      | inl h_onlyR =>
        right; left
        simp only [RowFields.has]
        rw [h_onlyR]; simp
      | inr h_common =>
        right; right; exact h_common
  | .cons l1 ty1 rest1, .nil =>
    -- Left non-empty, right empty: l1 goes to onlyL, recurse
    unfold decomposeFieldsGo
    apply decomposeFieldsGo_right_coverage rest1 .nil common (.cons l1 ty1 onlyL) onlyR l
    simp only [RowFields.has] at h_in
    cases h_in with
    | inl h => exact absurd h (by decide)
    | inr h => exact .inr h
  | .cons l1 ty1 rest1, .cons l2 ty2 rest2 =>
    -- Both non-empty: case split on label comparison
    unfold decomposeFieldsGo
    by_cases h_lt : l1 < l2
    · -- l1 < l2: l1 goes to onlyL, recurse with full right
      simp only [h_lt, ↓reduceIte]
      apply decomposeFieldsGo_right_coverage rest1 (.cons l2 ty2 rest2) common
        (.cons l1 ty1 onlyL) onlyR l
      exact h_in
    · simp only [h_lt, ↓reduceIte]
      by_cases h_lt2 : l2 < l1
      · -- l2 < l1: l2 goes to onlyR, recurse with full left
        simp only [h_lt2, ↓reduceIte]
        apply decomposeFieldsGo_right_coverage (.cons l1 ty1 rest1) rest2 common
          onlyL (.cons l2 ty2 onlyR) l
        cases h_in with
        | inl h_right =>
          simp only [RowFields.has] at h_right
          cases h_eq : (l2 == l) with
          | true =>
            right; left
            simp only [RowFields.has, h_eq, Bool.true_or]
          | false =>
            simp only [h_eq, Bool.false_or] at h_right
            left; exact h_right
        | inr h =>
          cases h with
          | inl h_onlyR =>
            right; left
            simp only [RowFields.has]
            rw [h_onlyR]; simp
          | inr h_common =>
            right; right; exact h_common
      · -- l1 = l2: both go to common, recurse with rests
        simp only [h_lt2, ↓reduceIte]
        apply decomposeFieldsGo_right_coverage rest1 rest2 ((l1, ty1, ty2) :: common)
          onlyL onlyR l
        cases h_in with
        | inl h_right =>
          simp only [RowFields.has] at h_right
          cases h_eq : (l2 == l) with
          | true =>
            -- l2 = l, and l1 = l2 (from not lt either way), so (l, ty1, ty2) ∈ common
            have h_l2_eq : l2 = l := beq_iff_eq.mp h_eq
            have h_l1_eq : l1 = l2 := label_eq_of_not_lt l1 l2 h_lt h_lt2
            right; right
            exact ⟨ty1, ty2, by rw [h_l1_eq, h_l2_eq]; exact .head _⟩
          | false =>
            simp only [h_eq, Bool.false_or] at h_right
            left; exact h_right
        | inr h =>
          cases h with
          | inl h_onlyR =>
            right; left; exact h_onlyR
          | inr h_common =>
            right; right
            obtain ⟨t1, t2, h_mem⟩ := h_common
            exact ⟨t1, t2, .tail _ h_mem⟩

/-- Corollary: every label in the right field list appears in either the
    common list or onlyRight after decomposition. -/
theorem decomposeFields_right_coverage
    (left right : RowFields) (l : Label) :
    right.has l = true →
    let (common, _onlyL, onlyR) := decomposeFields left right
    onlyR.has l = true ∨ (∃ ty1 ty2, (l, ty1, ty2) ∈ common) := by
  intro h_has
  unfold decomposeFields
  exact decomposeFieldsGo_right_coverage left right [] .nil .nil l (.inl h_has)

/-- Symmetric version: every label in the left field list appears in either
    the common list or onlyLeft after decomposition. -/
theorem decomposeFieldsGo_left_coverage
    (left right : RowFields)
    (common : List (Label × Ty × Ty))
    (onlyL onlyR : RowFields) (l : Label) :
    left.has l = true ∨ onlyL.has l = true ∨ (∃ ty1 ty2, (l, ty1, ty2) ∈ common) →
    let result := decomposeFieldsGo left right common onlyL onlyR
    result.2.1.has l = true ∨ (∃ ty1 ty2, (l, ty1, ty2) ∈ result.1) := by
  intro h_in
  match left, right with
  | .nil, .nil =>
    unfold decomposeFieldsGo
    simp only [RowFields.has] at h_in
    cases h_in with
    | inl h => exact absurd h (by decide)
    | inr h =>
      cases h with
      | inl h_onlyL => exact .inl h_onlyL
      | inr h_common =>
        right
        obtain ⟨ty1, ty2, h_mem⟩ := h_common
        exact ⟨ty1, ty2, List.mem_reverse.mpr h_mem⟩
  | .nil, .cons l2 ty2 rest2 =>
    -- Right non-empty, left empty: l2 goes to onlyR
    unfold decomposeFieldsGo
    apply decomposeFieldsGo_left_coverage .nil rest2 common onlyL (.cons l2 ty2 onlyR) l
    simp only [RowFields.has] at h_in
    cases h_in with
    | inl h => exact absurd h (by decide)
    | inr h => exact .inr h
  | .cons l1 ty1 rest1, .nil =>
    -- Left non-empty: l1 goes to onlyL, recurse
    unfold decomposeFieldsGo
    apply decomposeFieldsGo_left_coverage rest1 .nil common (.cons l1 ty1 onlyL) onlyR l
    cases h_in with
    | inl h_left =>
      simp only [RowFields.has] at h_left
      cases h_eq : (l1 == l) with
      | true =>
        right; left
        simp only [RowFields.has, h_eq, Bool.true_or]
      | false =>
        simp only [h_eq, Bool.false_or] at h_left
        left; exact h_left
    | inr h =>
      cases h with
      | inl h_onlyL =>
        right; left
        simp only [RowFields.has]
        rw [h_onlyL]; simp
      | inr h_common =>
        right; right; exact h_common
  | .cons l1 ty1 rest1, .cons l2 ty2 rest2 =>
    unfold decomposeFieldsGo
    by_cases h_lt : l1 < l2
    · -- l1 < l2: l1 goes to onlyL, recurse
      simp only [h_lt, ↓reduceIte]
      apply decomposeFieldsGo_left_coverage rest1 (.cons l2 ty2 rest2) common
        (.cons l1 ty1 onlyL) onlyR l
      cases h_in with
      | inl h_left =>
        simp only [RowFields.has] at h_left
        cases h_eq : (l1 == l) with
        | true =>
          right; left
          simp only [RowFields.has, h_eq, Bool.true_or]
        | false =>
          simp only [h_eq, Bool.false_or] at h_left
          left; exact h_left
      | inr h =>
        cases h with
        | inl h_onlyL =>
          right; left
          simp only [RowFields.has]
          rw [h_onlyL]; simp
        | inr h_common =>
          right; right; exact h_common
    · simp only [h_lt, ↓reduceIte]
      by_cases h_lt2 : l2 < l1
      · -- l2 < l1: l2 goes to onlyR, recurse with full left
        simp only [h_lt2, ↓reduceIte]
        apply decomposeFieldsGo_left_coverage (.cons l1 ty1 rest1) rest2 common
          onlyL (.cons l2 ty2 onlyR) l
        exact h_in
      · -- l1 = l2: both go to common
        simp only [h_lt2, ↓reduceIte]
        apply decomposeFieldsGo_left_coverage rest1 rest2 ((l1, ty1, ty2) :: common)
          onlyL onlyR l
        cases h_in with
        | inl h_left =>
          simp only [RowFields.has] at h_left
          cases h_eq : (l1 == l) with
          | true =>
            right; right
            exact ⟨ty1, ty2, by rw [beq_iff_eq.mp h_eq]; exact .head _⟩
          | false =>
            simp only [h_eq, Bool.false_or] at h_left
            left; exact h_left
        | inr h =>
          cases h with
          | inl h_onlyL =>
            right; left; exact h_onlyL
          | inr h_common =>
            right; right
            obtain ⟨t1, t2, h_mem⟩ := h_common
            exact ⟨t1, t2, .tail _ h_mem⟩

/-- Corollary: every label in the left field list appears in either the
    common list or onlyLeft after decomposition. -/
theorem decomposeFields_left_coverage
    (left right : RowFields) (l : Label) :
    left.has l = true →
    let (common, onlyL, _onlyR) := decomposeFields left right
    onlyL.has l = true ∨ (∃ ty1 ty2, (l, ty1, ty2) ∈ common) := by
  intro h_has
  unfold decomposeFields
  exact decomposeFieldsGo_left_coverage left right [] .nil .nil l (.inl h_has)

/-- Helper: if rest has l, then cons l' ty rest also has l. -/
private theorem RowFields.has_of_tail (l l' : Label) (ty' : Ty) (rest : RowFields) :
    RowFields.has rest l = true → RowFields.has (RowFields.cons l' ty' rest) l = true := by
  intro h; unfold RowFields.has; rw [h]; simp

/-- Go-level: every entry in the result common list either came from the
    accumulator or corresponds to a label in the left input. -/
theorem decomposeFieldsGo_common_in_left
    (left right : RowFields)
    (common : List (Label × Ty × Ty))
    (onlyL onlyR : RowFields) (l : Label) (ty1 ty2 : Ty) :
    (l, ty1, ty2) ∈ (decomposeFieldsGo left right common onlyL onlyR).1 →
    left.has l = true ∨ (l, ty1, ty2) ∈ common := by
  match left, right with
  | .nil, .nil =>
    unfold decomposeFieldsGo
    intro h
    exact .inr (List.mem_reverse.mp h)
  | .nil, .cons l2 ty2' rest2 =>
    unfold decomposeFieldsGo
    intro h
    have ih := decomposeFieldsGo_common_in_left .nil rest2 common onlyL (.cons l2 ty2' onlyR) l ty1 ty2 h
    cases ih with
    | inl h_has => simp [RowFields.has] at h_has
    | inr h_mem => exact .inr h_mem
  | .cons l1 ty1' rest1, .nil =>
    unfold decomposeFieldsGo
    intro h
    have ih := decomposeFieldsGo_common_in_left rest1 .nil common (.cons l1 ty1' onlyL) onlyR l ty1 ty2 h
    cases ih with
    | inl h_has => exact .inl (RowFields.has_of_tail l l1 ty1' rest1 h_has)
    | inr h_mem => exact .inr h_mem
  | .cons l1 ty1' rest1, .cons l2 ty2' rest2 =>
    unfold decomposeFieldsGo
    by_cases h_lt : l1 < l2
    · simp only [h_lt, ↓reduceIte]
      intro h
      have ih := decomposeFieldsGo_common_in_left rest1 (.cons l2 ty2' rest2) common
        (.cons l1 ty1' onlyL) onlyR l ty1 ty2 h
      cases ih with
      | inl h_has => exact .inl (RowFields.has_of_tail l l1 ty1' rest1 h_has)
      | inr h_mem => exact .inr h_mem
    · simp only [h_lt, ↓reduceIte]
      by_cases h_lt2 : l2 < l1
      · simp only [h_lt2, ↓reduceIte]
        intro h
        have ih := decomposeFieldsGo_common_in_left (.cons l1 ty1' rest1) rest2 common
          onlyL (.cons l2 ty2' onlyR) l ty1 ty2 h
        exact ih
      · -- l1 = l2
        simp only [h_lt2, ↓reduceIte]
        intro h
        have ih := decomposeFieldsGo_common_in_left rest1 rest2 ((l1, ty1', ty2') :: common)
          onlyL onlyR l ty1 ty2 h
        cases ih with
        | inl h_has => exact .inl (RowFields.has_of_tail l l1 ty1' rest1 h_has)
        | inr h_mem =>
          cases h_mem with
          | head =>
            -- Lean unifies (l, ty1, ty2) with (l1, ty1', ty2'), so l = l1
            exact .inl (by simp only [RowFields.has]; simp)
          | tail _ h_rest =>
            exact .inr h_rest

/-- Common labels appear in both left and right. -/
theorem decomposeFields_common_in_left
    (left right : RowFields) (l : Label) (ty1 ty2 : Ty) :
    (l, ty1, ty2) ∈ (decomposeFields left right).1 →
    left.has l = true := by
  intro h
  unfold decomposeFields at h
  have ih := decomposeFieldsGo_common_in_left left right [] .nil .nil l ty1 ty2 h
  cases ih with
  | inl h_has => exact h_has
  | inr h_mem => exact absurd h_mem (by simp)

/-- Go-level: every entry in the result common list either came from the
    accumulator or corresponds to a label in the right input. -/
theorem decomposeFieldsGo_common_in_right
    (left right : RowFields)
    (common : List (Label × Ty × Ty))
    (onlyL onlyR : RowFields) (l : Label) (ty1 ty2 : Ty) :
    (l, ty1, ty2) ∈ (decomposeFieldsGo left right common onlyL onlyR).1 →
    right.has l = true ∨ (l, ty1, ty2) ∈ common := by
  match left, right with
  | .nil, .nil =>
    unfold decomposeFieldsGo
    intro h
    exact .inr (List.mem_reverse.mp h)
  | .nil, .cons l2 ty2' rest2 =>
    unfold decomposeFieldsGo
    intro h
    have ih := decomposeFieldsGo_common_in_right .nil rest2 common onlyL (.cons l2 ty2' onlyR) l ty1 ty2 h
    cases ih with
    | inl h_has => exact .inl (RowFields.has_of_tail l l2 ty2' rest2 h_has)
    | inr h_mem => exact .inr h_mem
  | .cons l1 ty1' rest1, .nil =>
    unfold decomposeFieldsGo
    intro h
    have ih := decomposeFieldsGo_common_in_right rest1 .nil common (.cons l1 ty1' onlyL) onlyR l ty1 ty2 h
    cases ih with
    | inl h_has => simp [RowFields.has] at h_has
    | inr h_mem => exact .inr h_mem
  | .cons l1 ty1' rest1, .cons l2 ty2' rest2 =>
    unfold decomposeFieldsGo
    by_cases h_lt : l1 < l2
    · simp only [h_lt, ↓reduceIte]
      intro h
      have ih := decomposeFieldsGo_common_in_right rest1 (.cons l2 ty2' rest2) common
        (.cons l1 ty1' onlyL) onlyR l ty1 ty2 h
      exact ih
    · simp only [h_lt, ↓reduceIte]
      by_cases h_lt2 : l2 < l1
      · simp only [h_lt2, ↓reduceIte]
        intro h
        have ih := decomposeFieldsGo_common_in_right (.cons l1 ty1' rest1) rest2 common
          onlyL (.cons l2 ty2' onlyR) l ty1 ty2 h
        cases ih with
        | inl h_has => exact .inl (RowFields.has_of_tail l l2 ty2' rest2 h_has)
        | inr h_mem => exact .inr h_mem
      · -- l1 = l2
        simp only [h_lt2, ↓reduceIte]
        intro h
        have ih := decomposeFieldsGo_common_in_right rest1 rest2 ((l1, ty1', ty2') :: common)
          onlyL onlyR l ty1 ty2 h
        cases ih with
        | inl h_has => exact .inl (RowFields.has_of_tail l l2 ty2' rest2 h_has)
        | inr h_mem =>
          cases h_mem with
          | head =>
            -- Lean unifies l := l1, so now h_lt : ¬(l < l2), h_lt2 : ¬(l2 < l)
            -- label_eq_of_not_lt gives l = l2
            exact .inl (by simp only [RowFields.has]; rw [label_eq_of_not_lt _ _ h_lt h_lt2]; simp)
          | tail _ h_rest =>
            exact .inr h_rest

/-- Common labels appear in both left and right. -/
theorem decomposeFields_common_in_right
    (left right : RowFields) (l : Label) (ty1 ty2 : Ty) :
    (l, ty1, ty2) ∈ (decomposeFields left right).1 →
    right.has l = true := by
  intro h
  unfold decomposeFields at h
  have ih := decomposeFieldsGo_common_in_right left right [] .nil .nil l ty1 ty2 h
  cases ih with
  | inl h_has => exact h_has
  | inr h_mem => exact absurd h_mem (by simp)
