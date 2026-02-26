/-
  Kea.Properties.UnifyExtends — Unification extends substitution row bindings.

  Property: The mutual unification functions only add new bindings to the
  substitution, never remove existing row bindings.

  Key results:
  - bindTypeVar_preserves_rowMap: bindTypeVar doesn't touch rowMap
  - Subst.bindRow_preserves: bindRow preserves other variables' bindings
  - applySubstRow_rest_unbound_idempotent: resolved rest vars are unbound
    (requires Subst.Idempotent)
  - freshAndBindTwoRows_extends_of_resolved_rests_idempotent_with_lacks:
    exact open-open branch update shape preserves row-binding extension
    under idempotent resolved-rest preconditions

  IMPORTANT — extends_mutual is FALSE without preconditions:

  Counterexample: s = { rv0 → .nil|(rv1), rv1 → (a: Int) },
    r1 = .nil|(rv0), r2 = (b: String), fuel = 2.

    At fuel 2, applySubstRow resolves rv0 but runs out of fuel before
    resolving rv1, leaving r1' = .nil|(rv1). Then unifyRows matches
    (some rv1, none) and binds rv1 → (b: String), overwriting the
    existing rv1 → (a: Int). ExtendsRowBindings breaks.

  The Rust implementation is correct because apply() has no fuel limit
  (unbounded resolution). The counterexample is unreachable in practice
  because the Rust unifier always fully resolves row variables before
  matching on their structure.

  Current status:
  - WF bridge lemmas are now in place for substitution-level bindType/bindRow
    consistency under idempotent substitutions.
  - The global `unifyRows_extends_rowMap` theorem remains deferred because
    unification itself still recurses on fuel; overwrites can still appear in
    low-fuel intermediate states.

  Maps to Rust proptests: (implicit in all unification tests — the Rust
  implementation uses in-place mutation that naturally extends the map)
-/

import Kea.Unify
import Kea.Properties.SubstIdempotent
import Kea.Properties.SubstBridge

-- =========================================================================
-- Row binding extension relation
-- =========================================================================

/-- st' extends st on row bindings: every binding in st is preserved in st'. -/
def ExtendsRowBindings (st st' : UnifyState) : Prop :=
  ∀ v row, st.subst.rowMap v = some row → st'.subst.rowMap v = some row

theorem ExtendsRowBindings.refl (st : UnifyState) : ExtendsRowBindings st st :=
  fun _ _ h => h

theorem ExtendsRowBindings.trans {st1 st2 st3 : UnifyState}
    (h12 : ExtendsRowBindings st1 st2) (h23 : ExtendsRowBindings st2 st3) :
    ExtendsRowBindings st1 st3 :=
  fun v row h => h23 v row (h12 v row h)

/-- Row-binding extension depends only on the substitution map.
    If `st''` has the same substitution as `st'`, any extension fact to `st'`
    transports to `st''`. -/
theorem ExtendsRowBindings.of_subst_eq
    {st st' st'' : UnifyState}
    (h_ext : ExtendsRowBindings st st')
    (h_subst : st''.subst = st'.subst) :
    ExtendsRowBindings st st'' := by
  intro v row h_bound
  rw [h_subst]
  exact h_ext v row h_bound

/-- Changing only `lacks` preserves row-binding extension. -/
theorem ExtendsRowBindings.with_lacks
    {st st' : UnifyState}
    (h_ext : ExtendsRowBindings st st')
    (lacks' : Lacks) :
    ExtendsRowBindings st { st' with lacks := lacks' } := by
  exact ExtendsRowBindings.of_subst_eq h_ext rfl

/-- Changing only `traitBounds` preserves row-binding extension. -/
theorem ExtendsRowBindings.with_traitBounds
    {st st' : UnifyState}
    (h_ext : ExtendsRowBindings st st')
    (bounds' : TraitBounds) :
    ExtendsRowBindings st { st' with traitBounds := bounds' } := by
  exact ExtendsRowBindings.of_subst_eq h_ext rfl

/-- Changing only `nextTypeVar` preserves row-binding extension. -/
theorem ExtendsRowBindings.with_nextTypeVar
    {st st' : UnifyState}
    (h_ext : ExtendsRowBindings st st')
    (next' : Nat) :
    ExtendsRowBindings st { st' with nextTypeVar := next' } := by
  exact ExtendsRowBindings.of_subst_eq h_ext rfl

/-- Changing only `nextRowVar` preserves row-binding extension. -/
theorem ExtendsRowBindings.with_nextRowVar
    {st st' : UnifyState}
    (h_ext : ExtendsRowBindings st st')
    (next' : Nat) :
    ExtendsRowBindings st { st' with nextRowVar := next' } := by
  exact ExtendsRowBindings.of_subst_eq h_ext rfl

/-- Changing any combination of non-`subst` fields preserves row-binding
    extension. -/
theorem ExtendsRowBindings.with_non_subst_fields
    {st st' : UnifyState}
    (h_ext : ExtendsRowBindings st st')
    (lacks' : Lacks)
    (bounds' : TraitBounds)
    (nextType' : Nat)
    (nextRow' : Nat) :
    ExtendsRowBindings st
      { st' with
          lacks := lacks',
          traitBounds := bounds',
          nextTypeVar := nextType',
          nextRowVar := nextRow' } := by
  exact ExtendsRowBindings.of_subst_eq h_ext rfl

-- =========================================================================
-- Helper: bindTypeVar preserves all row bindings
-- =========================================================================

/-- bindTypeVar only modifies typeMap, never rowMap. -/
theorem bindTypeVar_preserves_rowMap (st : UnifyState) (v : TypeVarId)
    (ty : Ty) (fuel : Nat) (st' : UnifyState) :
    bindTypeVar st v ty fuel = .ok st' →
    st'.subst.rowMap = st.subst.rowMap := by
  intro h
  unfold bindTypeVar at h
  split at h
  · -- ty == .var v: st' = st
    simp [UnifyResult.ok.injEq] at h
    rw [← h]
  · split at h
    · -- occurs check failed: .err
      exact absurd h (by intro h'; exact UnifyResult.noConfusion h')
    · -- binding succeeds: st' = { st with subst := st.subst.bindType v ty }
      simp [UnifyResult.ok.injEq] at h
      rw [← h]
      rfl

/-- Corollary: bindTypeVar extends row bindings. -/
theorem bindTypeVar_extends (st : UnifyState) (tv : TypeVarId)
    (ty : Ty) (fuel : Nat) (st' : UnifyState) :
    bindTypeVar st tv ty fuel = .ok st' →
    ExtendsRowBindings st st' := by
  intro h_bind rv row h_bound
  have h_eq := bindTypeVar_preserves_rowMap st tv ty fuel st' h_bind
  rw [← h_eq] at h_bound
  exact h_bound

-- =========================================================================
-- Helper: Subst.bindRow preserves bindings for other variables
-- =========================================================================

/-- bindRow preserves rowMap for variables other than the target. -/
theorem Subst.bindRow_preserves (s : Subst) (v : RowVarId) (r : Row)
    (w : RowVarId) (row : Row) :
    s.rowMap w = some row → w ≠ v →
    (s.bindRow v r).rowMap w = some row := by
  intro h_bound h_ne
  unfold Subst.bindRow
  have h_beq_false : (w == v) = false := by
    cases Nat.decEq w v with
    | isTrue h => exact absurd h h_ne
    | isFalse h => simp [BEq.beq, h]
  simp [h_beq_false]
  exact h_bound

-- =========================================================================
-- Helper: Subst.bindRow self-lookup
-- =========================================================================

/-- Looking up the bound variable in a bindRow returns the bound row. -/
theorem Subst.bindRow_self_lookup (s : Subst) (v : RowVarId) (r : Row) :
    (s.bindRow v r).rowMap v = some r := by
  unfold Subst.bindRow
  simp [BEq.beq]

-- =========================================================================
-- Key structural lemma: resolved row rest variables are unbound
-- =========================================================================

/-- With an idempotent substitution, the rest variable of a resolved row
    is always unbound. This is because:
    - For unbound row variables: applySubstRow preserves them as-is
    - For bound row variables: the resolved row's free variables are
      outside the domain (by idempotency), so its rest is unbound

    This property is crucial for proving that unifyRows' bindRow calls
    never overwrite existing bindings — the row variables being bound
    are always fresh/unbound in the current substitution. -/
theorem applySubstRow_rest_unbound_idempotent
    (s : Subst) (fuel : Nat) (r : Row) (rv : RowVarId)
    (h_idemp : s.Idempotent)
    (h_rest : (applySubstRow s (fuel + 1) r).rest = some rv) :
    s.rowMap rv = none := by
  match r with
  | .mk fields none =>
    -- Closed row: applySubstRow preserves rest = none
    unfold applySubstRow at h_rest
    simp [Row.rest] at h_rest
  | .mk fields (some rv0) =>
    unfold applySubstRow at h_rest
    cases h_lk : s.rowMap rv0 with
    | none =>
      -- Unbound: result.rest = some rv0
      simp [h_lk, Row.rest] at h_rest
      rw [← h_rest]; exact h_lk
    | some resolvedRow =>
      -- Bound: tail = applySubstRow s fuel resolvedRow
      -- By idempotency, resolvedRow has no domain vars
      have ⟨h_rtv, h_rrv⟩ := h_idemp.rowRange rv0 resolvedRow h_lk
      have h_noop := (applySubst_noop s fuel).2.1 resolvedRow h_rtv h_rrv
      -- After unfolding: result = .mk (fields'.append tail.fields) tail.rest
      -- where tail = applySubstRow s fuel resolvedRow = resolvedRow (by h_noop)
      -- So result.rest = resolvedRow.rest
      simp only [h_lk, h_noop] at h_rest
      -- h_rest : resolvedRow.rest = some rv (through Row.rest accessor)
      match resolvedRow, h_rrv with
      | .mk rFields rRest, h_rrv =>
        -- h_rest involves matching tail = .mk rFields rRest
        simp only [Row.rest] at h_rest
        -- h_rest : rRest = some rv
        cases rRest with
        | none => exact absurd h_rest (by simp)
        | some rv2 =>
          -- h_rest gives rv2 = rv; we need s.rowMap rv = none
          -- Since rv2 is in freeRowVarsRow resolvedRow, idempotency gives s.rowMap rv2 = none
          have h_rv2_unbound : s.rowMap rv2 = none :=
            h_rrv rv2 (by simp [freeRowVarsRow])
          have h_eq : rv2 = rv := Option.some.inj h_rest
          rw [← h_eq]
          exact h_rv2_unbound

-- =========================================================================
-- Helper: bindRow extends if target is unbound
-- =========================================================================

/-- If `rv` is unbound in `st.subst`, then binding `rv` preserves all existing row bindings. -/
theorem bindRow_extends_if_unbound (st : UnifyState) (rv : RowVarId) (row : Row)
    (h_unbound : st.subst.rowMap rv = none) :
    ExtendsRowBindings st { st with subst := st.subst.bindRow rv row } := by
  intro w r h_bound
  by_cases h_eq : w = rv
  · -- w = rv: but st.subst.rowMap rv = none, contradicts h_bound
    rw [h_eq] at h_bound; simp [h_unbound] at h_bound
  · -- w ≠ rv: preserved by bindRow
    exact Subst.bindRow_preserves st.subst rv row w r h_bound h_eq

/-- If `st'` already extends `st`, and `rv` is unbound in `st'`, then binding
    `rv` to a closed row in `st'` still extends `st`. -/
theorem bindClosedRow_extends_of_unbound
    (st st' : UnifyState) (rv : RowVarId) (fields : RowFields)
    (h_ext : ExtendsRowBindings st st')
    (h_unbound : st'.subst.rowMap rv = none) :
    ExtendsRowBindings st { st' with subst := st'.subst.bindRow rv (Row.closed fields) } := by
  exact ExtendsRowBindings.trans h_ext
    (bindRow_extends_if_unbound st' rv (Row.closed fields) h_unbound)

/-- Two-state variant: if `st'` extends `st` and `rv` is unbound in `st'`, then
    binding `rv` to any row in `st'` still extends `st`. -/
theorem bindRow_extends_if_unbound_two_state
    (st st' : UnifyState) (rv : RowVarId) (row : Row)
    (h_ext : ExtendsRowBindings st st')
    (h_unbound : st'.subst.rowMap rv = none) :
    ExtendsRowBindings st { st' with subst := st'.subst.bindRow rv row } := by
  exact ExtendsRowBindings.trans h_ext (bindRow_extends_if_unbound st' rv row h_unbound)

/-- If a row variable appears as the rest of a resolved row under an idempotent
    substitution, then binding that variable preserves all existing row bindings. -/
theorem bindRow_extends_of_resolved_rest_idempotent
    (st : UnifyState) (fuel : Nat) (r row : Row) (rv : RowVarId)
    (h_idemp : st.subst.Idempotent)
    (h_rest : (applySubstRow st.subst (fuel + 1) r).rest = some rv) :
    ExtendsRowBindings st { st with subst := st.subst.bindRow rv row } := by
  have h_unbound : st.subst.rowMap rv = none :=
    applySubstRow_rest_unbound_idempotent st.subst fuel r rv h_idemp h_rest
  exact bindRow_extends_if_unbound st rv row h_unbound

/-- Two-state variant: if `st'` extends `st`, and `rv` appears as the rest of a
    resolved row under `st'`'s idempotent substitution, then binding `rv` to a
    closed row in `st'` still extends `st`. -/
theorem bindClosedRow_extends_of_resolved_rest_idempotent
    (st st' : UnifyState) (fuel : Nat) (r : Row) (rv : RowVarId) (fields : RowFields)
    (h_ext : ExtendsRowBindings st st')
    (h_idemp : st'.subst.Idempotent)
    (h_rest : (applySubstRow st'.subst (fuel + 1) r).rest = some rv) :
    ExtendsRowBindings st { st' with subst := st'.subst.bindRow rv (Row.closed fields) } := by
  exact ExtendsRowBindings.trans h_ext
    (bindRow_extends_of_resolved_rest_idempotent st' fuel r (Row.closed fields) rv h_idemp h_rest)

/-- If two distinct row variables are both unbound, then two sequential row
    bindings preserve all existing row bindings. -/
theorem bindTwoRows_extends_of_unbound
    (st : UnifyState) (rv1 rv2 : RowVarId) (row1 row2 : Row)
    (h_ne : rv2 ≠ rv1)
    (h_unbound1 : st.subst.rowMap rv1 = none)
    (h_unbound2 : st.subst.rowMap rv2 = none) :
    ExtendsRowBindings st
      { st with subst := Subst.bindRow (Subst.bindRow st.subst rv1 row1) rv2 row2 } := by
  let st1 : UnifyState := { st with subst := st.subst.bindRow rv1 row1 }
  have h_ext1 : ExtendsRowBindings st st1 := bindRow_extends_if_unbound st rv1 row1 h_unbound1
  have h_unbound2_after_first : st1.subst.rowMap rv2 = none := by
    dsimp [st1]
    unfold Subst.bindRow
    have h_beq_false : (rv2 == rv1) = false := by
      cases Nat.decEq rv2 rv1 with
      | isTrue h_eq => exact absurd h_eq h_ne
      | isFalse h_neq => simp [BEq.beq, h_neq]
    simp [h_beq_false, h_unbound2]
  have h_ext2 :
      ExtendsRowBindings st1 { st1 with subst := st1.subst.bindRow rv2 row2 } :=
    bindRow_extends_if_unbound st1 rv2 row2 h_unbound2_after_first
  have h_eq_final :
      { st1 with subst := st1.subst.bindRow rv2 row2 }
        =
      { st with subst := Subst.bindRow (Subst.bindRow st.subst rv1 row1) rv2 row2 } := by
    rfl
  rw [← h_eq_final]
  exact ExtendsRowBindings.trans h_ext1 h_ext2

/-- Two-state variant: if `st'` extends `st`, then adding two distinct unbound
    row bindings in `st'` still extends `st`. -/
theorem bindTwoRows_extends_of_unbound_two_state
    (st st' : UnifyState) (rv1 rv2 : RowVarId) (row1 row2 : Row)
    (h_ext : ExtendsRowBindings st st')
    (h_ne : rv2 ≠ rv1)
    (h_unbound1 : st'.subst.rowMap rv1 = none)
    (h_unbound2 : st'.subst.rowMap rv2 = none) :
    ExtendsRowBindings st
      { st' with subst := Subst.bindRow (Subst.bindRow st'.subst rv1 row1) rv2 row2 } := by
  exact ExtendsRowBindings.trans h_ext
    (bindTwoRows_extends_of_unbound st' rv1 rv2 row1 row2 h_ne h_unbound1 h_unbound2)

/-- Open-open branch shape: if `st'` extends `st`, then `freshRowVar` followed
    by two distinct unbound row bindings still extends `st`. -/
theorem freshAndBindTwoRows_extends_of_unbound
    (st st' st'' : UnifyState) (rv1 rv2 r3 : RowVarId) (onlyLeft onlyRight : RowFields)
    (h_ext : ExtendsRowBindings st st')
    (h_fresh : (r3, st'') = st'.freshRowVar)
    (h_ne : rv2 ≠ rv1)
    (h_unbound1 : st'.subst.rowMap rv1 = none)
    (h_unbound2 : st'.subst.rowMap rv2 = none) :
    ExtendsRowBindings st
      { st'' with
          subst := Subst.bindRow
            (Subst.bindRow st''.subst rv1 (Row.mkOpen onlyRight r3))
            rv2
            (Row.mkOpen onlyLeft r3) } := by
  have h_ext_to_fresh : ExtendsRowBindings st st'' := by
    have h_fresh_ext : ExtendsRowBindings st' st'' := by
      cases h_fresh
      intro v row h_bound
      exact h_bound
    exact ExtendsRowBindings.trans h_ext h_fresh_ext
  have h_subst_eq : st''.subst = st'.subst := by
    cases h_fresh
    rfl
  have h_unbound1_fresh : st''.subst.rowMap rv1 = none := by simpa [h_subst_eq] using h_unbound1
  have h_unbound2_fresh : st''.subst.rowMap rv2 = none := by simpa [h_subst_eq] using h_unbound2
  exact bindTwoRows_extends_of_unbound_two_state
    st st'' rv1 rv2 (Row.mkOpen onlyRight r3) (Row.mkOpen onlyLeft r3)
    h_ext_to_fresh h_ne h_unbound1_fresh h_unbound2_fresh

/-- Open-open branch shape with resolved-rest/idempotence premises: if `rv1`
    and `rv2` come from resolved rests under an idempotent substitution, then
    the fresh+bind sequence preserves row-binding extension. -/
theorem freshAndBindTwoRows_extends_of_resolved_rests_idempotent
    (st st' st'' : UnifyState) (fuel : Nat)
    (r1 r2 : Row) (rv1 rv2 r3 : RowVarId) (onlyLeft onlyRight : RowFields)
    (h_ext : ExtendsRowBindings st st')
    (h_fresh : (r3, st'') = st'.freshRowVar)
    (h_ne : rv2 ≠ rv1)
    (h_idemp : st'.subst.Idempotent)
    (h_rest1 : (applySubstRow st'.subst (fuel + 1) r1).rest = some rv1)
    (h_rest2 : (applySubstRow st'.subst (fuel + 1) r2).rest = some rv2) :
    ExtendsRowBindings st
      { st'' with
          subst := Subst.bindRow
            (Subst.bindRow st''.subst rv1 (Row.mkOpen onlyRight r3))
            rv2
            (Row.mkOpen onlyLeft r3) } := by
  have h_unbound1 : st'.subst.rowMap rv1 = none :=
    applySubstRow_rest_unbound_idempotent st'.subst fuel r1 rv1 h_idemp h_rest1
  have h_unbound2 : st'.subst.rowMap rv2 = none :=
    applySubstRow_rest_unbound_idempotent st'.subst fuel r2 rv2 h_idemp h_rest2
  exact freshAndBindTwoRows_extends_of_unbound
    st st' st'' rv1 rv2 r3 onlyLeft onlyRight h_ext h_fresh h_ne h_unbound1 h_unbound2

/-- Exact open-open final-state shape from `unifyRows`: allows an arbitrary
    `lacks` update while preserving row-binding extension. -/
theorem freshAndBindTwoRows_extends_of_resolved_rests_idempotent_with_lacks
    (st st' st'' : UnifyState) (fuel : Nat)
    (r1 r2 : Row) (rv1 rv2 r3 : RowVarId) (onlyLeft onlyRight : RowFields)
    (lacks'' : Lacks)
    (h_ext : ExtendsRowBindings st st')
    (h_fresh : (r3, st'') = st'.freshRowVar)
    (h_ne : rv2 ≠ rv1)
    (h_idemp : st'.subst.Idempotent)
    (h_rest1 : (applySubstRow st'.subst (fuel + 1) r1).rest = some rv1)
    (h_rest2 : (applySubstRow st'.subst (fuel + 1) r2).rest = some rv2) :
    ExtendsRowBindings st
      { st'' with
          subst := Subst.bindRow
            (Subst.bindRow st''.subst rv1 (Row.mkOpen onlyRight r3))
            rv2
            (Row.mkOpen onlyLeft r3),
          lacks := lacks'' } := by
  have h_base : ExtendsRowBindings st
      { st'' with
          subst := Subst.bindRow
            (Subst.bindRow st''.subst rv1 (Row.mkOpen onlyRight r3))
            rv2
            (Row.mkOpen onlyLeft r3) } :=
    freshAndBindTwoRows_extends_of_resolved_rests_idempotent
      st st' st'' fuel r1 r2 rv1 rv2 r3 onlyLeft onlyRight
      h_ext h_fresh h_ne h_idemp h_rest1 h_rest2
  exact ExtendsRowBindings.with_lacks h_base lacks''

/-- Open-open final-state shape with arbitrary non-`subst` updates. -/
theorem freshAndBindTwoRows_extends_of_resolved_rests_idempotent_with_state
    (st st' st'' : UnifyState) (fuel : Nat)
    (r1 r2 : Row) (rv1 rv2 r3 : RowVarId) (onlyLeft onlyRight : RowFields)
    (lacks'' : Lacks) (bounds'' : TraitBounds) (nextType'' nextRow'' : Nat)
    (h_ext : ExtendsRowBindings st st')
    (h_fresh : (r3, st'') = st'.freshRowVar)
    (h_ne : rv2 ≠ rv1)
    (h_idemp : st'.subst.Idempotent)
    (h_rest1 : (applySubstRow st'.subst (fuel + 1) r1).rest = some rv1)
    (h_rest2 : (applySubstRow st'.subst (fuel + 1) r2).rest = some rv2) :
    ExtendsRowBindings st
      { st'' with
          subst := Subst.bindRow
            (Subst.bindRow st''.subst rv1 (Row.mkOpen onlyRight r3))
            rv2
            (Row.mkOpen onlyLeft r3),
          lacks := lacks'',
          traitBounds := bounds'',
          nextTypeVar := nextType'',
          nextRowVar := nextRow'' } := by
  have h_base : ExtendsRowBindings st
      { st'' with
          subst := Subst.bindRow
            (Subst.bindRow st''.subst rv1 (Row.mkOpen onlyRight r3))
            rv2
            (Row.mkOpen onlyLeft r3) } :=
    freshAndBindTwoRows_extends_of_resolved_rests_idempotent
      st st' st'' fuel r1 r2 rv1 rv2 r3 onlyLeft onlyRight
      h_ext h_fresh h_ne h_idemp h_rest1 h_rest2
  exact ExtendsRowBindings.with_non_subst_fields h_base lacks'' bounds'' nextType'' nextRow''

/-- `unifyRows` open-open branch update preserves extension under the resolved-rest
    idempotence preconditions (wrapper with branch-shaped naming). -/
theorem unifyRows_open_open_update_extends_idempotent
    (st st' st'' : UnifyState) (fuel : Nat)
    (r1 r2 : Row) (rv1 rv2 r3 : RowVarId) (onlyLeft onlyRight : RowFields)
    (lacks'' : Lacks)
    (h_ext : ExtendsRowBindings st st')
    (h_fresh : (r3, st'') = st'.freshRowVar)
    (h_ne : rv2 ≠ rv1)
    (h_idemp : st'.subst.Idempotent)
    (h_rest1 : (applySubstRow st'.subst (fuel + 1) r1).rest = some rv1)
    (h_rest2 : (applySubstRow st'.subst (fuel + 1) r2).rest = some rv2) :
    let subst' :=
      Subst.bindRow
        (Subst.bindRow st''.subst rv1 (Row.mkOpen onlyRight r3))
        rv2
        (Row.mkOpen onlyLeft r3)
    ExtendsRowBindings st { st'' with subst := subst', lacks := lacks'' } := by
  simpa using freshAndBindTwoRows_extends_of_resolved_rests_idempotent_with_lacks
    st st' st'' fuel r1 r2 rv1 rv2 r3 onlyLeft onlyRight lacks''
    h_ext h_fresh h_ne h_idemp h_rest1 h_rest2

/-- Open-open branch wrapper targeting arbitrary non-`subst` final-state fields. -/
theorem unifyRows_open_open_update_extends_idempotent_full_state
    (st st' st'' : UnifyState) (fuel : Nat)
    (r1 r2 : Row) (rv1 rv2 r3 : RowVarId) (onlyLeft onlyRight : RowFields)
    (lacks'' : Lacks) (bounds'' : TraitBounds) (nextType'' nextRow'' : Nat)
    (h_ext : ExtendsRowBindings st st')
    (h_fresh : (r3, st'') = st'.freshRowVar)
    (h_ne : rv2 ≠ rv1)
    (h_idemp : st'.subst.Idempotent)
    (h_rest1 : (applySubstRow st'.subst (fuel + 1) r1).rest = some rv1)
    (h_rest2 : (applySubstRow st'.subst (fuel + 1) r2).rest = some rv2) :
    let subst' :=
      Subst.bindRow
        (Subst.bindRow st''.subst rv1 (Row.mkOpen onlyRight r3))
        rv2
        (Row.mkOpen onlyLeft r3)
    ExtendsRowBindings st
      { st'' with
          subst := subst',
          lacks := lacks'',
          traitBounds := bounds'',
          nextTypeVar := nextType'',
          nextRowVar := nextRow'' } := by
  simpa using freshAndBindTwoRows_extends_of_resolved_rests_idempotent_with_state
    st st' st'' fuel r1 r2 rv1 rv2 r3 onlyLeft onlyRight
    lacks'' bounds'' nextType'' nextRow''
    h_ext h_fresh h_ne h_idemp h_rest1 h_rest2

/-- Full-state open-open branch wrapper using `freshRowVar` directly. -/
theorem unifyRows_open_open_update_extends_idempotent_full_state_fresh
    (st st' : UnifyState) (fuel : Nat)
    (r1 r2 : Row) (rv1 rv2 : RowVarId) (onlyLeft onlyRight : RowFields)
    (lacks'' : Lacks) (bounds'' : TraitBounds) (nextType'' nextRow'' : Nat)
    (h_ext : ExtendsRowBindings st st')
    (h_ne : rv2 ≠ rv1)
    (h_idemp : st'.subst.Idempotent)
    (h_rest1 : (applySubstRow st'.subst (fuel + 1) r1).rest = some rv1)
    (h_rest2 : (applySubstRow st'.subst (fuel + 1) r2).rest = some rv2) :
    let fr := st'.freshRowVar
    let r3 := fr.1
    let st'' := fr.2
    let subst' :=
      Subst.bindRow
        (Subst.bindRow st''.subst rv1 (Row.mkOpen onlyRight r3))
        rv2
        (Row.mkOpen onlyLeft r3)
    ExtendsRowBindings st
      { st'' with
          subst := subst',
          lacks := lacks'',
          traitBounds := bounds'',
          nextTypeVar := nextType'',
          nextRowVar := nextRow'' } := by
  dsimp
  simpa using unifyRows_open_open_update_extends_idempotent_full_state
    st st' (st'.freshRowVar).2 fuel r1 r2 rv1 rv2 (st'.freshRowVar).1 onlyLeft onlyRight
    lacks'' bounds'' nextType'' nextRow'' h_ext rfl h_ne h_idemp h_rest1 h_rest2

/-- Open-open branch wrapper using `freshRowVar` directly (no explicit
    `h_fresh` equality argument). -/
theorem unifyRows_open_open_update_extends_idempotent_fresh
    (st st' : UnifyState) (fuel : Nat)
    (r1 r2 : Row) (rv1 rv2 : RowVarId) (onlyLeft onlyRight : RowFields)
    (lacks'' : Lacks)
    (h_ext : ExtendsRowBindings st st')
    (h_ne : rv2 ≠ rv1)
    (h_idemp : st'.subst.Idempotent)
    (h_rest1 : (applySubstRow st'.subst (fuel + 1) r1).rest = some rv1)
    (h_rest2 : (applySubstRow st'.subst (fuel + 1) r2).rest = some rv2) :
    let fr := st'.freshRowVar
    let r3 := fr.1
    let st'' := fr.2
    let subst' :=
      Subst.bindRow
        (Subst.bindRow st''.subst rv1 (Row.mkOpen onlyRight r3))
        rv2
        (Row.mkOpen onlyLeft r3)
    ExtendsRowBindings st { st'' with subst := subst', lacks := lacks'' } := by
  dsimp
  simpa using unifyRows_open_open_update_extends_idempotent
    st st' (st'.freshRowVar).2 fuel r1 r2 rv1 rv2 (st'.freshRowVar).1 onlyLeft onlyRight lacks''
    h_ext rfl h_ne h_idemp h_rest1 h_rest2

/-- Open-open branch wrapper using `freshRowVar` directly and leaving `lacks`
    unchanged from the fresh state. -/
theorem unifyRows_open_open_update_extends_idempotent_fresh_no_lacks_update
    (st st' : UnifyState) (fuel : Nat)
    (r1 r2 : Row) (rv1 rv2 : RowVarId) (onlyLeft onlyRight : RowFields)
    (h_ext : ExtendsRowBindings st st')
    (h_ne : rv2 ≠ rv1)
    (h_idemp : st'.subst.Idempotent)
    (h_rest1 : (applySubstRow st'.subst (fuel + 1) r1).rest = some rv1)
    (h_rest2 : (applySubstRow st'.subst (fuel + 1) r2).rest = some rv2) :
    let fr := st'.freshRowVar
    let r3 := fr.1
    let st'' := fr.2
    let subst' :=
      Subst.bindRow
        (Subst.bindRow st''.subst rv1 (Row.mkOpen onlyRight r3))
        rv2
        (Row.mkOpen onlyLeft r3)
    ExtendsRowBindings st { st'' with subst := subst' } := by
  dsimp
  exact unifyRows_open_open_update_extends_idempotent
    st st' (st'.freshRowVar).2 fuel r1 r2 rv1 rv2 (st'.freshRowVar).1 onlyLeft onlyRight (st'.freshRowVar).2.lacks
    h_ext rfl h_ne h_idemp h_rest1 h_rest2

/-- Generic single-bind row update branch: if a rest variable comes from a
    resolved open row under an idempotent substitution, binding it to a closed
    row preserves extension. Used by both `(some rv, none)` and `(none, some rv)`
    successful `unifyRows` branches. -/
theorem unifyRows_single_bind_update_extends_idempotent
    (st st' : UnifyState) (fuel : Nat)
    (rOpen : Row) (rv : RowVarId) (fields : RowFields)
    (h_ext : ExtendsRowBindings st st')
    (h_idemp : st'.subst.Idempotent)
    (h_rest : (applySubstRow st'.subst (fuel + 1) rOpen).rest = some rv) :
    ExtendsRowBindings st
      { st' with subst := st'.subst.bindRow rv (Row.closed fields) } := by
  simpa using bindClosedRow_extends_of_resolved_rest_idempotent
    st st' fuel rOpen rv fields h_ext h_idemp h_rest

/-- `unifyRows` `(some rv, none)` branch update preserves extension under the
    resolved-rest idempotence precondition (branch-shaped wrapper). -/
theorem unifyRows_open_closed_update_extends_idempotent
    (st st' : UnifyState) (fuel : Nat)
    (rOpen : Row) (rv : RowVarId) (onlyRight : RowFields)
    (h_ext : ExtendsRowBindings st st')
    (h_idemp : st'.subst.Idempotent)
    (h_rest : (applySubstRow st'.subst (fuel + 1) rOpen).rest = some rv) :
    ExtendsRowBindings st
      { st' with subst := st'.subst.bindRow rv (Row.closed onlyRight) } := by
  exact unifyRows_single_bind_update_extends_idempotent
    st st' fuel rOpen rv onlyRight h_ext h_idemp h_rest

/-- `unifyRows` `(none, some rv)` branch update preserves extension under the
    resolved-rest idempotence precondition (symmetric branch wrapper). -/
theorem unifyRows_closed_open_update_extends_idempotent
    (st st' : UnifyState) (fuel : Nat)
    (rOpen : Row) (rv : RowVarId) (onlyLeft : RowFields)
    (h_ext : ExtendsRowBindings st st')
    (h_idemp : st'.subst.Idempotent)
    (h_rest : (applySubstRow st'.subst (fuel + 1) rOpen).rest = some rv) :
    ExtendsRowBindings st
      { st' with subst := st'.subst.bindRow rv (Row.closed onlyLeft) } := by
  exact unifyRows_single_bind_update_extends_idempotent
    st st' fuel rOpen rv onlyLeft h_ext h_idemp h_rest

/-- Generic no-substitution-update success branch: extension is preserved
    directly. Used by closed-closed and same-var successful `unifyRows` cases. -/
theorem unifyRows_no_subst_update_success_extends
    (st st' : UnifyState)
    (h_ext : ExtendsRowBindings st st') :
    ExtendsRowBindings st st' := by
  exact h_ext

/-- `unifyRows` closed-closed success branch does not update substitution, so
    extension is preserved directly. -/
theorem unifyRows_closed_closed_success_extends
    (st st' : UnifyState)
    (h_ext : ExtendsRowBindings st st') :
    ExtendsRowBindings st st' := by
  exact unifyRows_no_subst_update_success_extends st st' h_ext

/-- `unifyRows` same-rest-var success branch (`rv1 == rv2` with no extras)
    does not update substitution, so extension is preserved directly. -/
theorem unifyRows_same_var_success_extends
    (st st' : UnifyState)
    (h_ext : ExtendsRowBindings st st') :
    ExtendsRowBindings st st' := by
  exact unifyRows_no_subst_update_success_extends st st' h_ext

/-- Recognized successful `unifyRows` update shapes (under a fixed intermediate
    state `st'` and fuel index). This is the explicit precondition used by the
    preconditioned global extension theorem. -/
def UnifyRowsSuccessUpdateShape
    (st' stNext : UnifyState) (fuel : Nat) : Prop :=
  stNext = st'
  ∨ (∃ rOpen rv fields,
      (applySubstRow st'.subst (fuel + 1) rOpen).rest = some rv
      ∧ stNext = { st' with subst := st'.subst.bindRow rv (Row.closed fields) })
  ∨ (∃ r1 r2 rv1 rv2 onlyLeft onlyRight,
      rv2 ≠ rv1
      ∧ (applySubstRow st'.subst (fuel + 1) r1).rest = some rv1
      ∧ (applySubstRow st'.subst (fuel + 1) r2).rest = some rv2
      ∧ let fr := st'.freshRowVar
        let r3 := fr.1
        let st'' := fr.2
        let subst' :=
          Subst.bindRow
            (Subst.bindRow st''.subst rv1 (Row.mkOpen onlyRight r3))
            rv2
            (Row.mkOpen onlyLeft r3)
        stNext = { st'' with subst := subst' })

/-- Preconditioned dispatcher: if a successful `unifyRows` step is known to be
    one of the supported success-update shapes, extension follows. This folds
    the branch-local theorems into one reusable entry point. -/
theorem unifyRows_success_update_extends_idempotent
    (st st' stNext : UnifyState) (fuel : Nat)
    (h_ext : ExtendsRowBindings st st')
    (h_idemp : st'.subst.Idempotent)
    (h_case : UnifyRowsSuccessUpdateShape st' stNext fuel) :
    ExtendsRowBindings st stNext := by
  rcases h_case with h_no_update | h_single_bind | h_open_open
  · rw [h_no_update]
    exact unifyRows_no_subst_update_success_extends st st' h_ext
  · rcases h_single_bind with ⟨rOpen, rv, fields, h_rest, h_next⟩
    rw [h_next]
    exact unifyRows_single_bind_update_extends_idempotent
      st st' fuel rOpen rv fields h_ext h_idemp h_rest
  · rcases h_open_open with ⟨r1, r2, rv1, rv2, onlyLeft, onlyRight, h_ne, h_rest1, h_rest2, h_next⟩
    have h_open_open_ext :
        let fr := st'.freshRowVar
        let r3 := fr.1
        let st'' := fr.2
        let subst' :=
          Subst.bindRow
            (Subst.bindRow st''.subst rv1 (Row.mkOpen onlyRight r3))
            rv2
            (Row.mkOpen onlyLeft r3)
        ExtendsRowBindings st { st'' with subst := subst' } :=
      unifyRows_open_open_update_extends_idempotent_fresh_no_lacks_update
        st st' fuel r1 r2 rv1 rv2 onlyLeft onlyRight h_ext h_ne h_idemp h_rest1 h_rest2
    rw [h_next]
    simpa using h_open_open_ext

/-- Preconditioned global extension theorem for `unifyRows` updates:
    when the resulting state matches one of the recognized successful branch
    update shapes and the intermediate substitution is idempotent, row bindings
    from `st` are preserved in the result. -/
theorem unifyRows_extends_rowMap_preconditioned
    (st st' stNext : UnifyState) (fuel : Nat)
    (h_ext : ExtendsRowBindings st st')
    (h_idemp : st'.subst.Idempotent)
    (h_shape : UnifyRowsSuccessUpdateShape st' stNext fuel) :
    ExtendsRowBindings st stNext := by
  exact unifyRows_success_update_extends_idempotent st st' stNext fuel h_ext h_idemp h_shape

-- =========================================================================
-- Helper: freshRowVar extends row bindings
-- =========================================================================

/-- `freshRowVar` only increments the counter; it preserves substitution row bindings. -/
theorem freshRowVar_extends (st : UnifyState) :
    ExtendsRowBindings st (st.freshRowVar).2 := by
  intro v row h_bound
  unfold UnifyState.freshRowVar
  exact h_bound

-- =========================================================================
-- WF bridge helper for row-binding branch
-- =========================================================================

/-- Bounded-WF row-tail consistency for `bindRow`, lifted to `UnifyState`. -/
theorem bindRowTailConsistentWFBoundedIdempotent
    (st : UnifyState) (rv : RowVarId) (row : Row)
    (h_idemp : (st.subst.bindRow rv row).Idempotent) :
    let ac := Subst.acyclicOfIdempotent h_idemp
    applySubstRowBounded (st.subst.bindRow rv row) ac 1 (ac.rowRank rv + 1) (Row.mk .nil (some rv)) =
      applySubstRowBounded (st.subst.bindRow rv row) ac 1 (ac.rowRank rv) row := by
  simpa using applySubstRowBounded_bindRow_consistent_of_idempotent st.subst rv row h_idemp

/-- Full-WF row-tail consistency for `bindRow`, lifted to `UnifyState`. -/
theorem bindRowTailConsistentWFIdempotent
    (st : UnifyState) (rv : RowVarId) (row : Row)
    (h_idemp : (st.subst.bindRow rv row).Idempotent) :
    let ac := Subst.acyclicOfIdempotent h_idemp
    applySubstRowWF (st.subst.bindRow rv row) ac (Row.mk .nil (some rv)) =
      applySubstRowWF (st.subst.bindRow rv row) ac row := by
  simpa using applySubstRowWF_bindRow_consistent_of_idempotent st.subst rv row h_idemp

/--
Predicate packaging the "swap `applySubstCompat` for WF substitution" agreement
on all domain lookups reachable from a state substitution.
-/
def CompatWFAgreeOnDomainLookups
    (st : UnifyState) (fuel : Nat) (h_idemp : st.subst.Idempotent) : Prop :=
  (∀ v ty, st.subst.typeMap v = some ty →
    let ac := Subst.acyclicOfIdempotent h_idemp
    applySubstCompat st.subst (fuel + 1) (.var v) =
      applySubstWF st.subst ac (.var v))
  ∧
  (∀ rv row, st.subst.rowMap rv = some row →
    let ac := Subst.acyclicOfIdempotent h_idemp
    applySubstRowCompat st.subst (fuel + 1) (Row.mk .nil (some rv)) =
      applySubstRowWF st.subst ac (Row.mk .nil (some rv)))

/--
Acyclic-parameterized version of the compat/WF swap-invariance predicate.
This is the weakest form needed by downstream consumers that only require
well-founded substitution execution.
-/
def CompatWFAgreeOnDomainLookupsAcyclic
    (st : UnifyState) (fuel : Nat) (h_ac : st.subst.Acyclic) : Prop :=
  (∀ v ty, st.subst.typeMap v = some ty →
    applySubstCompat st.subst (fuel + 1) (.var v) =
      applySubstWF st.subst h_ac (.var v))
  ∧
  (∀ rv row, st.subst.rowMap rv = some row →
    applySubstRowCompat st.subst (fuel + 1) (Row.mk .nil (some rv)) =
      applySubstRowWF st.subst h_ac (Row.mk .nil (some rv)))

/--
Assumption split bridge: any idempotent-based swap-invariance fact can be
re-exported as an acyclic-based fact via `acyclicOfIdempotent`.
-/
theorem compatWFAgreeOnDomainLookupsAcyclic_of_idempotent
    (st : UnifyState) (fuel : Nat)
    (h_idemp : st.subst.Idempotent)
    (h_agree : CompatWFAgreeOnDomainLookups st fuel h_idemp) :
    let h_ac := Subst.acyclicOfIdempotent h_idemp
    CompatWFAgreeOnDomainLookupsAcyclic st fuel h_ac := by
  let h_ac : st.subst.Acyclic := Subst.acyclicOfIdempotent h_idemp
  rcases h_agree with ⟨h_ty, h_row⟩
  refine ⟨?_, ?_⟩
  · intro v ty h_lookup
    have h_eq := h_ty v ty h_lookup
    simpa [h_ac] using h_eq
  · intro rv row h_lookup
    have h_eq := h_row rv row h_lookup
    simpa [h_ac] using h_eq

/--
Bridge schema for successful `unifyRows` updates: under a recognized success
shape and idempotent result substitution, fueled compat substitution and WF
substitution agree on all domain lookup values reachable from that result
state (bound type vars and bound row-tail vars).
-/
theorem unifyRows_success_update_domain_lookup_compat_wf_agree
    (st' stNext : UnifyState) (fuel : Nat)
    (_h_shape : UnifyRowsSuccessUpdateShape st' stNext fuel)
    (h_idemp_next : stNext.subst.Idempotent) :
    CompatWFAgreeOnDomainLookups stNext fuel h_idemp_next := by
  refine ⟨?_, ?_⟩
  · intro v ty h_lookup
    exact applySubstCompat_var_eq_applySubstWF_of_idempotent
      stNext.subst (fuel + 1) v ty (Nat.succ_pos _) h_idemp_next h_lookup
  · intro rv row h_lookup
    exact applySubstRowCompat_empty_open_eq_applySubstRowWF_of_row_lookup_idempotent
      stNext.subst (fuel + 1) rv row (Nat.succ_pos _) h_idemp_next h_lookup

/--
Branch-local compat/WF agreement wrapper for no-substitution-update successful
`unifyRows` branches (closed-closed and same-rest-var success paths).
-/
theorem unifyRows_no_update_domain_lookup_compat_wf_agree
    (st' : UnifyState) (fuel : Nat)
    (h_idemp : st'.subst.Idempotent) :
    (∀ v ty, st'.subst.typeMap v = some ty →
      let ac := Subst.acyclicOfIdempotent h_idemp
      applySubstCompat st'.subst (fuel + 1) (.var v) =
        applySubstWF st'.subst ac (.var v))
    ∧
    (∀ rv row, st'.subst.rowMap rv = some row →
      let ac := Subst.acyclicOfIdempotent h_idemp
      applySubstRowCompat st'.subst (fuel + 1) (Row.mk .nil (some rv)) =
        applySubstRowWF st'.subst ac (Row.mk .nil (some rv))) := by
  exact unifyRows_success_update_domain_lookup_compat_wf_agree
    st' st' fuel (Or.inl rfl) h_idemp

/--
Branch-local compat/WF agreement wrapper for the single-bind successful
`unifyRows` branch family (`(some rv, none)` and `(none, some rv)`).
-/
theorem unifyRows_single_bind_domain_lookup_compat_wf_agree
    (st' : UnifyState) (fuel : Nat)
    (rOpen : Row) (rv : RowVarId) (fields : RowFields)
    (h_rest : (applySubstRow st'.subst (fuel + 1) rOpen).rest = some rv)
    (h_idemp_next : ({ st' with subst := st'.subst.bindRow rv (Row.closed fields) }).subst.Idempotent) :
    let stNext := { st' with subst := st'.subst.bindRow rv (Row.closed fields) }
    (∀ v ty, stNext.subst.typeMap v = some ty →
      let ac := Subst.acyclicOfIdempotent h_idemp_next
      applySubstCompat stNext.subst (fuel + 1) (.var v) =
        applySubstWF stNext.subst ac (.var v))
    ∧
    (∀ rv' row, stNext.subst.rowMap rv' = some row →
      let ac := Subst.acyclicOfIdempotent h_idemp_next
      applySubstRowCompat stNext.subst (fuel + 1) (Row.mk .nil (some rv')) =
        applySubstRowWF stNext.subst ac (Row.mk .nil (some rv'))) := by
  let stNext : UnifyState := { st' with subst := st'.subst.bindRow rv (Row.closed fields) }
  have h_shape : UnifyRowsSuccessUpdateShape st' stNext fuel :=
    Or.inr (Or.inl ⟨rOpen, rv, fields, h_rest, rfl⟩)
  simpa [stNext] using
    (unifyRows_success_update_domain_lookup_compat_wf_agree st' stNext fuel h_shape h_idemp_next)

/--
Branch-local compat/WF agreement wrapper for the open-open successful
`unifyRows` branch family (fresh row var + dual bind update).
-/
theorem unifyRows_open_open_domain_lookup_compat_wf_agree
    (st' : UnifyState) (fuel : Nat)
    (r1 r2 : Row) (rv1 rv2 : RowVarId) (onlyLeft onlyRight : RowFields)
    (h_ne : rv2 ≠ rv1)
    (h_rest1 : (applySubstRow st'.subst (fuel + 1) r1).rest = some rv1)
    (h_rest2 : (applySubstRow st'.subst (fuel + 1) r2).rest = some rv2)
    (h_idemp_next :
      (let fr := st'.freshRowVar
       let r3 := fr.1
       let st'' := fr.2
       let subst' :=
         Subst.bindRow
           (Subst.bindRow st''.subst rv1 (Row.mkOpen onlyRight r3))
           rv2
           (Row.mkOpen onlyLeft r3)
       ({ st'' with subst := subst' }).subst.Idempotent)) :
    let fr := st'.freshRowVar
    let r3 := fr.1
    let st'' := fr.2
    let subst' :=
      Subst.bindRow
        (Subst.bindRow st''.subst rv1 (Row.mkOpen onlyRight r3))
        rv2
        (Row.mkOpen onlyLeft r3)
    let stNext := { st'' with subst := subst' }
    (∀ v ty, stNext.subst.typeMap v = some ty →
      let ac := Subst.acyclicOfIdempotent h_idemp_next
      applySubstCompat stNext.subst (fuel + 1) (.var v) =
        applySubstWF stNext.subst ac (.var v))
    ∧
    (∀ rv row, stNext.subst.rowMap rv = some row →
      let ac := Subst.acyclicOfIdempotent h_idemp_next
      applySubstRowCompat stNext.subst (fuel + 1) (Row.mk .nil (some rv)) =
        applySubstRowWF stNext.subst ac (Row.mk .nil (some rv))) := by
  let fr := st'.freshRowVar
  let r3 := fr.1
  let st'' := fr.2
  let subst' :=
    Subst.bindRow
      (Subst.bindRow st''.subst rv1 (Row.mkOpen onlyRight r3))
      rv2
      (Row.mkOpen onlyLeft r3)
  let stNext : UnifyState := { st'' with subst := subst' }
  have h_shape : UnifyRowsSuccessUpdateShape st' stNext fuel :=
    Or.inr (Or.inr ⟨r1, r2, rv1, rv2, onlyLeft, onlyRight, h_ne, h_rest1, h_rest2, rfl⟩)
  simpa [fr, r3, st'', subst', stNext] using
    (unifyRows_success_update_domain_lookup_compat_wf_agree st' stNext fuel h_shape h_idemp_next)

/--
M2 capstone: successful `unifyRows` updates are invariant under swapping
fuel-based compat substitution with WF substitution on all reachable
domain lookups, under the current idempotence precondition.
-/
theorem unifyRows_success_update_compat_wf_swap_invariant
    (st' stNext : UnifyState) (fuel : Nat)
    (h_shape : UnifyRowsSuccessUpdateShape st' stNext fuel)
    (h_idemp_next : stNext.subst.Idempotent) :
    CompatWFAgreeOnDomainLookups stNext fuel h_idemp_next := by
  exact unifyRows_success_update_domain_lookup_compat_wf_agree
    st' stNext fuel h_shape h_idemp_next

/--
M3 contract theorem (WF phrasing): the preconditioned global row-binding
extension result together with compat/WF swap invariance for successful
`unifyRows` updates.
-/
theorem unifyRows_extends_rowMap_preconditioned_wf
    (st st' stNext : UnifyState) (fuel : Nat)
    (h_ext : ExtendsRowBindings st st')
    (h_idemp : st'.subst.Idempotent)
    (h_shape : UnifyRowsSuccessUpdateShape st' stNext fuel)
    (h_idemp_next : stNext.subst.Idempotent) :
    ExtendsRowBindings st stNext
    ∧ CompatWFAgreeOnDomainLookups stNext fuel h_idemp_next := by
  refine ⟨?_, ?_⟩
  · exact unifyRows_extends_rowMap_preconditioned
      st st' stNext fuel h_ext h_idemp h_shape
  · exact unifyRows_success_update_compat_wf_swap_invariant
      st' stNext fuel h_shape h_idemp_next

/--
M3 contract variant with explicit assumption split:
- extension guarantee keeps the existing idempotent precondition on `st'`
- compat/WF swap guarantee is exported in acyclic form for consumers.
-/
theorem unifyRows_extends_rowMap_preconditioned_wf_split
    (st st' stNext : UnifyState) (fuel : Nat)
    (h_ext : ExtendsRowBindings st st')
    (h_idemp : st'.subst.Idempotent)
    (h_shape : UnifyRowsSuccessUpdateShape st' stNext fuel)
    (h_idemp_next : stNext.subst.Idempotent) :
    ExtendsRowBindings st stNext
    ∧ (let h_ac := Subst.acyclicOfIdempotent h_idemp_next
       CompatWFAgreeOnDomainLookupsAcyclic stNext fuel h_ac) := by
  refine ⟨?_, ?_⟩
  · exact unifyRows_extends_rowMap_preconditioned
      st st' stNext fuel h_ext h_idemp h_shape
  · exact compatWFAgreeOnDomainLookupsAcyclic_of_idempotent
      stNext fuel h_idemp_next
      (unifyRows_success_update_compat_wf_swap_invariant
        st' stNext fuel h_shape h_idemp_next)

/--
Canonical downstream WF contract name.
Use this theorem as the primary import surface for unifyRows bridge consumers.
-/
theorem unifyRows_contract_wf
    (st st' stNext : UnifyState) (fuel : Nat)
    (h_ext : ExtendsRowBindings st st')
    (h_idemp : st'.subst.Idempotent)
    (h_shape : UnifyRowsSuccessUpdateShape st' stNext fuel)
    (h_idemp_next : stNext.subst.Idempotent) :
    ExtendsRowBindings st stNext
    ∧ (let h_ac := Subst.acyclicOfIdempotent h_idemp_next
       CompatWFAgreeOnDomainLookupsAcyclic stNext fuel h_ac) := by
  exact unifyRows_extends_rowMap_preconditioned_wf_split
    st st' stNext fuel h_ext h_idemp h_shape h_idemp_next

/--
Legacy compatibility projection: recover the previous non-split WF theorem
shape from the canonical downstream contract.
-/
theorem unifyRows_extends_rowMap_preconditioned_wf_of_contract
    (st st' stNext : UnifyState) (fuel : Nat)
    (h_ext : ExtendsRowBindings st st')
    (h_idemp : st'.subst.Idempotent)
    (h_shape : UnifyRowsSuccessUpdateShape st' stNext fuel)
    (h_idemp_next : stNext.subst.Idempotent) :
    ExtendsRowBindings st stNext
    ∧ CompatWFAgreeOnDomainLookups stNext fuel h_idemp_next := by
  refine ⟨?_, ?_⟩
  · exact (unifyRows_contract_wf st st' stNext fuel h_ext h_idemp h_shape h_idemp_next).1
  · exact unifyRows_success_update_compat_wf_swap_invariant
      st' stNext fuel h_shape h_idemp_next

-- =========================================================================
-- Deferred global extension theorem
-- =========================================================================

/-
  NOTE:
  The unconditional theorem
    `unifyRows st fuel r1 r2 = .ok st' -> ExtendsRowBindings st st'`
  is false in the fuel model (see file header counterexample). The global
  extension proof is deferred until substitution application is fully
  well-founded (fuel-free) in unification.
-/
