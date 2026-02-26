/-
  Kea.Properties.RemyPreservesLabels — Rémy decomposition label preservation.

  Maps to Rust proptests:
    - `remy_preserves_all_labels` (prop_tests.rs:396)
    - `remy_tail_lacks_all_labels` (prop_tests.rs:438)

  Property: After Rémy decomposition of two open rows, every label from
  both inputs appears in the fully resolved result.
-/

import Kea.Unify
import Kea.Properties.UnifyExtends
import Kea.Properties.DecomposeFields

-- =========================================================================
-- Infrastructure: RowFields.has and List.Mem connection
-- =========================================================================

-- has rf l = true → l ∈ labels rf
private theorem RowFields.has_implies_mem_labels (rf : RowFields) (l : Label) :
    rf.has l = true → l ∈ rf.labels := by
  match rf with
  | .nil => intro h; simp [RowFields.has] at h
  | .cons label _ty rest =>
    intro h
    simp only [RowFields.has] at h
    simp only [RowFields.labels]
    cases h_eq : (label == l) with
    | true =>
      have : label = l := by exact beq_iff_eq.mp h_eq
      rw [this]; exact List.Mem.head _
    | false =>
      simp [h_eq] at h
      exact List.Mem.tail _ (RowFields.has_implies_mem_labels rest l h)

-- l ∈ labels rf → has rf l = true
private theorem RowFields.mem_labels_implies_has (rf : RowFields) (l : Label) :
    l ∈ rf.labels → rf.has l = true := by
  match rf with
  | .nil => intro h; simp [RowFields.labels] at h
  | .cons label _ty rest =>
    intro h
    simp only [RowFields.labels] at h
    simp only [RowFields.has]
    cases h with
    | head => simp
    | tail _ h' =>
      have ih := RowFields.mem_labels_implies_has rest l h'
      rw [ih]; simp

-- =========================================================================
-- Infrastructure: applySubstRowFields preserves label membership
-- =========================================================================

-- Substitution on row fields preserves the `has` predicate
-- (substitution changes types but not labels).
private theorem applySubstRowFields_preserves_has (s : Subst) (fuel : Nat) (rf : RowFields) (l : Label) :
    RowFields.has (applySubstRowFields s fuel rf) l = RowFields.has rf l := by
  match fuel with
  | 0 => rfl
  | fuel + 1 =>
    match rf with
    | .nil => simp [applySubstRowFields, RowFields.has]
    | .cons label _ty rest =>
      simp only [applySubstRowFields, RowFields.has]
      congr 1
      exact applySubstRowFields_preserves_has s fuel rest l

-- =========================================================================
-- Infrastructure: RowFields.has distributes over append
-- =========================================================================

private theorem RowFields.has_append_left (a b : RowFields) (l : Label) :
    RowFields.has a l = true → RowFields.has (a.append b) l = true := by
  match a with
  | .nil => intro h; simp [RowFields.has] at h
  | .cons label _ty rest =>
    intro h
    simp only [RowFields.append, RowFields.has] at h ⊢
    cases h_eq : (label == l) with
    | true => simp
    | false =>
      simp only [h_eq, Bool.false_or] at h
      simp only [Bool.false_or]
      exact RowFields.has_append_left rest b l h

private theorem RowFields.has_append_right (a b : RowFields) (l : Label) :
    RowFields.has b l = true → RowFields.has (a.append b) l = true := by
  match a with
  | .nil => simp [RowFields.append]
  | .cons label _ty rest =>
    intro h
    simp only [RowFields.append, RowFields.has]
    rw [RowFields.has_append_right rest b l h]; simp

private theorem RowFields.has_append_or (a b : RowFields) (l : Label) :
    RowFields.has (a.append b) l = true →
    RowFields.has a l = true ∨ RowFields.has b l = true := by
  match a with
  | .nil =>
    simp only [RowFields.append]
    intro h; exact .inr h
  | .cons label _ty rest =>
    intro h
    simp only [RowFields.append, RowFields.has] at h
    cases h_eq : (label == l) with
    | true =>
      left; simp only [RowFields.has, h_eq, Bool.true_or]
    | false =>
      simp only [h_eq, Bool.false_or] at h
      cases RowFields.has_append_or rest b l h with
      | inl h_rest =>
        left; simp only [RowFields.has, h_eq, Bool.false_or]; exact h_rest
      | inr h_b =>
        right; exact h_b

-- =========================================================================
-- Infrastructure: applySubstRow preserves original field labels
-- =========================================================================

-- Helper: what are the fields of applySubstRow for a closed row?
private theorem applySubstRow_fields_closed (s : Subst) (fuel : Nat) (fields : RowFields) :
    (applySubstRow s (fuel + 1) (Row.mk fields none)).fields =
    applySubstRowFields s fuel fields := by
  unfold applySubstRow; rfl

-- Helper: what are the fields for an unbound open row?
private theorem applySubstRow_fields_unbound (s : Subst) (fuel : Nat) (fields : RowFields)
    (var : RowVarId) (h_unbound : s.rowMap var = none) :
    (applySubstRow s (fuel + 1) (Row.mk fields (some var))).fields =
    applySubstRowFields s fuel fields := by
  unfold applySubstRow; simp [h_unbound, Row.fields]

-- Main: applying any substitution at any fuel preserves the original field labels.
-- This is because substitution changes types but not labels, and resolving
-- row variables only appends additional fields (never removes existing ones).
private theorem applySubstRow_preserves_original_has (s : Subst) (fuel : Nat) (r : Row) (l : Label) :
    l ∈ RowFields.labels r.fields → RowFields.has (applySubstRow s fuel r).fields l = true := by
  intro h_mem
  have h_has := RowFields.mem_labels_implies_has r.fields l h_mem
  match fuel with
  | 0 => exact h_has
  | fuel + 1 =>
    match r with
    | .mk fields none =>
      rw [applySubstRow_fields_closed, applySubstRowFields_preserves_has]
      exact h_has
    | .mk fields (some var) =>
      have h_rf_has : RowFields.has (applySubstRowFields s fuel fields) l = true := by
        rw [applySubstRowFields_preserves_has]; exact h_has
      cases h_lk : s.rowMap var with
      | none =>
        rw [applySubstRow_fields_unbound _ _ _ _ h_lk]
        exact h_rf_has
      | some resolvedRow =>
        -- Result is: Row.mk ((applySubstRowFields ...).append tailFields) tailRest
        -- where tail = applySubstRow s fuel resolvedRow
        -- We need has on result.fields, which includes the applied original fields
        show RowFields.has (applySubstRow s (fuel + 1) (Row.mk fields (some var))).fields l = true
        unfold applySubstRow
        simp only [h_lk]
        -- Generalize the inner applySubstRow call to expose match structure
        generalize applySubstRow s fuel resolvedRow = tail
        match tail with
        | .mk _tailFields _tailRest =>
          simp only [Row.fields]
          exact RowFields.has_append_left _ _ l h_rf_has

-- =========================================================================
-- Infrastructure: substitution extension preserves labels
-- =========================================================================

-- If s' extends s on row bindings (every binding in s is also in s'),
-- then labels in the resolved row under s are preserved under s'.
-- This is because extending a substitution only adds resolution steps
-- (revealing more labels from newly-bound row variables), never removes them.
private theorem applySubstRow_extension_preserves_has
    (s s' : Subst) (fuel : Nat) (r : Row) (l : Label)
    (h_ext_row : ∀ v row, s.rowMap v = some row → s'.rowMap v = some row) :
    RowFields.has (applySubstRow s fuel r).fields l = true →
    RowFields.has (applySubstRow s' fuel r).fields l = true := by
  match fuel with
  | 0 => exact id  -- both are identity
  | fuel + 1 =>
    match r with
    | .mk fields none =>
      -- Closed row: labels = has fields (substitution-invariant)
      simp only [applySubstRow_fields_closed, applySubstRowFields_preserves_has]
      exact id
    | .mk fields (some var) =>
      intro h_has
      cases h_lk : s.rowMap var with
      | none =>
        -- var unbound in s: has = has fields
        rw [applySubstRow_fields_unbound _ _ _ _ h_lk, applySubstRowFields_preserves_has] at h_has
        -- In s', var might be bound or unbound
        cases h_lk' : s'.rowMap var with
        | none =>
          rw [applySubstRow_fields_unbound _ _ _ _ h_lk', applySubstRowFields_preserves_has]
          exact h_has
        | some resolvedRow' =>
          -- s' binds var: more labels. Original labels still there.
          show RowFields.has (applySubstRow s' (fuel + 1) (Row.mk fields (some var))).fields l = true
          unfold applySubstRow
          simp only [h_lk']
          generalize applySubstRow s' fuel resolvedRow' = tail'
          match tail' with
          | .mk _tf _tr =>
            simp only [Row.fields]
            have h_rf : RowFields.has (applySubstRowFields s' fuel fields) l = true := by
              rw [applySubstRowFields_preserves_has]; exact h_has
            exact RowFields.has_append_left _ _ l h_rf
      | some resolvedRow =>
        -- var bound in s: s' must also bind it (by h_ext_row)
        have h_lk' : s'.rowMap var = some resolvedRow := h_ext_row var resolvedRow h_lk
        -- Decompose s-side: unfold h_has to see it's fields.append tail
        have h_has' := h_has
        unfold applySubstRow at h_has'
        simp only [h_lk] at h_has'
        -- h_has' now has the expanded outer call; inner applySubstRow s fuel resolvedRow is intact
        generalize h_gen_s : applySubstRow s fuel resolvedRow = tail_s at h_has'
        match tail_s with
        | .mk tf_s tr_s =>
          simp only [Row.fields] at h_has'
          -- h_has' : ((applySubstRowFields s fuel fields).append tf_s).has l = true
          cases RowFields.has_append_or _ _ l h_has' with
          | inl h_from_fields =>
            -- Label comes from original fields (after subst): preserved in s' too
            rw [applySubstRowFields_preserves_has] at h_from_fields
            -- h_from_fields : fields.has l = true
            -- Construct s'-side result
            show RowFields.has (applySubstRow s' (fuel + 1) (Row.mk fields (some var))).fields l = true
            unfold applySubstRow
            simp only [h_lk']
            generalize applySubstRow s' fuel resolvedRow = tail'
            match tail' with
            | .mk _tf' _tr' =>
              simp only [Row.fields]
              exact RowFields.has_append_left _ _ l (by rw [applySubstRowFields_preserves_has]; exact h_from_fields)
          | inr h_from_tail =>
            -- Label comes from resolved tail under s
            -- Recover: (applySubstRow s fuel resolvedRow).fields = tf_s
            have h_tail_has : RowFields.has (applySubstRow s fuel resolvedRow).fields l = true := by
              rw [h_gen_s]; exact h_from_tail
            -- By IH: label preserved under s'
            have ih := applySubstRow_extension_preserves_has s s' fuel resolvedRow l h_ext_row h_tail_has
            -- Construct s'-side result
            show RowFields.has (applySubstRow s' (fuel + 1) (Row.mk fields (some var))).fields l = true
            unfold applySubstRow
            simp only [h_lk']
            -- Replace inner call in both goal and ih simultaneously
            generalize h_gen' : applySubstRow s' fuel resolvedRow = tail' at ih ⊢
            match tail' with
            | .mk _tf' _tr' =>
              simp only [Row.fields] at ih ⊢
              exact RowFields.has_append_right _ _ l ih

-- =========================================================================
-- Infrastructure: binding a rest variable introduces fields at higher fuel
-- =========================================================================

/-- If `applySubstRow s (fuel+1) r` has rest = some rv (meaning rv is the
    terminus of the chain under s), and s' extends s with rv additionally
    bound to boundRow, then at some sufficient fuel level the resolved row
    under s' includes boundRow's fields.

    The proof is by induction on fuel (the chain depth from r to rv):
    - Base (fuel=0): r is open with rest rv0. If rv0 is unbound (rv0=rv),
      fuel'=2 suffices. If rv0 is bound, the chain is resolved in one step
      and resolvedRow0.rest = rv; fuel'=2 still suffices.
    - Step: recursion through the chain via resolvedRow0, using IH to get
      fuel'_inner, then fuel' = fuel'_inner + 1 for one more level. -/
private theorem applySubstRow_newly_bound_has
    (s s' : Subst) (rv : RowVarId) (boundRow : Row) (l : Label)
    (h_ext : ∀ v row, s.rowMap v = some row → s'.rowMap v = some row)
    (h_rv : s'.rowMap rv = some boundRow)
    (h_l : RowFields.has boundRow.fields l = true) :
    ∀ fuel r,
    (applySubstRow s (fuel + 1) r).rest = some rv →
    ∃ fuel', RowFields.has (applySubstRow s' fuel' r).fields l = true := by
  -- Reusable sub-lemma: if rv0 is directly rv and unbound in s,
  -- then fuel'=2 resolves it under s' (rv bound to boundRow).
  have unbound_case : ∀ fields rv0,
      rv0 = rv →
      ∃ fuel', RowFields.has (applySubstRow s' fuel' (Row.mk fields (some rv0))).fields l = true := by
    intro fields rv0 h_eq
    refine ⟨2, ?_⟩
    -- Precompute: tail's fields have l
    have h_tail_has : RowFields.has (applySubstRow s' 1 boundRow).fields l = true :=
      applySubstRow_preserves_original_has s' 1 boundRow l
        (RowFields.has_implies_mem_labels boundRow.fields l h_l)
    show RowFields.has (applySubstRow s' 2 (Row.mk fields (some rv0))).fields l = true
    unfold applySubstRow
    dsimp only  -- reduce match on Row.mk
    rw [h_eq]   -- rv0 → rv
    simp only [h_rv]
    generalize h_gt : applySubstRow s' 1 boundRow = tail at h_tail_has
    match tail with
    | .mk tf _tr =>
      simp only [Row.fields] at h_tail_has ⊢
      exact RowFields.has_append_right _ _ l h_tail_has
  intro fuel
  induction fuel with
  | zero =>
    intro r h_rest
    match r with
    | .mk fields none =>
      unfold applySubstRow at h_rest; simp [Row.rest] at h_rest
    | .mk fields (some rv0) =>
      unfold applySubstRow at h_rest
      cases h_lk : s.rowMap rv0 with
      | none =>
        simp [h_lk, Row.rest] at h_rest
        -- h_rest : rv0 = rv
        exact unbound_case fields rv0 h_rest
      | some resolvedRow0 =>
        simp [h_lk] at h_rest
        -- At fuel 0, inner applySubstRow s 0 resolvedRow0 = resolvedRow0
        -- Extract: resolvedRow0.rest = some rv
        -- applySubstRow s 0 is identity, so the match on it gives resolvedRow0 directly
        have h_id : applySubstRow s 0 resolvedRow0 = resolvedRow0 := rfl
        simp only [h_id] at h_rest
        match resolvedRow0 with
        | .mk rf rrest =>
          simp only [Row.rest] at h_rest
          -- h_rest : rrest = some rv
          -- Pick fuel' = 2: s' maps rv0 to Row.mk rf (some rv),
          -- and then rv to boundRow
          refine ⟨2, ?_⟩
          have h_rv0_s' := h_ext rv0 (Row.mk rf rrest) h_lk
          show RowFields.has (applySubstRow s' 2 (Row.mk fields (some rv0))).fields l = true
          unfold applySubstRow
          simp only [h_rv0_s']
          -- inner tail = applySubstRow s' 1 (Row.mk rf rrest)
          -- We know rrest = some rv and s'.rowMap rv = some boundRow
          -- So this unfolds to include boundRow's fields
          subst h_rest
          -- Now rrest is replaced by (some rv) everywhere
          unfold applySubstRow
          simp only [h_rv]
          -- Reduce fuel-0 identity calls and nested matches
          -- Destruct boundRow to let Lean reduce all matches
          obtain ⟨bf, brest⟩ := boundRow
          simp only [Row.fields] at h_l ⊢
          apply RowFields.has_append_right
          apply RowFields.has_append_right
          exact h_l
  | succ n ih =>
    intro r h_rest
    match r with
    | .mk fields none =>
      unfold applySubstRow at h_rest; simp [Row.rest] at h_rest
    | .mk fields (some rv0) =>
      unfold applySubstRow at h_rest
      cases h_lk : s.rowMap rv0 with
      | none =>
        simp [h_lk, Row.rest] at h_rest
        exact unbound_case fields rv0 h_rest
      | some resolvedRow0 =>
        simp [h_lk] at h_rest
        -- tail = applySubstRow s (n+1) resolvedRow0
        generalize h_gen : applySubstRow s (n + 1) resolvedRow0 = tail at h_rest
        match tail with
        | .mk _tf tr =>
          simp [Row.rest] at h_rest
          -- h_rest : tr = some rv
          have h_tail_rest : (applySubstRow s (n + 1) resolvedRow0).rest = some rv := by
            rw [h_gen]; simp [Row.rest]; exact h_rest
          obtain ⟨fuel'_inner, h_inner⟩ := ih resolvedRow0 h_tail_rest
          refine ⟨fuel'_inner + 1, ?_⟩
          show RowFields.has (applySubstRow s' (fuel'_inner + 1) (Row.mk fields (some rv0))).fields l = true
          have h_rv0_s' := h_ext rv0 resolvedRow0 h_lk
          unfold applySubstRow
          simp only [h_rv0_s']
          generalize applySubstRow s' fuel'_inner resolvedRow0 = tail' at h_inner
          match tail' with
          | .mk tf' _tr' =>
            simp only [Row.fields] at h_inner ⊢
            exact RowFields.has_append_right _ _ l h_inner

-- =========================================================================
-- Infrastructure: onlyR.has l → length > 0 (for contradiction in closed branches)
-- =========================================================================

private theorem RowFields.has_implies_length_pos (rf : RowFields) (l : Label) :
    rf.has l = true → rf.length > 0 := by
  match rf with
  | .nil => intro h; simp [RowFields.has] at h
  | .cons _ _ _ => intro _; unfold RowFields.length; omega

-- =========================================================================
-- Extraction: unifyRows with non-empty onlyR provides a binding
-- =========================================================================

/-- When unifyRows succeeds and the decomposition's onlyRight has label l,
    there exists a rest variable rv in the resolved r1 that st' binds to a row
    containing l. This encapsulates the unifyRows case analysis. -/
private theorem unifyRows_provides_onlyR_binding
    (st st' : UnifyState) (fuel : Nat) (r1 r2 : Row)
    (common : List (Label × Ty × Ty)) (onlyL onlyR : RowFields) (l : Label)
    (h_unify : unifyRows st (fuel + 1) r1 r2 = .ok st')
    (h_dc : decomposeFields (applySubstRow st.subst fuel r1).fields
                            (applySubstRow st.subst fuel r2).fields = (common, onlyL, onlyR))
    (h_onlyR : RowFields.has onlyR l = true) :
    ∃ rv boundRow,
      (applySubstRow st.subst fuel r1).rest = some rv ∧
      st'.subst.rowMap rv = some boundRow ∧
      RowFields.has boundRow.fields l = true := by
  have h_onlyR_len : RowFields.length onlyR > 0 :=
    RowFields.has_implies_length_pos onlyR l h_onlyR
  -- Unfold unifyRows to expose match structure
  unfold unifyRows at h_unify; dsimp only at h_unify
  -- Connect decomposition to our names
  generalize h_df_inner : decomposeFields (applySubstRow st.subst fuel r1).fields
    (applySubstRow st.subst fuel r2).fields = df_inner at h_unify
  have h_df_eq : df_inner = (common, onlyL, onlyR) := by rw [← h_df_inner, h_dc]
  subst h_df_eq
  -- Case-split on unifyCommonFields
  generalize h_cf : unifyCommonFields st fuel common = cf_result at h_unify
  cases cf_result with
  | err e => simp at h_unify
  | ok st_cf =>
    simp only [] at h_unify
    -- Case-split on (r1'.rest, r2'.rest) using split
    split at h_unify
    · -- none/none: if onlyL > 0 || onlyR > 0 then .err else .ok
      -- onlyR.length > 0 → condition true → .err → contradiction
      split at h_unify
      · simp at h_unify  -- .err = .ok
      · -- The else branch: condition false, i.e., ¬(onlyL.len > 0 ∨ onlyR.len > 0)
        -- But onlyR.length > 0. Contradiction.
        -- The split should give us the negation of the condition.
        -- This case is unreachable given h_onlyR_len.
        -- Else branch: ¬(onlyL.len > 0 || onlyR.len > 0), but onlyR.len > 0
        rename_i h_neg
        exfalso; apply h_neg
        simp [Bool.or_eq_true, decide_eq_true_eq]
        exact Or.inr h_onlyR_len
    · -- some rv / none: THE KEY CASE
      split at h_unify
      · simp at h_unify
      · split at h_unify
        · simp at h_unify
        · -- st' = { st_cf with subst := st_cf.subst.bindRow rv (Row.closed onlyR) }
          rename_i rv h_rest1 _ _ _
          simp [UnifyResult.ok.injEq] at h_unify
          refine ⟨rv, Row.closed onlyR, h_rest1, ?_, h_onlyR⟩
          rw [← h_unify]
          exact Subst.bindRow_self_lookup st_cf.subst rv (Row.closed onlyR)
    · -- none / some rv: onlyR > 0 → .err → contradiction
      split at h_unify
      · simp at h_unify
      · -- ¬(onlyR.length > 0), contradicts h_onlyR_len
        rename_i h_neg
        exact absurd h_onlyR_len h_neg
    · -- some rv1 / some rv2
      split at h_unify
      · -- rv1 == rv2: if onlyL > 0 || onlyR > 0 then .err
        split at h_unify
        · simp at h_unify
        · -- Else: ¬(onlyL > 0 || onlyR > 0), contradicts h_onlyR_len
          rename_i h_neg
          exfalso; apply h_neg
          simp [Bool.or_eq_true, decide_eq_true_eq]
          exact Or.inr h_onlyR_len
      · -- rv1 ≠ rv2: binding to Row.mkOpen onlyR r3
        split at h_unify
        · simp at h_unify
        · split at h_unify
          · simp at h_unify
          · -- Success: extract the binding
            rename_i rv1 rv2 h_rest1 _ h_ne_beq _ _
            simp [UnifyResult.ok.injEq] at h_unify
            refine ⟨rv1, Row.mkOpen onlyR (st_cf.freshRowVar).1, h_rest1, ?_, h_onlyR⟩
            -- h_unify : { ... with subst := bindRow (bindRow _ rv1 _) rv2 _ } = st'
            rw [← h_unify]
            -- Struct projection reduces: { ... with subst := s }.subst = s
            -- Goal: (bindRow (bindRow _ rv1 (mkOpen onlyR r3)) rv2 (mkOpen onlyL r3)).rowMap rv1 = some (mkOpen onlyR r3)
            -- outer bindRow preserves rv1 since rv1 ≠ rv2; inner bindRow self-lookup
            have h_ne : rv1 ≠ rv2 := by
              intro h_eq; exact h_ne_beq (by simp [h_eq])
            exact Subst.bindRow_preserves _ rv2 _ rv1 _
              (Subst.bindRow_self_lookup _ rv1 _) h_ne

-- =========================================================================
-- Counterexample witness (without extension precondition)
-- =========================================================================

private def remyNoExtCounterexample : Bool :=
  let s : Subst :=
    { typeMap := fun _ => none
      rowMap := fun v =>
        if v == 0 then none
        else if v == 1 then some (Row.mk (.cons "a" .int .nil) (some 1))
        else none }
  let st : UnifyState :=
    { subst := s, lacks := Lacks.empty, traitBounds := [], nextTypeVar := 0, nextRowVar := 2 }
  let r1 : Row := Row.mk .nil (some 1)
  let r2 : Row := Row.mk (.cons "a" .int .nil) (some 0)
  match unifyRows st 3 r1 r2 with
  | .err _ => false
  | .ok st' =>
    -- No fuel up to 50 reintroduces label "a" into the resolved left row.
    ((List.range 51).all (fun f => RowFields.has (applySubstRow st'.subst f r1).fields "a" = false))

private theorem remyNoExtCounterexample_true :
    remyNoExtCounterexample = true := by
  native_decide

-- =========================================================================
-- Main theorem: remyPreservesLabels
-- =========================================================================

/-- After successful row unification, if `st'` extends `st` on row bindings,
    all labels from both input rows appear in the resolved result at some
    sufficient fuel level.

    The extension precondition is necessary in the fuel model: without it,
    successful `unifyRows` can overwrite existing row bindings (see
    `UnifyExtends` counterexample discussion), and previously visible labels
    may disappear from the re-resolved left row.

    NOTE: The conclusion uses existential fuel (∃ fuel') rather than the same
    fuel as unifyRows. This is necessary because the fuel-based Lean model
    can't always resolve the full chain at the same fuel: unifyRows at fuel+1
    uses fuel internally for applySubstRow, reaching rest variable rv.
    After binding rv, re-resolving r1 needs one MORE step to follow rv → boundRow.
    The Rust implementation has no fuel limit, so this is a model artifact.

    Counterexample for fixed fuel: st.subst = { rv0 → #{ | rv } }, rv unbound.
    r1 = #{ | rv0 }, r2 = #{ x: Int }. unifyRows at fuel 2 succeeds, binds
    rv → #{ x: Int }. But applySubstRow st'.subst 1 r1 follows rv0 → #{ | rv }
    at fuel 0 (identity), missing rv's new binding. Needs fuel 2 to see "x". -/
theorem remyPreservesLabels (st : UnifyState) (fuel : Nat) (r1 r2 : Row) (st' : UnifyState)
    (h_ext_row : ExtendsRowBindings st st') :
    unifyRows st (fuel + 1) r1 r2 = .ok st' →
    ∀ l, l ∈ RowFields.labels r1.fields ∨ l ∈ RowFields.labels r2.fields →
      ∃ fuel', RowFields.has (applySubstRow st'.subst fuel' r1).fields l = true := by
  intro h_unify l h_label
  cases h_label with
  | inl h_r1 =>
    -- l from r1.fields: preserved by any substitution application at any fuel
    exact ⟨fuel, applySubstRow_preserves_original_has st'.subst fuel r1 l h_r1⟩
  | inr h_r2 =>
    -- l from r2.fields. Case split: is l also in r1.fields?
    by_cases h_r1_mem : l ∈ RowFields.labels r1.fields
    · -- l is in both r1.fields and r2.fields: same argument as inl
      exact ⟨fuel, applySubstRow_preserves_original_has st'.subst fuel r1 l h_r1_mem⟩
    · -- l ∈ r2.fields but l ∉ r1.fields: l enters r1 through row variable binding
      -- or through resolved row variable in the common fields.
      --
      -- Strategy: use decomposeFields_right_coverage to split into two cases:
      --   (a) l in common → l in r1'.fields → preserved by extension to st'
      --   (b) l in onlyRight → enters through bindRow in unifyRows
      --
      -- Step 1: l is in the resolved r2's fields
      have h_r2_has : RowFields.has (applySubstRow st.subst fuel r2).fields l = true :=
        applySubstRow_preserves_original_has st.subst fuel r2 l h_r2
      -- Step 2: decomposeFields coverage — l ends up in common or onlyRight
      have h_cov := decomposeFields_right_coverage
        (applySubstRow st.subst fuel r1).fields
        (applySubstRow st.subst fuel r2).fields l h_r2_has
      -- Step 3: generalize the decomposition to match h_cov's let binding
      generalize h_dc : decomposeFields
        (applySubstRow st.subst fuel r1).fields
        (applySubstRow st.subst fuel r2).fields = dc at h_cov
      obtain ⟨common, onlyL, onlyR⟩ := dc
      -- Now h_cov : onlyR.has l = true ∨ ∃ ty1 ty2, (l, ty1, ty2) ∈ common
      cases h_cov with
      | inl h_onlyR =>
        -- l in onlyRight: enters r1 through bindRow in unifyRows.
        -- Extract: ∃ rv, rest of resolved r1 = some rv, st' binds rv to row with l
        obtain ⟨rv, boundRow, h_rest, h_binding, h_bound_has⟩ :=
          unifyRows_provides_onlyR_binding st st' fuel r1 r2 common onlyL onlyR l
            h_unify h_dc h_onlyR
        have h_ext := h_ext_row
        -- Case split: applySubstRow_newly_bound_has needs fuel+1 precondition
        cases fuel with
        | zero =>
          -- fuel = 0: applySubstRow _ 0 _ is identity, so r1.rest = some rv
          -- At fuel' = 1 under st'.subst, rv resolves to boundRow which has l
          refine ⟨1, ?_⟩
          obtain ⟨fields, rest_opt⟩ := r1
          -- Force reduction of applySubstRow _ 0 _ = id (mutual rec doesn't auto-reduce)
          have h0 : applySubstRow st.subst 0 (Row.mk fields rest_opt) = Row.mk fields rest_opt := rfl
          simp only [h0, Row.rest] at h_rest
          cases rest_opt with
          | none => simp at h_rest
          | some rv0 =>
            simp at h_rest
            subst h_rest
            unfold applySubstRow; simp only [h_binding]
            obtain ⟨bf, brest⟩ := boundRow
            simp only [Row.fields] at h_bound_has ⊢
            exact RowFields.has_append_right _ _ l h_bound_has
        | succ n =>
          -- fuel = n+1: h_rest matches applySubstRow_newly_bound_has precondition exactly
          exact applySubstRow_newly_bound_has st.subst st'.subst rv boundRow l
            h_ext h_binding h_bound_has n r1 h_rest
      | inr h_common =>
        -- l in common → l is already in r1'.fields (the resolved r1 under st.subst)
        obtain ⟨ty1, ty2, h_mem⟩ := h_common
        -- Recover the membership as being in (decomposeFields ...).1
        have h_mem' : (l, ty1, ty2) ∈ (decomposeFields
          (applySubstRow st.subst fuel r1).fields
          (applySubstRow st.subst fuel r2).fields).1 := by
          rw [h_dc]; exact h_mem
        have h_r1'_has : RowFields.has (applySubstRow st.subst fuel r1).fields l = true :=
          decomposeFields_common_in_left
            (applySubstRow st.subst fuel r1).fields
            (applySubstRow st.subst fuel r2).fields l ty1 ty2 h_mem'
        -- Use the provided row-extension hypothesis.
        have h_ext := h_ext_row
        -- Preserved by extension: l in r1' → l in resolved r1 under st'
        exact ⟨fuel, applySubstRow_extension_preserves_has
          st.subst st'.subst fuel r1 l h_ext h_r1'_has⟩

-- =========================================================================
-- remyTailLacks: FALSE AS STATED — removed
-- =========================================================================

-- The original `remyTailLacks` theorem claimed:
--   After unifyRows, the tail variable of the resolved row lacks all labels
--   from both input rows.
--
-- This is FALSE. Counterexample:
--   r1 = r2 = #{ a: Int | rv₀ } (shared row variable)
--   unifyRows empty 3 r1 r2 succeeds via the rv1 == rv2 branch (Unify.lean:216)
--   No row variable binding occurs, no lacks constraints are added
--   The resolved row still has rest = some rv₀
--   But Lacks.lacksLabel empty.lacks rv₀ "a" = false
--
-- The correct statement would restrict to the rv1 ≠ rv2 branch (line 220+),
-- where a fresh r3 is allocated and lacks for all labels are explicitly
-- added to r3 (line 229). The shared-variable branch needs no lacks because
-- the variable already appears in both rows with matching structure.
--
-- Verification: applySubstRow empty.subst 2 (Row.mk (.cons "a" .int .nil) (some 0))
-- produces Row.mk (.cons "a" .int .nil) (some 0) — same as input (rfl).
-- Lacks.lacksLabel Lacks.empty 0 "a" = false (rfl).
-- The only gap is computing unifyRows through mutual recursion, which the Lean
-- kernel cannot reduce via rfl for compiled mutual definitions.
