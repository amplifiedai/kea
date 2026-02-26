/-
  Kea.Properties.SubstIdempotent — Substitution idempotence.

  Maps to Rust proptests:
    - `substitution_idempotent` (prop_tests.rs:143)
    - `row_substitution_idempotent` (prop_tests.rs:158)

  Property: apply(s, apply(s, t)) = apply(s, t)

  This holds for *idempotent* substitutions — those where every type in the
  range contains no variables that are in the domain. The Rust proptest
  constructs such substitutions (binding vars to ground types only).

  The theorem is FALSE for arbitrary substitutions with chains and limited
  fuel. Counterexample: s = {0 → Var(1), 1 → Var(2), 2 → Int}, fuel = 2,
  ty = Var(0). First apply yields Var(2), second yields Int. The fuel
  exhaustion on the first pass leaves resolvable variables that the second
  pass can resolve further.
-/

import Kea.Substitution
import Kea.FreeVars

-- =========================================================================
-- Idempotent substitution: range variables disjoint from domain
-- =========================================================================

/-- A substitution is idempotent if every type/row in its range contains
    no free variables that are themselves in the domain. This ensures
    single-pass resolution: after one lookup, no further lookups are
    needed within the resolved value.

    This matches the Rust proptest, which binds vars to ground types
    (Int, String, Bool, Float) — trivially satisfying this condition. -/
structure Subst.Idempotent (s : Subst) : Prop where
  typeRange : ∀ v ty, s.typeMap v = some ty →
    (∀ w ∈ freeTypeVars ty, s.typeMap w = none) ∧
    (∀ w ∈ freeRowVars ty, s.rowMap w = none)
  rowRange : ∀ v r, s.rowMap v = some r →
    (∀ w ∈ freeTypeVarsRow r, s.typeMap w = none) ∧
    (∀ w ∈ freeRowVarsRow r, s.rowMap w = none)

-- =========================================================================
-- Key lemma: types with no domain vars are fixed points of applySubst
-- =========================================================================

/-- Combined no-op lemma: if a type/row/tylist/rowfields has no free
    variables that are mapped by the substitution, then applying the
    substitution at any fuel level returns it unchanged.

    This is the foundation of the idempotence proof: after resolving a
    variable to a value whose free vars are outside the domain, applying
    the substitution to that value is a no-op. -/
theorem applySubst_noop (s : Subst) :
    ∀ fuel,
    (∀ ty, (∀ v ∈ freeTypeVars ty, s.typeMap v = none) →
           (∀ v ∈ freeRowVars ty, s.rowMap v = none) →
           applySubst s fuel ty = ty) ∧
    (∀ r, (∀ v ∈ freeTypeVarsRow r, s.typeMap v = none) →
          (∀ v ∈ freeRowVarsRow r, s.rowMap v = none) →
          applySubstRow s fuel r = r) ∧
    (∀ tl, (∀ v ∈ freeTypeVarsTyList tl, s.typeMap v = none) →
           (∀ v ∈ freeRowVarsTyList tl, s.rowMap v = none) →
           applySubstTyList s fuel tl = tl) ∧
    (∀ rf, (∀ v ∈ freeTypeVarsRowFields rf, s.typeMap v = none) →
           (∀ v ∈ freeRowVarsRowFields rf, s.rowMap v = none) →
           applySubstRowFields s fuel rf = rf) := by
  intro fuel
  induction fuel with
  | zero =>
    -- fuel = 0: all four functions return their input by definition
    exact ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩
  | succ n ih =>
    obtain ⟨ih_ty, ih_row, ih_tl, ih_rf⟩ := ih
    refine ⟨?_, ?_, ?_, ?_⟩
    -- Part 1: Ty
    · intro ty htv hrv
      match ty with
      | .int => rfl
      | .intN _ _ => rfl
      | .float => rfl
      | .floatN _ => rfl
      | .decimal _ _ => rfl
      | .bool => rfl
      | .string => rfl
      | .html => rfl
      | .markdown => rfl
      | .atom => rfl
      | .date => rfl
      | .dateTime => rfl
      | .unit => rfl
      | .dynamic => rfl
      | .var v =>
        simp only [applySubst]
        have hv : s.typeMap v = none := htv v (by simp [freeTypeVars])
        simp [hv]
      | .list inner =>
        simp only [applySubst]
        congr 1
        exact ih_ty inner
          (fun v hv => htv v (by simp [freeTypeVars]; exact hv))
          (fun v hv => hrv v (by simp [freeRowVars]; exact hv))
      | .set inner =>
        simp only [applySubst]
        congr 1
        exact ih_ty inner
          (fun v hv => htv v (by simp [freeTypeVars]; exact hv))
          (fun v hv => hrv v (by simp [freeRowVars]; exact hv))
      | .option inner =>
        simp only [applySubst]
        congr 1
        exact ih_ty inner
          (fun v hv => htv v (by simp [freeTypeVars]; exact hv))
          (fun v hv => hrv v (by simp [freeRowVars]; exact hv))
      | .dataframe inner =>
        simp only [applySubst]
        congr 1
        exact ih_ty inner
          (fun v hv => htv v (by simp [freeTypeVars]; exact hv))
          (fun v hv => hrv v (by simp [freeRowVars]; exact hv))
      | .column inner =>
        simp only [applySubst]
        congr 1
        exact ih_ty inner
          (fun v hv => htv v (by simp [freeTypeVars]; exact hv))
          (fun v hv => hrv v (by simp [freeRowVars]; exact hv))
      | .stream inner =>
        simp only [applySubst]
        congr 1
        exact ih_ty inner
          (fun v hv => htv v (by simp [freeTypeVars]; exact hv))
          (fun v hv => hrv v (by simp [freeRowVars]; exact hv))
      | .groupedFrame inner keys =>
        simp only [applySubst]
        congr 1
        exact ih_ty inner
          (fun v hv => htv v (by simp [freeTypeVars]; exact hv))
          (fun v hv => hrv v (by simp [freeRowVars]; exact hv))
      | .tagged inner tags =>
        simp only [applySubst]
        congr 1
        exact ih_ty inner
          (fun v hv => htv v (by simp [freeTypeVars]; exact hv))
          (fun v hv => hrv v (by simp [freeRowVars]; exact hv))
      | .task inner =>
        simp only [applySubst]
        congr 1
        exact ih_ty inner
          (fun v hv => htv v (by simp [freeTypeVars]; exact hv))
          (fun v hv => hrv v (by simp [freeRowVars]; exact hv))
      | .actor inner =>
        simp only [applySubst]
        congr 1
        exact ih_ty inner
          (fun v hv => htv v (by simp [freeTypeVars]; exact hv))
          (fun v hv => hrv v (by simp [freeRowVars]; exact hv))
      | .arc inner =>
        simp only [applySubst]
        congr 1
        exact ih_ty inner
          (fun v hv => htv v (by simp [freeTypeVars]; exact hv))
          (fun v hv => hrv v (by simp [freeRowVars]; exact hv))
      | .fixedSizeList inner d =>
        simp only [applySubst]
        congr 1
        exact ih_ty inner
          (fun v hv => htv v (by simp [freeTypeVars]; exact hv))
          (fun v hv => hrv v (by simp [freeRowVars]; exact hv))
      | .tensor inner shape =>
        simp only [applySubst]
        congr 1
        exact ih_ty inner
          (fun v hv => htv v (by simp [freeTypeVars]; exact hv))
          (fun v hv => hrv v (by simp [freeRowVars]; exact hv))
      | .sum name args =>
        simp only [applySubst]
        congr 1
        exact ih_tl args
          (fun v hv => htv v (by simp [freeTypeVars]; exact hv))
          (fun v hv => hrv v (by simp [freeRowVars]; exact hv))
      | .existential bounds assoc =>
        simp only [applySubst]
        congr 1
        exact ih_tl assoc
          (fun v hv => htv v (by simp [freeTypeVars]; exact hv))
          (fun v hv => hrv v (by simp [freeRowVars]; exact hv))
      | .opaque name params =>
        simp only [applySubst]
        congr 1
        exact ih_tl params
          (fun v hv => htv v (by simp [freeTypeVars]; exact hv))
          (fun v hv => hrv v (by simp [freeRowVars]; exact hv))
      | .map k v =>
        simp only [applySubst]
        congr 1
        · exact ih_ty k
            (fun w hw => htv w (by simp [freeTypeVars, List.mem_append]; left; exact hw))
            (fun w hw => hrv w (by simp [freeRowVars, List.mem_append]; left; exact hw))
        · exact ih_ty v
            (fun w hw => htv w (by simp [freeTypeVars, List.mem_append]; right; exact hw))
            (fun w hw => hrv w (by simp [freeRowVars, List.mem_append]; right; exact hw))
      | .result ok err =>
        simp only [applySubst]
        congr 1
        · exact ih_ty ok
            (fun w hw => htv w (by simp [freeTypeVars, List.mem_append]; left; exact hw))
            (fun w hw => hrv w (by simp [freeRowVars, List.mem_append]; left; exact hw))
        · exact ih_ty err
            (fun w hw => htv w (by simp [freeTypeVars, List.mem_append]; right; exact hw))
            (fun w hw => hrv w (by simp [freeRowVars, List.mem_append]; right; exact hw))
      | .record name r =>
        simp only [applySubst]
        congr 1
        exact ih_row r
          (fun v hv => htv v (by simp [freeTypeVars]; exact hv))
          (fun v hv => hrv v (by simp [freeRowVars]; exact hv))
      | .anonRecord r =>
        simp only [applySubst]
        congr 1
        exact ih_row r
          (fun v hv => htv v (by simp [freeTypeVars]; exact hv))
          (fun v hv => hrv v (by simp [freeRowVars]; exact hv))
      | .row r =>
        simp only [applySubst]
        congr 1
        exact ih_row r
          (fun v hv => htv v (by simp [freeTypeVars]; exact hv))
          (fun v hv => hrv v (by simp [freeRowVars]; exact hv))
      | .function params ret =>
        simp only [applySubst]
        congr 1
        · exact ih_tl params
            (fun w hw => htv w (by simp [freeTypeVars, List.mem_append]; left; exact hw))
            (fun w hw => hrv w (by simp [freeRowVars, List.mem_append]; left; exact hw))
        · exact ih_ty ret
            (fun w hw => htv w (by simp [freeTypeVars, List.mem_append]; right; exact hw))
            (fun w hw => hrv w (by simp [freeRowVars, List.mem_append]; right; exact hw))
      | .functionEff params effects ret =>
        cases effects with
        | mk effectRow =>
          simp only [applySubst]
          congr 1
          · exact ih_tl params
              (fun w hw => htv w (by simp [freeTypeVars, freeTypeVarsEffectRow, List.mem_append, hw]))
              (fun w hw => hrv w (by simp [freeRowVars, freeRowVarsEffectRow, List.mem_append, hw]))
          · exact congrArg EffectRow.mk <|
              ih_row effectRow
                (fun w hw => htv w (by simp [freeTypeVars, freeTypeVarsEffectRow, List.mem_append, hw]))
                (fun w hw => hrv w (by simp [freeRowVars, freeRowVarsEffectRow, List.mem_append, hw]))
          · exact ih_ty ret
              (fun w hw => htv w (by simp [freeTypeVars, freeTypeVarsEffectRow, List.mem_append, hw]))
              (fun w hw => hrv w (by simp [freeRowVars, freeRowVarsEffectRow, List.mem_append, hw]))
      | .forall vars body =>
        simp only [applySubst]
        congr 1
        exact ih_ty body
          (fun v hv => htv v (by simp [freeTypeVars]; exact hv))
          (fun v hv => hrv v (by simp [freeRowVars]; exact hv))
      | .app ctor args =>
        simp only [applySubst]
        congr 1
        · exact ih_ty ctor
            (fun w hw => htv w (by simp [freeTypeVars, List.mem_append]; left; exact hw))
            (fun w hw => hrv w (by simp [freeRowVars, List.mem_append]; left; exact hw))
        · exact ih_tl args
            (fun w hw => htv w (by simp [freeTypeVars, List.mem_append]; right; exact hw))
            (fun w hw => hrv w (by simp [freeRowVars, List.mem_append]; right; exact hw))
      | .constructor name fixedArgs arity =>
        simp only [applySubst]
        congr 1
        exact ih_tl fixedArgs
          (fun v hv => htv v (by simp [freeTypeVars]; exact hv))
          (fun v hv => hrv v (by simp [freeRowVars]; exact hv))
      | .tuple elems =>
        simp only [applySubst]
        congr 1
        exact ih_tl elems
          (fun v hv => htv v (by simp [freeTypeVars]; exact hv))
          (fun v hv => hrv v (by simp [freeRowVars]; exact hv))
    -- Part 2: Row
    · intro r htv hrv
      match r with
      | .mk fields rest =>
        simp only [applySubstRow]
        have hrf : applySubstRowFields s n fields = fields :=
          ih_rf fields
            (fun v hv => htv v (by simp [freeTypeVarsRow]; exact hv))
            (fun v hv => by
              apply hrv v
              simp only [freeRowVarsRow]
              match rest with
              | none => exact hv
              | some _ => exact List.mem_cons_of_mem _ hv)
        match rest with
        | none =>
          rw [hrf]
        | some rv =>
          have hrm : s.rowMap rv = none := hrv rv (by
            simp only [freeRowVarsRow]
            exact .head _)
          simp only [hrm, hrf]
    -- Part 3: TyList
    · intro tl htv hrv
      match tl with
      | .nil => rfl
      | .cons t rest =>
        simp only [applySubstTyList]
        congr 1
        · exact ih_ty t
            (fun v hv => htv v (by simp [freeTypeVarsTyList, List.mem_append]; left; exact hv))
            (fun v hv => hrv v (by simp [freeRowVarsTyList, List.mem_append]; left; exact hv))
        · exact ih_tl rest
            (fun v hv => htv v (by simp [freeTypeVarsTyList, List.mem_append]; right; exact hv))
            (fun v hv => hrv v (by simp [freeRowVarsTyList, List.mem_append]; right; exact hv))
    -- Part 4: RowFields
    · intro rf htv hrv
      match rf with
      | .nil => rfl
      | .cons l ty rest =>
        simp only [applySubstRowFields]
        congr 1
        · exact ih_ty ty
            (fun v hv => htv v (by simp [freeTypeVarsRowFields, List.mem_append]; left; exact hv))
            (fun v hv => hrv v (by simp [freeRowVarsRowFields, List.mem_append]; left; exact hv))
        · exact ih_rf rest
            (fun v hv => htv v (by simp [freeTypeVarsRowFields, List.mem_append]; right; exact hv))
            (fun v hv => hrv v (by simp [freeRowVarsRowFields, List.mem_append]; right; exact hv))

-- =========================================================================
-- Helper: applySubstRowFields is stable over append when suffix has no domain vars
-- =========================================================================

/-- If applying to `a` returns `a`, and `b` is invariant under any fuel,
    then applying to `a.append b` returns `a.append b`.

    This handles the row-merge case in the idempotence proof: after the first
    application merges fields from a resolved row variable, the second
    application must produce the same merged result. -/
private theorem applySubstRowFields_append_stable (s : Subst) :
    ∀ fuel (a b : RowFields),
    applySubstRowFields s fuel a = a →
    (∀ f, applySubstRowFields s f b = b) →
    applySubstRowFields s fuel (a.append b) = a.append b := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ n ih =>
    intro a b ha hb
    match a with
    | .nil =>
      simp only [RowFields.append]
      exact hb (n + 1)
    | .cons l ty rest =>
      -- From ha: .cons l (applySubst s n ty) (applySubstRowFields s n rest) = .cons l ty rest
      simp only [applySubstRowFields] at ha
      -- Extract component equalities from cons injectivity
      have hty : applySubst s n ty = ty := by
        have := congrArg (fun | .cons _ t _ => t | _ => ty) ha
        exact this
      have hrest : applySubstRowFields s n rest = rest := by
        have := congrArg (fun | .cons _ _ r => r | _ => rest) ha
        exact this
      simp only [RowFields.append, applySubstRowFields, hty]
      congr 1
      exact ih rest b hrest hb

-- =========================================================================
-- Helper: applySubst on a variable unfolds predictably
-- =========================================================================

private theorem applySubst_var_some (s : Subst) (n : Nat) (v : TypeVarId)
    (resolved : Ty) (hv : s.typeMap v = some resolved) :
    applySubst s (n + 1) (.var v) = applySubst s n resolved := by
  simp [applySubst, hv]

private theorem applySubst_var_none (s : Subst) (n : Nat) (v : TypeVarId)
    (hv : s.typeMap v = none) :
    applySubst s (n + 1) (.var v) = .var v := by
  simp [applySubst, hv]

-- =========================================================================
-- Main theorems: idempotence for idempotent substitutions
-- =========================================================================

/-- Combined idempotence for all four mutual types at once, by fuel induction.
    The main theorems substIdempotent and substRowIdempotent extract from this. -/
private theorem substIdempotent_all (s : Subst) (h : s.Idempotent) :
    ∀ fuel,
    (∀ ty, applySubst s fuel (applySubst s fuel ty) = applySubst s fuel ty) ∧
    (∀ r, applySubstRow s fuel (applySubstRow s fuel r) = applySubstRow s fuel r) ∧
    (∀ tl, applySubstTyList s fuel (applySubstTyList s fuel tl) = applySubstTyList s fuel tl) ∧
    (∀ rf, applySubstRowFields s fuel (applySubstRowFields s fuel rf) = applySubstRowFields s fuel rf) := by
  intro fuel
  induction fuel with
  | zero => exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  | succ n ih =>
    obtain ⟨ih_ty, ih_row, ih_tl, ih_rf⟩ := ih
    -- Get the noop lemma components for fuel n and n+1
    obtain ⟨noop_ty_n, noop_row_n, _, _⟩ := applySubst_noop s n
    obtain ⟨noop_ty_s, noop_row_s, _, _⟩ := applySubst_noop s (n + 1)
    refine ⟨?_, ?_, ?_, ?_⟩
    -- Part 1: Ty
    · intro ty
      match ty with
      | .int => rfl
      | .intN _ _ => rfl
      | .float => rfl
      | .floatN _ => rfl
      | .decimal _ _ => rfl
      | .bool => rfl
      | .string => rfl
      | .html => rfl
      | .markdown => rfl
      | .atom => rfl
      | .date => rfl
      | .dateTime => rfl
      | .unit => rfl
      | .dynamic => rfl
      | .var v =>
        cases hv : s.typeMap v with
        | none =>
          -- Both applications return .var v since s.typeMap v = none
          rw [applySubst_var_none s n v hv, applySubst_var_none s n v hv]
        | some resolved =>
          -- By Idempotent: resolved has no domain vars
          have ⟨htv, hrv⟩ := h.typeRange v resolved hv
          -- Rewrite both inner occurrences
          rw [applySubst_var_some s n v resolved hv]
          -- Goal: applySubst s (n+1) (applySubst s n resolved) = applySubst s n resolved
          -- By noop: applySubst s n resolved = resolved
          rw [noop_ty_n resolved htv hrv]
          -- Goal: applySubst s (n+1) resolved = resolved
          exact noop_ty_s resolved htv hrv
      | .list inner =>
        simp only [applySubst]; congr 1; exact ih_ty inner
      | .set inner =>
        simp only [applySubst]; congr 1; exact ih_ty inner
      | .option inner =>
        simp only [applySubst]; congr 1; exact ih_ty inner
      | .dataframe inner =>
        simp only [applySubst]; congr 1; exact ih_ty inner
      | .column inner =>
        simp only [applySubst]; congr 1; exact ih_ty inner
      | .stream inner =>
        simp only [applySubst]; congr 1; exact ih_ty inner
      | .groupedFrame inner keys =>
        simp only [applySubst]; congr 1; exact ih_ty inner
      | .tagged inner tags =>
        simp only [applySubst]; congr 1; exact ih_ty inner
      | .task inner =>
        simp only [applySubst]; congr 1; exact ih_ty inner
      | .actor inner =>
        simp only [applySubst]; congr 1; exact ih_ty inner
      | .arc inner =>
        simp only [applySubst]; congr 1; exact ih_ty inner
      | .fixedSizeList inner d =>
        simp only [applySubst]; congr 1; exact ih_ty inner
      | .tensor inner shape =>
        simp only [applySubst]; congr 1; exact ih_ty inner
      | .sum name args =>
        simp only [applySubst]; congr 1; exact ih_tl args
      | .existential bounds assoc =>
        simp only [applySubst]; congr 1; exact ih_tl assoc
      | .opaque name params =>
        simp only [applySubst]; congr 1; exact ih_tl params
      | .map k v =>
        simp only [applySubst]
        congr 1
        · exact ih_ty k
        · exact ih_ty v
      | .result ok err =>
        simp only [applySubst]
        congr 1
        · exact ih_ty ok
        · exact ih_ty err
      | .record name r =>
        simp only [applySubst]; congr 1; exact ih_row r
      | .anonRecord r =>
        simp only [applySubst]; congr 1; exact ih_row r
      | .row r =>
        simp only [applySubst]; congr 1; exact ih_row r
      | .function params ret =>
        simp only [applySubst]
        congr 1
        · exact ih_tl params
        · exact ih_ty ret
      | .functionEff params effects ret =>
        cases effects with
        | mk effectRow =>
          simp only [applySubst]
          congr 1
          · exact ih_tl params
          · exact congrArg EffectRow.mk (ih_row effectRow)
          · exact ih_ty ret
      | .forall vars body =>
        simp only [applySubst]
        congr 1
        exact ih_ty body
      | .app ctor args =>
        simp only [applySubst]
        congr 1
        · exact ih_ty ctor
        · exact ih_tl args
      | .constructor name fixedArgs arity =>
        simp only [applySubst]
        congr 1
        exact ih_tl fixedArgs
      | .tuple elems =>
        simp only [applySubst]; congr 1; exact ih_tl elems
    -- Part 2: Row
    · intro r
      match r with
      | .mk fields rest =>
        match rest with
        | none =>
          -- First: .mk (applySubstRowFields s n fields) none
          -- Second: .mk (applySubstRowFields s n (applySubstRowFields s n fields)) none
          simp only [applySubstRow]
          congr 1
          exact ih_rf fields
        | some rv =>
          cases hrv : s.rowMap rv with
          | none =>
            -- First: .mk (applySubstRowFields s n fields) (some rv)
            -- Second: same, since s.rowMap rv = none
            simp only [applySubstRow, hrv]
            congr 1
            exact ih_rf fields
          | some resolvedRow =>
            -- Get no-domain-vars conditions from idempotent
            have ⟨h_rtv, h_rrv⟩ := h.rowRange rv resolvedRow hrv
            -- By noop: applying s to resolvedRow is a no-op
            have h_noop_rr : applySubstRow s n resolvedRow = resolvedRow :=
              noop_row_n resolvedRow h_rtv h_rrv
            -- Destructure to access fields and rest
            obtain ⟨rfields, rrest⟩ := resolvedRow
            -- Establish what the first application produces
            have h_first : applySubstRow s (n + 1) (Row.mk fields (some rv)) =
                Row.mk ((applySubstRowFields s n fields).append rfields) rrest := by
              simp only [applySubstRow, hrv, h_noop_rr]
            rw [h_first]
            -- Noop for resolved row fields at any fuel
            have h_noop_rf : ∀ f, applySubstRowFields s f rfields = rfields := by
              intro f
              exact (applySubst_noop s f).2.2.2 rfields
                (fun v hv => h_rtv v (by simp [freeTypeVarsRow]; exact hv))
                (fun v hv => by
                  apply h_rrv v
                  simp only [freeRowVarsRow]
                  cases rrest with
                  | none => exact hv
                  | some _ => exact List.mem_cons_of_mem _ hv)
            -- Merged fields are stable under second application
            have h_merged : applySubstRowFields s n
                ((applySubstRowFields s n fields).append rfields) =
                (applySubstRowFields s n fields).append rfields :=
              applySubstRowFields_append_stable s n _ rfields (ih_rf fields) h_noop_rf
            -- Handle resolved row's rest variable
            cases rrest with
            | none =>
              simp only [applySubstRow, h_merged]
            | some rv2 =>
              have h_rv2 : s.rowMap rv2 = none := h_rrv rv2 (by
                simp only [freeRowVarsRow]
                exact .head _)
              simp only [applySubstRow, h_rv2, h_merged]
    -- Part 3: TyList
    · intro tl
      match tl with
      | .nil => rfl
      | .cons t rest =>
        simp only [applySubstTyList]
        congr 1
        · exact ih_ty t
        · exact ih_tl rest
    -- Part 4: RowFields
    · intro rf
      match rf with
      | .nil => rfl
      | .cons l ty rest =>
        simp only [applySubstRowFields]
        congr 1
        · exact ih_ty ty
        · exact ih_rf rest

/-- Substitution is idempotent for idempotent substitutions.
    Applying twice = applying once, for any fuel. -/
theorem substIdempotent (s : Subst) (fuel : Nat) (ty : Ty)
    (h : s.Idempotent) :
    applySubst s fuel (applySubst s fuel ty) = applySubst s fuel ty :=
  (substIdempotent_all s h fuel).1 ty

/-- Row substitution is idempotent for idempotent substitutions. -/
theorem substRowIdempotent (s : Subst) (fuel : Nat) (r : Row)
    (h : s.Idempotent) :
    applySubstRow s fuel (applySubstRow s fuel r) = applySubstRow s fuel r :=
  (substIdempotent_all s h fuel).2.1 r
