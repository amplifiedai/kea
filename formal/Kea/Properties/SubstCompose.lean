/-
  Kea.Properties.SubstCompose — Substitution extension absorbs inner application.

  Key property: For an idempotent substitution s' that extends s,
  applying s first then s' gives the same result as applying s' alone:
    applySubst s' fuel (applySubst s fuel ty) = applySubst s' fuel ty

  This is the foundation for unifyConsistent and other properties that
  require reasoning about how unification's incremental bindings compose.

  No direct Rust proptest counterpart — this is a pure proof infrastructure
  lemma that enables reasoning about unification's output substitution.
-/

import Kea.Substitution
import Kea.Properties.SubstIdempotent
import Kea.FreeVars

-- =========================================================================
-- Extension relation for substitutions
-- =========================================================================

/-- s' extends s: every binding in s is also in s' with the same value. -/
structure Subst.Extends (s s' : Subst) : Prop where
  typeExt : ∀ v ty, s.typeMap v = some ty → s'.typeMap v = some ty
  rowExt  : ∀ v r, s.rowMap v = some r → s'.rowMap v = some r

-- =========================================================================
-- Contrapositive: unmapped in s' → unmapped in s
-- =========================================================================

private theorem ext_unmapped_type {s s' : Subst} (h_ext : Subst.Extends s s')
    (w : TypeVarId) (h : s'.typeMap w = none) : s.typeMap w = none := by
  cases h_w : s.typeMap w with
  | none => rfl
  | some tw => simp [h_ext.typeExt w tw h_w] at h

private theorem ext_unmapped_row {s s' : Subst} (h_ext : Subst.Extends s s')
    (w : RowVarId) (h : s'.rowMap w = none) : s.rowMap w = none := by
  cases h_w : s.rowMap w with
  | none => rfl
  | some rw => simp [h_ext.rowExt w rw h_w] at h

-- =========================================================================
-- Noop for s: types/rows in the range of s have no s-domain vars
-- =========================================================================

-- When s' is idempotent and extends s, values bound in s are fixed points
-- of s (because they have no s'-domain vars, hence no s-domain vars).

private theorem noop_s_for_type_range (s s' : Subst) (fuel : Nat)
    (h_idemp : s'.Idempotent) (h_ext : Subst.Extends s s')
    (v : TypeVarId) (ty : Ty) (hv : s.typeMap v = some ty) :
    applySubst s fuel ty = ty := by
  have h_sv := h_ext.typeExt v ty hv
  have ⟨h_tv, h_rv⟩ := h_idemp.typeRange v ty h_sv
  exact (applySubst_noop s fuel).1 ty
    (fun w hw => ext_unmapped_type h_ext w (h_tv w hw))
    (fun w hw => ext_unmapped_row h_ext w (h_rv w hw))

private theorem noop_s_for_row_range (s s' : Subst) (fuel : Nat)
    (h_idemp : s'.Idempotent) (h_ext : Subst.Extends s s')
    (v : RowVarId) (r : Row) (hv : s.rowMap v = some r) :
    applySubstRow s fuel r = r := by
  have h_sv := h_ext.rowExt v r hv
  have ⟨h_tv, h_rv⟩ := h_idemp.rowRange v r h_sv
  exact (applySubst_noop s fuel).2.1 r
    (fun w hw => ext_unmapped_type h_ext w (h_tv w hw))
    (fun w hw => ext_unmapped_row h_ext w (h_rv w hw))

-- =========================================================================
-- Helper: applySubstRowFields distributes over append (noop right)
-- =========================================================================

/-- Substitution distributes over RowFields.append when the right part is
    a fixed point. This handles the row-merge case in the composition proof. -/
private theorem applySubstRowFields_append_noop_right (s : Subst) :
    ∀ fuel (a b : RowFields),
    (∀ f, applySubstRowFields s f b = b) →
    applySubstRowFields s fuel (a.append b) = (applySubstRowFields s fuel a).append b := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ n ih =>
    intro a b h_noop
    match a with
    | .nil =>
      -- (.nil.append b) = b, applySubstRowFields s (n+1) .nil = .nil
      -- Goal reduces to: applySubstRowFields s (n+1) b = b
      exact h_noop (n + 1)
    | .cons l ty rest =>
      simp only [RowFields.append, applySubstRowFields]
      congr 1
      exact ih rest b h_noop

-- =========================================================================
-- Main theorem: substitution extension absorbs inner application
-- =========================================================================

/-- If s' is idempotent and extends s, applying s before s' is redundant.
    This is the key composition property for reasoning about unification:
    after unify extends the substitution from s to s', any pre-application
    of s is absorbed by the post-application of s'. -/
theorem substCompose_all (s s' : Subst)
    (h_idemp : s'.Idempotent) (h_ext : Subst.Extends s s') :
    ∀ fuel,
    (∀ ty, applySubst s' fuel (applySubst s fuel ty) = applySubst s' fuel ty) ∧
    (∀ r, applySubstRow s' fuel (applySubstRow s fuel r) = applySubstRow s' fuel r) ∧
    (∀ tl, applySubstTyList s' fuel (applySubstTyList s fuel tl) = applySubstTyList s' fuel tl) ∧
    (∀ rf, applySubstRowFields s' fuel (applySubstRowFields s fuel rf) = applySubstRowFields s' fuel rf) := by
  intro fuel
  induction fuel with
  | zero =>
    -- fuel 0: all four functions are identity
    exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  | succ n ih =>
    obtain ⟨ih_ty, ih_row, ih_tl, ih_rf⟩ := ih
    -- Noop lemmas for s' at fuel n and n+1
    obtain ⟨noop_s'_ty_s, noop_s'_row_s, _, _⟩ := applySubst_noop s' (n + 1)
    obtain ⟨noop_s'_ty_n, noop_s'_row_n, _, _⟩ := applySubst_noop s' n
    refine ⟨?_, ?_, ?_, ?_⟩
    -- Part 1: Ty
    · intro ty
      match ty with
      | .int | .intN _ _ | .float | .floatN _ | .decimal _ _ | .bool | .string | .html | .markdown | .atom | .date | .dateTime | .unit | .dynamic => rfl
      | .var v =>
        cases hv : s.typeMap v with
        | none =>
          -- s doesn't bind v: applySubst s (n+1) (.var v) = .var v
          simp only [applySubst, hv]
        | some resolved =>
          -- s binds v → resolved
          have h_sv := h_ext.typeExt v resolved hv
          have ⟨h_tv, h_rv⟩ := h_idemp.typeRange v resolved h_sv
          -- applySubst s (n+1) (.var v) = resolved (via noop on resolved)
          have h_inner : applySubst s (n + 1) (.var v) = resolved := by
            simp only [applySubst, hv]
            exact noop_s_for_type_range s s' n h_idemp h_ext v resolved hv
          -- applySubst s' (n+1) (.var v) = resolved (via extension + noop)
          have h_rhs : applySubst s' (n + 1) (.var v) = resolved := by
            simp only [applySubst, h_sv]
            exact noop_s'_ty_n resolved h_tv h_rv
          -- Both sides equal resolved
          rw [h_inner, noop_s'_ty_s resolved h_tv h_rv, h_rhs]
      | .list inner => simp only [applySubst]; congr 1; exact ih_ty inner
      | .set inner => simp only [applySubst]; congr 1; exact ih_ty inner
      | .option inner => simp only [applySubst]; congr 1; exact ih_ty inner
      | .column inner => simp only [applySubst]; congr 1; exact ih_ty inner
      | .stream inner => simp only [applySubst]; congr 1; exact ih_ty inner
      | .groupedFrame inner keys => simp only [applySubst]; congr 1; exact ih_ty inner
      | .tagged inner tags => simp only [applySubst]; congr 1; exact ih_ty inner
      | .task inner => simp only [applySubst]; congr 1; exact ih_ty inner
      | .actor inner => simp only [applySubst]; congr 1; exact ih_ty inner
      | .arc inner => simp only [applySubst]; congr 1; exact ih_ty inner
      | .fixedSizeList inner d => simp only [applySubst]; congr 1; exact ih_ty inner
      | .tensor inner shape => simp only [applySubst]; congr 1; exact ih_ty inner
      | .sum name args => simp only [applySubst]; congr 1; exact ih_tl args
      | .existential bounds assoc => simp only [applySubst]; congr 1; exact ih_tl assoc
      | .opaque name params => simp only [applySubst]; congr 1; exact ih_tl params
      | .dataframe inner => simp only [applySubst]; congr 1; exact ih_ty inner
      | .map k v =>
        simp only [applySubst]; congr 1
        · exact ih_ty k
        · exact ih_ty v
      | .result ok err =>
        simp only [applySubst]; congr 1
        · exact ih_ty ok
        · exact ih_ty err
      | .record name r => simp only [applySubst]; congr 1; exact ih_row r
      | .anonRecord r => simp only [applySubst]; congr 1; exact ih_row r
      | .row r => simp only [applySubst]; congr 1; exact ih_row r
      | .function params ret =>
        simp only [applySubst]; congr 1
        · exact ih_tl params
        · exact ih_ty ret
      | .forall vars body =>
        simp only [applySubst]
        congr 1
        exact ih_ty body
      | .app ctor args =>
        simp only [applySubst]; congr 1
        · exact ih_ty ctor
        · exact ih_tl args
      | .constructor name fixedArgs arity =>
        simp only [applySubst]; congr 1
        exact ih_tl fixedArgs
      | .tuple elems => simp only [applySubst]; congr 1; exact ih_tl elems
    -- Part 2: Row (the hardest part)
    · intro r
      match r with
      | .mk fields rest =>
        match rest with
        | none =>
          -- Closed row: no row variable, just fields
          simp only [applySubstRow]
          congr 1
          exact ih_rf fields
        | some rv =>
          cases hrv : s.rowMap rv with
          | none =>
            -- s doesn't bind rv
            -- Both sides look up rv in s': same result either way
            cases h_sv_rv : s'.rowMap rv with
            | none =>
              -- Neither s nor s' bind rv
              simp only [applySubstRow, hrv, h_sv_rv]
              congr 1
              exact ih_rf fields
            | some resolvedRow' =>
              -- s doesn't bind rv, but s' does
              simp only [applySubstRow, hrv, h_sv_rv]
              -- Both sides expand to: .mk (fields'.append tail.fields) tail.rest
              -- where tail = applySubstRow s' n resolvedRow'
              -- The only difference is whether fields were pre-applied by s
              generalize applySubstRow s' n resolvedRow' = tail
              match tail with
              | .mk tf tr =>
                -- Reduce: match Row.mk tf tr with | Row.mk t r => ... ↝ ...
                dsimp only
                -- Goal: Row.mk ((...s-then-s'-fields...).append tf) tr
                --     = Row.mk ((...s'-fields...).append tf) tr
                congr 1
                congr 1
                exact ih_rf fields
          | some resolvedRow =>
            -- s binds rv → resolvedRow
            obtain ⟨rfields, rrest⟩ := resolvedRow
            -- Noop: applySubstRow s n (.mk rfields rrest) = .mk rfields rrest
            have h_noop := noop_s_for_row_range s s' n h_idemp h_ext rv (.mk rfields rrest) hrv
            -- Extension: s' also binds rv → (.mk rfields rrest)
            have h_sv_rv := h_ext.rowExt rv (.mk rfields rrest) hrv
            -- Idempotency: resolvedRow has no s'-domain vars
            have ⟨h_rtv, h_rrv⟩ := h_idemp.rowRange rv (.mk rfields rrest) h_sv_rv
            -- s' noop on resolvedRow
            have h_noop_s'_row := noop_s'_row_n (.mk rfields rrest) h_rtv h_rrv
            -- Noop on rfields under s' at any fuel
            have h_rf_noop : ∀ f, applySubstRowFields s' f rfields = rfields := by
              intro f
              exact (applySubst_noop s' f).2.2.2 rfields
                (fun w hw => h_rtv w (by
                  unfold freeTypeVarsRow; exact hw))
                (fun w hw => by
                  apply h_rrv w
                  unfold freeRowVarsRow
                  cases rrest with
                  | none => exact hw
                  | some _ => exact List.mem_cons_of_mem _ hw)
            -- Compute inner: applySubstRow s (n+1) (.mk fields (some rv))
            have h_inner : applySubstRow s (n + 1) (Row.mk fields (some rv)) =
                Row.mk ((applySubstRowFields s n fields).append rfields) rrest := by
              simp only [applySubstRow, hrv, h_noop]
            -- Compute RHS: applySubstRow s' (n+1) (.mk fields (some rv))
            have h_rhs : applySubstRow s' (n + 1) (Row.mk fields (some rv)) =
                Row.mk ((applySubstRowFields s' n fields).append rfields) rrest := by
              simp only [applySubstRow, h_sv_rv, h_noop_s'_row]
            -- Compute LHS: applySubstRow s' (n+1) (.mk (sfields.append rfields) rrest)
            -- This depends on rrest being none or some rv2 (unbound in s')
            rw [h_inner, h_rhs]
            -- Goal: applySubstRow s' (n+1) (.mk (sfields.append rfields) rrest)
            --     = .mk ((applySubstRowFields s' n fields).append rfields) rrest
            match rrest with
            | none =>
              -- Closed resolved row
              simp only [applySubstRow]
              congr 1
              rw [applySubstRowFields_append_noop_right s' n _ rfields h_rf_noop]
              congr 1
              exact ih_rf fields
            | some rv2 =>
              -- Open resolved row, rv2 unbound in s'
              have h_rv2 : s'.rowMap rv2 = none :=
                h_rrv rv2 (by unfold freeRowVarsRow; exact .head _)
              simp only [applySubstRow, h_rv2]
              congr 1
              rw [applySubstRowFields_append_noop_right s' n _ rfields h_rf_noop]
              congr 1
              exact ih_rf fields
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

-- =========================================================================
-- Extracted versions for convenience
-- =========================================================================

/-- Substitution extension absorbs inner application (type level). -/
theorem substCompose (s s' : Subst) (fuel : Nat) (ty : Ty)
    (h_idemp : s'.Idempotent) (h_ext : Subst.Extends s s') :
    applySubst s' fuel (applySubst s fuel ty) = applySubst s' fuel ty :=
  (substCompose_all s s' h_idemp h_ext fuel).1 ty

/-- Substitution extension absorbs inner application (row level). -/
theorem substComposeRow (s s' : Subst) (fuel : Nat) (r : Row)
    (h_idemp : s'.Idempotent) (h_ext : Subst.Extends s s') :
    applySubstRow s' fuel (applySubstRow s fuel r) = applySubstRow s' fuel r :=
  (substCompose_all s s' h_idemp h_ext fuel).2.1 r
