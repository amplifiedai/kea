import Kea.Unify
import Kea.WellFormed
import Kea.Properties.WfSubstitution

/-
  Kea.Properties.WfUnify — WF helpers for unification updates.

  These lemmas establish that core substitution-extension steps used by unifier
  branches preserve the "well-formed substitution range" invariant.
-/

theorem subst_bindType_preserves_wf_range
    (s : Subst) (kctx : KindCtx) (rctx : RowCtx) (v : TypeVarId) (ty : Ty)
    (h_range : Subst.WellFormedRange s kctx rctx)
    (h_ty : Ty.WellFormed kctx rctx ty) :
    Subst.WellFormedRange (s.bindType v ty) kctx rctx := by
  exact Subst.wellFormedRange_bindType s kctx rctx v ty h_range h_ty

theorem subst_bindRow_preserves_wf_range
    (s : Subst) (kctx : KindCtx) (rctx : RowCtx) (rv : RowVarId) (row : Row)
    (h_range : Subst.WellFormedRange s kctx rctx)
    (h_row : Row.WellFormed kctx rctx row) :
    Subst.WellFormedRange (s.bindRow rv row) kctx rctx := by
  exact Subst.wellFormedRange_bindRow s kctx rctx rv row h_range h_row

theorem subst_bindRow_bindRow_preserves_wf_range
    (s : Subst) (kctx : KindCtx) (rctx : RowCtx)
    (rv1 rv2 : RowVarId) (row1 row2 : Row)
    (h_range : Subst.WellFormedRange s kctx rctx)
    (h_row1 : Row.WellFormed kctx rctx row1)
    (h_row2 : Row.WellFormed kctx rctx row2) :
    Subst.WellFormedRange
      (Subst.bindRow (Subst.bindRow s rv1 row1) rv2 row2)
      kctx rctx := by
  exact Subst.wellFormedRange_bindRow_bindRow
    s kctx rctx rv1 rv2 row1 row2 h_range h_row1 h_row2

theorem bindTypeVar_ok_preserves_wf_range
    (st st' : UnifyState) (v : TypeVarId) (ty : Ty) (fuel : Nat)
    (kctx : KindCtx) (rctx : RowCtx)
    (h_ok : bindTypeVar st v ty fuel = .ok st')
    (h_range : Subst.WellFormedRange st.subst kctx rctx)
    (h_ty : Ty.WellFormed kctx rctx ty) :
    Subst.WellFormedRange st'.subst kctx rctx := by
  unfold bindTypeVar at h_ok
  by_cases h_eq : ty == .var v
  · simp [h_eq] at h_ok
    cases h_ok
    exact h_range
  · by_cases h_occ : occursIn v (applySubstCompat st.subst fuel ty)
    · simp [h_eq, h_occ] at h_ok
    · simp [h_eq, h_occ] at h_ok
      cases h_ok
      simpa using subst_bindType_preserves_wf_range st.subst kctx rctx v ty h_range h_ty
