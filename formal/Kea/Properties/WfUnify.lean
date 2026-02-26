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

theorem subst_bindClosedRow_preserves_wf_range
    (s : Subst) (kctx : KindCtx) (rctx : RowCtx)
    (rv : RowVarId) (fields : RowFields)
    (h_range : Subst.WellFormedRange s kctx rctx)
    (h_fields : RowFields.WellFormed kctx rctx fields) :
    Subst.WellFormedRange (s.bindRow rv (Row.closed fields)) kctx rctx := by
  exact subst_bindRow_preserves_wf_range s kctx rctx rv (Row.closed fields)
    h_range ((Row.wellFormed_closed_iff kctx rctx fields).2 h_fields)

theorem subst_bindOpenRows_preserves_wf_range
    (s : Subst) (kctx : KindCtx) (rctx : RowCtx)
    (rv1 rv2 r3 : RowVarId) (onlyLeft onlyRight : RowFields)
    (h_range : Subst.WellFormedRange s kctx rctx)
    (h_left : RowFields.WellFormed kctx rctx onlyLeft)
    (h_right : RowFields.WellFormed kctx rctx onlyRight)
    (h_r3 : r3 ∈ rctx) :
    Subst.WellFormedRange
      (Subst.bindRow
        (Subst.bindRow s rv1 (Row.mkOpen onlyRight r3))
        rv2 (Row.mkOpen onlyLeft r3))
      kctx rctx := by
  have h_row_right : Row.WellFormed kctx rctx (Row.mkOpen onlyRight r3) :=
    (Row.wellFormed_mkOpen_iff kctx rctx onlyRight r3).2 ⟨h_right, h_r3⟩
  have h_row_left : Row.WellFormed kctx rctx (Row.mkOpen onlyLeft r3) :=
    (Row.wellFormed_mkOpen_iff kctx rctx onlyLeft r3).2 ⟨h_left, h_r3⟩
  exact subst_bindRow_bindRow_preserves_wf_range
    s kctx rctx rv1 rv2 (Row.mkOpen onlyRight r3) (Row.mkOpen onlyLeft r3)
    h_range h_row_right h_row_left

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
