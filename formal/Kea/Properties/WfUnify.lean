import Kea.Unify
import Kea.WellFormed
import Kea.Properties.WfSubstitution

/-
  Kea.Properties.WfUnify — WF helpers for unification updates.

  These lemmas establish that core substitution-extension steps used by unifier
  branches preserve the "well-formed substitution range" invariant.
-/

namespace UnifyState

/-- State-level packaging of substitution-range well-formedness. -/
def SubstWellFormedRange
    (st : UnifyState) (kctx : KindCtx) (rctx : RowCtx) : Prop :=
  Subst.WellFormedRange st.subst kctx rctx

@[simp] theorem substWellFormedRange_empty
    (kctx : KindCtx) (rctx : RowCtx) :
    SubstWellFormedRange UnifyState.empty kctx rctx := by
  simpa [SubstWellFormedRange, UnifyState.empty] using
    Subst.wellFormedRange_empty kctx rctx

theorem substWellFormedRange_of_subst_eq
    (st st' : UnifyState) (kctx : KindCtx) (rctx : RowCtx)
    (h_eq : st'.subst = st.subst)
    (h_wf : SubstWellFormedRange st kctx rctx) :
    SubstWellFormedRange st' kctx rctx := by
  simpa [SubstWellFormedRange, h_eq] using h_wf

theorem substWellFormedRange_with_lacks
    (st : UnifyState) (kctx : KindCtx) (rctx : RowCtx) (lacks' : Lacks)
    (h_wf : SubstWellFormedRange st kctx rctx) :
    SubstWellFormedRange { st with lacks := lacks' } kctx rctx := by
  exact substWellFormedRange_of_subst_eq st { st with lacks := lacks' } kctx rctx rfl h_wf

theorem substWellFormedRange_with_traitBounds
    (st : UnifyState) (kctx : KindCtx) (rctx : RowCtx) (bounds' : TraitBounds)
    (h_wf : SubstWellFormedRange st kctx rctx) :
    SubstWellFormedRange { st with traitBounds := bounds' } kctx rctx := by
  exact substWellFormedRange_of_subst_eq st { st with traitBounds := bounds' } kctx rctx rfl h_wf

theorem substWellFormedRange_with_nextTypeVar
    (st : UnifyState) (kctx : KindCtx) (rctx : RowCtx) (next' : Nat)
    (h_wf : SubstWellFormedRange st kctx rctx) :
    SubstWellFormedRange { st with nextTypeVar := next' } kctx rctx := by
  exact substWellFormedRange_of_subst_eq st { st with nextTypeVar := next' } kctx rctx rfl h_wf

theorem substWellFormedRange_with_nextRowVar
    (st : UnifyState) (kctx : KindCtx) (rctx : RowCtx) (next' : Nat)
    (h_wf : SubstWellFormedRange st kctx rctx) :
    SubstWellFormedRange { st with nextRowVar := next' } kctx rctx := by
  exact substWellFormedRange_of_subst_eq st { st with nextRowVar := next' } kctx rctx rfl h_wf

theorem substWellFormedRange_with_non_subst_fields
    (st : UnifyState) (kctx : KindCtx) (rctx : RowCtx)
    (lacks' : Lacks) (bounds' : TraitBounds) (nextType' nextRow' : Nat)
    (h_wf : SubstWellFormedRange st kctx rctx) :
    SubstWellFormedRange
      { st with
          lacks := lacks',
          traitBounds := bounds',
          nextTypeVar := nextType',
          nextRowVar := nextRow' } kctx rctx := by
  exact substWellFormedRange_of_subst_eq
    st
    { st with
        lacks := lacks',
        traitBounds := bounds',
        nextTypeVar := nextType',
        nextRowVar := nextRow' }
    kctx rctx rfl h_wf

theorem substWellFormedRange_freshTypeVar
    (st : UnifyState) (kctx : KindCtx) (rctx : RowCtx)
    (h_wf : SubstWellFormedRange st kctx rctx) :
    SubstWellFormedRange (st.freshTypeVar).2 kctx rctx := by
  unfold UnifyState.freshTypeVar
  simpa using substWellFormedRange_with_nextTypeVar st kctx rctx (st.nextTypeVar + 1) h_wf

theorem substWellFormedRange_freshRowVar
    (st : UnifyState) (kctx : KindCtx) (rctx : RowCtx)
    (h_wf : SubstWellFormedRange st kctx rctx) :
    SubstWellFormedRange (st.freshRowVar).2 kctx rctx := by
  unfold UnifyState.freshRowVar
  simpa using substWellFormedRange_with_nextRowVar st kctx rctx (st.nextRowVar + 1) h_wf

end UnifyState

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

theorem bindTypeVar_ok_preserves_substWellFormedRange
    (st st' : UnifyState) (v : TypeVarId) (ty : Ty) (fuel : Nat)
    (kctx : KindCtx) (rctx : RowCtx)
    (h_ok : bindTypeVar st v ty fuel = .ok st')
    (h_range : UnifyState.SubstWellFormedRange st kctx rctx)
    (h_ty : Ty.WellFormed kctx rctx ty) :
    UnifyState.SubstWellFormedRange st' kctx rctx := by
  exact bindTypeVar_ok_preserves_wf_range st st' v ty fuel kctx rctx h_ok h_range h_ty

theorem bindClosedRow_update_preserves_wf_range
    (st : UnifyState) (kctx : KindCtx) (rctx : RowCtx)
    (rv : RowVarId) (fields : RowFields)
    (h_range : Subst.WellFormedRange st.subst kctx rctx)
    (h_fields : RowFields.WellFormed kctx rctx fields) :
    Subst.WellFormedRange
      ({ st with subst := st.subst.bindRow rv (Row.closed fields) }.subst)
      kctx rctx := by
  simpa using subst_bindClosedRow_preserves_wf_range
    st.subst kctx rctx rv fields h_range h_fields

theorem bindClosedRow_update_preserves_substWellFormedRange
    (st : UnifyState) (kctx : KindCtx) (rctx : RowCtx)
    (rv : RowVarId) (fields : RowFields)
    (h_range : UnifyState.SubstWellFormedRange st kctx rctx)
    (h_fields : RowFields.WellFormed kctx rctx fields) :
    UnifyState.SubstWellFormedRange
      { st with subst := st.subst.bindRow rv (Row.closed fields) } kctx rctx := by
  exact bindClosedRow_update_preserves_wf_range st kctx rctx rv fields h_range h_fields

theorem bindClosedRow_update_with_lacks_preserves_substWellFormedRange
    (st : UnifyState) (kctx : KindCtx) (rctx : RowCtx)
    (rv : RowVarId) (fields : RowFields) (lacks' : Lacks)
    (h_range : UnifyState.SubstWellFormedRange st kctx rctx)
    (h_fields : RowFields.WellFormed kctx rctx fields) :
    UnifyState.SubstWellFormedRange
      { st with
          subst := st.subst.bindRow rv (Row.closed fields),
          lacks := lacks' } kctx rctx := by
  let stBound : UnifyState := { st with subst := st.subst.bindRow rv (Row.closed fields) }
  have h_bound : UnifyState.SubstWellFormedRange stBound kctx rctx :=
    bindClosedRow_update_preserves_substWellFormedRange st kctx rctx rv fields h_range h_fields
  have h_lacks := UnifyState.substWellFormedRange_with_lacks stBound kctx rctx lacks' h_bound
  simpa [stBound] using h_lacks

theorem bindOpenRows_update_preserves_wf_range
    (st : UnifyState) (kctx : KindCtx) (rctx : RowCtx)
    (rv1 rv2 r3 : RowVarId) (onlyLeft onlyRight : RowFields)
    (h_range : Subst.WellFormedRange st.subst kctx rctx)
    (h_left : RowFields.WellFormed kctx rctx onlyLeft)
    (h_right : RowFields.WellFormed kctx rctx onlyRight)
    (h_r3 : r3 ∈ rctx) :
    Subst.WellFormedRange
      ({ st with
          subst :=
            Subst.bindRow
              (Subst.bindRow st.subst rv1 (Row.mkOpen onlyRight r3))
              rv2 (Row.mkOpen onlyLeft r3) }.subst)
      kctx rctx := by
  simpa using subst_bindOpenRows_preserves_wf_range
    st.subst kctx rctx rv1 rv2 r3 onlyLeft onlyRight h_range h_left h_right h_r3

theorem bindOpenRows_update_preserves_substWellFormedRange
    (st : UnifyState) (kctx : KindCtx) (rctx : RowCtx)
    (rv1 rv2 r3 : RowVarId) (onlyLeft onlyRight : RowFields)
    (h_range : UnifyState.SubstWellFormedRange st kctx rctx)
    (h_left : RowFields.WellFormed kctx rctx onlyLeft)
    (h_right : RowFields.WellFormed kctx rctx onlyRight)
    (h_r3 : r3 ∈ rctx) :
    UnifyState.SubstWellFormedRange
      { st with
          subst :=
            Subst.bindRow
              (Subst.bindRow st.subst rv1 (Row.mkOpen onlyRight r3))
              rv2 (Row.mkOpen onlyLeft r3) } kctx rctx := by
  exact bindOpenRows_update_preserves_wf_range
    st kctx rctx rv1 rv2 r3 onlyLeft onlyRight h_range h_left h_right h_r3

theorem bindOpenRows_update_with_lacks_preserves_substWellFormedRange
    (st : UnifyState) (kctx : KindCtx) (rctx : RowCtx)
    (rv1 rv2 r3 : RowVarId) (onlyLeft onlyRight : RowFields) (lacks' : Lacks)
    (h_range : UnifyState.SubstWellFormedRange st kctx rctx)
    (h_left : RowFields.WellFormed kctx rctx onlyLeft)
    (h_right : RowFields.WellFormed kctx rctx onlyRight)
    (h_r3 : r3 ∈ rctx) :
    UnifyState.SubstWellFormedRange
      { st with
          subst :=
            Subst.bindRow
              (Subst.bindRow st.subst rv1 (Row.mkOpen onlyRight r3))
              rv2 (Row.mkOpen onlyLeft r3),
          lacks := lacks' } kctx rctx := by
  let stBound : UnifyState := {
    st with
      subst :=
        Subst.bindRow
          (Subst.bindRow st.subst rv1 (Row.mkOpen onlyRight r3))
          rv2 (Row.mkOpen onlyLeft r3)
  }
  have h_bound : UnifyState.SubstWellFormedRange stBound kctx rctx :=
    bindOpenRows_update_preserves_substWellFormedRange
      st kctx rctx rv1 rv2 r3 onlyLeft onlyRight h_range h_left h_right h_r3
  have h_lacks := UnifyState.substWellFormedRange_with_lacks stBound kctx rctx lacks' h_bound
  simpa [stBound] using h_lacks

theorem freshOpenRows_update_with_lacks_preserves_substWellFormedRange
    (st : UnifyState) (kctx : KindCtx) (rctx : RowCtx)
    (rv1 rv2 : RowVarId) (onlyLeft onlyRight : RowFields) (lacks' : Lacks)
    (h_range : UnifyState.SubstWellFormedRange st kctx rctx)
    (h_left : RowFields.WellFormed kctx rctx onlyLeft)
    (h_right : RowFields.WellFormed kctx rctx onlyRight)
    (h_fresh_in_ctx : (st.freshRowVar).1 ∈ rctx) :
    UnifyState.SubstWellFormedRange
      { (st.freshRowVar).2 with
          subst :=
            Subst.bindRow
              (Subst.bindRow (st.freshRowVar).2.subst rv1 (Row.mkOpen onlyRight (st.freshRowVar).1))
              rv2 (Row.mkOpen onlyLeft (st.freshRowVar).1),
          lacks := lacks' } kctx rctx := by
  have h_fresh : UnifyState.SubstWellFormedRange (st.freshRowVar).2 kctx rctx :=
    UnifyState.substWellFormedRange_freshRowVar st kctx rctx h_range
  exact bindOpenRows_update_with_lacks_preserves_substWellFormedRange
    (st.freshRowVar).2 kctx rctx rv1 rv2 (st.freshRowVar).1 onlyLeft onlyRight lacks'
    h_fresh h_left h_right h_fresh_in_ctx
