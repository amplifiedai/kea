import Kea.Properties.UnifyExtends
import Kea.Properties.WfUnify

/-
  Kea.Properties.WfUnifyExtends — combined branch contracts.

  These lemmas package two facts for row-bind branches:
  - row-binding extension (from `UnifyExtends`)
  - substitution-range well-formedness preservation (from `WfUnify`)
-/

def ExtendsAndWfRange
    (st st' : UnifyState) (kctx : KindCtx) (rctx : RowCtx) : Prop :=
  ExtendsRowBindings st st' ∧ UnifyState.SubstWellFormedRange st' kctx rctx

theorem closedBind_extendsAndWfRange
    (st st' : UnifyState) (kctx : KindCtx) (rctx : RowCtx)
    (rv : RowVarId) (fields : RowFields)
    (h_ext : ExtendsRowBindings st st')
    (h_unbound : st'.subst.rowMap rv = none)
    (h_wf : UnifyState.SubstWellFormedRange st' kctx rctx)
    (h_fields : RowFields.WellFormed kctx rctx fields) :
    ExtendsAndWfRange st
      { st' with subst := st'.subst.bindRow rv (Row.closed fields) }
      kctx rctx := by
  constructor
  · exact bindRow_extends_if_unbound_two_state
      st st' rv (Row.closed fields) h_ext h_unbound
  · exact bindClosedRow_update_preserves_substWellFormedRange
      st' kctx rctx rv fields h_wf h_fields

theorem closedBindWithLacks_extendsAndWfRange
    (st st' : UnifyState) (kctx : KindCtx) (rctx : RowCtx)
    (rv : RowVarId) (fields : RowFields) (lacks' : Lacks)
    (h_ext : ExtendsRowBindings st st')
    (h_unbound : st'.subst.rowMap rv = none)
    (h_wf : UnifyState.SubstWellFormedRange st' kctx rctx)
    (h_fields : RowFields.WellFormed kctx rctx fields) :
    ExtendsAndWfRange st
      { st' with
          subst := st'.subst.bindRow rv (Row.closed fields),
          lacks := lacks' }
      kctx rctx := by
  have h_base :
      ExtendsAndWfRange st
        { st' with subst := st'.subst.bindRow rv (Row.closed fields) }
        kctx rctx :=
    closedBind_extendsAndWfRange st st' kctx rctx rv fields h_ext h_unbound h_wf h_fields
  constructor
  · exact ExtendsRowBindings.with_lacks h_base.1 lacks'
  · exact bindClosedRow_update_with_lacks_preserves_substWellFormedRange
      st' kctx rctx rv fields lacks' h_wf h_fields

/-- Combined contract for the `(some rv, none)` successful `unifyRows` update. -/
theorem unifyRows_open_closed_update_extendsAndWf_idempotent
    (st st' : UnifyState) (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat)
    (rOpen : Row) (rv : RowVarId) (onlyRight : RowFields)
    (h_ext : ExtendsRowBindings st st')
    (h_idemp : st'.subst.Idempotent)
    (h_rest : (applySubstRow st'.subst (fuel + 1) rOpen).rest = some rv)
    (h_wf : UnifyState.SubstWellFormedRange st' kctx rctx)
    (h_onlyRight : RowFields.WellFormed kctx rctx onlyRight) :
    ExtendsAndWfRange st
      { st' with subst := st'.subst.bindRow rv (Row.closed onlyRight) }
      kctx rctx := by
  constructor
  · exact unifyRows_open_closed_update_extends_idempotent
      st st' fuel rOpen rv onlyRight h_ext h_idemp h_rest
  · exact bindClosedRow_update_preserves_substWellFormedRange
      st' kctx rctx rv onlyRight h_wf h_onlyRight

/-- Combined contract for the `(none, some rv)` successful `unifyRows` update. -/
theorem unifyRows_closed_open_update_extendsAndWf_idempotent
    (st st' : UnifyState) (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat)
    (rOpen : Row) (rv : RowVarId) (onlyLeft : RowFields)
    (h_ext : ExtendsRowBindings st st')
    (h_idemp : st'.subst.Idempotent)
    (h_rest : (applySubstRow st'.subst (fuel + 1) rOpen).rest = some rv)
    (h_wf : UnifyState.SubstWellFormedRange st' kctx rctx)
    (h_onlyLeft : RowFields.WellFormed kctx rctx onlyLeft) :
    ExtendsAndWfRange st
      { st' with subst := st'.subst.bindRow rv (Row.closed onlyLeft) }
      kctx rctx := by
  constructor
  · exact unifyRows_closed_open_update_extends_idempotent
      st st' fuel rOpen rv onlyLeft h_ext h_idemp h_rest
  · exact bindClosedRow_update_preserves_substWellFormedRange
      st' kctx rctx rv onlyLeft h_wf h_onlyLeft

/-- Combined contract for the open-open fresh-row successful `unifyRows` update. -/
theorem unifyRows_open_open_update_extendsAndWf_idempotent_fresh
    (st st' : UnifyState) (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat)
    (r1 r2 : Row) (rv1 rv2 : RowVarId) (onlyLeft onlyRight : RowFields)
    (lacks'' : Lacks)
    (h_ext : ExtendsRowBindings st st')
    (h_ne : rv2 ≠ rv1)
    (h_idemp : st'.subst.Idempotent)
    (h_rest1 : (applySubstRow st'.subst (fuel + 1) r1).rest = some rv1)
    (h_rest2 : (applySubstRow st'.subst (fuel + 1) r2).rest = some rv2)
    (h_wf : UnifyState.SubstWellFormedRange st' kctx rctx)
    (h_onlyLeft : RowFields.WellFormed kctx rctx onlyLeft)
    (h_onlyRight : RowFields.WellFormed kctx rctx onlyRight)
    (h_fresh_in_ctx : (st'.freshRowVar).1 ∈ rctx) :
    let fr := st'.freshRowVar
    let r3 := fr.1
    let st'' := fr.2
    let subst' :=
      Subst.bindRow
        (Subst.bindRow st''.subst rv1 (Row.mkOpen onlyRight r3))
        rv2
        (Row.mkOpen onlyLeft r3)
    ExtendsAndWfRange st { st'' with subst := subst', lacks := lacks'' } kctx rctx := by
  dsimp
  constructor
  · exact unifyRows_open_open_update_extends_idempotent_fresh
      st st' fuel r1 r2 rv1 rv2 onlyLeft onlyRight lacks''
      h_ext h_ne h_idemp h_rest1 h_rest2
  · exact freshOpenRows_update_with_lacks_preserves_substWellFormedRange
      st' kctx rctx rv1 rv2 onlyLeft onlyRight lacks''
      h_wf h_onlyLeft h_onlyRight h_fresh_in_ctx

/-- Full-state open-open combined contract (including non-`subst` updates). -/
theorem unifyRows_open_open_update_extendsAndWf_idempotent_full_state_fresh
    (st st' : UnifyState) (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat)
    (r1 r2 : Row) (rv1 rv2 : RowVarId) (onlyLeft onlyRight : RowFields)
    (lacks'' : Lacks) (bounds'' : TraitBounds) (nextType'' nextRow'' : Nat)
    (h_ext : ExtendsRowBindings st st')
    (h_ne : rv2 ≠ rv1)
    (h_idemp : st'.subst.Idempotent)
    (h_rest1 : (applySubstRow st'.subst (fuel + 1) r1).rest = some rv1)
    (h_rest2 : (applySubstRow st'.subst (fuel + 1) r2).rest = some rv2)
    (h_wf : UnifyState.SubstWellFormedRange st' kctx rctx)
    (h_onlyLeft : RowFields.WellFormed kctx rctx onlyLeft)
    (h_onlyRight : RowFields.WellFormed kctx rctx onlyRight)
    (h_fresh_in_ctx : (st'.freshRowVar).1 ∈ rctx) :
    let fr := st'.freshRowVar
    let r3 := fr.1
    let st'' := fr.2
    let subst' :=
      Subst.bindRow
        (Subst.bindRow st''.subst rv1 (Row.mkOpen onlyRight r3))
        rv2
        (Row.mkOpen onlyLeft r3)
    ExtendsAndWfRange st
      { st'' with
          subst := subst',
          lacks := lacks'',
          traitBounds := bounds'',
          nextTypeVar := nextType'',
          nextRowVar := nextRow'' }
      kctx rctx := by
  dsimp
  constructor
  · exact unifyRows_open_open_update_extends_idempotent_full_state_fresh
      st st' fuel r1 r2 rv1 rv2 onlyLeft onlyRight
      lacks'' bounds'' nextType'' nextRow''
      h_ext h_ne h_idemp h_rest1 h_rest2
  ·
    let stBase : UnifyState :=
      { (st'.freshRowVar).2 with
          subst :=
            Subst.bindRow
              (Subst.bindRow (st'.freshRowVar).2.subst rv1 (Row.mkOpen onlyRight (st'.freshRowVar).1))
              rv2
              (Row.mkOpen onlyLeft (st'.freshRowVar).1),
          lacks := lacks'' }
    have h_base : UnifyState.SubstWellFormedRange stBase kctx rctx :=
      freshOpenRows_update_with_lacks_preserves_substWellFormedRange
        st' kctx rctx rv1 rv2 onlyLeft onlyRight lacks''
        h_wf h_onlyLeft h_onlyRight h_fresh_in_ctx
    exact UnifyState.substWellFormedRange_of_subst_eq
      stBase
      { (st'.freshRowVar).2 with
          subst :=
            Subst.bindRow
              (Subst.bindRow (st'.freshRowVar).2.subst rv1 (Row.mkOpen onlyRight (st'.freshRowVar).1))
              rv2
              (Row.mkOpen onlyLeft (st'.freshRowVar).1),
          lacks := lacks'',
          traitBounds := bounds'',
          nextTypeVar := nextType'',
          nextRowVar := nextRow'' }
      kctx rctx rfl h_base
