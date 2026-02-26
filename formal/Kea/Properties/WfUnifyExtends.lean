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
