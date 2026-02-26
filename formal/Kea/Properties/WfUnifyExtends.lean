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

/-- Recognized successful `unifyRows` update shapes with WF side conditions. -/
def UnifyRowsSuccessUpdateShapeWf
    (st' stNext : UnifyState) (fuel : Nat) (kctx : KindCtx) (rctx : RowCtx) : Prop :=
  stNext = st'
  ∨ (∃ rOpen rv fields,
      (applySubstRow st'.subst (fuel + 1) rOpen).rest = some rv
      ∧ RowFields.WellFormed kctx rctx fields
      ∧ stNext = { st' with subst := st'.subst.bindRow rv (Row.closed fields) })
  ∨ (∃ r1 r2 rv1 rv2 onlyLeft onlyRight,
      rv2 ≠ rv1
      ∧ (applySubstRow st'.subst (fuel + 1) r1).rest = some rv1
      ∧ (applySubstRow st'.subst (fuel + 1) r2).rest = some rv2
      ∧ RowFields.WellFormed kctx rctx onlyLeft
      ∧ RowFields.WellFormed kctx rctx onlyRight
      ∧ (st'.freshRowVar).1 ∈ rctx
      ∧ let fr := st'.freshRowVar
        let r3 := fr.1
        let st'' := fr.2
        let subst' :=
          Subst.bindRow
            (Subst.bindRow st''.subst rv1 (Row.mkOpen onlyRight r3))
            rv2
            (Row.mkOpen onlyLeft r3)
        stNext = { st'' with subst := subst' })

theorem unifyRowsSuccessUpdateShapeWf_implies_shape
    (st' stNext : UnifyState) (fuel : Nat) (kctx : KindCtx) (rctx : RowCtx)
    (h_shape : UnifyRowsSuccessUpdateShapeWf st' stNext fuel kctx rctx) :
    UnifyRowsSuccessUpdateShape st' stNext fuel := by
  rcases h_shape with h_no_update | h_single_bind | h_open_open
  · exact Or.inl h_no_update
  · rcases h_single_bind with ⟨rOpen, rv, fields, h_rest, _h_fields, h_next⟩
    exact Or.inr (Or.inl ⟨rOpen, rv, fields, h_rest, h_next⟩)
  · rcases h_open_open with
      ⟨r1, r2, rv1, rv2, onlyLeft, onlyRight, h_ne, h_rest1, h_rest2,
       _h_left, _h_right, _h_fresh_in_ctx, h_next⟩
    exact Or.inr (Or.inr ⟨r1, r2, rv1, rv2, onlyLeft, onlyRight, h_ne, h_rest1, h_rest2, h_next⟩)

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

/-- Preconditioned dispatcher combining extension and WF-range preservation. -/
theorem unifyRows_success_update_extendsAndWf_idempotent
    (st st' stNext : UnifyState) (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat)
    (h_ext : ExtendsRowBindings st st')
    (h_idemp : st'.subst.Idempotent)
    (h_wf : UnifyState.SubstWellFormedRange st' kctx rctx)
    (h_shape : UnifyRowsSuccessUpdateShapeWf st' stNext fuel kctx rctx) :
    ExtendsAndWfRange st stNext kctx rctx := by
  rcases h_shape with h_no_update | h_single_bind | h_open_open
  · rw [h_no_update]
    exact ⟨h_ext, h_wf⟩
  · rcases h_single_bind with ⟨rOpen, rv, fields, h_rest, h_fields, h_next⟩
    rw [h_next]
    constructor
    · exact unifyRows_single_bind_update_extends_idempotent
        st st' fuel rOpen rv fields h_ext h_idemp h_rest
    · exact bindClosedRow_update_preserves_substWellFormedRange
        st' kctx rctx rv fields h_wf h_fields
  · rcases h_open_open with
      ⟨r1, r2, rv1, rv2, onlyLeft, onlyRight, h_ne, h_rest1, h_rest2,
       h_left, h_right, h_fresh_in_ctx, h_next⟩
    rw [h_next]
    constructor
    ·
      simpa using unifyRows_open_open_update_extends_idempotent_fresh_no_lacks_update
        st st' fuel r1 r2 rv1 rv2 onlyLeft onlyRight h_ext h_ne h_idemp h_rest1 h_rest2
    ·
      have h_fresh :
          UnifyState.SubstWellFormedRange (st'.freshRowVar).2 kctx rctx :=
        UnifyState.substWellFormedRange_freshRowVar st' kctx rctx h_wf
      exact bindOpenRows_update_preserves_substWellFormedRange
        (st'.freshRowVar).2 kctx rctx rv1 rv2 (st'.freshRowVar).1 onlyLeft onlyRight
        h_fresh h_left h_right h_fresh_in_ctx

/--
Canonical downstream contract name for the preconditioned row-update branch
surface that packages extension and WF-range preservation together.
-/
theorem unifyRows_contract_extendsAndWf
    (st st' stNext : UnifyState) (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat)
    (h_ext : ExtendsRowBindings st st')
    (h_idemp : st'.subst.Idempotent)
    (h_wf : UnifyState.SubstWellFormedRange st' kctx rctx)
    (h_shape : UnifyRowsSuccessUpdateShapeWf st' stNext fuel kctx rctx) :
    ExtendsAndWfRange st stNext kctx rctx := by
  exact unifyRows_success_update_extendsAndWf_idempotent
    st st' stNext kctx rctx fuel h_ext h_idemp h_wf h_shape

/-- Compatibility projection: recover extension-only guarantee from contract. -/
theorem unifyRows_extends_rowMap_preconditioned_of_contract_extendsAndWf
    (st st' stNext : UnifyState) (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat)
    (h_ext : ExtendsRowBindings st st')
    (h_idemp : st'.subst.Idempotent)
    (h_wf : UnifyState.SubstWellFormedRange st' kctx rctx)
    (h_shape : UnifyRowsSuccessUpdateShapeWf st' stNext fuel kctx rctx) :
    ExtendsRowBindings st stNext := by
  exact (unifyRows_contract_extendsAndWf
    st st' stNext kctx rctx fuel h_ext h_idemp h_wf h_shape).1

/--
Combined canonical contract: extension + WF-range preservation from
`WfUnifyExtends`, paired with compat/WF swap-invariance from `UnifyExtends`.
-/
theorem unifyRows_contract_full_wf
    (st st' stNext : UnifyState) (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat)
    (h_ext : ExtendsRowBindings st st')
    (h_idemp : st'.subst.Idempotent)
    (h_wf : UnifyState.SubstWellFormedRange st' kctx rctx)
    (h_shape_wf : UnifyRowsSuccessUpdateShapeWf st' stNext fuel kctx rctx)
    (h_idemp_next : stNext.subst.Idempotent) :
    ExtendsAndWfRange st stNext kctx rctx
    ∧ (let h_ac := Subst.acyclicOfIdempotent h_idemp_next
       CompatWFAgreeOnDomainLookupsAcyclic stNext fuel h_ac) := by
  refine ⟨?_, ?_⟩
  · exact unifyRows_contract_extendsAndWf
      st st' stNext kctx rctx fuel h_ext h_idemp h_wf h_shape_wf
  ·
    have h_shape : UnifyRowsSuccessUpdateShape st' stNext fuel :=
      unifyRowsSuccessUpdateShapeWf_implies_shape st' stNext fuel kctx rctx h_shape_wf
    exact (unifyRows_contract_wf
      st st' stNext fuel h_ext h_idemp h_shape h_idemp_next).2

/-- Projection: recover `stNext` WF-range from the full combined contract. -/
theorem unifyRows_substWellFormedRange_of_contract_full_wf
    (st st' stNext : UnifyState) (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat)
    (h_ext : ExtendsRowBindings st st')
    (h_idemp : st'.subst.Idempotent)
    (h_wf : UnifyState.SubstWellFormedRange st' kctx rctx)
    (h_shape_wf : UnifyRowsSuccessUpdateShapeWf st' stNext fuel kctx rctx)
    (h_idemp_next : stNext.subst.Idempotent) :
    UnifyState.SubstWellFormedRange stNext kctx rctx := by
  exact (unifyRows_contract_full_wf
    st st' stNext kctx rctx fuel h_ext h_idemp h_wf h_shape_wf h_idemp_next).1.2

/-- Projection: recover the legacy `unifyRows_contract_wf` surface from the
WF-annotated-shape contract. -/
theorem unifyRows_contract_wf_of_shape_wf
    (st st' stNext : UnifyState) (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat)
    (h_ext : ExtendsRowBindings st st')
    (h_idemp : st'.subst.Idempotent)
    (h_shape_wf : UnifyRowsSuccessUpdateShapeWf st' stNext fuel kctx rctx)
    (h_idemp_next : stNext.subst.Idempotent) :
    ExtendsRowBindings st stNext
    ∧ (let h_ac := Subst.acyclicOfIdempotent h_idemp_next
       CompatWFAgreeOnDomainLookupsAcyclic stNext fuel h_ac) := by
  have h_shape : UnifyRowsSuccessUpdateShape st' stNext fuel :=
    unifyRowsSuccessUpdateShapeWf_implies_shape st' stNext fuel kctx rctx h_shape_wf
  exact unifyRows_contract_wf
    st st' stNext fuel h_ext h_idemp h_shape h_idemp_next

/-- Projection: recover the legacy unsplit compat/WF contract directly from
WF-annotated-shape assumptions. -/
theorem unifyRows_extends_rowMap_preconditioned_wf_of_shape_wf
    (st st' stNext : UnifyState) (kctx : KindCtx) (rctx : RowCtx) (fuel : Nat)
    (h_ext : ExtendsRowBindings st st')
    (h_idemp : st'.subst.Idempotent)
    (h_shape_wf : UnifyRowsSuccessUpdateShapeWf st' stNext fuel kctx rctx)
    (h_idemp_next : stNext.subst.Idempotent) :
    ExtendsRowBindings st stNext
    ∧ CompatWFAgreeOnDomainLookups stNext fuel h_idemp_next := by
  have h_shape : UnifyRowsSuccessUpdateShape st' stNext fuel :=
    unifyRowsSuccessUpdateShapeWf_implies_shape st' stNext fuel kctx rctx h_shape_wf
  exact unifyRows_extends_rowMap_preconditioned_wf_of_contract
    st st' stNext fuel h_ext h_idemp h_shape h_idemp_next
