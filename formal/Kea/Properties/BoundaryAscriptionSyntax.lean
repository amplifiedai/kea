import Kea.Properties.BoundaryAssignability
import Kea.Properties.DynamicBoundaryTypingBridge
import Kea.Properties.WrapperBoundaryTypingBridge
import Kea.Properties.GroupedTaggedTypingBridge

/-!
  Kea.Properties.BoundaryAscriptionSyntax

  Expression-level ascription surface for boundary typing bridges. This keeps
  the existing boundary relations unchanged while making the ascription step
  explicit in a syntax/judgment layer.
-/

-- `CoreExprWithAscription` and `HasTypeWithAscription` now live in
-- `Kea.Typing`; this module specializes them to boundary-policy families.

/-- Dynamic boundary relation used by expression-level ascription typing. -/
abbrev DynamicAscriptionAllowsAtSite
    (site : DynamicBoundarySite) : Ty → Ty → Prop :=
  allowsByBool (dynamicBoundaryAllowsAtSite site)

/-- Wrapper boundary relation used by expression-level ascription typing. -/
abbrev WrapperAscriptionAllowsAtSite
    (site : WrapperBoundarySite) : Ty → Ty → Prop :=
  allowsByBoolAndUnify (wrapperBoundaryAllowsAtSite site) UnifyState.empty 2

/-- Grouped/tagged boundary relation used by expression-level ascription typing. -/
abbrev GroupedTaggedAscriptionAllowsAtSite
    (site : GroupedTaggedBoundarySite) : Ty → Ty → Prop :=
  allowsByBoolAndUnify (groupedTaggedBoundaryAllowsAtSite site) UnifyState.empty 2

/-- Expression-level Dynamic ascription typing. -/
abbrev HasTypeWithDynamicAscriptionAtSite
    (site : DynamicBoundarySite)
    (env : TermEnv) (e : CoreExprWithAscription) (ty : Ty) : Prop :=
  HasTypeWithAscription (DynamicAscriptionAllowsAtSite site) env e ty

/-- Expression-level wrapper ascription typing. -/
abbrev HasTypeWithWrapperAscriptionAtSite
    (site : WrapperBoundarySite)
    (env : TermEnv) (e : CoreExprWithAscription) (ty : Ty) : Prop :=
  HasTypeWithAscription (WrapperAscriptionAllowsAtSite site) env e ty

/-- Expression-level grouped/tagged ascription typing. -/
abbrev HasTypeWithGroupedTaggedAscriptionAtSite
    (site : GroupedTaggedBoundarySite)
    (env : TermEnv) (e : CoreExprWithAscription) (ty : Ty) : Prop :=
  HasTypeWithAscription (GroupedTaggedAscriptionAllowsAtSite site) env e ty

/-- Dynamic boundary gate and Dynamic ascription expression typing are
    equivalent at each site. -/
theorem hasTypeWithDynamicAscription_ascribe_iff_boundary
    (site : DynamicBoundarySite)
    (env : TermEnv) (e : CoreExpr) (expected : Ty) :
    HasTypeWithDynamicAscriptionAtSite site env (.ascribe e expected) expected
      ↔ HasTypeAtAscriptionBoundaryAtSite site env e expected := by
  simpa [HasTypeWithDynamicAscriptionAtSite, DynamicAscriptionAllowsAtSite,
    HasTypeAtAscriptionBoundaryAtSite]
    using hasTypeWithAscription_ascribe_iff
      (allowsByBool (dynamicBoundaryAllowsAtSite site)) env e expected

/-- Wrapper boundary gate and wrapper ascription expression typing are
    equivalent at each site. -/
theorem hasTypeWithWrapperAscription_ascribe_iff_boundary
    (site : WrapperBoundarySite)
    (env : TermEnv) (e : CoreExpr) (expected : Ty) :
    HasTypeWithWrapperAscriptionAtSite site env (.ascribe e expected) expected
      ↔ HasTypeAtWrapperBoundaryAtSite site env e expected := by
  simpa [HasTypeWithWrapperAscriptionAtSite, WrapperAscriptionAllowsAtSite,
    HasTypeAtWrapperBoundaryAtSite]
    using hasTypeWithAscription_ascribe_iff
      (allowsByBoolAndUnify (wrapperBoundaryAllowsAtSite site) UnifyState.empty 2)
      env e expected

/-- Grouped/tagged boundary gate and grouped/tagged ascription expression
    typing are equivalent at each site. -/
theorem hasTypeWithGroupedTaggedAscription_ascribe_iff_boundary
    (site : GroupedTaggedBoundarySite)
    (env : TermEnv) (e : CoreExpr) (expected : Ty) :
    HasTypeWithGroupedTaggedAscriptionAtSite site env (.ascribe e expected) expected
      ↔ HasTypeAtGroupedTaggedBoundaryAtSite site env e expected := by
  simpa [HasTypeWithGroupedTaggedAscriptionAtSite,
    GroupedTaggedAscriptionAllowsAtSite, HasTypeAtGroupedTaggedBoundaryAtSite]
    using hasTypeWithAscription_ascribe_iff
      (allowsByBoolAndUnify
        (groupedTaggedBoundaryAllowsAtSite site)
        UnifyState.empty
        2)
      env e expected

/-- Dynamic expression-level ascription typing is currently site-invariant on
    explicit `ascribe` nodes. -/
theorem hasTypeWithDynamicAscription_ascribe_iff_ascription
    (site : DynamicBoundarySite)
    (env : TermEnv) (e : CoreExpr) (expected : Ty) :
    HasTypeWithDynamicAscriptionAtSite site env (.ascribe e expected) expected
      ↔ HasTypeWithDynamicAscriptionAtSite .ascription env (.ascribe e expected) expected := by
  constructor
  · intro h
    have h_boundary : HasTypeAtAscriptionBoundaryAtSite site env e expected :=
      (hasTypeWithDynamicAscription_ascribe_iff_boundary site env e expected).1 h
    have h_ascr :
        HasTypeAtAscriptionBoundaryAtSite .ascription env e expected :=
      (hasTypeAtAscriptionBoundaryAtSite_iff_ascription site env e expected).1 h_boundary
    exact (hasTypeWithDynamicAscription_ascribe_iff_boundary
      .ascription env e expected).2 h_ascr
  · intro h
    have h_boundary : HasTypeAtAscriptionBoundaryAtSite .ascription env e expected :=
      (hasTypeWithDynamicAscription_ascribe_iff_boundary
        .ascription env e expected).1 h
    have h_site :
        HasTypeAtAscriptionBoundaryAtSite site env e expected :=
      (hasTypeAtAscriptionBoundaryAtSite_iff_ascription site env e expected).2 h_boundary
    exact (hasTypeWithDynamicAscription_ascribe_iff_boundary site env e expected).2 h_site

/-- Wrapper expression-level ascription typing is currently site-invariant on
    explicit `ascribe` nodes. -/
theorem hasTypeWithWrapperAscription_ascribe_iff_ascription
    (site : WrapperBoundarySite)
    (env : TermEnv) (e : CoreExpr) (expected : Ty) :
    HasTypeWithWrapperAscriptionAtSite site env (.ascribe e expected) expected
      ↔ HasTypeWithWrapperAscriptionAtSite .ascription env (.ascribe e expected) expected := by
  constructor
  · intro h
    have h_boundary : HasTypeAtWrapperBoundaryAtSite site env e expected :=
      (hasTypeWithWrapperAscription_ascribe_iff_boundary site env e expected).1 h
    have h_ascr : HasTypeAtWrapperBoundaryAtSite .ascription env e expected :=
      (hasTypeAtWrapperBoundaryAtSite_iff_ascription site env e expected).1 h_boundary
    exact (hasTypeWithWrapperAscription_ascribe_iff_boundary
      .ascription env e expected).2 h_ascr
  · intro h
    have h_boundary : HasTypeAtWrapperBoundaryAtSite .ascription env e expected :=
      (hasTypeWithWrapperAscription_ascribe_iff_boundary
        .ascription env e expected).1 h
    have h_site : HasTypeAtWrapperBoundaryAtSite site env e expected :=
      (hasTypeAtWrapperBoundaryAtSite_iff_ascription site env e expected).2 h_boundary
    exact (hasTypeWithWrapperAscription_ascribe_iff_boundary site env e expected).2 h_site

/-- Grouped/tagged expression-level ascription typing is currently
    site-invariant on explicit `ascribe` nodes. -/
theorem hasTypeWithGroupedTaggedAscription_ascribe_iff_ascription
    (site : GroupedTaggedBoundarySite)
    (env : TermEnv) (e : CoreExpr) (expected : Ty) :
    HasTypeWithGroupedTaggedAscriptionAtSite site env (.ascribe e expected) expected
      ↔ HasTypeWithGroupedTaggedAscriptionAtSite .ascription env (.ascribe e expected) expected := by
  constructor
  · intro h
    have h_boundary : HasTypeAtGroupedTaggedBoundaryAtSite site env e expected :=
      (hasTypeWithGroupedTaggedAscription_ascribe_iff_boundary site env e expected).1 h
    have h_ascr :
        HasTypeAtGroupedTaggedBoundaryAtSite .ascription env e expected :=
      (hasTypeAtGroupedTaggedBoundaryAtSite_iff_ascription site env e expected).1 h_boundary
    exact (hasTypeWithGroupedTaggedAscription_ascribe_iff_boundary
      .ascription env e expected).2 h_ascr
  · intro h
    have h_boundary :
        HasTypeAtGroupedTaggedBoundaryAtSite .ascription env e expected :=
      (hasTypeWithGroupedTaggedAscription_ascribe_iff_boundary
        .ascription env e expected).1 h
    have h_site :
        HasTypeAtGroupedTaggedBoundaryAtSite site env e expected :=
      (hasTypeAtGroupedTaggedBoundaryAtSite_iff_ascription site env e expected).2 h_boundary
    exact (hasTypeWithGroupedTaggedAscription_ascribe_iff_boundary
      site env e expected).2 h_site

/-- Minimal algorithmic checker for Dynamic ascriptions at a chosen boundary
    site. This reuses `inferExprWithAscription` from `Kea/Typing.lean`
    with the Dynamic boundary predicate. -/
def inferDynamicAscriptionAtSite
    (site : DynamicBoundarySite)
    (env : TermEnv) (e : CoreExpr) (expected : Ty) : Option Ty :=
  inferExprWithAscription (dynamicBoundaryAllowsAtSite site) env
    (.ascribe e expected)

/-- Soundness of `inferDynamicAscriptionAtSite` with respect to
    `HasTypeWithDynamicAscriptionAtSite`. -/
theorem inferDynamicAscriptionAtSite_sound
    (site : DynamicBoundarySite)
    (env : TermEnv) (e : CoreExpr) (expected : Ty)
    (h_infer : inferDynamicAscriptionAtSite site env e expected = some expected) :
    HasTypeWithDynamicAscriptionAtSite site env (.ascribe e expected) expected := by
  unfold inferDynamicAscriptionAtSite at h_infer
  have h_core :
      HasTypeWithAscription
        (fun exp act => dynamicBoundaryAllowsAtSite site exp act = true)
        env
        (.ascribe e expected)
        expected :=
    inferExprWithAscription_sound
      (dynamicBoundaryAllowsAtSite site) env (.ascribe e expected) expected h_infer
  simpa [HasTypeWithDynamicAscriptionAtSite, DynamicAscriptionAllowsAtSite,
    allowsByBool] using h_core

/-- Algorithmic Dynamic-ascription witness: narrowing `Dynamic -> Int`
    is rejected at all boundary-sensitive sites. -/
theorem inferDynamicAscriptionAtSite_var_rejects_int
    (site : DynamicBoundarySite) :
    inferDynamicAscriptionAtSite site [("x", .dynamic)] (.var "x") .int = none := by
  unfold inferDynamicAscriptionAtSite inferExprWithAscription
  simp [inferExpr, TermEnv.lookup,
    dynamic_boundary_rejects_int_from_dynamic_all_sites site]

/-- Algorithmic Dynamic-ascription witness: identity `Dynamic -> Dynamic`
    is accepted at all boundary-sensitive sites. -/
theorem inferDynamicAscriptionAtSite_var_accepts_dynamic
    (site : DynamicBoundarySite) :
    inferDynamicAscriptionAtSite site [("x", .dynamic)] (.var "x") .dynamic
      = some .dynamic := by
  unfold inferDynamicAscriptionAtSite inferExprWithAscription
  simp [inferExpr, TermEnv.lookup,
    dynamic_boundary_allows_dynamic_from_any_all_sites site .dynamic]

/-- Packaged algorithmic Dynamic-ascription bridge at a chosen boundary site. -/
theorem inferDynamicAscriptionAtSite_var_bridge
    (site : DynamicBoundarySite) :
    inferDynamicAscriptionAtSite site [("x", .dynamic)] (.var "x") .int = none
    ∧ inferDynamicAscriptionAtSite site [("x", .dynamic)] (.var "x") .dynamic = some .dynamic
    ∧ HasTypeWithDynamicAscriptionAtSite site
        [("x", .dynamic)] (.ascribe (.var "x") .dynamic) .dynamic := by
  refine ⟨
    inferDynamicAscriptionAtSite_var_rejects_int site,
    inferDynamicAscriptionAtSite_var_accepts_dynamic site,
    ?_⟩
  exact inferDynamicAscriptionAtSite_sound site
    [("x", .dynamic)] (.var "x") .dynamic
    (inferDynamicAscriptionAtSite_var_accepts_dynamic site)

/-- Declarative rejection witness corresponding to
    `inferDynamicAscriptionAtSite_var_rejects_int`. -/
theorem hasTypeWithDynamicAscriptionAtSite_var_rejects_int
    (site : DynamicBoundarySite) :
    ¬ HasTypeWithDynamicAscriptionAtSite site
        [("x", .dynamic)] (.ascribe (.var "x") .int) .int := by
  intro h
  have h_boundary : HasTypeAtAscriptionBoundaryAtSite site [("x", .dynamic)] (.var "x") .int :=
    (hasTypeWithDynamicAscription_ascribe_iff_boundary site
      [("x", .dynamic)] (.var "x") .int).1 h
  have h_ascr : HasTypeAtAscriptionBoundaryAtSite .ascription
      [("x", .dynamic)] (.var "x") .int :=
    (hasTypeAtAscriptionBoundaryAtSite_iff_ascription site
      [("x", .dynamic)] (.var "x") .int).1 h_boundary
  exact hasType_ascription_dynamic_to_int_rejected h_ascr

/-- Declarative acceptance witness corresponding to
    `inferDynamicAscriptionAtSite_var_accepts_dynamic`. -/
theorem hasTypeWithDynamicAscriptionAtSite_var_accepts_dynamic
    (site : DynamicBoundarySite) :
    HasTypeWithDynamicAscriptionAtSite site
      [("x", .dynamic)] (.ascribe (.var "x") .dynamic) .dynamic := by
  exact inferDynamicAscriptionAtSite_sound site
    [("x", .dynamic)] (.var "x") .dynamic
    (inferDynamicAscriptionAtSite_var_accepts_dynamic site)

/-- Algorithmic/declarative alignment for the Dynamic variable witness at a
    chosen site. -/
theorem dynamicAscriptionAlgorithmicDeclarativeVarAlignmentAtSite
    (site : DynamicBoundarySite) :
    (inferDynamicAscriptionAtSite site [("x", .dynamic)] (.var "x") .int = none
      ↔
      ¬ HasTypeWithDynamicAscriptionAtSite site
          [("x", .dynamic)] (.ascribe (.var "x") .int) .int)
    ∧
    (inferDynamicAscriptionAtSite site [("x", .dynamic)] (.var "x") .dynamic = some .dynamic
      ↔
      HasTypeWithDynamicAscriptionAtSite site
        [("x", .dynamic)] (.ascribe (.var "x") .dynamic) .dynamic) := by
  refine ⟨?_, ?_⟩
  · constructor
    · intro _h
      exact hasTypeWithDynamicAscriptionAtSite_var_rejects_int site
    · intro _h
      exact inferDynamicAscriptionAtSite_var_rejects_int site
  · constructor
    · intro _h
      exact hasTypeWithDynamicAscriptionAtSite_var_accepts_dynamic site
    · intro _h
      exact inferDynamicAscriptionAtSite_var_accepts_dynamic site

/-- Packaged algorithmic Dynamic-ascription slice at a chosen boundary site. -/
def DynamicAscriptionAlgorithmicSliceAtSite
    (site : DynamicBoundarySite) : Prop :=
  inferDynamicAscriptionAtSite site [("x", .dynamic)] (.var "x") .int = none
  ∧ inferDynamicAscriptionAtSite site [("x", .dynamic)] (.var "x") .dynamic = some .dynamic
  ∧ HasTypeWithDynamicAscriptionAtSite site
      [("x", .dynamic)] (.ascribe (.var "x") .dynamic) .dynamic

/-- Ascription-specialized alias for `DynamicAscriptionAlgorithmicSliceAtSite`. -/
abbrev DynamicAscriptionAlgorithmicSlice : Prop :=
  DynamicAscriptionAlgorithmicSliceAtSite .ascription

/-- Proof witness for `DynamicAscriptionAlgorithmicSliceAtSite`. -/
theorem dynamicAscriptionAlgorithmicSliceAtSite_proved
    (site : DynamicBoundarySite) :
    DynamicAscriptionAlgorithmicSliceAtSite site := by
  exact inferDynamicAscriptionAtSite_var_bridge site

/-- Proof witness for ascription-specialized
    `DynamicAscriptionAlgorithmicSlice`. -/
theorem dynamicAscriptionAlgorithmicSlice_proved :
    DynamicAscriptionAlgorithmicSlice := by
  simpa [DynamicAscriptionAlgorithmicSlice]
    using dynamicAscriptionAlgorithmicSliceAtSite_proved .ascription

/-- Minimal algorithmic checker for wrapper ascriptions at a chosen boundary
    site. This reuses `inferExprWithAscription`, the wrapper boundary
    predicate, and the explicit unifier-success gate used by
    `WrapperAscriptionAllowsAtSite`. -/
def wrapperAscriptionAllowsBoolAtSite
    (site : WrapperBoundarySite)
    (expected actual : Ty) : Bool :=
  if wrapperBoundaryAllowsAtSite site expected actual
  then
    match unify UnifyState.empty 2 expected actual with
    | .ok _ => true
    | .err _ => false
  else false

/-- Minimal algorithmic checker for wrapper ascriptions at a chosen boundary
    site. -/
def inferWrapperAscriptionAtSite
    (site : WrapperBoundarySite)
    (env : TermEnv) (e : CoreExpr) (expected : Ty) : Option Ty :=
  inferExprWithAscription (wrapperAscriptionAllowsBoolAtSite site) env
    (.ascribe e expected)

/-- Boolean wrapper ascription gate agrees with the declarative
    wrapper-ascription relation. -/
theorem wrapperAscriptionAllowsBoolAtSite_true_iff
    (site : WrapperBoundarySite)
    (expected actual : Ty) :
    wrapperAscriptionAllowsBoolAtSite site expected actual = true
      ↔ WrapperAscriptionAllowsAtSite site expected actual := by
  constructor
  · intro h_gate
    unfold wrapperAscriptionAllowsBoolAtSite at h_gate
    by_cases h_allow : wrapperBoundaryAllowsAtSite site expected actual = true
    · have h_unify :
          ∃ st', unify UnifyState.empty 2 expected actual = .ok st' := by
        cases h_u : unify UnifyState.empty 2 expected actual with
        | ok st' =>
            exact ⟨st', rfl⟩
        | err _ =>
            simp [h_allow, h_u] at h_gate
      exact ⟨h_allow, h_unify⟩
    · simp [h_allow] at h_gate
  · intro h_rel
    rcases h_rel with ⟨h_allow, h_unify⟩
    rcases h_unify with ⟨st', h_unify⟩
    unfold wrapperAscriptionAllowsBoolAtSite
    simp [h_allow, h_unify]

/-- Successful wrapper ascription inference always returns the annotated type. -/
theorem inferWrapperAscriptionAtSite_some_implies_expected
    (site : WrapperBoundarySite)
    (env : TermEnv) (e : CoreExpr) (expected ty : Ty)
    (h_infer : inferWrapperAscriptionAtSite site env e expected = some ty) :
    ty = expected := by
  unfold inferWrapperAscriptionAtSite inferExprWithAscription at h_infer
  cases h_expr : inferExpr env e with
  | none =>
      simp [h_expr] at h_infer
  | some actual =>
      by_cases h_gate : wrapperAscriptionAllowsBoolAtSite site expected actual = true
      · simp [h_expr, h_gate] at h_infer
        cases h_infer
        rfl
      · simp [h_expr, h_gate] at h_infer

/-- Soundness of `inferWrapperAscriptionAtSite` with respect to
    `HasTypeWithWrapperAscriptionAtSite`. -/
theorem inferWrapperAscriptionAtSite_sound
    (site : WrapperBoundarySite)
    (env : TermEnv) (e : CoreExpr) (expected : Ty)
    (h_infer : inferWrapperAscriptionAtSite site env e expected = some expected) :
    HasTypeWithWrapperAscriptionAtSite site env (.ascribe e expected) expected := by
  unfold inferWrapperAscriptionAtSite inferExprWithAscription at h_infer
  cases h_expr : inferExpr env e with
  | none =>
      simp [h_expr] at h_infer
  | some actual =>
      have h_gate_true : wrapperAscriptionAllowsBoolAtSite site expected actual = true := by
        by_cases h_gate : wrapperAscriptionAllowsBoolAtSite site expected actual = true
        · exact h_gate
        · simp [h_expr, h_gate] at h_infer
      have h_actual : HasType env e actual :=
        inferExpr_sound env e actual h_expr
      have h_rel : WrapperAscriptionAllowsAtSite site expected actual :=
        (wrapperAscriptionAllowsBoolAtSite_true_iff site expected actual).1 h_gate_true
      exact HasTypeWithAscription.ascribe env e expected ⟨actual, h_actual, h_rel⟩

/-- Wrapper ascription inference is equivalent to modeled wrapper boundary
    assignability on explicit `ascribe` nodes. -/
theorem inferWrapperAscriptionAtSite_iff_boundary
    (site : WrapperBoundarySite)
    (env : TermEnv) (e : CoreExpr) (expected : Ty) :
    inferWrapperAscriptionAtSite site env e expected = some expected
      ↔ HasTypeAtWrapperBoundaryAtSite site env e expected := by
  have h_core :
      inferWrapperAscriptionAtSite site env e expected = some expected
        ↔
        HasTypeAtCoreBoundary
          (fun exp act =>
            wrapperAscriptionAllowsBoolAtSite site exp act = true)
          env e expected := by
    simpa [inferWrapperAscriptionAtSite]
      using inferExprWithAscription_ascribe_iff_boundary
        (wrapperAscriptionAllowsBoolAtSite site) env e expected
  have h_rel :
      HasTypeAtCoreBoundary
          (fun exp act =>
            wrapperAscriptionAllowsBoolAtSite site exp act = true)
          env e expected
        ↔
        HasTypeAtWrapperBoundaryAtSite site env e expected := by
    simpa [HasTypeAtWrapperBoundaryAtSite, WrapperAscriptionAllowsAtSite,
      HasTypeAtBoundary]
      using (hasTypeAtBoundary_congr
        (fun exp act =>
          wrapperAscriptionAllowsBoolAtSite site exp act = true)
        (WrapperAscriptionAllowsAtSite site)
        env e expected
        (by
          intro exp act
          exact wrapperAscriptionAllowsBoolAtSite_true_iff site exp act))
  exact h_core.trans h_rel

/-- Wrapper ascription inference is equivalent to wrapper ascription typing at
    explicit `ascribe` nodes. -/
theorem inferWrapperAscriptionAtSite_iff
    (site : WrapperBoundarySite)
    (env : TermEnv) (e : CoreExpr) (expected : Ty) :
    inferWrapperAscriptionAtSite site env e expected = some expected
      ↔ HasTypeWithWrapperAscriptionAtSite site env
          (.ascribe e expected) expected := by
  exact (inferWrapperAscriptionAtSite_iff_boundary site env e expected).trans
    (hasTypeWithWrapperAscription_ascribe_iff_boundary
      site env e expected).symm

/-- Wrapper algorithmic witness: `Task(Bool) -> Task(Int)` rejects at all
    boundary-sensitive sites. -/
theorem inferWrapperAscriptionAtSite_task_rejects
    (site : WrapperBoundarySite) :
    inferWrapperAscriptionAtSite site
      wrapperTaskVarBoolEnv (.var "t") (.task .int) = none := by
  have h_allow : wrapperBoundaryAllowsAtSite site (.task .int) (.task .bool) = false := by
    simpa [wrapperBoundaryAllowsAtSite] using wrapper_boundary_rejects_task_inner_mismatch
  have h_gate :
      wrapperAscriptionAllowsBoolAtSite site (.task .int) (.task .bool) = false := by
    unfold wrapperAscriptionAllowsBoolAtSite
    simp [h_allow]
  simp [inferWrapperAscriptionAtSite, inferExprWithAscription, inferExpr,
    TermEnv.lookup, h_gate]

/-- Wrapper algorithmic witness: `Task(Int) -> Task(Int)` accepts at all
    boundary-sensitive sites. -/
theorem inferWrapperAscriptionAtSite_task_accepts
    (site : WrapperBoundarySite) :
    inferWrapperAscriptionAtSite site
      wrapperTaskVarIntEnv (.var "t") (.task .int) = some (.task .int) := by
  have h_allow : wrapperBoundaryAllowsAtSite site (.task .int) (.task .int) = true := by
    cases site <;> native_decide
  have h_unify : unify UnifyState.empty 2 (.task .int) (.task .int) = .ok UnifyState.empty := by
    simpa using (task_unifies_with_self UnifyState.empty 1 .int)
  have h_gate :
      wrapperAscriptionAllowsBoolAtSite site (.task .int) (.task .int) = true := by
    unfold wrapperAscriptionAllowsBoolAtSite
    simp [h_allow, h_unify]
  simp [inferWrapperAscriptionAtSite, inferExprWithAscription, inferExpr,
    TermEnv.lookup, h_gate]

/-- Packaged wrapper algorithmic ascription bridge at a chosen boundary site. -/
theorem inferWrapperAscriptionAtSite_task_bridge
    (site : WrapperBoundarySite) :
    inferWrapperAscriptionAtSite site
      wrapperTaskVarBoolEnv (.var "t") (.task .int) = none
    ∧
    inferWrapperAscriptionAtSite site
      wrapperTaskVarIntEnv (.var "t") (.task .int) = some (.task .int)
    ∧
    HasTypeWithWrapperAscriptionAtSite site
      wrapperTaskVarIntEnv (.ascribe (.var "t") (.task .int)) (.task .int) := by
  refine ⟨
    inferWrapperAscriptionAtSite_task_rejects site,
    inferWrapperAscriptionAtSite_task_accepts site,
    ?_⟩
  refine HasTypeWithAscription.ascribe
    wrapperTaskVarIntEnv (.var "t") (.task .int) ?_
  refine ⟨.task .int, ?_, ?_⟩
  · exact HasType.var wrapperTaskVarIntEnv "t" (.task .int) (by
      simp [TermEnv.lookup])
  · refine ⟨?_, ?_⟩
    · cases site <;> native_decide
    · refine ⟨UnifyState.empty, ?_⟩
      simpa using (task_unifies_with_self UnifyState.empty 1 .int)

/-- Packaged wrapper algorithmic ascription slice at a chosen boundary site. -/
def WrapperAscriptionAlgorithmicSliceAtSite
    (site : WrapperBoundarySite) : Prop :=
  inferWrapperAscriptionAtSite site
    wrapperTaskVarBoolEnv (.var "t") (.task .int) = none
  ∧
  inferWrapperAscriptionAtSite site
    wrapperTaskVarIntEnv (.var "t") (.task .int) = some (.task .int)
  ∧
  HasTypeWithWrapperAscriptionAtSite site
    wrapperTaskVarIntEnv (.ascribe (.var "t") (.task .int)) (.task .int)

/-- Proof witness for `WrapperAscriptionAlgorithmicSliceAtSite`. -/
theorem wrapperAscriptionAlgorithmicSliceAtSite_proved
    (site : WrapperBoundarySite) :
    WrapperAscriptionAlgorithmicSliceAtSite site := by
  exact inferWrapperAscriptionAtSite_task_bridge site

/-- Declarative rejection witness corresponding to
    `inferWrapperAscriptionAtSite_task_rejects`. -/
theorem hasTypeWithWrapperAscriptionAtSite_task_rejects
    (site : WrapperBoundarySite) :
    ¬ HasTypeWithWrapperAscriptionAtSite site
        wrapperTaskVarBoolEnv (.ascribe (.var "t") (.task .int)) (.task .int) := by
  intro h
  have h_boundary : HasTypeAtWrapperBoundaryAtSite site
      wrapperTaskVarBoolEnv (.var "t") (.task .int) :=
    (hasTypeWithWrapperAscription_ascribe_iff_boundary
      site wrapperTaskVarBoolEnv (.var "t") (.task .int)).1 h
  have h_ascr : HasTypeAtWrapperBoundaryAtSite .ascription
      wrapperTaskVarBoolEnv (.var "t") (.task .int) :=
    (hasTypeAtWrapperBoundaryAtSite_iff_ascription
      site wrapperTaskVarBoolEnv (.var "t") (.task .int)).1 h_boundary
  exact hasType_ascription_task_inner_mismatch_rejected h_ascr

/-- Algorithmic/declarative alignment for the wrapper Task witness at a chosen
    site. -/
theorem wrapperAscriptionAlgorithmicDeclarativeTaskAlignmentAtSite
    (site : WrapperBoundarySite) :
    (inferWrapperAscriptionAtSite site
      wrapperTaskVarBoolEnv (.var "t") (.task .int) = none
      ↔
      ¬ HasTypeWithWrapperAscriptionAtSite site
          wrapperTaskVarBoolEnv (.ascribe (.var "t") (.task .int)) (.task .int))
    ∧
    (inferWrapperAscriptionAtSite site
      wrapperTaskVarIntEnv (.var "t") (.task .int) = some (.task .int)
      ↔
      HasTypeWithWrapperAscriptionAtSite site
        wrapperTaskVarIntEnv (.ascribe (.var "t") (.task .int)) (.task .int)) := by
  refine ⟨?_, ?_⟩
  · constructor
    · intro _h
      exact hasTypeWithWrapperAscriptionAtSite_task_rejects site
    · intro _h
      exact inferWrapperAscriptionAtSite_task_rejects site
  · constructor
    · intro _h
      exact (inferWrapperAscriptionAtSite_task_bridge site).2.2
    · intro _h
      exact inferWrapperAscriptionAtSite_task_accepts site

/-- Minimal algorithmic checker for grouped/tagged ascriptions at a chosen
    boundary site. This reuses `inferExprWithAscription`, the grouped/tagged
    boundary predicate, and the explicit unifier-success gate used by
    `GroupedTaggedAscriptionAllowsAtSite`. -/
def groupedTaggedAscriptionAllowsBoolAtSite
    (site : GroupedTaggedBoundarySite)
    (expected actual : Ty) : Bool :=
  if groupedTaggedBoundaryAllowsAtSite site expected actual
  then
    match unify UnifyState.empty 2 expected actual with
    | .ok _ => true
    | .err _ => false
  else false

/-- Minimal algorithmic checker for grouped/tagged ascriptions at a chosen
    boundary site. -/
def inferGroupedTaggedAscriptionAtSite
    (site : GroupedTaggedBoundarySite)
    (env : TermEnv) (e : CoreExpr) (expected : Ty) : Option Ty :=
  inferExprWithAscription (groupedTaggedAscriptionAllowsBoolAtSite site) env
    (.ascribe e expected)

/-- Boolean grouped/tagged ascription gate agrees with the declarative
    grouped/tagged ascription relation. -/
theorem groupedTaggedAscriptionAllowsBoolAtSite_true_iff
    (site : GroupedTaggedBoundarySite)
    (expected actual : Ty) :
    groupedTaggedAscriptionAllowsBoolAtSite site expected actual = true
      ↔ GroupedTaggedAscriptionAllowsAtSite site expected actual := by
  constructor
  · intro h_gate
    unfold groupedTaggedAscriptionAllowsBoolAtSite at h_gate
    by_cases h_allow : groupedTaggedBoundaryAllowsAtSite site expected actual = true
    · have h_unify :
          ∃ st', unify UnifyState.empty 2 expected actual = .ok st' := by
        cases h_u : unify UnifyState.empty 2 expected actual with
        | ok st' =>
            exact ⟨st', rfl⟩
        | err _ =>
            simp [h_allow, h_u] at h_gate
      exact ⟨h_allow, h_unify⟩
    · simp [h_allow] at h_gate
  · intro h_rel
    rcases h_rel with ⟨h_allow, h_unify⟩
    rcases h_unify with ⟨st', h_unify⟩
    unfold groupedTaggedAscriptionAllowsBoolAtSite
    simp [h_allow, h_unify]

/-- Successful grouped/tagged ascription inference always returns the
    annotated type. -/
theorem inferGroupedTaggedAscriptionAtSite_some_implies_expected
    (site : GroupedTaggedBoundarySite)
    (env : TermEnv) (e : CoreExpr) (expected ty : Ty)
    (h_infer : inferGroupedTaggedAscriptionAtSite site env e expected = some ty) :
    ty = expected := by
  unfold inferGroupedTaggedAscriptionAtSite inferExprWithAscription at h_infer
  cases h_expr : inferExpr env e with
  | none =>
      simp [h_expr] at h_infer
  | some actual =>
      by_cases h_gate :
          groupedTaggedAscriptionAllowsBoolAtSite site expected actual = true
      · simp [h_expr, h_gate] at h_infer
        cases h_infer
        rfl
      · simp [h_expr, h_gate] at h_infer

/-- Soundness of `inferGroupedTaggedAscriptionAtSite` with respect to
    `HasTypeWithGroupedTaggedAscriptionAtSite`. -/
theorem inferGroupedTaggedAscriptionAtSite_sound
    (site : GroupedTaggedBoundarySite)
    (env : TermEnv) (e : CoreExpr) (expected : Ty)
    (h_infer : inferGroupedTaggedAscriptionAtSite site env e expected = some expected) :
    HasTypeWithGroupedTaggedAscriptionAtSite site env
      (.ascribe e expected) expected := by
  unfold inferGroupedTaggedAscriptionAtSite inferExprWithAscription at h_infer
  cases h_expr : inferExpr env e with
  | none =>
      simp [h_expr] at h_infer
  | some actual =>
      have h_gate_true :
          groupedTaggedAscriptionAllowsBoolAtSite site expected actual = true := by
        by_cases h_gate :
            groupedTaggedAscriptionAllowsBoolAtSite site expected actual = true
        · exact h_gate
        · simp [h_expr, h_gate] at h_infer
      have h_actual : HasType env e actual :=
        inferExpr_sound env e actual h_expr
      have h_rel : GroupedTaggedAscriptionAllowsAtSite site expected actual :=
        (groupedTaggedAscriptionAllowsBoolAtSite_true_iff site expected actual).1 h_gate_true
      exact HasTypeWithAscription.ascribe env e expected ⟨actual, h_actual, h_rel⟩

/-- Grouped/tagged ascription inference is equivalent to modeled grouped/tagged
    boundary assignability on explicit `ascribe` nodes. -/
theorem inferGroupedTaggedAscriptionAtSite_iff_boundary
    (site : GroupedTaggedBoundarySite)
    (env : TermEnv) (e : CoreExpr) (expected : Ty) :
    inferGroupedTaggedAscriptionAtSite site env e expected = some expected
      ↔ HasTypeAtGroupedTaggedBoundaryAtSite site env e expected := by
  have h_core :
      inferGroupedTaggedAscriptionAtSite site env e expected = some expected
        ↔
        HasTypeAtCoreBoundary
          (fun exp act =>
            groupedTaggedAscriptionAllowsBoolAtSite site exp act = true)
          env e expected := by
    simpa [inferGroupedTaggedAscriptionAtSite]
      using inferExprWithAscription_ascribe_iff_boundary
        (groupedTaggedAscriptionAllowsBoolAtSite site) env e expected
  have h_rel :
      HasTypeAtCoreBoundary
          (fun exp act =>
            groupedTaggedAscriptionAllowsBoolAtSite site exp act = true)
          env e expected
        ↔
        HasTypeAtGroupedTaggedBoundaryAtSite site env e expected := by
    simpa [HasTypeAtGroupedTaggedBoundaryAtSite,
      GroupedTaggedAscriptionAllowsAtSite, HasTypeAtBoundary]
      using (hasTypeAtBoundary_congr
        (fun exp act =>
          groupedTaggedAscriptionAllowsBoolAtSite site exp act = true)
        (GroupedTaggedAscriptionAllowsAtSite site)
        env e expected
        (by
          intro exp act
          exact groupedTaggedAscriptionAllowsBoolAtSite_true_iff site exp act))
  exact h_core.trans h_rel

/-- Grouped/tagged ascription inference is equivalent to grouped/tagged
    ascription typing at explicit `ascribe` nodes. -/
theorem inferGroupedTaggedAscriptionAtSite_iff
    (site : GroupedTaggedBoundarySite)
    (env : TermEnv) (e : CoreExpr) (expected : Ty) :
    inferGroupedTaggedAscriptionAtSite site env e expected = some expected
      ↔ HasTypeWithGroupedTaggedAscriptionAtSite site env
          (.ascribe e expected) expected := by
  exact (inferGroupedTaggedAscriptionAtSite_iff_boundary
    site env e expected).trans
    (hasTypeWithGroupedTaggedAscription_ascribe_iff_boundary
      site env e expected).symm

/-- Grouped/tagged algorithmic witness: grouped inner mismatch at equal keys
    rejects at all boundary-sensitive sites. -/
theorem inferGroupedTaggedAscriptionAtSite_grouped_rejects
    (site : GroupedTaggedBoundarySite) :
    inferGroupedTaggedAscriptionAtSite site
      groupedVarBoolEnv (.var "g") (.groupedFrame .int ["a"]) = none := by
  have h_allow :
      groupedTaggedBoundaryAllowsAtSite site
        (.groupedFrame .int ["a"])
        (.groupedFrame .bool ["a"]) = true := by
    cases site <;> native_decide
  have h_unify :
      unify UnifyState.empty 2
        (.groupedFrame .int ["a"])
        (.groupedFrame .bool ["a"]) = .err "type mismatch" := by
    exact groupedFrame_inner_mismatch UnifyState.empty
  have h_gate :
      groupedTaggedAscriptionAllowsBoolAtSite site
        (.groupedFrame .int ["a"])
        (.groupedFrame .bool ["a"]) = false := by
    unfold groupedTaggedAscriptionAllowsBoolAtSite
    simp [h_allow, h_unify]
  simp [inferGroupedTaggedAscriptionAtSite, inferExprWithAscription, inferExpr,
    TermEnv.lookup, h_gate]

/-- Grouped/tagged algorithmic witness: grouped identity ascription accepts at
    all boundary-sensitive sites. -/
theorem inferGroupedTaggedAscriptionAtSite_grouped_accepts
    (site : GroupedTaggedBoundarySite) :
    inferGroupedTaggedAscriptionAtSite site
      groupedVarIntEnv (.var "g") (.groupedFrame .int ["a"])
      = some (.groupedFrame .int ["a"]) := by
  have h_allow :
      groupedTaggedBoundaryAllowsAtSite site
        (.groupedFrame .int ["a"])
        (.groupedFrame .int ["a"]) = true := by
    cases site <;> native_decide
  have h_unify :
      unify UnifyState.empty 2
        (.groupedFrame .int ["a"])
        (.groupedFrame .int ["a"]) = .ok UnifyState.empty := by
    simpa using (groupedFrame_unifies_with_self UnifyState.empty 1 .int ["a"])
  have h_gate :
      groupedTaggedAscriptionAllowsBoolAtSite site
        (.groupedFrame .int ["a"])
        (.groupedFrame .int ["a"]) = true := by
    unfold groupedTaggedAscriptionAllowsBoolAtSite
    simp [h_allow, h_unify]
  simp [inferGroupedTaggedAscriptionAtSite, inferExprWithAscription, inferExpr,
    TermEnv.lookup, h_gate]

/-- Packaged grouped/tagged algorithmic ascription bridge at a chosen boundary
    site. -/
theorem inferGroupedTaggedAscriptionAtSite_grouped_bridge
    (site : GroupedTaggedBoundarySite) :
    inferGroupedTaggedAscriptionAtSite site
      groupedVarBoolEnv (.var "g") (.groupedFrame .int ["a"]) = none
    ∧
    inferGroupedTaggedAscriptionAtSite site
      groupedVarIntEnv (.var "g") (.groupedFrame .int ["a"])
      = some (.groupedFrame .int ["a"])
    ∧
    HasTypeWithGroupedTaggedAscriptionAtSite site
      groupedVarIntEnv
      (.ascribe (.var "g") (.groupedFrame .int ["a"]))
      (.groupedFrame .int ["a"]) := by
  refine ⟨
    inferGroupedTaggedAscriptionAtSite_grouped_rejects site,
    inferGroupedTaggedAscriptionAtSite_grouped_accepts site,
    ?_⟩
  refine HasTypeWithAscription.ascribe
    groupedVarIntEnv (.var "g") (.groupedFrame .int ["a"]) ?_
  refine ⟨.groupedFrame .int ["a"], ?_, ?_⟩
  · exact HasType.var groupedVarIntEnv "g" (.groupedFrame .int ["a"]) (by
      simp [TermEnv.lookup])
  · refine ⟨?_, ?_⟩
    · cases site <;> native_decide
    · refine ⟨UnifyState.empty, ?_⟩
      simpa using (groupedFrame_unifies_with_self UnifyState.empty 1 .int ["a"])

/-- Packaged grouped/tagged algorithmic ascription slice at a chosen boundary
    site. -/
def GroupedTaggedAscriptionAlgorithmicSliceAtSite
    (site : GroupedTaggedBoundarySite) : Prop :=
  inferGroupedTaggedAscriptionAtSite site
    groupedVarBoolEnv (.var "g") (.groupedFrame .int ["a"]) = none
  ∧
  inferGroupedTaggedAscriptionAtSite site
    groupedVarIntEnv (.var "g") (.groupedFrame .int ["a"])
    = some (.groupedFrame .int ["a"])
  ∧
  HasTypeWithGroupedTaggedAscriptionAtSite site
    groupedVarIntEnv
    (.ascribe (.var "g") (.groupedFrame .int ["a"]))
    (.groupedFrame .int ["a"])

/-- Proof witness for `GroupedTaggedAscriptionAlgorithmicSliceAtSite`. -/
theorem groupedTaggedAscriptionAlgorithmicSliceAtSite_proved
    (site : GroupedTaggedBoundarySite) :
    GroupedTaggedAscriptionAlgorithmicSliceAtSite site := by
  exact inferGroupedTaggedAscriptionAtSite_grouped_bridge site

/-- Declarative rejection witness corresponding to
    `inferGroupedTaggedAscriptionAtSite_grouped_rejects`. -/
theorem hasTypeWithGroupedTaggedAscriptionAtSite_grouped_rejects
    (site : GroupedTaggedBoundarySite) :
    ¬ HasTypeWithGroupedTaggedAscriptionAtSite site
        groupedVarBoolEnv
        (.ascribe (.var "g") (.groupedFrame .int ["a"]))
        (.groupedFrame .int ["a"]) := by
  intro h
  have h_boundary : HasTypeAtGroupedTaggedBoundaryAtSite site
      groupedVarBoolEnv (.var "g") (.groupedFrame .int ["a"]) :=
    (hasTypeWithGroupedTaggedAscription_ascribe_iff_boundary
      site groupedVarBoolEnv (.var "g") (.groupedFrame .int ["a"])).1 h
  have h_ascr : HasTypeAtGroupedTaggedBoundaryAtSite .ascription
      groupedVarBoolEnv (.var "g") (.groupedFrame .int ["a"]) :=
    (hasTypeAtGroupedTaggedBoundaryAtSite_iff_ascription
      site groupedVarBoolEnv (.var "g") (.groupedFrame .int ["a"])).1 h_boundary
  exact hasType_ascription_grouped_inner_mismatch_rejected h_ascr

/-- Algorithmic/declarative alignment for the grouped witness at a chosen
    site. -/
theorem groupedAscriptionAlgorithmicDeclarativeAlignmentAtSite
    (site : GroupedTaggedBoundarySite) :
    (inferGroupedTaggedAscriptionAtSite site
      groupedVarBoolEnv (.var "g") (.groupedFrame .int ["a"]) = none
      ↔
      ¬ HasTypeWithGroupedTaggedAscriptionAtSite site
          groupedVarBoolEnv
          (.ascribe (.var "g") (.groupedFrame .int ["a"]))
          (.groupedFrame .int ["a"]))
    ∧
    (inferGroupedTaggedAscriptionAtSite site
      groupedVarIntEnv (.var "g") (.groupedFrame .int ["a"])
      = some (.groupedFrame .int ["a"])
      ↔
      HasTypeWithGroupedTaggedAscriptionAtSite site
        groupedVarIntEnv
        (.ascribe (.var "g") (.groupedFrame .int ["a"]))
        (.groupedFrame .int ["a"])) := by
  refine ⟨?_, ?_⟩
  · constructor
    · intro _h
      exact hasTypeWithGroupedTaggedAscriptionAtSite_grouped_rejects site
    · intro _h
      exact inferGroupedTaggedAscriptionAtSite_grouped_rejects site
  · constructor
    · intro _h
      exact (inferGroupedTaggedAscriptionAtSite_grouped_bridge site).2.2
    · intro _h
      exact inferGroupedTaggedAscriptionAtSite_grouped_accepts site

/-- Expression-level algorithmic inference with explicit Dynamic ascriptions:
    delegates to `inferExpr` on base expressions and to
    `inferDynamicAscriptionAtSite` on explicit ascription nodes. -/
def inferDynamicExprWithAscriptionAtSite
    (site : DynamicBoundarySite)
    (env : TermEnv) : CoreExprWithAscription → Option Ty
  | .base e => inferExpr env e
  | .ascribe e expected => inferDynamicAscriptionAtSite site env e expected

/-- Expression-level algorithmic inference with explicit wrapper ascriptions:
    delegates to `inferExpr` on base expressions and to
    `inferWrapperAscriptionAtSite` on explicit ascription nodes. -/
def inferWrapperExprWithAscriptionAtSite
    (site : WrapperBoundarySite)
    (env : TermEnv) : CoreExprWithAscription → Option Ty
  | .base e => inferExpr env e
  | .ascribe e expected => inferWrapperAscriptionAtSite site env e expected

/-- Expression-level algorithmic inference with explicit grouped/tagged
    ascriptions: delegates to `inferExpr` on base expressions and to
    `inferGroupedTaggedAscriptionAtSite` on explicit ascription nodes. -/
def inferGroupedTaggedExprWithAscriptionAtSite
    (site : GroupedTaggedBoundarySite)
    (env : TermEnv) : CoreExprWithAscription → Option Ty
  | .base e => inferExpr env e
  | .ascribe e expected => inferGroupedTaggedAscriptionAtSite site env e expected

/-- Dynamic expression-level ascription inference is routed through Typing core
    `inferExprWithAscription` with the Dynamic boundary predicate. -/
theorem inferDynamicExprWithAscriptionAtSite_eq_core
    (site : DynamicBoundarySite)
    (env : TermEnv) (e : CoreExprWithAscription) :
    inferDynamicExprWithAscriptionAtSite site env e
      = inferExprWithAscription (dynamicBoundaryAllowsAtSite site) env e := by
  cases e with
  | base _ => rfl
  | ascribe _ _ =>
      simp [inferDynamicExprWithAscriptionAtSite, inferDynamicAscriptionAtSite]

/-- Wrapper expression-level ascription inference is routed through Typing core
    `inferExprWithAscription` with the wrapper boundary+unifier gate. -/
theorem inferWrapperExprWithAscriptionAtSite_eq_core
    (site : WrapperBoundarySite)
    (env : TermEnv) (e : CoreExprWithAscription) :
    inferWrapperExprWithAscriptionAtSite site env e
      = inferExprWithAscription (wrapperAscriptionAllowsBoolAtSite site) env e := by
  cases e with
  | base _ => rfl
  | ascribe _ _ =>
      simp [inferWrapperExprWithAscriptionAtSite, inferWrapperAscriptionAtSite]

/-- Grouped/tagged expression-level ascription inference is routed through
    Typing core `inferExprWithAscription` with the grouped/tagged
    boundary+unifier gate. -/
theorem inferGroupedTaggedExprWithAscriptionAtSite_eq_core
    (site : GroupedTaggedBoundarySite)
    (env : TermEnv) (e : CoreExprWithAscription) :
    inferGroupedTaggedExprWithAscriptionAtSite site env e
      = inferExprWithAscription (groupedTaggedAscriptionAllowsBoolAtSite site) env e := by
  cases e with
  | base _ => rfl
  | ascribe _ _ =>
      simp [inferGroupedTaggedExprWithAscriptionAtSite,
        inferGroupedTaggedAscriptionAtSite]

/-- On base nodes, the Dynamic ascription adapter is definitionally equal to
    plain `inferExpr`. -/
theorem inferDynamicExprWithAscriptionAtSite_base_eq
    (site : DynamicBoundarySite) (env : TermEnv) (e : CoreExpr) :
    inferDynamicExprWithAscriptionAtSite site env (.base e) = inferExpr env e := by
  rfl

/-- On base nodes, the wrapper ascription adapter is definitionally equal to
    plain `inferExpr`. -/
theorem inferWrapperExprWithAscriptionAtSite_base_eq
    (site : WrapperBoundarySite) (env : TermEnv) (e : CoreExpr) :
    inferWrapperExprWithAscriptionAtSite site env (.base e) = inferExpr env e := by
  rfl

/-- On base nodes, the grouped/tagged ascription adapter is definitionally
    equal to plain `inferExpr`. -/
theorem inferGroupedTaggedExprWithAscriptionAtSite_base_eq
    (site : GroupedTaggedBoundarySite) (env : TermEnv) (e : CoreExpr) :
    inferGroupedTaggedExprWithAscriptionAtSite site env (.base e) = inferExpr env e := by
  rfl

/-- On base nodes, Dynamic expression-level typing coincides with `HasType`. -/
theorem hasTypeWithDynamicAscriptionAtSite_base_iff
    (site : DynamicBoundarySite)
    (env : TermEnv) (e : CoreExpr) (ty : Ty) :
    HasTypeWithDynamicAscriptionAtSite site env (.base e) ty
      ↔ HasType env e ty := by
  simpa [HasTypeWithDynamicAscriptionAtSite]
    using hasTypeWithAscription_base_iff
      (DynamicAscriptionAllowsAtSite site) env e ty

/-- On base nodes, wrapper expression-level typing coincides with `HasType`. -/
theorem hasTypeWithWrapperAscriptionAtSite_base_iff
    (site : WrapperBoundarySite)
    (env : TermEnv) (e : CoreExpr) (ty : Ty) :
    HasTypeWithWrapperAscriptionAtSite site env (.base e) ty
      ↔ HasType env e ty := by
  simpa [HasTypeWithWrapperAscriptionAtSite]
    using hasTypeWithAscription_base_iff
      (WrapperAscriptionAllowsAtSite site) env e ty

/-- On base nodes, grouped/tagged expression-level typing coincides with
    `HasType`. -/
theorem hasTypeWithGroupedTaggedAscriptionAtSite_base_iff
    (site : GroupedTaggedBoundarySite)
    (env : TermEnv) (e : CoreExpr) (ty : Ty) :
    HasTypeWithGroupedTaggedAscriptionAtSite site env (.base e) ty
      ↔ HasType env e ty := by
  simpa [HasTypeWithGroupedTaggedAscriptionAtSite]
    using hasTypeWithAscription_base_iff
      (GroupedTaggedAscriptionAllowsAtSite site) env e ty

/-- Packaged routing slice: expression-level ascription inference adapters are
    definitionally routed through Typing core `inferExprWithAscription`. -/
def AscriptionCoreInferRoutingSliceAtSites
    (dynamicSite : DynamicBoundarySite)
    (wrapperSite : WrapperBoundarySite)
    (groupedTaggedSite : GroupedTaggedBoundarySite) : Prop :=
  (∀ env e,
      inferDynamicExprWithAscriptionAtSite dynamicSite env e
        = inferExprWithAscription (dynamicBoundaryAllowsAtSite dynamicSite) env e)
  ∧
  (∀ env e,
      inferWrapperExprWithAscriptionAtSite wrapperSite env e
        = inferExprWithAscription (wrapperAscriptionAllowsBoolAtSite wrapperSite) env e)
  ∧
  (∀ env e,
      inferGroupedTaggedExprWithAscriptionAtSite groupedTaggedSite env e
        = inferExprWithAscription
            (groupedTaggedAscriptionAllowsBoolAtSite groupedTaggedSite) env e)

/-- Ascription-specialized alias for `AscriptionCoreInferRoutingSliceAtSites`. -/
abbrev AscriptionCoreInferRoutingSlice : Prop :=
  AscriptionCoreInferRoutingSliceAtSites .ascription .ascription .ascription

/-- Proof witness for `AscriptionCoreInferRoutingSliceAtSites`. -/
theorem ascriptionCoreInferRoutingSliceAtSites_proved
    (dynamicSite : DynamicBoundarySite)
    (wrapperSite : WrapperBoundarySite)
    (groupedTaggedSite : GroupedTaggedBoundarySite) :
    AscriptionCoreInferRoutingSliceAtSites
      dynamicSite wrapperSite groupedTaggedSite := by
  refine ⟨
    inferDynamicExprWithAscriptionAtSite_eq_core dynamicSite,
    inferWrapperExprWithAscriptionAtSite_eq_core wrapperSite,
    inferGroupedTaggedExprWithAscriptionAtSite_eq_core groupedTaggedSite
  ⟩

/-- Proof witness for ascription-specialized
    `AscriptionCoreInferRoutingSlice`. -/
theorem ascriptionCoreInferRoutingSlice_proved :
    AscriptionCoreInferRoutingSlice := by
  simpa [AscriptionCoreInferRoutingSlice]
    using ascriptionCoreInferRoutingSliceAtSites_proved
      .ascription .ascription .ascription

/-- Packaged `.base`-embedding slice: expression-level ascription adapters
    coincide with core `inferExpr`/`HasType` behavior on base expressions. -/
def AscriptionBaseEmbeddingSliceAtSites
    (dynamicSite : DynamicBoundarySite)
    (wrapperSite : WrapperBoundarySite)
    (groupedTaggedSite : GroupedTaggedBoundarySite) : Prop :=
  (∀ env e,
      inferDynamicExprWithAscriptionAtSite dynamicSite env (.base e)
        = inferExpr env e)
  ∧
  (∀ env e,
      inferWrapperExprWithAscriptionAtSite wrapperSite env (.base e)
        = inferExpr env e)
  ∧
  (∀ env e,
      inferGroupedTaggedExprWithAscriptionAtSite groupedTaggedSite env (.base e)
        = inferExpr env e)
  ∧
  (∀ env e ty,
      HasTypeWithDynamicAscriptionAtSite dynamicSite env (.base e) ty
        ↔ HasType env e ty)
  ∧
  (∀ env e ty,
      HasTypeWithWrapperAscriptionAtSite wrapperSite env (.base e) ty
        ↔ HasType env e ty)
  ∧
  (∀ env e ty,
      HasTypeWithGroupedTaggedAscriptionAtSite groupedTaggedSite env (.base e) ty
        ↔ HasType env e ty)

/-- Ascription-specialized alias for `AscriptionBaseEmbeddingSliceAtSites`. -/
abbrev AscriptionBaseEmbeddingSlice : Prop :=
  AscriptionBaseEmbeddingSliceAtSites .ascription .ascription .ascription

/-- Proof witness for `AscriptionBaseEmbeddingSliceAtSites`. -/
theorem ascriptionBaseEmbeddingSliceAtSites_proved
    (dynamicSite : DynamicBoundarySite)
    (wrapperSite : WrapperBoundarySite)
    (groupedTaggedSite : GroupedTaggedBoundarySite) :
    AscriptionBaseEmbeddingSliceAtSites
      dynamicSite wrapperSite groupedTaggedSite := by
  refine ⟨
    inferDynamicExprWithAscriptionAtSite_base_eq dynamicSite,
    inferWrapperExprWithAscriptionAtSite_base_eq wrapperSite,
    inferGroupedTaggedExprWithAscriptionAtSite_base_eq groupedTaggedSite,
    hasTypeWithDynamicAscriptionAtSite_base_iff dynamicSite,
    hasTypeWithWrapperAscriptionAtSite_base_iff wrapperSite,
    hasTypeWithGroupedTaggedAscriptionAtSite_base_iff groupedTaggedSite
  ⟩

/-- Proof witness for ascription-specialized
    `AscriptionBaseEmbeddingSlice`. -/
theorem ascriptionBaseEmbeddingSlice_proved :
    AscriptionBaseEmbeddingSlice := by
  simpa [AscriptionBaseEmbeddingSlice]
    using ascriptionBaseEmbeddingSliceAtSites_proved
      .ascription .ascription .ascription

/-- Successful Dynamic ascription inference always returns the annotated type. -/
theorem inferDynamicAscriptionAtSite_some_implies_expected
    (site : DynamicBoundarySite)
    (env : TermEnv) (e : CoreExpr) (expected ty : Ty)
    (h_infer : inferDynamicAscriptionAtSite site env e expected = some ty) :
    ty = expected := by
  unfold inferDynamicAscriptionAtSite inferExprWithAscription at h_infer
  cases h_expr : inferExpr env e with
  | none =>
      simp [h_expr] at h_infer
  | some actual =>
      cases h_allow : dynamicBoundaryAllowsAtSite site expected actual with
      | false =>
          simp [h_expr, h_allow] at h_infer
      | true =>
          simp [h_expr, h_allow] at h_infer
          cases h_infer
          rfl

/-- Soundness of expression-level Dynamic ascription inference with respect to
    `HasTypeWithDynamicAscriptionAtSite`. -/
theorem inferDynamicExprWithAscriptionAtSite_sound
    (site : DynamicBoundarySite)
    (env : TermEnv) (e : CoreExprWithAscription) (ty : Ty)
    (h_infer : inferDynamicExprWithAscriptionAtSite site env e = some ty) :
    HasTypeWithDynamicAscriptionAtSite site env e ty := by
  cases e with
  | base baseExpr =>
      simp [inferDynamicExprWithAscriptionAtSite] at h_infer
      exact HasTypeWithAscription.base env baseExpr ty
        (inferExpr_sound env baseExpr ty h_infer)
  | ascribe baseExpr expected =>
      simp [inferDynamicExprWithAscriptionAtSite] at h_infer
      have h_ty : ty = expected :=
        inferDynamicAscriptionAtSite_some_implies_expected
          site env baseExpr expected ty h_infer
      have h_infer_ty :
          inferDynamicAscriptionAtSite site env baseExpr ty = some ty := by
        cases h_ty
        simpa using h_infer
      cases h_ty
      exact inferDynamicAscriptionAtSite_sound
        site env baseExpr ty h_infer_ty

/-- Completeness of expression-level Dynamic ascription inference with respect
    to `HasTypeWithDynamicAscriptionAtSite`. -/
theorem inferDynamicExprWithAscriptionAtSite_complete
    (site : DynamicBoundarySite)
    (env : TermEnv) (e : CoreExprWithAscription) (ty : Ty)
    (h_ty : HasTypeWithDynamicAscriptionAtSite site env e ty) :
    inferDynamicExprWithAscriptionAtSite site env e = some ty := by
  cases h_ty with
  | base _ _ h_base =>
      simpa [inferDynamicExprWithAscriptionAtSite]
        using inferExpr_complete _ _ _ h_base
  | ascribe _ _ h_boundary =>
      rcases h_boundary with ⟨actual, h_actual, h_allow⟩
      unfold DynamicAscriptionAllowsAtSite allowsByBool at h_allow
      unfold inferDynamicExprWithAscriptionAtSite inferDynamicAscriptionAtSite
        inferExprWithAscription
      simp [inferExpr_complete _ _ _ h_actual, h_allow]

/-- Dynamic expression-level ascription inference is equivalent to
    `HasTypeWithDynamicAscriptionAtSite`. -/
theorem inferDynamicExprWithAscriptionAtSite_iff
    (site : DynamicBoundarySite)
    (env : TermEnv) (e : CoreExprWithAscription) (ty : Ty) :
    inferDynamicExprWithAscriptionAtSite site env e = some ty
      ↔ HasTypeWithDynamicAscriptionAtSite site env e ty := by
  constructor
  · intro h
    exact inferDynamicExprWithAscriptionAtSite_sound site env e ty h
  · intro h
    exact inferDynamicExprWithAscriptionAtSite_complete site env e ty h

/-- Dynamic ascription inference is equivalent to Dynamic ascription typing at
    explicit `ascribe` nodes. -/
theorem inferDynamicAscriptionAtSite_iff
    (site : DynamicBoundarySite)
    (env : TermEnv) (e : CoreExpr) (expected : Ty) :
    inferDynamicAscriptionAtSite site env e expected = some expected
      ↔ HasTypeWithDynamicAscriptionAtSite site env
          (.ascribe e expected) expected := by
  simpa [inferDynamicExprWithAscriptionAtSite]
    using (inferDynamicExprWithAscriptionAtSite_iff
      site env (.ascribe e expected) expected)

/-- Soundness of expression-level wrapper ascription inference with respect to
    `HasTypeWithWrapperAscriptionAtSite`. -/
theorem inferWrapperExprWithAscriptionAtSite_sound
    (site : WrapperBoundarySite)
    (env : TermEnv) (e : CoreExprWithAscription) (ty : Ty)
    (h_infer : inferWrapperExprWithAscriptionAtSite site env e = some ty) :
    HasTypeWithWrapperAscriptionAtSite site env e ty := by
  cases e with
  | base baseExpr =>
      simp [inferWrapperExprWithAscriptionAtSite] at h_infer
      exact HasTypeWithAscription.base env baseExpr ty
        (inferExpr_sound env baseExpr ty h_infer)
  | ascribe baseExpr expected =>
      simp [inferWrapperExprWithAscriptionAtSite] at h_infer
      have h_ty : ty = expected :=
        inferWrapperAscriptionAtSite_some_implies_expected
          site env baseExpr expected ty h_infer
      have h_infer_ty :
          inferWrapperAscriptionAtSite site env baseExpr ty = some ty := by
        cases h_ty
        simpa using h_infer
      cases h_ty
      exact inferWrapperAscriptionAtSite_sound
        site env baseExpr ty h_infer_ty

/-- Soundness of expression-level grouped/tagged ascription inference with
    respect to `HasTypeWithGroupedTaggedAscriptionAtSite`. -/
theorem inferGroupedTaggedExprWithAscriptionAtSite_sound
    (site : GroupedTaggedBoundarySite)
    (env : TermEnv) (e : CoreExprWithAscription) (ty : Ty)
    (h_infer : inferGroupedTaggedExprWithAscriptionAtSite site env e = some ty) :
    HasTypeWithGroupedTaggedAscriptionAtSite site env e ty := by
  cases e with
  | base baseExpr =>
      simp [inferGroupedTaggedExprWithAscriptionAtSite] at h_infer
      exact HasTypeWithAscription.base env baseExpr ty
        (inferExpr_sound env baseExpr ty h_infer)
  | ascribe baseExpr expected =>
      simp [inferGroupedTaggedExprWithAscriptionAtSite] at h_infer
      have h_ty : ty = expected :=
        inferGroupedTaggedAscriptionAtSite_some_implies_expected
          site env baseExpr expected ty h_infer
      have h_infer_ty :
          inferGroupedTaggedAscriptionAtSite site env baseExpr ty = some ty := by
        cases h_ty
        simpa using h_infer
      cases h_ty
      exact inferGroupedTaggedAscriptionAtSite_sound
        site env baseExpr ty h_infer_ty

/-- Completeness of expression-level wrapper ascription inference with respect
    to `HasTypeWithWrapperAscriptionAtSite`. -/
theorem inferWrapperExprWithAscriptionAtSite_complete
    (site : WrapperBoundarySite)
    (env : TermEnv) (e : CoreExprWithAscription) (ty : Ty)
    (h_ty : HasTypeWithWrapperAscriptionAtSite site env e ty) :
    inferWrapperExprWithAscriptionAtSite site env e = some ty := by
  cases h_ty with
  | base _ _ h_base =>
      simpa [inferWrapperExprWithAscriptionAtSite]
        using inferExpr_complete _ _ _ h_base
  | ascribe _ _ h_boundary =>
      rcases h_boundary with ⟨actual, h_actual, h_gate⟩
      rcases h_gate with ⟨h_allow, h_unify⟩
      rcases h_unify with ⟨_, h_unify⟩
      have h_gate_true :
          wrapperAscriptionAllowsBoolAtSite site ty actual = true := by
        unfold wrapperAscriptionAllowsBoolAtSite
        simp [h_allow, h_unify]
      unfold inferWrapperExprWithAscriptionAtSite inferWrapperAscriptionAtSite
        inferExprWithAscription
      simp [inferExpr_complete _ _ _ h_actual, h_gate_true]

/-- Completeness of expression-level grouped/tagged ascription inference with
    respect to `HasTypeWithGroupedTaggedAscriptionAtSite`. -/
theorem inferGroupedTaggedExprWithAscriptionAtSite_complete
    (site : GroupedTaggedBoundarySite)
    (env : TermEnv) (e : CoreExprWithAscription) (ty : Ty)
    (h_ty : HasTypeWithGroupedTaggedAscriptionAtSite site env e ty) :
    inferGroupedTaggedExprWithAscriptionAtSite site env e = some ty := by
  cases h_ty with
  | base _ _ h_base =>
      simpa [inferGroupedTaggedExprWithAscriptionAtSite]
        using inferExpr_complete _ _ _ h_base
  | ascribe _ _ h_boundary =>
      rcases h_boundary with ⟨actual, h_actual, h_gate⟩
      rcases h_gate with ⟨h_allow, h_unify⟩
      rcases h_unify with ⟨_, h_unify⟩
      have h_gate_true :
          groupedTaggedAscriptionAllowsBoolAtSite site ty actual = true := by
        unfold groupedTaggedAscriptionAllowsBoolAtSite
        simp [h_allow, h_unify]
      unfold inferGroupedTaggedExprWithAscriptionAtSite
        inferGroupedTaggedAscriptionAtSite inferExprWithAscription
      simp [inferExpr_complete _ _ _ h_actual, h_gate_true]

/-- Wrapper expression-level ascription inference is equivalent to
    `HasTypeWithWrapperAscriptionAtSite`. -/
theorem inferWrapperExprWithAscriptionAtSite_iff
    (site : WrapperBoundarySite)
    (env : TermEnv) (e : CoreExprWithAscription) (ty : Ty) :
    inferWrapperExprWithAscriptionAtSite site env e = some ty
      ↔ HasTypeWithWrapperAscriptionAtSite site env e ty := by
  constructor
  · intro h
    exact inferWrapperExprWithAscriptionAtSite_sound site env e ty h
  · intro h
    exact inferWrapperExprWithAscriptionAtSite_complete site env e ty h

/-- Grouped/tagged expression-level ascription inference is equivalent to
    `HasTypeWithGroupedTaggedAscriptionAtSite`. -/
theorem inferGroupedTaggedExprWithAscriptionAtSite_iff
    (site : GroupedTaggedBoundarySite)
    (env : TermEnv) (e : CoreExprWithAscription) (ty : Ty) :
    inferGroupedTaggedExprWithAscriptionAtSite site env e = some ty
      ↔ HasTypeWithGroupedTaggedAscriptionAtSite site env e ty := by
  constructor
  · intro h
    exact inferGroupedTaggedExprWithAscriptionAtSite_sound site env e ty h
  · intro h
    exact inferGroupedTaggedExprWithAscriptionAtSite_complete site env e ty h

/-- Packaged expression-level `inferExpr` equivalence slice (`infer` iff
    declarative typing) across Dynamic/wrapper/grouped ascription adapters. -/
def AscriptionInferExprIffSliceAtSites
    (dynamicSite : DynamicBoundarySite)
    (wrapperSite : WrapperBoundarySite)
    (groupedTaggedSite : GroupedTaggedBoundarySite) : Prop :=
  (∀ env e ty,
      inferDynamicExprWithAscriptionAtSite dynamicSite env e = some ty
        ↔ HasTypeWithDynamicAscriptionAtSite dynamicSite env e ty)
  ∧
  (∀ env e ty,
      inferWrapperExprWithAscriptionAtSite wrapperSite env e = some ty
        ↔ HasTypeWithWrapperAscriptionAtSite wrapperSite env e ty)
  ∧
  (∀ env e ty,
      inferGroupedTaggedExprWithAscriptionAtSite groupedTaggedSite env e = some ty
        ↔ HasTypeWithGroupedTaggedAscriptionAtSite groupedTaggedSite env e ty)

/-- Ascription-specialized alias for `AscriptionInferExprIffSliceAtSites`. -/
abbrev AscriptionInferExprIffSlice : Prop :=
  AscriptionInferExprIffSliceAtSites .ascription .ascription .ascription

/-- Proof witness for `AscriptionInferExprIffSliceAtSites`. -/
theorem ascriptionInferExprIffSliceAtSites_proved
    (dynamicSite : DynamicBoundarySite)
    (wrapperSite : WrapperBoundarySite)
    (groupedTaggedSite : GroupedTaggedBoundarySite) :
    AscriptionInferExprIffSliceAtSites
      dynamicSite wrapperSite groupedTaggedSite := by
  exact ⟨
    inferDynamicExprWithAscriptionAtSite_iff dynamicSite,
    inferWrapperExprWithAscriptionAtSite_iff wrapperSite,
    inferGroupedTaggedExprWithAscriptionAtSite_iff groupedTaggedSite
  ⟩

/-- Proof witness for ascription-specialized `AscriptionInferExprIffSlice`. -/
theorem ascriptionInferExprIffSlice_proved :
    AscriptionInferExprIffSlice := by
  simpa [AscriptionInferExprIffSlice]
    using ascriptionInferExprIffSliceAtSites_proved
      .ascription .ascription .ascription

/-- Wrapper witness lifted to expression-level ascription inference. -/
theorem inferWrapperExprWithAscriptionAtSite_task_bridge
    (site : WrapperBoundarySite) :
    inferWrapperExprWithAscriptionAtSite site
      wrapperTaskVarBoolEnv (.ascribe (.var "t") (.task .int)) = none
    ∧
    inferWrapperExprWithAscriptionAtSite site
      wrapperTaskVarIntEnv (.ascribe (.var "t") (.task .int))
      = some (.task .int)
    ∧
    HasTypeWithWrapperAscriptionAtSite site
      wrapperTaskVarIntEnv (.ascribe (.var "t") (.task .int)) (.task .int) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [inferWrapperExprWithAscriptionAtSite]
      using inferWrapperAscriptionAtSite_task_rejects site
  · simpa [inferWrapperExprWithAscriptionAtSite]
      using inferWrapperAscriptionAtSite_task_accepts site
  · exact (inferWrapperAscriptionAtSite_task_bridge site).2.2

/-- Grouped witness lifted to expression-level ascription inference. -/
theorem inferGroupedTaggedExprWithAscriptionAtSite_grouped_bridge
    (site : GroupedTaggedBoundarySite) :
    inferGroupedTaggedExprWithAscriptionAtSite site
      groupedVarBoolEnv
      (.ascribe (.var "g") (.groupedFrame .int ["a"])) = none
    ∧
    inferGroupedTaggedExprWithAscriptionAtSite site
      groupedVarIntEnv
      (.ascribe (.var "g") (.groupedFrame .int ["a"]))
      = some (.groupedFrame .int ["a"])
    ∧
    HasTypeWithGroupedTaggedAscriptionAtSite site
      groupedVarIntEnv
      (.ascribe (.var "g") (.groupedFrame .int ["a"]))
      (.groupedFrame .int ["a"]) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [inferGroupedTaggedExprWithAscriptionAtSite]
      using inferGroupedTaggedAscriptionAtSite_grouped_rejects site
  · simpa [inferGroupedTaggedExprWithAscriptionAtSite]
      using inferGroupedTaggedAscriptionAtSite_grouped_accepts site
  · exact (inferGroupedTaggedAscriptionAtSite_grouped_bridge site).2.2

/-- Packaged expression-level `inferExpr` integration slice for ascription
    boundaries across Dynamic/wrapper/grouped checks at explicit sites. -/
def AscriptionInferExprBridgeSliceAtSites
    (dynamicSite : DynamicBoundarySite)
    (wrapperSite : WrapperBoundarySite)
    (groupedTaggedSite : GroupedTaggedBoundarySite) : Prop :=
  (∀ env e ty,
      inferDynamicExprWithAscriptionAtSite dynamicSite env e = some ty →
      HasTypeWithDynamicAscriptionAtSite dynamicSite env e ty)
  ∧
  (∀ env e ty,
      inferWrapperExprWithAscriptionAtSite wrapperSite env e = some ty →
      HasTypeWithWrapperAscriptionAtSite wrapperSite env e ty)
  ∧
  (∀ env e ty,
      inferGroupedTaggedExprWithAscriptionAtSite groupedTaggedSite env e = some ty →
      HasTypeWithGroupedTaggedAscriptionAtSite groupedTaggedSite env e ty)

/-- Ascription-specialized alias for `AscriptionInferExprBridgeSliceAtSites`. -/
abbrev AscriptionInferExprBridgeSlice : Prop :=
  AscriptionInferExprBridgeSliceAtSites
    .ascription .ascription .ascription

/-- Proof witness for `AscriptionInferExprBridgeSliceAtSites`. -/
theorem ascriptionInferExprBridgeSliceAtSites_proved
    (dynamicSite : DynamicBoundarySite)
    (wrapperSite : WrapperBoundarySite)
    (groupedTaggedSite : GroupedTaggedBoundarySite) :
    AscriptionInferExprBridgeSliceAtSites
      dynamicSite wrapperSite groupedTaggedSite := by
  refine ⟨
    inferDynamicExprWithAscriptionAtSite_sound dynamicSite,
    inferWrapperExprWithAscriptionAtSite_sound wrapperSite,
    inferGroupedTaggedExprWithAscriptionAtSite_sound groupedTaggedSite
  ⟩

/-- Packaged expression-level `inferExpr` completeness slice for ascription
    boundaries across Dynamic/wrapper/grouped checks at explicit sites. -/
def AscriptionInferExprCompletenessSliceAtSites
    (dynamicSite : DynamicBoundarySite)
    (wrapperSite : WrapperBoundarySite)
    (groupedTaggedSite : GroupedTaggedBoundarySite) : Prop :=
  (∀ env e ty,
      HasTypeWithDynamicAscriptionAtSite dynamicSite env e ty →
      inferDynamicExprWithAscriptionAtSite dynamicSite env e = some ty)
  ∧
  (∀ env e ty,
      HasTypeWithWrapperAscriptionAtSite wrapperSite env e ty →
      inferWrapperExprWithAscriptionAtSite wrapperSite env e = some ty)
  ∧
  (∀ env e ty,
      HasTypeWithGroupedTaggedAscriptionAtSite groupedTaggedSite env e ty →
      inferGroupedTaggedExprWithAscriptionAtSite groupedTaggedSite env e = some ty)

/-- Ascription-specialized alias for
    `AscriptionInferExprCompletenessSliceAtSites`. -/
abbrev AscriptionInferExprCompletenessSlice : Prop :=
  AscriptionInferExprCompletenessSliceAtSites
    .ascription .ascription .ascription

/-- Proof witness for `AscriptionInferExprCompletenessSliceAtSites`. -/
theorem ascriptionInferExprCompletenessSliceAtSites_proved
    (dynamicSite : DynamicBoundarySite)
    (wrapperSite : WrapperBoundarySite)
    (groupedTaggedSite : GroupedTaggedBoundarySite) :
    AscriptionInferExprCompletenessSliceAtSites
      dynamicSite wrapperSite groupedTaggedSite := by
  exact ⟨
    inferDynamicExprWithAscriptionAtSite_complete dynamicSite,
    inferWrapperExprWithAscriptionAtSite_complete wrapperSite,
    inferGroupedTaggedExprWithAscriptionAtSite_complete groupedTaggedSite
  ⟩

/-- The packaged `infer`↔`HasType` equivalence slice implies the packaged
    expression-level `inferExpr` soundness bridge slice. -/
theorem ascriptionInferExprIffSliceAtSites_implies_bridge
    (dynamicSite : DynamicBoundarySite)
    (wrapperSite : WrapperBoundarySite)
    (groupedTaggedSite : GroupedTaggedBoundarySite)
    (h_iff : AscriptionInferExprIffSliceAtSites
      dynamicSite wrapperSite groupedTaggedSite) :
    AscriptionInferExprBridgeSliceAtSites
      dynamicSite wrapperSite groupedTaggedSite := by
  rcases h_iff with ⟨h_dyn, h_wrap, h_grouped⟩
  refine ⟨?_, ?_, ?_⟩
  · intro env e ty h_infer
    exact (h_dyn env e ty).1 h_infer
  · intro env e ty h_infer
    exact (h_wrap env e ty).1 h_infer
  · intro env e ty h_infer
    exact (h_grouped env e ty).1 h_infer

/-- The packaged `infer`↔`HasType` equivalence slice implies the packaged
    expression-level `inferExpr` completeness slice. -/
theorem ascriptionInferExprIffSliceAtSites_implies_completeness
    (dynamicSite : DynamicBoundarySite)
    (wrapperSite : WrapperBoundarySite)
    (groupedTaggedSite : GroupedTaggedBoundarySite)
    (h_iff : AscriptionInferExprIffSliceAtSites
      dynamicSite wrapperSite groupedTaggedSite) :
    AscriptionInferExprCompletenessSliceAtSites
      dynamicSite wrapperSite groupedTaggedSite := by
  rcases h_iff with ⟨h_dyn, h_wrap, h_grouped⟩
  refine ⟨?_, ?_, ?_⟩
  · intro env e ty h_ty
    exact (h_dyn env e ty).2 h_ty
  · intro env e ty h_ty
    exact (h_wrap env e ty).2 h_ty
  · intro env e ty h_ty
    exact (h_grouped env e ty).2 h_ty

/-- Proof witness for ascription-specialized
    `AscriptionInferExprCompletenessSlice`. -/
theorem ascriptionInferExprCompletenessSlice_proved :
    AscriptionInferExprCompletenessSlice := by
  simpa [AscriptionInferExprCompletenessSlice]
    using ascriptionInferExprCompletenessSliceAtSites_proved
      .ascription .ascription .ascription

/-- Proof witness for ascription-specialized
    `AscriptionInferExprBridgeSlice`. -/
theorem ascriptionInferExprBridgeSlice_proved :
    AscriptionInferExprBridgeSlice := by
  simpa [AscriptionInferExprBridgeSlice]
    using ascriptionInferExprBridgeSliceAtSites_proved
      .ascription .ascription .ascription

/-- Packaged algorithmic↔declarative ascription alignment slice across
    Dynamic/wrapper/grouped ascription adapters at explicit sites. -/
def AscriptionAlgorithmicDeclarativeAlignmentSliceAtSites
    (dynamicSite : DynamicBoundarySite)
    (wrapperSite : WrapperBoundarySite)
    (groupedTaggedSite : GroupedTaggedBoundarySite) : Prop :=
  (∀ env e expected,
      inferDynamicAscriptionAtSite dynamicSite env e expected = some expected
        ↔ HasTypeWithDynamicAscriptionAtSite dynamicSite env
            (.ascribe e expected) expected)
  ∧
  (∀ env e expected,
      inferWrapperAscriptionAtSite wrapperSite env e expected = some expected
        ↔ HasTypeWithWrapperAscriptionAtSite wrapperSite env
            (.ascribe e expected) expected)
  ∧
  (∀ env e expected,
      inferGroupedTaggedAscriptionAtSite groupedTaggedSite env e expected
          = some expected
        ↔ HasTypeWithGroupedTaggedAscriptionAtSite groupedTaggedSite env
            (.ascribe e expected) expected)

/-- Ascription-specialized alias for
    `AscriptionAlgorithmicDeclarativeAlignmentSliceAtSites`. -/
abbrev AscriptionAlgorithmicDeclarativeAlignmentSlice : Prop :=
  AscriptionAlgorithmicDeclarativeAlignmentSliceAtSites
    .ascription .ascription .ascription

/-- Proof witness for `AscriptionAlgorithmicDeclarativeAlignmentSliceAtSites`. -/
theorem ascriptionAlgorithmicDeclarativeAlignmentSliceAtSites_proved
    (dynamicSite : DynamicBoundarySite)
    (wrapperSite : WrapperBoundarySite)
    (groupedTaggedSite : GroupedTaggedBoundarySite) :
    AscriptionAlgorithmicDeclarativeAlignmentSliceAtSites
      dynamicSite wrapperSite groupedTaggedSite := by
  exact ⟨
    inferDynamicAscriptionAtSite_iff dynamicSite,
    inferWrapperAscriptionAtSite_iff wrapperSite,
    inferGroupedTaggedAscriptionAtSite_iff groupedTaggedSite
  ⟩

/-- Proof witness for ascription-specialized
    `AscriptionAlgorithmicDeclarativeAlignmentSlice`. -/
theorem ascriptionAlgorithmicDeclarativeAlignmentSlice_proved :
    AscriptionAlgorithmicDeclarativeAlignmentSlice := by
  simpa [AscriptionAlgorithmicDeclarativeAlignmentSlice]
    using ascriptionAlgorithmicDeclarativeAlignmentSliceAtSites_proved
      .ascription .ascription .ascription

/-- Packaged expression-level ascription slice across Dynamic, wrapper, and
    grouped/tagged boundaries at explicit sites. -/
def BoundaryAscriptionSyntaxSliceAtSites
    (dynamicSite : DynamicBoundarySite)
    (wrapperSite : WrapperBoundarySite)
    (groupedTaggedSite : GroupedTaggedBoundarySite) : Prop :=
  (¬ HasTypeWithDynamicAscriptionAtSite dynamicSite
      [("x", .dynamic)] (.ascribe (.var "x") .int) .int)
  ∧
  (HasTypeWithDynamicAscriptionAtSite dynamicSite
      [("x", .dynamic)] (.ascribe (.var "x") .dynamic) .dynamic)
  ∧
  (¬ HasTypeWithWrapperAscriptionAtSite wrapperSite
      wrapperTaskVarBoolEnv (.ascribe (.var "t") (.task .int)) (.task .int))
  ∧
  (HasTypeWithWrapperAscriptionAtSite wrapperSite
      wrapperTaskVarIntEnv (.ascribe (.var "t") (.task .int)) (.task .int))
  ∧
  (¬ HasTypeWithGroupedTaggedAscriptionAtSite groupedTaggedSite
      groupedVarBoolEnv
      (.ascribe (.var "g") (.groupedFrame .int ["a"]))
      (.groupedFrame .int ["a"]))
  ∧
  (HasTypeWithGroupedTaggedAscriptionAtSite groupedTaggedSite
      groupedVarIntEnv
      (.ascribe (.var "g") (.groupedFrame .int ["a"]))
      (.groupedFrame .int ["a"]))

/-- Ascription-specialized alias for
    `BoundaryAscriptionSyntaxSliceAtSites`. -/
abbrev BoundaryAscriptionSyntaxSlice : Prop :=
  BoundaryAscriptionSyntaxSliceAtSites .ascription .ascription .ascription

/-- Packaged expression-level ascription site-invariance slice across
    Dynamic/wrapper/grouped-tagged boundaries. -/
def BoundaryAscriptionSyntaxSiteInvarianceSliceAtSites
    (dynamicSite : DynamicBoundarySite)
    (wrapperSite : WrapperBoundarySite)
    (groupedTaggedSite : GroupedTaggedBoundarySite) : Prop :=
  (HasTypeWithDynamicAscriptionAtSite dynamicSite
      [("x", .dynamic)] (.ascribe (.var "x") .int) .int
      ↔
    HasTypeWithDynamicAscriptionAtSite .ascription
      [("x", .dynamic)] (.ascribe (.var "x") .int) .int)
  ∧
  (HasTypeWithWrapperAscriptionAtSite wrapperSite
      wrapperTaskVarBoolEnv (.ascribe (.var "t") (.task .int)) (.task .int)
      ↔
    HasTypeWithWrapperAscriptionAtSite .ascription
      wrapperTaskVarBoolEnv (.ascribe (.var "t") (.task .int)) (.task .int))
  ∧
  (HasTypeWithGroupedTaggedAscriptionAtSite groupedTaggedSite
      groupedVarBoolEnv
      (.ascribe (.var "g") (.groupedFrame .int ["a"]))
      (.groupedFrame .int ["a"])
      ↔
    HasTypeWithGroupedTaggedAscriptionAtSite .ascription
      groupedVarBoolEnv
      (.ascribe (.var "g") (.groupedFrame .int ["a"]))
      (.groupedFrame .int ["a"]))

/-- Ascription-specialized alias for
    `BoundaryAscriptionSyntaxSiteInvarianceSliceAtSites`. -/
abbrev BoundaryAscriptionSyntaxSiteInvarianceSlice : Prop :=
  BoundaryAscriptionSyntaxSiteInvarianceSliceAtSites
    .ascription .ascription .ascription

/-- Proof witness for `BoundaryAscriptionSyntaxSliceAtSites`. -/
theorem boundaryAscriptionSyntaxSliceAtSites_proved
    (dynamicSite : DynamicBoundarySite)
    (wrapperSite : WrapperBoundarySite)
    (groupedTaggedSite : GroupedTaggedBoundarySite) :
    BoundaryAscriptionSyntaxSliceAtSites
      dynamicSite wrapperSite groupedTaggedSite := by
  rcases dynamic_boundary_typing_bridge_ascription_all_sites dynamicSite with
    ⟨_h_dyn_reject, h_dyn_narrow, h_dyn_accept⟩
  rcases wrapper_typing_bridge_all_sites wrapperSite with
    ⟨h_task_inner, _h_task_non_wrapper, h_task_id,
      _h_actor_inner, _h_actor_non_wrapper, _h_actor_id,
      _h_arc_inner, _h_arc_non_wrapper, _h_arc_id⟩
  rcases grouped_tagged_typing_bridge_all_sites groupedTaggedSite with
    ⟨h_grouped_inner, _h_grouped_non_wrapper, h_grouped_id,
      _h_tagged_inner, _h_tagged_non_wrapper, _h_tagged_id⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have h_boundary :
        HasTypeAtAscriptionBoundaryAtSite dynamicSite
          [("x", .dynamic)] (.var "x") .int :=
      (hasTypeWithDynamicAscription_ascribe_iff_boundary
        dynamicSite [("x", .dynamic)] (.var "x") .int).1 h
    exact h_dyn_narrow h_boundary
  · exact (hasTypeWithDynamicAscription_ascribe_iff_boundary
      dynamicSite [("x", .dynamic)] (.var "x") .dynamic).2 h_dyn_accept
  · intro h
    have h_boundary :
        HasTypeAtWrapperBoundaryAtSite wrapperSite
          wrapperTaskVarBoolEnv (.var "t") (.task .int) :=
      (hasTypeWithWrapperAscription_ascribe_iff_boundary
        wrapperSite wrapperTaskVarBoolEnv (.var "t") (.task .int)).1 h
    exact h_task_inner h_boundary
  · exact (hasTypeWithWrapperAscription_ascribe_iff_boundary
      wrapperSite wrapperTaskVarIntEnv (.var "t") (.task .int)).2 h_task_id
  · intro h
    have h_boundary :
        HasTypeAtGroupedTaggedBoundaryAtSite groupedTaggedSite
          groupedVarBoolEnv (.var "g") (.groupedFrame .int ["a"]) :=
      (hasTypeWithGroupedTaggedAscription_ascribe_iff_boundary
        groupedTaggedSite groupedVarBoolEnv (.var "g")
        (.groupedFrame .int ["a"])).1 h
    exact h_grouped_inner h_boundary
  · exact (hasTypeWithGroupedTaggedAscription_ascribe_iff_boundary
      groupedTaggedSite groupedVarIntEnv (.var "g")
      (.groupedFrame .int ["a"])).2 h_grouped_id

/-- Proof witness for ascription-specialized `BoundaryAscriptionSyntaxSlice`. -/
theorem boundaryAscriptionSyntaxSlice_proved :
    BoundaryAscriptionSyntaxSlice := by
  simpa [BoundaryAscriptionSyntaxSlice]
    using boundaryAscriptionSyntaxSliceAtSites_proved
      .ascription .ascription .ascription

/-- Proof witness for `BoundaryAscriptionSyntaxSiteInvarianceSliceAtSites`. -/
theorem boundaryAscriptionSyntaxSiteInvarianceSliceAtSites_proved
    (dynamicSite : DynamicBoundarySite)
    (wrapperSite : WrapperBoundarySite)
    (groupedTaggedSite : GroupedTaggedBoundarySite) :
    BoundaryAscriptionSyntaxSiteInvarianceSliceAtSites
      dynamicSite wrapperSite groupedTaggedSite := by
  refine ⟨?_, ?_, ?_⟩
  · exact hasTypeWithDynamicAscription_ascribe_iff_ascription
      dynamicSite [("x", .dynamic)] (.var "x") .int
  · exact hasTypeWithWrapperAscription_ascribe_iff_ascription
      wrapperSite wrapperTaskVarBoolEnv (.var "t") (.task .int)
  · exact hasTypeWithGroupedTaggedAscription_ascribe_iff_ascription
      groupedTaggedSite groupedVarBoolEnv (.var "g") (.groupedFrame .int ["a"])

/-- Proof witness for ascription-specialized
    `BoundaryAscriptionSyntaxSiteInvarianceSlice`. -/
theorem boundaryAscriptionSyntaxSiteInvarianceSlice_proved :
    BoundaryAscriptionSyntaxSiteInvarianceSlice := by
  simpa [BoundaryAscriptionSyntaxSiteInvarianceSlice]
    using boundaryAscriptionSyntaxSiteInvarianceSliceAtSites_proved
      .ascription .ascription .ascription

/-- Packaged cross-surface ascription bridge suite at explicit sites. -/
def BoundaryAscriptionBridgeSuiteAtSites
    (dynamicSite : DynamicBoundarySite)
    (wrapperSite : WrapperBoundarySite)
    (groupedTaggedSite : GroupedTaggedBoundarySite) : Prop :=
  BoundaryAscriptionSyntaxSliceAtSites
    dynamicSite wrapperSite groupedTaggedSite
  ∧
  BoundaryAscriptionSyntaxSiteInvarianceSliceAtSites
    dynamicSite wrapperSite groupedTaggedSite
  ∧
  DynamicAscriptionAlgorithmicSliceAtSite dynamicSite
  ∧
  WrapperAscriptionAlgorithmicSliceAtSite wrapperSite
  ∧
  GroupedTaggedAscriptionAlgorithmicSliceAtSite groupedTaggedSite
  ∧
  AscriptionAlgorithmicDeclarativeAlignmentSliceAtSites
    dynamicSite wrapperSite groupedTaggedSite
  ∧
  AscriptionInferExprBridgeSliceAtSites
    dynamicSite wrapperSite groupedTaggedSite
  ∧
  AscriptionInferExprCompletenessSliceAtSites
    dynamicSite wrapperSite groupedTaggedSite
  ∧
  AscriptionInferExprIffSliceAtSites
    dynamicSite wrapperSite groupedTaggedSite
  ∧
  AscriptionCoreInferRoutingSliceAtSites
    dynamicSite wrapperSite groupedTaggedSite
  ∧
  AscriptionBaseEmbeddingSliceAtSites
    dynamicSite wrapperSite groupedTaggedSite

/-- Ascription-specialized alias for `BoundaryAscriptionBridgeSuiteAtSites`. -/
abbrev BoundaryAscriptionBridgeSuite : Prop :=
  BoundaryAscriptionBridgeSuiteAtSites
    .ascription .ascription .ascription

/-- Proof witness for `BoundaryAscriptionBridgeSuiteAtSites`. -/
theorem boundaryAscriptionBridgeSuiteAtSites_proved
    (dynamicSite : DynamicBoundarySite)
    (wrapperSite : WrapperBoundarySite)
    (groupedTaggedSite : GroupedTaggedBoundarySite) :
    BoundaryAscriptionBridgeSuiteAtSites
      dynamicSite wrapperSite groupedTaggedSite := by
  refine ⟨
    boundaryAscriptionSyntaxSliceAtSites_proved
      dynamicSite wrapperSite groupedTaggedSite,
    boundaryAscriptionSyntaxSiteInvarianceSliceAtSites_proved
      dynamicSite wrapperSite groupedTaggedSite,
    dynamicAscriptionAlgorithmicSliceAtSite_proved dynamicSite,
    wrapperAscriptionAlgorithmicSliceAtSite_proved wrapperSite,
    groupedTaggedAscriptionAlgorithmicSliceAtSite_proved groupedTaggedSite,
    ascriptionAlgorithmicDeclarativeAlignmentSliceAtSites_proved
      dynamicSite wrapperSite groupedTaggedSite,
    ascriptionInferExprBridgeSliceAtSites_proved
      dynamicSite wrapperSite groupedTaggedSite,
    ascriptionInferExprCompletenessSliceAtSites_proved
      dynamicSite wrapperSite groupedTaggedSite,
    ascriptionInferExprIffSliceAtSites_proved
      dynamicSite wrapperSite groupedTaggedSite,
    ascriptionCoreInferRoutingSliceAtSites_proved
      dynamicSite wrapperSite groupedTaggedSite,
    ascriptionBaseEmbeddingSliceAtSites_proved
      dynamicSite wrapperSite groupedTaggedSite
  ⟩

/-- Proof witness for ascription-specialized `BoundaryAscriptionBridgeSuite`. -/
theorem boundaryAscriptionBridgeSuite_proved :
    BoundaryAscriptionBridgeSuite := by
  simpa [BoundaryAscriptionBridgeSuite]
    using boundaryAscriptionBridgeSuiteAtSites_proved
      .ascription .ascription .ascription
