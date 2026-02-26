import Kea.Typing
import Kea.Properties.NominalAdtParity
import Kea.Properties.BoundaryAssignability

/-!
  Kea.Properties.NominalAdtTypingBridge

  Language-level bridge for nominal ADT (`Sum`/`Opaque`) boundary behavior at
  a modeled ascription boundary gate.
-/

/-- Modeled nominal ADT boundary gate at a chosen boundary site:
    expression `e` inhabits `expected` iff it has some actual type that both
    passes nominal ADT boundary policy and unifies with `expected`. -/
def HasTypeAtNominalAdtBoundaryAtSite
    (site : NominalAdtBoundarySite)
    (env : TermEnv) (e : CoreExpr) (expected : Ty) : Prop :=
  HasTypeAtBoundary
    (allowsByBoolAndUnify
      (nominalAdtBoundaryAllowsAtSite site)
      UnifyState.empty
      2)
    env e expected

/-- Modeled nominal ADT ascription gate (site-specialized alias). -/
abbrev HasTypeAtNominalAdtBoundary
    (env : TermEnv) (e : CoreExpr) (expected : Ty) : Prop :=
  HasTypeAtNominalAdtBoundaryAtSite .ascription env e expected

/-- Nominal ADT typing gate is site-invariant because nominal ADT boundary
    policy is currently site-invariant. -/
theorem hasTypeAtNominalAdtBoundaryAtSite_iff_ascription
    (site : NominalAdtBoundarySite)
    (env : TermEnv) (e : CoreExpr) (expected : Ty) :
    HasTypeAtNominalAdtBoundaryAtSite site env e expected
      ↔ HasTypeAtNominalAdtBoundary env e expected := by
  refine hasTypeAtBoundary_congr
    (allowsByBoolAndUnify (nominalAdtBoundaryAllowsAtSite site) UnifyState.empty 2)
    (allowsByBoolAndUnify (nominalAdtBoundaryAllowsAtSite .ascription) UnifyState.empty 2)
    env e expected ?_
  intro exp act
  have h_site :
      nominalAdtBoundaryAllowsAtSite site exp act
        = nominalAdtBoundaryAllowsAtSite .ascription exp act :=
    nominal_adt_boundary_policy_site_invariant site .ascription exp act
  unfold allowsByBoolAndUnify
  simp [h_site]

abbrev nominalSumAEnv : TermEnv := [("x", .sum "A" .nil)]
abbrev nominalSumBEnv : TermEnv := [("x", .sum "B" .nil)]
abbrev nominalOpaqueUserIdEnv : TermEnv := [("x", .opaque "UserId" .nil)]
abbrev nominalOpaqueOrderIdEnv : TermEnv := [("x", .opaque "OrderId" .nil)]
abbrev nominalIntEnv : TermEnv := [("x", .int)]

/-- `x` has the unique `Sum A` type in `nominalSumAEnv`. -/
theorem hasType_var_sumA_unique
    (ty : Ty)
    (h_ty : HasType nominalSumAEnv (.var "x") ty) :
    ty = .sum "A" .nil := by
  cases h_ty with
  | var env name ty' h_lookup =>
      simpa [nominalSumAEnv, TermEnv.lookup] using h_lookup.symm

/-- `x` has the unique `Sum B` type in `nominalSumBEnv`. -/
theorem hasType_var_sumB_unique
    (ty : Ty)
    (h_ty : HasType nominalSumBEnv (.var "x") ty) :
    ty = .sum "B" .nil := by
  cases h_ty with
  | var env name ty' h_lookup =>
      simpa [nominalSumBEnv, TermEnv.lookup] using h_lookup.symm

/-- `x` has the unique `Opaque UserId` type in `nominalOpaqueUserIdEnv`. -/
theorem hasType_var_opaqueUserId_unique
    (ty : Ty)
    (h_ty : HasType nominalOpaqueUserIdEnv (.var "x") ty) :
    ty = .opaque "UserId" .nil := by
  cases h_ty with
  | var env name ty' h_lookup =>
      simpa [nominalOpaqueUserIdEnv, TermEnv.lookup] using h_lookup.symm

/-- `x` has the unique `Opaque OrderId` type in `nominalOpaqueOrderIdEnv`. -/
theorem hasType_var_opaqueOrderId_unique
    (ty : Ty)
    (h_ty : HasType nominalOpaqueOrderIdEnv (.var "x") ty) :
    ty = .opaque "OrderId" .nil := by
  cases h_ty with
  | var env name ty' h_lookup =>
      simpa [nominalOpaqueOrderIdEnv, TermEnv.lookup] using h_lookup.symm

/-- `x` has the unique bare `Int` type in `nominalIntEnv`. -/
theorem hasType_var_nominal_int_unique
    (ty : Ty)
    (h_ty : HasType nominalIntEnv (.var "x") ty) :
    ty = .int := by
  cases h_ty with
  | var env name ty' h_lookup =>
      simpa [nominalIntEnv, TermEnv.lookup] using h_lookup.symm

/-- Distinct nominal `Sum` names are rejected by modeled ascription gate. -/
theorem hasType_ascription_sum_name_mismatch_rejected :
    ¬ HasTypeAtNominalAdtBoundary nominalSumBEnv (.var "x") (.sum "A" .nil) := by
  intro h
  rcases h with ⟨actual, h_ty, h_rel⟩
  rcases h_rel with ⟨h_allow, _h_unify⟩
  have h_actual : actual = .sum "B" .nil := hasType_var_sumB_unique actual h_ty
  subst h_actual
  have h_reject :
      nominalAdtBoundaryAllowsAtSite .ascription
        (.sum "A" .nil)
        (.sum "B" .nil)
      = false := by
    exact nominal_adt_boundary_rejects_sum_name_mismatch
  simp [h_reject] at h_allow

/-- Distinct nominal `Opaque` names are rejected by modeled ascription gate. -/
theorem hasType_ascription_opaque_name_mismatch_rejected :
    ¬ HasTypeAtNominalAdtBoundary nominalOpaqueOrderIdEnv (.var "x")
      (.opaque "UserId" .nil) := by
  intro h
  rcases h with ⟨actual, h_ty, h_rel⟩
  rcases h_rel with ⟨h_allow, _h_unify⟩
  have h_actual : actual = .opaque "OrderId" .nil :=
    hasType_var_opaqueOrderId_unique actual h_ty
  subst h_actual
  have h_reject :
      nominalAdtBoundaryAllowsAtSite .ascription
        (.opaque "UserId" .nil)
        (.opaque "OrderId" .nil)
      = false := by
    exact nominal_adt_boundary_rejects_opaque_name_mismatch
  simp [h_reject] at h_allow

/-- Non-nominal actuals are rejected when nominal `Sum` is expected. -/
theorem hasType_ascription_sum_from_int_rejected :
    ¬ HasTypeAtNominalAdtBoundary nominalIntEnv (.var "x") (.sum "A" .nil) := by
  intro h
  rcases h with ⟨actual, h_ty, h_rel⟩
  rcases h_rel with ⟨h_allow, _h_unify⟩
  have h_actual : actual = .int := hasType_var_nominal_int_unique actual h_ty
  subst h_actual
  have h_reject :
      nominalAdtBoundaryAllowsAtSite .ascription
        (.sum "A" .nil)
        .int
      = false := by
    exact nominal_adt_boundary_rejects_non_nominal_actual
  simp [h_reject] at h_allow

/-- `Sum` identity ascription remains accepted. -/
theorem hasType_ascription_sum_accepts :
    HasTypeAtNominalAdtBoundary nominalSumAEnv (.var "x") (.sum "A" .nil) := by
  refine ⟨.sum "A" .nil, ?_, ?_⟩
  · exact HasType.var nominalSumAEnv "x" (.sum "A" .nil) (by
      simp [TermEnv.lookup])
  · refine ⟨?_, ?_⟩
    · native_decide
    · refine ⟨UnifyState.empty, ?_⟩
      simpa using (sum_unifies_with_self UnifyState.empty 1 "A" .nil)

/-- `Opaque` identity ascription remains accepted. -/
theorem hasType_ascription_opaque_accepts :
    HasTypeAtNominalAdtBoundary nominalOpaqueUserIdEnv (.var "x")
      (.opaque "UserId" .nil) := by
  refine ⟨.opaque "UserId" .nil, ?_, ?_⟩
  · exact HasType.var nominalOpaqueUserIdEnv "x" (.opaque "UserId" .nil) (by
      simp [TermEnv.lookup])
  · refine ⟨?_, ?_⟩
    · native_decide
    · refine ⟨UnifyState.empty, ?_⟩
      simpa using (opaque_unifies_with_self UnifyState.empty 1 "UserId" .nil)

/-- Packaged nominal ADT typing bridge at modeled ascription boundary:
    distinct-name and non-nominal rejection hold, while nominal identity
    controls remain accepted. -/
theorem nominal_adt_typing_bridge_ascription :
    ¬ HasTypeAtNominalAdtBoundary nominalSumBEnv (.var "x") (.sum "A" .nil)
    ∧
    ¬ HasTypeAtNominalAdtBoundary nominalOpaqueOrderIdEnv (.var "x")
      (.opaque "UserId" .nil)
    ∧
    ¬ HasTypeAtNominalAdtBoundary nominalIntEnv (.var "x") (.sum "A" .nil)
    ∧
    HasTypeAtNominalAdtBoundary nominalSumAEnv (.var "x") (.sum "A" .nil)
    ∧
    HasTypeAtNominalAdtBoundary nominalOpaqueUserIdEnv (.var "x")
      (.opaque "UserId" .nil) := by
  refine ⟨
    hasType_ascription_sum_name_mismatch_rejected,
    hasType_ascription_opaque_name_mismatch_rejected,
    hasType_ascription_sum_from_int_rejected,
    hasType_ascription_sum_accepts,
    hasType_ascription_opaque_accepts
  ⟩

/-- Site-generalized nominal ADT typing bridge:
    ascription bridge outcomes are preserved at all boundary-sensitive sites. -/
theorem nominal_adt_typing_bridge_all_sites
    (site : NominalAdtBoundarySite) :
    ¬ HasTypeAtNominalAdtBoundaryAtSite site nominalSumBEnv (.var "x") (.sum "A" .nil)
    ∧
    ¬ HasTypeAtNominalAdtBoundaryAtSite site nominalOpaqueOrderIdEnv (.var "x")
      (.opaque "UserId" .nil)
    ∧
    ¬ HasTypeAtNominalAdtBoundaryAtSite site nominalIntEnv (.var "x") (.sum "A" .nil)
    ∧
    HasTypeAtNominalAdtBoundaryAtSite site nominalSumAEnv (.var "x") (.sum "A" .nil)
    ∧
    HasTypeAtNominalAdtBoundaryAtSite site nominalOpaqueUserIdEnv (.var "x")
      (.opaque "UserId" .nil) := by
  rcases nominal_adt_typing_bridge_ascription with
    ⟨h_sum_mismatch, h_opaque_mismatch, h_sum_non_nominal, h_sum_id, h_opaque_id⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have h_ascr :
        HasTypeAtNominalAdtBoundary nominalSumBEnv (.var "x") (.sum "A" .nil) :=
      (hasTypeAtNominalAdtBoundaryAtSite_iff_ascription site
        nominalSumBEnv (.var "x") (.sum "A" .nil)).1 h
    exact h_sum_mismatch h_ascr
  · intro h
    have h_ascr :
        HasTypeAtNominalAdtBoundary nominalOpaqueOrderIdEnv (.var "x")
          (.opaque "UserId" .nil) :=
      (hasTypeAtNominalAdtBoundaryAtSite_iff_ascription site
        nominalOpaqueOrderIdEnv (.var "x") (.opaque "UserId" .nil)).1 h
    exact h_opaque_mismatch h_ascr
  · intro h
    have h_ascr :
        HasTypeAtNominalAdtBoundary nominalIntEnv (.var "x") (.sum "A" .nil) :=
      (hasTypeAtNominalAdtBoundaryAtSite_iff_ascription site
        nominalIntEnv (.var "x") (.sum "A" .nil)).1 h
    exact h_sum_non_nominal h_ascr
  · exact (hasTypeAtNominalAdtBoundaryAtSite_iff_ascription site
      nominalSumAEnv (.var "x") (.sum "A" .nil)).2 h_sum_id
  · exact (hasTypeAtNominalAdtBoundaryAtSite_iff_ascription site
      nominalOpaqueUserIdEnv (.var "x") (.opaque "UserId" .nil)).2 h_opaque_id

/-- Packaged site-level nominal ADT typing-bridge slice. -/
def NominalAdtTypingBridgeSliceAtSites
    (site : NominalAdtBoundarySite) : Prop :=
  ¬ HasTypeAtNominalAdtBoundaryAtSite site nominalSumBEnv (.var "x") (.sum "A" .nil)
  ∧
  ¬ HasTypeAtNominalAdtBoundaryAtSite site nominalOpaqueOrderIdEnv (.var "x")
    (.opaque "UserId" .nil)
  ∧
  ¬ HasTypeAtNominalAdtBoundaryAtSite site nominalIntEnv (.var "x") (.sum "A" .nil)
  ∧
  HasTypeAtNominalAdtBoundaryAtSite site nominalSumAEnv (.var "x") (.sum "A" .nil)
  ∧
  HasTypeAtNominalAdtBoundaryAtSite site nominalOpaqueUserIdEnv (.var "x")
    (.opaque "UserId" .nil)

/-- Proof witness for `NominalAdtTypingBridgeSliceAtSites`. -/
theorem nominalAdtTypingBridgeSliceAtSites_proved
    (site : NominalAdtBoundarySite) :
    NominalAdtTypingBridgeSliceAtSites site := by
  exact nominal_adt_typing_bridge_all_sites site

/-- Minimal algorithmic nominal ascription checker at a boundary site:
    infer the inner type, then require nominal boundary policy acceptance plus
    existential unifier success against the annotation. -/
def nominalAscriptionAllowsBoolAtSite
    (site : NominalAdtBoundarySite)
    (expected actual : Ty) : Bool :=
  nominalAdtBoundaryAllowsAtSite site expected actual
  &&
  (match unify UnifyState.empty 2 expected actual with
   | .ok _ => true
   | .err _ => false)

/-- Boolean nominal ascription gate is equivalent to the declarative nominal
    boundary relation with existential unifier success. -/
theorem nominalAscriptionAllowsBoolAtSite_true_iff
    (site : NominalAdtBoundarySite)
    (expected actual : Ty) :
    nominalAscriptionAllowsBoolAtSite site expected actual = true
      ↔
      allowsByBoolAndUnify
        (nominalAdtBoundaryAllowsAtSite site)
        UnifyState.empty
        2
        expected actual := by
  unfold nominalAscriptionAllowsBoolAtSite allowsByBoolAndUnify
  cases h_unify : unify UnifyState.empty 2 expected actual with
  | ok st =>
      simp
  | err e =>
      simp

/-- Minimal algorithmic nominal ascription checker at a boundary site:
    infer the inner type, then require nominal boundary policy acceptance plus
    existential unifier success against the annotation. -/
def inferNominalAscriptionAtSite
    (site : NominalAdtBoundarySite)
    (env : TermEnv) (e : CoreExpr) (expected : Ty) : Option Ty :=
  inferExprWithAscription
    (nominalAscriptionAllowsBoolAtSite site)
    env
    (.ascribe e expected)

/-- Successful nominal ascription inference always returns the annotation
    type. -/
theorem inferNominalAscriptionAtSite_some_implies_expected
    (site : NominalAdtBoundarySite)
    (env : TermEnv) (e : CoreExpr) (expected ty : Ty)
    (h : inferNominalAscriptionAtSite site env e expected = some ty) :
    ty = expected := by
  unfold inferNominalAscriptionAtSite inferExprWithAscription at h
  cases h_expr : inferExpr env e with
  | none =>
      simp [h_expr] at h
  | some actual =>
      cases h_allow : nominalAscriptionAllowsBoolAtSite site expected actual with
      | false =>
          simp [h_expr, h_allow] at h
      | true =>
          simp [h_expr, h_allow] at h
          exact h.symm

/-- Nominal ascription inference is equivalent to modeled nominal boundary
    typing on explicit `ascribe` nodes. -/
theorem inferNominalAscriptionAtSite_iff
    (site : NominalAdtBoundarySite)
    (env : TermEnv) (e : CoreExpr) (expected : Ty) :
    inferNominalAscriptionAtSite site env e expected = some expected
      ↔ HasTypeAtNominalAdtBoundaryAtSite site env e expected := by
  have h_core :
      inferNominalAscriptionAtSite site env e expected = some expected
        ↔
        HasTypeAtCoreBoundary
          (fun exp act =>
            nominalAscriptionAllowsBoolAtSite site exp act = true)
          env e expected := by
    simpa [inferNominalAscriptionAtSite]
      using inferExprWithAscription_ascribe_iff_boundary
        (nominalAscriptionAllowsBoolAtSite site)
        env e expected
  have h_rel :
      HasTypeAtCoreBoundary
          (fun exp act =>
            nominalAscriptionAllowsBoolAtSite site exp act = true)
          env e expected
        ↔
        HasTypeAtNominalAdtBoundaryAtSite site env e expected := by
    simpa [HasTypeAtNominalAdtBoundaryAtSite, HasTypeAtBoundary]
      using (hasTypeAtBoundary_congr
        (fun exp act =>
          nominalAscriptionAllowsBoolAtSite site exp act = true)
        (allowsByBoolAndUnify
          (nominalAdtBoundaryAllowsAtSite site)
          UnifyState.empty
          2)
        env e expected
        (by
          intro exp act
          exact nominalAscriptionAllowsBoolAtSite_true_iff site exp act))
  exact h_core.trans h_rel

/-- Algorithmic nominal `Sum` mismatch witness:
    `B as A` is rejected at any boundary-sensitive site. -/
theorem inferNominalAscriptionAtSite_sum_name_mismatch
    (site : NominalAdtBoundarySite) :
    inferNominalAscriptionAtSite site nominalSumBEnv (.var "x") (.sum "A" .nil) = none := by
  have h_not_some :
      ¬ inferNominalAscriptionAtSite site nominalSumBEnv (.var "x") (.sum "A" .nil) =
          some (.sum "A" .nil) := by
    intro h_some
    have h_boundary :
        HasTypeAtNominalAdtBoundaryAtSite site nominalSumBEnv (.var "x") (.sum "A" .nil) :=
      (inferNominalAscriptionAtSite_iff site nominalSumBEnv (.var "x") (.sum "A" .nil)).1 h_some
    have h_ascr :
        HasTypeAtNominalAdtBoundary nominalSumBEnv (.var "x") (.sum "A" .nil) :=
      (hasTypeAtNominalAdtBoundaryAtSite_iff_ascription site
        nominalSumBEnv (.var "x") (.sum "A" .nil)).1 h_boundary
    exact hasType_ascription_sum_name_mismatch_rejected h_ascr
  cases h_infer : inferNominalAscriptionAtSite site nominalSumBEnv (.var "x") (.sum "A" .nil) with
  | none => rfl
  | some ty =>
      have h_ty : ty = .sum "A" .nil :=
        inferNominalAscriptionAtSite_some_implies_expected
          site nominalSumBEnv (.var "x") (.sum "A" .nil) ty h_infer
      subst h_ty
      exact (h_not_some h_infer).elim

/-- Algorithmic nominal `Opaque` mismatch witness:
    `OrderId as UserId` is rejected at any boundary-sensitive site. -/
theorem inferNominalAscriptionAtSite_opaque_name_mismatch
    (site : NominalAdtBoundarySite) :
    inferNominalAscriptionAtSite site nominalOpaqueOrderIdEnv (.var "x")
      (.opaque "UserId" .nil) = none := by
  have h_not_some :
      ¬ inferNominalAscriptionAtSite site nominalOpaqueOrderIdEnv (.var "x")
          (.opaque "UserId" .nil) =
          some (.opaque "UserId" .nil) := by
    intro h_some
    have h_boundary :
        HasTypeAtNominalAdtBoundaryAtSite site nominalOpaqueOrderIdEnv (.var "x")
          (.opaque "UserId" .nil) :=
      (inferNominalAscriptionAtSite_iff site nominalOpaqueOrderIdEnv
        (.var "x") (.opaque "UserId" .nil)).1 h_some
    have h_ascr :
        HasTypeAtNominalAdtBoundary nominalOpaqueOrderIdEnv (.var "x")
          (.opaque "UserId" .nil) :=
      (hasTypeAtNominalAdtBoundaryAtSite_iff_ascription site
        nominalOpaqueOrderIdEnv (.var "x") (.opaque "UserId" .nil)).1 h_boundary
    exact hasType_ascription_opaque_name_mismatch_rejected h_ascr
  cases h_infer :
      inferNominalAscriptionAtSite site nominalOpaqueOrderIdEnv (.var "x")
        (.opaque "UserId" .nil) with
  | none => rfl
  | some ty =>
      have h_ty : ty = .opaque "UserId" .nil :=
        inferNominalAscriptionAtSite_some_implies_expected
          site nominalOpaqueOrderIdEnv (.var "x")
          (.opaque "UserId" .nil) ty h_infer
      subst h_ty
      exact (h_not_some h_infer).elim

/-- Algorithmic nominal `Sum` identity witness:
    `A as A` is accepted at any boundary-sensitive site. -/
theorem inferNominalAscriptionAtSite_sum_identity
    (site : NominalAdtBoundarySite) :
    inferNominalAscriptionAtSite site nominalSumAEnv (.var "x") (.sum "A" .nil) =
      some (.sum "A" .nil) := by
  have h_ascr :
      HasTypeAtNominalAdtBoundary nominalSumAEnv (.var "x") (.sum "A" .nil) :=
    hasType_ascription_sum_accepts
  have h_site :
      HasTypeAtNominalAdtBoundaryAtSite site nominalSumAEnv (.var "x") (.sum "A" .nil) :=
    (hasTypeAtNominalAdtBoundaryAtSite_iff_ascription site
      nominalSumAEnv (.var "x") (.sum "A" .nil)).2 h_ascr
  exact (inferNominalAscriptionAtSite_iff site
    nominalSumAEnv (.var "x") (.sum "A" .nil)).2 h_site

/-- Algorithmic nominal `Opaque` identity witness:
    `UserId as UserId` is accepted at any boundary-sensitive site. -/
theorem inferNominalAscriptionAtSite_opaque_identity
    (site : NominalAdtBoundarySite) :
    inferNominalAscriptionAtSite site nominalOpaqueUserIdEnv (.var "x")
      (.opaque "UserId" .nil) = some (.opaque "UserId" .nil) := by
  have h_ascr :
      HasTypeAtNominalAdtBoundary nominalOpaqueUserIdEnv (.var "x")
        (.opaque "UserId" .nil) :=
    hasType_ascription_opaque_accepts
  have h_site :
      HasTypeAtNominalAdtBoundaryAtSite site nominalOpaqueUserIdEnv (.var "x")
        (.opaque "UserId" .nil) :=
    (hasTypeAtNominalAdtBoundaryAtSite_iff_ascription site
      nominalOpaqueUserIdEnv (.var "x") (.opaque "UserId" .nil)).2 h_ascr
  exact (inferNominalAscriptionAtSite_iff site
    nominalOpaqueUserIdEnv (.var "x") (.opaque "UserId" .nil)).2 h_site

/-- Packaged algorithmic nominal ascription slice at any boundary site. -/
def NominalAdtAscriptionAlgorithmicSliceAtSite
    (site : NominalAdtBoundarySite) : Prop :=
  inferNominalAscriptionAtSite site nominalSumBEnv (.var "x") (.sum "A" .nil) = none
  ∧
  inferNominalAscriptionAtSite site nominalOpaqueOrderIdEnv (.var "x")
    (.opaque "UserId" .nil) = none
  ∧
  inferNominalAscriptionAtSite site nominalSumAEnv (.var "x") (.sum "A" .nil) =
    some (.sum "A" .nil)
  ∧
  inferNominalAscriptionAtSite site nominalOpaqueUserIdEnv (.var "x")
    (.opaque "UserId" .nil) = some (.opaque "UserId" .nil)

/-- Proof witness for `NominalAdtAscriptionAlgorithmicSliceAtSite`. -/
theorem nominalAdtAscriptionAlgorithmicSliceAtSite_proved
    (site : NominalAdtBoundarySite) :
    NominalAdtAscriptionAlgorithmicSliceAtSite site := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact inferNominalAscriptionAtSite_sum_name_mismatch site
  · exact inferNominalAscriptionAtSite_opaque_name_mismatch site
  · exact inferNominalAscriptionAtSite_sum_identity site
  · exact inferNominalAscriptionAtSite_opaque_identity site
