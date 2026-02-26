import Kea.Typing
import Kea.Properties.RuntimeWrapperParity
import Kea.Properties.BoundaryAssignability

/-!
  Kea.Properties.DynamicBoundaryTypingBridge

  Small language-level bridge: connect the Dynamic boundary policy to the
  declarative core typing judgment.
-/

/-- Canonical core-typing witness: a variable bound to `Dynamic` has type
    `Dynamic`. -/
theorem hasType_var_dynamic :
    HasType [("x", .dynamic)] (.var "x") .dynamic := by
  exact HasType.var [("x", .dynamic)] "x" .dynamic (by simp [TermEnv.lookup])

/-- In the same environment, implicit `Dynamic -> Int` narrowing is not
    derivable in declarative core typing. -/
theorem hasType_var_dynamic_not_int :
    ¬ HasType [("x", .dynamic)] (.var "x") .int := by
  intro h
  cases h with
  | var env name ty h_lookup =>
      simp [TermEnv.lookup] at h_lookup

/-- Core app witness expression used for Dynamic argument boundary checks. -/
abbrev dynArgAppExpr : CoreExpr := .app (.var "f") (.var "x")

/-- Environment where `f` expects an `Int` argument and `x` is `Dynamic`. -/
abbrev dynArgIntEnv : TermEnv :=
  [("f", .function (.cons .int .nil) .int), ("x", .dynamic)]

/-- Environment where both `f` and `x` are Dynamic-compatible. -/
abbrev dynArgDynEnv : TermEnv :=
  [("f", .function (.cons .dynamic .nil) .dynamic), ("x", .dynamic)]

/-- In `dynArgIntEnv`, `x` does not have type `Int`. -/
theorem hasType_var_x_not_int_in_dynArgIntEnv :
    ¬ HasType dynArgIntEnv (.var "x") .int := by
  intro h
  cases h with
  | var env name ty h_lookup =>
      simp [TermEnv.lookup] at h_lookup

/-- Call-argument bridge (negative path):
    passing `Dynamic` where `Int` is required is not derivable in core typing. -/
theorem hasType_app_dynamic_arg_not_int :
    ¬ HasType dynArgIntEnv dynArgAppExpr .int := by
  intro h
  cases h with
  | app env fn arg paramTy retTy h_fn h_arg =>
      have h_param : paramTy = .int := by
        cases h_fn with
        | var env' name ty h_lookup =>
            simp [TermEnv.lookup] at h_lookup
            cases h_lookup
            rfl
      subst h_param
      exact hasType_var_x_not_int_in_dynArgIntEnv h_arg

/-- Call-argument bridge (positive control):
    Dynamic-compatible app remains derivable when the function expects Dynamic. -/
theorem hasType_app_dynamic_arg_dynamic :
    HasType dynArgDynEnv dynArgAppExpr .dynamic := by
  refine HasType.app dynArgDynEnv (.var "f") (.var "x") .dynamic .dynamic ?_ ?_
  · exact HasType.var dynArgDynEnv "f" (.function (.cons .dynamic .nil) .dynamic) (by
      simp [TermEnv.lookup])
  · exact HasType.var dynArgDynEnv "x" .dynamic (by
      simp [TermEnv.lookup])

/-- Core let witness expression used for Dynamic let-boundary checks. -/
abbrev dynLetExpr : CoreExpr := .letE "y" (.var "x") (.var "y")

/-- In `x : Dynamic` environment, the let-bound expression cannot be typed as
    `Int` via implicit narrowing. -/
theorem hasType_let_dynamic_not_int :
    ¬ HasType [("x", .dynamic)] dynLetExpr .int := by
  intro h
  cases h with
  | letE env name value body valueTy bodyTy h_value h_body =>
      have h_value_int : valueTy = .int := by
        cases h_body with
        | var env' varName ty h_lookup =>
            simp [TermEnv.lookup] at h_lookup
            cases h_lookup
            rfl
      subst h_value_int
      exact hasType_var_dynamic_not_int h_value

/-- Positive let control: let-bound Dynamic value remains typable as Dynamic. -/
theorem hasType_let_dynamic_dynamic :
    HasType [("x", .dynamic)] dynLetExpr .dynamic := by
  refine HasType.letE [("x", .dynamic)] "y" (.var "x") (.var "y") .dynamic .dynamic ?_ ?_
  · exact hasType_var_dynamic
  · exact HasType.var [("y", .dynamic), ("x", .dynamic)] "y" .dynamic (by
      simp [TermEnv.lookup])

/-- Core lambda witness expression used for Dynamic return-boundary checks. -/
abbrev dynLamExpr : CoreExpr := .lam "x" .dynamic (.var "x")

/-- Return-path bridge (negative path):
    lambda body `x : Dynamic` cannot inhabit an `Int` return slot implicitly. -/
theorem hasType_lam_dynamic_not_int_return :
    ¬ HasType [] dynLamExpr (.function (.cons .dynamic .nil) .int) := by
  intro h
  cases h with
  | lam env param paramTy bodyTy body h_body =>
      exact hasType_var_dynamic_not_int h_body

/-- Return-path positive control:
    the same lambda is typable with Dynamic return. -/
theorem hasType_lam_dynamic_dynamic_return :
    HasType [] dynLamExpr (.function (.cons .dynamic .nil) .dynamic) := by
  refine HasType.lam [] "x" .dynamic .dynamic (.var "x") ?_
  exact hasType_var_dynamic

/-- Modeled Dynamic boundary gate at a chosen boundary site:
    expression `e` can inhabit `expected` at ascription boundary iff it has
    some actual type accepted by Dynamic boundary policy at `.ascription`. -/
def HasTypeAtAscriptionBoundaryAtSite
    (site : DynamicBoundarySite)
    (env : TermEnv) (e : CoreExpr) (expected : Ty) : Prop :=
  HasTypeAtBoundary
    (allowsByBool (dynamicBoundaryAllowsAtSite site))
    env e expected

/-- Modeled Dynamic ascription boundary gate (site-specialized alias). -/
abbrev HasTypeAtAscriptionBoundary
    (env : TermEnv) (e : CoreExpr) (expected : Ty) : Prop :=
  HasTypeAtAscriptionBoundaryAtSite .ascription env e expected

/-- Dynamic typing gate is site-invariant because Dynamic boundary policy is
    currently site-invariant. -/
theorem hasTypeAtAscriptionBoundaryAtSite_iff_ascription
    (site : DynamicBoundarySite)
    (env : TermEnv) (e : CoreExpr) (expected : Ty) :
    HasTypeAtAscriptionBoundaryAtSite site env e expected
      ↔ HasTypeAtAscriptionBoundary env e expected := by
  refine hasTypeAtBoundary_congr
    (allowsByBool (dynamicBoundaryAllowsAtSite site))
    (allowsByBool (dynamicBoundaryAllowsAtSite .ascription))
    env e expected ?_
  intro exp act
  have h_site :
      dynamicBoundaryAllowsAtSite site exp act
        = dynamicBoundaryAllowsAtSite .ascription exp act :=
    dynamic_boundary_policy_site_invariant site .ascription exp act
  unfold allowsByBool
  simp [h_site]

/-- For `x : Dynamic`, any declarative typing of `x` resolves to `Dynamic`. -/
theorem hasType_var_dynamic_unique
    (ty : Ty)
    (h_ty : HasType [("x", .dynamic)] (.var "x") ty) :
    ty = .dynamic := by
  cases h_ty with
  | var env name ty' h_lookup =>
      simpa [TermEnv.lookup] using h_lookup.symm

/-- Ascription bridge (negative path):
    a Dynamic value cannot inhabit `Int` at the ascription boundary. -/
theorem hasType_ascription_dynamic_to_int_rejected :
    ¬ HasTypeAtAscriptionBoundary [("x", .dynamic)] (.var "x") .int := by
  intro h
  rcases h with ⟨actual, h_ty, h_allow⟩
  have h_actual : actual = .dynamic := hasType_var_dynamic_unique actual h_ty
  subst h_actual
  have h_reject : dynamicBoundaryAllowsAtSite .ascription .int .dynamic = false :=
    dynamic_boundary_rejects_int_from_dynamic_all_sites .ascription
  unfold allowsByBool at h_allow
  have : False := by
    simp [h_reject] at h_allow
  exact this.elim

/-- Ascription bridge (positive control):
    Dynamic-preserving ascription remains accepted. -/
theorem hasType_ascription_dynamic_to_dynamic_accepts :
    HasTypeAtAscriptionBoundary [("x", .dynamic)] (.var "x") .dynamic := by
  refine ⟨.dynamic, hasType_var_dynamic, ?_⟩
  exact dynamic_boundary_allows_dynamic_from_any_all_sites .ascription .dynamic

/-- Packaged bridge: Dynamic boundary-policy rejection aligns with the
    declarative core typing surface for a simple variable boundary case. -/
theorem dynamic_boundary_typing_bridge_var
    (site : DynamicBoundarySite) :
    dynamicBoundaryAllowsAtSite site .int .dynamic = false
    ∧ HasType [("x", .dynamic)] (.var "x") .dynamic
    ∧ ¬ HasType [("x", .dynamic)] (.var "x") .int := by
  refine ⟨?_, hasType_var_dynamic, hasType_var_dynamic_not_int⟩
  exact dynamic_boundary_rejects_int_from_dynamic_all_sites site

/-- Packaged bridge for Dynamic call-argument boundaries in core typing:
    a Dynamic argument cannot inhabit an `Int` parameter path, while a
    Dynamic-compatible function path remains typable. -/
theorem dynamic_boundary_typing_bridge_app
    (site : DynamicBoundarySite) :
    dynamicBoundaryAllowsAtSite site .int .dynamic = false
    ∧ ¬ HasType dynArgIntEnv dynArgAppExpr .int
    ∧ HasType dynArgDynEnv dynArgAppExpr .dynamic := by
  refine ⟨?_, hasType_app_dynamic_arg_not_int, hasType_app_dynamic_arg_dynamic⟩
  exact dynamic_boundary_rejects_int_from_dynamic_all_sites site

/-- Packaged bridge for Dynamic let-boundary behavior in core typing:
    implicit Dynamic->Int narrowing through let-binding is not derivable, while
    Dynamic-preserving let paths remain typable. -/
theorem dynamic_boundary_typing_bridge_let
    (site : DynamicBoundarySite) :
    dynamicBoundaryAllowsAtSite site .int .dynamic = false
    ∧ ¬ HasType [("x", .dynamic)] dynLetExpr .int
    ∧ HasType [("x", .dynamic)] dynLetExpr .dynamic := by
  refine ⟨?_, hasType_let_dynamic_not_int, hasType_let_dynamic_dynamic⟩
  exact dynamic_boundary_rejects_int_from_dynamic_all_sites site

/-- Packaged bridge for Dynamic return boundaries in core typing:
    implicit Dynamic->Int return narrowing is not derivable, while
    Dynamic-preserving return paths remain typable. -/
theorem dynamic_boundary_typing_bridge_return
    (site : DynamicBoundarySite) :
    dynamicBoundaryAllowsAtSite site .int .dynamic = false
    ∧ ¬ HasType [] dynLamExpr (.function (.cons .dynamic .nil) .int)
    ∧ HasType [] dynLamExpr (.function (.cons .dynamic .nil) .dynamic) := by
  refine ⟨?_, hasType_lam_dynamic_not_int_return, hasType_lam_dynamic_dynamic_return⟩
  exact dynamic_boundary_rejects_int_from_dynamic_all_sites site

/-- Packaged bridge for Dynamic ascription boundaries:
    modeled ascription gate rejects Dynamic->Int and accepts Dynamic->Dynamic. -/
theorem dynamic_boundary_typing_bridge_ascription :
    dynamicBoundaryAllowsAtSite .ascription .int .dynamic = false
    ∧ ¬ HasTypeAtAscriptionBoundary [("x", .dynamic)] (.var "x") .int
    ∧ HasTypeAtAscriptionBoundary [("x", .dynamic)] (.var "x") .dynamic := by
  refine ⟨?_, hasType_ascription_dynamic_to_int_rejected,
    hasType_ascription_dynamic_to_dynamic_accepts⟩
  exact dynamic_boundary_rejects_int_from_dynamic_all_sites .ascription

/-- Site-generalized Dynamic ascription bridge:
    Dynamic ascription bridge outcomes are preserved at all
    boundary-sensitive sites. -/
theorem dynamic_boundary_typing_bridge_ascription_all_sites
    (site : DynamicBoundarySite) :
    dynamicBoundaryAllowsAtSite site .int .dynamic = false
    ∧ ¬ HasTypeAtAscriptionBoundaryAtSite site [("x", .dynamic)] (.var "x") .int
    ∧ HasTypeAtAscriptionBoundaryAtSite site [("x", .dynamic)] (.var "x") .dynamic := by
  rcases dynamic_boundary_typing_bridge_ascription with
    ⟨h_reject, h_narrow, h_accept⟩
  refine ⟨?_, ?_, ?_⟩
  · exact dynamic_boundary_rejects_int_from_dynamic_all_sites site
  · intro h
    have h_ascr :
        HasTypeAtAscriptionBoundary [("x", .dynamic)] (.var "x") .int :=
      (hasTypeAtAscriptionBoundaryAtSite_iff_ascription site
        [("x", .dynamic)] (.var "x") .int).1 h
    exact h_narrow h_ascr
  · exact (hasTypeAtAscriptionBoundaryAtSite_iff_ascription site
      [("x", .dynamic)] (.var "x") .dynamic).2 h_accept
