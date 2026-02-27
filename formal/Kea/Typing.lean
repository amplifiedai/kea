/-
  Kea.Typing — Minimal core expression typing model.

  This module introduces a small expression language and a syntax-directed
  inference function plus declarative typing judgment. It is intentionally
  narrow: literals, variables, closed anonymous records, and field projection.

  Purpose: provide a first M4 anchor for algorithmic-vs-declarative soundness
  over the current row-polymorphic core, without requiring full parser/runtime
  expression coverage.
-/

import Kea.Ty
import Kea.Properties.UnifyReflexive
import Kea.Properties.UnifyConsistent
import Kea.Properties.SubstCompose
import Kea.Unify
import Kea.Substitution

/-- Term environment for the core typing model. -/
abbrev TermEnv := List (String × Ty)

namespace TermEnv

/-- Lookup a variable in the term environment (first binding wins). -/
def lookup (env : TermEnv) (name : String) : Option Ty :=
  match env with
  | [] => none
  | (n, ty) :: rest => if n == name then some ty else lookup rest name

end TermEnv

mutual
  /-- Minimal core expressions for M4 typing-soundness kickoff. -/
  inductive CoreExpr : Type where
    | intLit : Int → CoreExpr
    | boolLit : Bool → CoreExpr
    | stringLit : String → CoreExpr
    | var : String → CoreExpr
    | lam : String → Ty → CoreExpr → CoreExpr
    | app : CoreExpr → CoreExpr → CoreExpr
    | letE : String → CoreExpr → CoreExpr → CoreExpr
    | record : CoreFields → CoreExpr
    | proj : CoreExpr → Label → CoreExpr

  /-- Field syntax for core anonymous records. -/
  inductive CoreFields : Type where
    | nil : CoreFields
    | cons : Label → CoreExpr → CoreFields → CoreFields
end

mutual
  /-- Algorithmic inference for core expressions. -/
  def inferExpr (env : TermEnv) : CoreExpr → Option Ty
    | .intLit _ => some .int
    | .boolLit _ => some .bool
    | .stringLit _ => some .string
    | .var name => TermEnv.lookup env name
    | .lam param paramTy body =>
      match inferExpr ((param, paramTy) :: env) body with
      | some bodyTy => some (.function (.cons paramTy .nil) bodyTy)
      | none => none
    | .app fn arg =>
      match inferExpr env fn, inferExpr env arg with
      | some (.function (.cons paramTy .nil) retTy), some argTy =>
        if beqTy paramTy argTy then some retTy else none
      | _, _ => none
    | .letE name value body =>
      match inferExpr env value with
      | some valueTy => inferExpr ((name, valueTy) :: env) body
      | none => none
    | .record fields =>
      match inferFields env fields with
      | some rowFields => some (.anonRecord (.mk rowFields none))
      | none => none
    | .proj e label =>
      match inferExpr env e with
      | some (.anonRecord (.mk rowFields none)) => RowFields.get rowFields label
      | _ => none

  /-- Algorithmic inference for core record fields. -/
  def inferFields (env : TermEnv) : CoreFields → Option RowFields
    | .nil => some .nil
    | .cons label e rest =>
      match inferExpr env e, inferFields env rest with
      | some ty, some restFields => some (.cons label ty restFields)
      | _, _ => none
end

mutual
  /-- Declarative typing judgment for core expressions. -/
  inductive HasType : TermEnv → CoreExpr → Ty → Prop where
    | int (env : TermEnv) (n : Int) :
        HasType env (.intLit n) .int
    | bool (env : TermEnv) (b : Bool) :
        HasType env (.boolLit b) .bool
    | string (env : TermEnv) (s : String) :
        HasType env (.stringLit s) .string
    | var (env : TermEnv) (name : String) (ty : Ty)
        (h_lookup : TermEnv.lookup env name = some ty) :
        HasType env (.var name) ty
    | lam (env : TermEnv) (param : String) (paramTy bodyTy : Ty) (body : CoreExpr)
        (h_body : HasType ((param, paramTy) :: env) body bodyTy) :
        HasType env (.lam param paramTy body) (.function (.cons paramTy .nil) bodyTy)
    | app (env : TermEnv) (fn arg : CoreExpr) (paramTy retTy : Ty)
        (h_fn : HasType env fn (.function (.cons paramTy .nil) retTy))
        (h_arg : HasType env arg paramTy) :
        HasType env (.app fn arg) retTy
    | letE (env : TermEnv) (name : String) (value body : CoreExpr) (valueTy bodyTy : Ty)
        (h_value : HasType env value valueTy)
        (h_body : HasType ((name, valueTy) :: env) body bodyTy) :
        HasType env (.letE name value body) bodyTy
    | record (env : TermEnv) (fields : CoreFields) (rowFields : RowFields)
        (h_fields : HasFieldsType env fields rowFields) :
        HasType env (.record fields) (.anonRecord (.mk rowFields none))
    | proj (env : TermEnv) (e : CoreExpr) (rowFields : RowFields) (label : Label) (ty : Ty)
        (h_e : HasType env e (.anonRecord (.mk rowFields none)))
        (h_get : RowFields.get rowFields label = some ty) :
        HasType env (.proj e label) ty

  /-- Declarative typing judgment for core record field syntax. -/
  inductive HasFieldsType : TermEnv → CoreFields → RowFields → Prop where
    | nil (env : TermEnv) :
        HasFieldsType env .nil .nil
    | cons (env : TermEnv) (label : Label) (e : CoreExpr) (rest : CoreFields)
        (ty : Ty) (restFields : RowFields)
        (h_head : HasType env e ty)
        (h_rest : HasFieldsType env rest restFields) :
        HasFieldsType env (.cons label e rest) (.cons label ty restFields)
end

mutual
  /--
  Unification-aware declarative typing: same core rules as `HasType`, plus an
  explicit substitution admissibility rule.
  -/
  inductive HasTypeU : TermEnv → CoreExpr → Ty → Prop where
    | int (env : TermEnv) (n : Int) :
        HasTypeU env (.intLit n) .int
    | bool (env : TermEnv) (b : Bool) :
        HasTypeU env (.boolLit b) .bool
    | string (env : TermEnv) (s : String) :
        HasTypeU env (.stringLit s) .string
    | var (env : TermEnv) (name : String) (ty : Ty)
        (h_lookup : TermEnv.lookup env name = some ty) :
        HasTypeU env (.var name) ty
    | lam (env : TermEnv) (param : String) (paramTy bodyTy : Ty) (body : CoreExpr)
        (h_body : HasTypeU ((param, paramTy) :: env) body bodyTy) :
        HasTypeU env (.lam param paramTy body) (.function (.cons paramTy .nil) bodyTy)
    | app (env : TermEnv) (fn arg : CoreExpr) (paramTy retTy : Ty)
        (h_fn : HasTypeU env fn (.function (.cons paramTy .nil) retTy))
        (h_arg : HasTypeU env arg paramTy) :
        HasTypeU env (.app fn arg) retTy
    | letE (env : TermEnv) (name : String) (value body : CoreExpr) (valueTy bodyTy : Ty)
        (h_value : HasTypeU env value valueTy)
        (h_body : HasTypeU ((name, valueTy) :: env) body bodyTy) :
        HasTypeU env (.letE name value body) bodyTy
    | record (env : TermEnv) (fields : CoreFields) (rowFields : RowFields)
        (h_fields : HasFieldsTypeU env fields rowFields) :
        HasTypeU env (.record fields) (.anonRecord (.mk rowFields none))
    | proj (env : TermEnv) (e : CoreExpr) (rowFields : RowFields) (label : Label) (ty : Ty)
        (h_e : HasTypeU env e (.anonRecord (.mk rowFields none)))
        (h_get : RowFields.get rowFields label = some ty) :
        HasTypeU env (.proj e label) ty
    | subst (env : TermEnv) (e : CoreExpr) (ty : Ty) (s : Subst) (fuel : Nat)
        (h_ty : HasTypeU env e ty) :
        HasTypeU env e (applySubstCompat s fuel ty)

  /-- Field typing for `HasTypeU`. -/
  inductive HasFieldsTypeU : TermEnv → CoreFields → RowFields → Prop where
    | nil (env : TermEnv) :
        HasFieldsTypeU env .nil .nil
    | cons (env : TermEnv) (label : Label) (e : CoreExpr) (rest : CoreFields)
        (ty : Ty) (restFields : RowFields)
        (h_head : HasTypeU env e ty)
        (h_rest : HasFieldsTypeU env rest restFields) :
        HasFieldsTypeU env (.cons label e rest) (.cons label ty restFields)
end

mutual
  /-- Lift monomorphic declarative typing derivations into `HasTypeU`. -/
  theorem hasType_to_hasTypeU
      {env : TermEnv} {e : CoreExpr} {ty : Ty}
      (h_ty : HasType env e ty) :
      HasTypeU env e ty := by
    cases h_ty with
    | int env n => exact HasTypeU.int env n
    | bool env b => exact HasTypeU.bool env b
    | string env s => exact HasTypeU.string env s
    | var env name ty h_lookup => exact HasTypeU.var env name ty h_lookup
    | lam env param paramTy bodyTy body h_body =>
      exact HasTypeU.lam env param paramTy bodyTy body (hasType_to_hasTypeU h_body)
    | app env fn arg paramTy _ h_fn h_arg =>
      exact HasTypeU.app env fn arg paramTy ty
        (hasType_to_hasTypeU h_fn) (hasType_to_hasTypeU h_arg)
    | letE env name value body valueTy _ h_value h_body =>
      exact HasTypeU.letE env name value body valueTy ty
        (hasType_to_hasTypeU h_value) (hasType_to_hasTypeU h_body)
    | record env fields rowFields h_fields =>
      exact HasTypeU.record env fields rowFields (hasFieldsType_to_hasFieldsTypeU h_fields)
    | proj env e rowFields label ty h_e h_get =>
      exact HasTypeU.proj env e rowFields label ty (hasType_to_hasTypeU h_e) h_get

  /-- Lift monomorphic field typing derivations into `HasFieldsTypeU`. -/
  theorem hasFieldsType_to_hasFieldsTypeU
      {env : TermEnv} {fs : CoreFields} {rowFields : RowFields}
      (h_fs : HasFieldsType env fs rowFields) :
      HasFieldsTypeU env fs rowFields := by
    cases h_fs with
    | nil env => exact HasFieldsTypeU.nil env
    | cons env label e rest ty restFields h_head h_rest =>
      exact HasFieldsTypeU.cons env label e rest ty restFields
        (hasType_to_hasTypeU h_head) (hasFieldsType_to_hasFieldsTypeU h_rest)
end

mutual
  /-- Algorithmic inference is sound with respect to declarative typing. -/
  theorem inferExpr_sound (env : TermEnv) (e : CoreExpr) :
      ∀ ty, inferExpr env e = some ty → HasType env e ty := by
    cases e with
    | intLit n =>
      intro ty h
      simp [inferExpr] at h
      cases h
      exact HasType.int env n
    | boolLit b =>
      intro ty h
      simp [inferExpr] at h
      cases h
      exact HasType.bool env b
    | stringLit s =>
      intro ty h
      simp [inferExpr] at h
      cases h
      exact HasType.string env s
    | var name =>
      intro ty h
      simp [inferExpr] at h
      exact HasType.var env name ty h
    | lam param paramTy body =>
      intro ty h
      simp [inferExpr] at h
      cases h_body : inferExpr ((param, paramTy) :: env) body with
      | none =>
        simp [h_body] at h
      | some bodyTy =>
        simp [h_body] at h
        cases h
        exact HasType.lam env param paramTy bodyTy body
          (inferExpr_sound ((param, paramTy) :: env) body bodyTy h_body)
    | app fn arg =>
      intro ty h
      simp [inferExpr] at h
      cases h_fn : inferExpr env fn with
      | none =>
        simp [h_fn] at h
      | some fnTy =>
        cases h_arg : inferExpr env arg with
        | none =>
          simp [h_fn, h_arg] at h
        | some argTy =>
          cases fnTy with
          | function params retTy =>
            cases params with
            | nil =>
              simp [h_fn, h_arg] at h
            | cons paramTy rest =>
              cases rest with
              | nil =>
                cases h_eq : beqTy paramTy argTy with
                | false =>
                  simp [h_fn, h_arg, h_eq] at h
                | true =>
                  simp [h_fn, h_arg, h_eq] at h
                  cases h
                  have h_param_eq : paramTy = argTy := beqTy_sound paramTy argTy h_eq
                  have h_fn_eq : inferExpr env fn = some (.function (.cons paramTy .nil) ty) := by
                    simpa using h_fn
                  have h_fn_ty : HasType env fn (.function (.cons paramTy .nil) ty) :=
                    inferExpr_sound env fn (.function (.cons paramTy .nil) ty) h_fn_eq
                  have h_arg_ty : HasType env arg argTy :=
                    inferExpr_sound env arg argTy h_arg
                  rw [← h_param_eq] at h_arg_ty
                  exact HasType.app env fn arg paramTy ty h_fn_ty h_arg_ty
              | cons _ _ =>
                simp [h_fn, h_arg] at h
          | int | intN _ _ | float | floatN _ | decimal _ _ | bool | string | html | markdown | atom | date | dateTime | unit =>
            simp [h_fn, h_arg] at h
          | list _ | map _ _ | set _ | option _ | result _ _ | existential _ _ | fixedSizeList _ _ | tensor _ _ | sum _ _ | «opaque» _ _ | functionEff _ _ _
            | record _ _ | anonRecord _ | dataframe _ | groupedFrame _ _ | tagged _ _ | dynamic | column _ | stream _ | task _ | actor _ | arc _
            | «forall» _ _ | app _ _ | constructor _ _ _ | var _ | row _ | tuple _ =>
            simp [h_fn, h_arg] at h
    | letE name value body =>
      intro ty h
      simp [inferExpr] at h
      cases h_value : inferExpr env value with
      | none =>
        simp [h_value] at h
      | some valueTy =>
        have h_value_ty : HasType env value valueTy :=
          inferExpr_sound env value valueTy h_value
        have h_body_ty : HasType ((name, valueTy) :: env) body ty := by
          exact inferExpr_sound ((name, valueTy) :: env) body ty (by simpa [h_value] using h)
        exact HasType.letE env name value body valueTy ty h_value_ty h_body_ty
    | record fields =>
      intro ty h
      simp [inferExpr] at h
      cases h_fields : inferFields env fields with
      | none =>
        simp [h_fields] at h
      | some rowFields =>
        simp [h_fields] at h
        cases h
        exact HasType.record env fields rowFields
          (inferFields_sound env fields rowFields h_fields)
    | proj e label =>
      intro ty h
      simp [inferExpr] at h
      cases h_e : inferExpr env e with
      | none =>
        simp [h_e] at h
      | some tySub =>
        cases tySub with
        | int | intN _ _ | float | floatN _ | decimal _ _ | bool | string | html | markdown | atom | date | dateTime | unit =>
          simp [h_e] at h
        | list _ | map _ _ | set _ | option _ | result _ _ | existential _ _ | fixedSizeList _ _ | tensor _ _ | sum _ _ | «opaque» _ _
          | record _ _ | dataframe _ | groupedFrame _ _ | tagged _ _ | dynamic | column _ | stream _ | task _ | actor _ | arc _
          | function _ _ | functionEff _ _ _ | «forall» _ _ | app _ _ | constructor _ _ _ | var _ | row _ | tuple _ =>
          simp [h_e] at h
        | anonRecord row =>
          cases row with
          | mk rowFields rest =>
            cases rest with
            | some rv =>
              simp [h_e] at h
            | none =>
              cases h_get : RowFields.get rowFields label with
              | none =>
                simp [h_e, h_get] at h
              | some foundTy =>
                simp [h_e, h_get] at h
                cases h
                have h_sub : HasType env e (.anonRecord (.mk rowFields none)) :=
                  inferExpr_sound env e (.anonRecord (.mk rowFields none)) h_e
                exact HasType.proj env e rowFields label ty h_sub h_get

  /-- Field inference is sound with respect to declarative field typing. -/
  theorem inferFields_sound (env : TermEnv) (fs : CoreFields) :
      ∀ rowFields, inferFields env fs = some rowFields → HasFieldsType env fs rowFields := by
    cases fs with
    | nil =>
      intro rowFields h
      simp [inferFields] at h
      cases h
      exact HasFieldsType.nil env
    | cons label e rest =>
      intro rowFields h
      simp [inferFields] at h
      cases h_e : inferExpr env e <;> simp [h_e] at h
      case _ tyHead =>
        cases h_rest : inferFields env rest <;> simp [h_rest] at h
        case _ restFields =>
          cases h
          exact HasFieldsType.cons env label e rest tyHead restFields
            (inferExpr_sound env e tyHead h_e)
            (inferFields_sound env rest restFields h_rest)
end

mutual
  /-- Declarative typing is complete with respect to algorithmic inference. -/
  theorem inferExpr_complete
      (env : TermEnv) (e : CoreExpr) (ty : Ty)
      (h_ty : HasType env e ty) :
      inferExpr env e = some ty := by
    cases h_ty with
    | int env n =>
      simp [inferExpr]
    | bool env b =>
      simp [inferExpr]
    | string env s =>
      simp [inferExpr]
    | var env name ty h_lookup =>
      simpa [inferExpr] using h_lookup
    | lam env param paramTy bodyTy body h_body =>
      simp [inferExpr, inferExpr_complete ((param, paramTy) :: env) body bodyTy h_body]
    | app env fn arg paramTy retTy h_fn h_arg =>
      simp [inferExpr,
        inferExpr_complete env fn (.function (.cons paramTy .nil) ty) h_fn,
        inferExpr_complete env arg paramTy h_arg,
        beqTy_refl paramTy]
    | letE env name value body valueTy bodyTy h_value h_body =>
      simp [inferExpr,
        inferExpr_complete env value valueTy h_value,
        inferExpr_complete ((name, valueTy) :: env) body ty h_body]
    | record env fields rowFields h_fields =>
      simp [inferExpr, inferFields_complete env fields rowFields h_fields]
    | proj env e rowFields label ty h_e h_get =>
      simp [inferExpr, inferExpr_complete env e (.anonRecord (.mk rowFields none)) h_e, h_get]

  /-- Declarative field typing is complete wrt algorithmic field inference. -/
  theorem inferFields_complete
      (env : TermEnv) (fs : CoreFields) (rowFields : RowFields)
      (h_fs : HasFieldsType env fs rowFields) :
      inferFields env fs = some rowFields := by
    cases h_fs with
    | nil env =>
      simp [inferFields]
    | cons env label e rest ty restFields h_head h_rest =>
      simp [inferFields, inferExpr_complete env e ty h_head, inferFields_complete env rest restFields h_rest]
end

/-- Algorithmic and declarative typing coincide on the current core slice. -/
theorem inferExpr_iff_hasType (env : TermEnv) (e : CoreExpr) (ty : Ty) :
    inferExpr env e = some ty ↔ HasType env e ty := by
  constructor
  · intro h
    exact inferExpr_sound env e ty h
  · intro h
    exact inferExpr_complete env e ty h

/-- Declarative field typing is functional on the core slice. -/
theorem hasFieldsType_unique
    {env : TermEnv} {fs : CoreFields} {row₁ row₂ : RowFields}
    (h₁ : HasFieldsType env fs row₁)
    (h₂ : HasFieldsType env fs row₂) :
    row₁ = row₂ := by
  have h_inf₁ : inferFields env fs = some row₁ := inferFields_complete env fs row₁ h₁
  have h_inf₂ : inferFields env fs = some row₂ := inferFields_complete env fs row₂ h₂
  rw [h_inf₁] at h_inf₂
  exact Option.some.inj h_inf₂

/-- Principal-field-typing corollary from one successful `inferFields` run. -/
theorem inferFields_principal
    {env : TermEnv} {fs : CoreFields} {row : RowFields}
    (h_inf : inferFields env fs = some row) :
    ∀ {row' : RowFields}, HasFieldsType env fs row' → row' = row := by
  intro row' h_row'
  have h_row : HasFieldsType env fs row := inferFields_sound env fs row h_inf
  exact hasFieldsType_unique h_row' h_row

/-- Declarative typing is functional on the core slice. -/
theorem hasType_unique
    {env : TermEnv} {e : CoreExpr} {ty₁ ty₂ : Ty}
    (h₁ : HasType env e ty₁)
    (h₂ : HasType env e ty₂) :
    ty₁ = ty₂ := by
  have h_inf₁ : inferExpr env e = some ty₁ := inferExpr_complete env e ty₁ h₁
  have h_inf₂ : inferExpr env e = some ty₂ := inferExpr_complete env e ty₂ h₂
  rw [h_inf₁] at h_inf₂
  exact Option.some.inj h_inf₂

/-- Principal-typing corollary from one successful `inferExpr` run. -/
theorem inferExpr_principal
    {env : TermEnv} {e : CoreExpr} {ty : Ty}
    (h_inf : inferExpr env e = some ty) :
    ∀ {ty' : Ty}, HasType env e ty' → ty' = ty := by
  intro ty' h_ty'
  have h_ty : HasType env e ty := inferExpr_sound env e ty h_inf
  exact hasType_unique h_ty' h_ty

/-- Packaged principal-typing surface for core `inferExpr`. -/
structure PrincipalTypingSliceCore
    (env : TermEnv) (e : CoreExpr) (ty : Ty) : Prop where
  sound : HasType env e ty
  unique : ∀ {ty' : Ty}, HasType env e ty' → ty' = ty

/-- Packaged principal-field-typing surface for core `inferFields`. -/
structure PrincipalFieldTypingSliceCore
    (env : TermEnv) (fs : CoreFields) (row : RowFields) : Prop where
  sound : HasFieldsType env fs row
  unique : ∀ {row' : RowFields}, HasFieldsType env fs row' → row' = row

/-- Build the core principal-typing bundle from `inferExpr` success. -/
theorem principalTypingSliceCore_of_infer
    {env : TermEnv} {e : CoreExpr} {ty : Ty}
    (h_inf : inferExpr env e = some ty) :
    PrincipalTypingSliceCore env e ty := by
  refine {
    sound := inferExpr_sound env e ty h_inf
    unique := ?_
  }
  intro ty' h_ty'
  exact inferExpr_principal h_inf h_ty'

/-- Build the core principal-field-typing bundle from `inferFields` success. -/
theorem principalFieldTypingSliceCore_of_infer
    {env : TermEnv} {fs : CoreFields} {row : RowFields}
    (h_inf : inferFields env fs = some row) :
    PrincipalFieldTypingSliceCore env fs row := by
  refine {
    sound := inferFields_sound env fs row h_inf
    unique := ?_
  }
  intro row' h_row'
  exact inferFields_principal h_inf h_row'

/-- Generic boundary assignability judgment for core expressions. -/
def HasTypeAtCoreBoundary
    (allows : Ty → Ty → Prop)
    (env : TermEnv) (e : CoreExpr) (expected : Ty) : Prop :=
  ∃ actual, HasType env e actual ∧ allows expected actual

/-- Core expressions with an explicit ascription form. -/
inductive CoreExprWithAscription : Type where
  | base : CoreExpr → CoreExprWithAscription
  | ascribe : CoreExpr → Ty → CoreExprWithAscription

/-- Declarative typing for `CoreExprWithAscription` under a boundary relation. -/
inductive HasTypeWithAscription
    (allows : Ty → Ty → Prop)
    : TermEnv → CoreExprWithAscription → Ty → Prop where
  | base (env : TermEnv) (e : CoreExpr) (ty : Ty)
      (h_ty : HasType env e ty) :
      HasTypeWithAscription allows env (.base e) ty
  | ascribe (env : TermEnv) (e : CoreExpr) (expected : Ty)
      (h_boundary : HasTypeAtCoreBoundary allows env e expected) :
      HasTypeWithAscription allows env (.ascribe e expected) expected

/-- `base` nodes in `HasTypeWithAscription` coincide with `HasType`. -/
theorem hasTypeWithAscription_base_iff
    (allows : Ty → Ty → Prop)
    (env : TermEnv) (e : CoreExpr) (ty : Ty) :
    HasTypeWithAscription allows env (.base e) ty
      ↔ HasType env e ty := by
  constructor
  · intro h
    cases h with
    | base _ _ h_ty => exact h_ty
  · intro h_ty
    exact HasTypeWithAscription.base env e ty h_ty

/-- `ascribe` nodes in `HasTypeWithAscription` coincide with core boundary
    assignability at the annotated type. -/
theorem hasTypeWithAscription_ascribe_iff
    (allows : Ty → Ty → Prop)
    (env : TermEnv) (e : CoreExpr) (expected : Ty) :
    HasTypeWithAscription allows env (.ascribe e expected) expected
      ↔ HasTypeAtCoreBoundary allows env e expected := by
  constructor
  · intro h
    cases h with
    | ascribe _ _ h_boundary => exact h_boundary
  · intro h_boundary
    exact HasTypeWithAscription.ascribe env e expected h_boundary

/-- Algorithmic typing for explicit ascription expressions under a boundary
    predicate. -/
def inferExprWithAscription
    (allows : Ty → Ty → Bool)
    (env : TermEnv) : CoreExprWithAscription → Option Ty
  | .base e => inferExpr env e
  | .ascribe e expected =>
    match inferExpr env e with
    | some actual =>
      if allows expected actual then some expected else none
    | none => none

/-- `inferExprWithAscription` is definitionally conservative on `.base`
    expressions. -/
theorem inferExprWithAscription_base_eq
    (allows : Ty → Ty → Bool)
    (env : TermEnv) (e : CoreExpr) :
    inferExprWithAscription allows env (.base e) = inferExpr env e := by
  rfl

/-- On `.base` expressions, `inferExprWithAscription` has exactly the same
    success/failure behavior as `inferExpr`. -/
theorem inferExprWithAscription_base_iff
    (allows : Ty → Ty → Bool)
    (env : TermEnv) (e : CoreExpr) (ty : Ty) :
    inferExprWithAscription allows env (.base e) = some ty
      ↔ inferExpr env e = some ty := by
  simp [inferExprWithAscription_base_eq allows env e]

/-- Soundness of `inferExprWithAscription` with respect to
    `HasTypeWithAscription` instantiated with the boolean boundary relation. -/
theorem inferExprWithAscription_sound
    (allows : Ty → Ty → Bool)
    (env : TermEnv) (e : CoreExprWithAscription) :
    ∀ ty,
      inferExprWithAscription allows env e = some ty →
      HasTypeWithAscription (fun expected actual => allows expected actual = true) env e ty := by
  intro ty h_infer
  cases e with
  | base e =>
    exact HasTypeWithAscription.base env e ty
      (inferExpr_sound env e ty h_infer)
  | ascribe e expected =>
    unfold inferExprWithAscription at h_infer
    cases h_expr : inferExpr env e with
    | none =>
      simp [h_expr] at h_infer
    | some actual =>
      cases h_allow : allows expected actual with
      | false =>
        simp [h_expr, h_allow] at h_infer
      | true =>
        have h_ty_eq : expected = ty := by
          simpa [inferExprWithAscription, h_expr, h_allow] using h_infer
        have h_expected :
            HasTypeWithAscription
              (fun expected actual => allows expected actual = true)
              env
              (.ascribe e expected)
              expected :=
          HasTypeWithAscription.ascribe env e expected
            ⟨actual, inferExpr_sound env e actual h_expr, h_allow⟩
        exact h_ty_eq ▸ h_expected

/-- Completeness of `inferExprWithAscription` with respect to
    `HasTypeWithAscription` instantiated with the boolean boundary relation. -/
theorem inferExprWithAscription_complete
    (allows : Ty → Ty → Bool)
    (env : TermEnv) (e : CoreExprWithAscription) (ty : Ty)
    (h_ty : HasTypeWithAscription (fun expected actual => allows expected actual = true) env e ty) :
    inferExprWithAscription allows env e = some ty := by
  cases h_ty with
  | base _ _ h_base =>
    have h_infer_base : inferExpr env _ = some ty :=
      inferExpr_complete env _ ty h_base
    simpa [inferExprWithAscription] using h_infer_base
  | ascribe _ _ h_boundary =>
    rcases h_boundary with ⟨actual, h_actual, h_allow⟩
    have h_infer_actual : inferExpr env _ = some actual :=
      inferExpr_complete env _ actual h_actual
    simp [inferExprWithAscription, h_infer_actual, h_allow]

/-- Algorithmic and declarative ascription typing coincide for
    `inferExprWithAscription`. -/
theorem inferExprWithAscription_iff_hasTypeWithAscription
    (allows : Ty → Ty → Bool)
    (env : TermEnv) (e : CoreExprWithAscription) (ty : Ty) :
    inferExprWithAscription allows env e = some ty
      ↔ HasTypeWithAscription (fun expected actual => allows expected actual = true) env e ty := by
  constructor
  · intro h
    exact inferExprWithAscription_sound allows env e ty h
  · intro h
    exact inferExprWithAscription_complete allows env e ty h

/-- On explicit `ascribe` nodes, algorithmic ascription inference at the
    annotated type is equivalent to core boundary assignability. -/
theorem inferExprWithAscription_ascribe_iff_boundary
    (allows : Ty → Ty → Bool)
    (env : TermEnv) (e : CoreExpr) (expected : Ty) :
    inferExprWithAscription allows env (.ascribe e expected) = some expected
      ↔
      HasTypeAtCoreBoundary
        (fun exp act => allows exp act = true)
        env e expected := by
  constructor
  · intro h_infer
    have h_ty :
        HasTypeWithAscription
          (fun exp act => allows exp act = true)
          env
          (.ascribe e expected)
          expected :=
      (inferExprWithAscription_iff_hasTypeWithAscription
        allows env (.ascribe e expected) expected).1 h_infer
    exact (hasTypeWithAscription_ascribe_iff
      (fun exp act => allows exp act = true) env e expected).1 h_ty
  · intro h_boundary
    have h_ty :
        HasTypeWithAscription
          (fun exp act => allows exp act = true)
          env
          (.ascribe e expected)
          expected :=
      (hasTypeWithAscription_ascribe_iff
        (fun exp act => allows exp act = true) env e expected).2 h_boundary
    exact (inferExprWithAscription_iff_hasTypeWithAscription
      allows env (.ascribe e expected) expected).2 h_ty

private theorem lookup_eq_cons
    {env env' : TermEnv}
    (h_lookup_eq : ∀ n, TermEnv.lookup env n = TermEnv.lookup env' n)
    (x : String) (xTy : Ty) :
    ∀ n, TermEnv.lookup ((x, xTy) :: env) n = TermEnv.lookup ((x, xTy) :: env') n := by
  intro n
  by_cases h : n = x
  · subst h
    simp [TermEnv.lookup]
  · simp [TermEnv.lookup, h_lookup_eq n]

mutual
  /--
  Declarative typing is invariant under lookup-equivalent environments.
  This is a generalized weakening-style transport lemma for the core model.
  -/
  theorem hasType_lookup_congr
      {env env' : TermEnv} {e : CoreExpr} {ty : Ty}
      (h_lookup_eq : ∀ n, TermEnv.lookup env n = TermEnv.lookup env' n) :
      HasType env e ty → HasType env' e ty := by
    intro h_ty
    cases h_ty with
    | int _ n =>
      exact HasType.int env' n
    | bool _ b =>
      exact HasType.bool env' b
    | string _ s =>
      exact HasType.string env' s
    | var _ name ty h_lookup =>
      exact HasType.var env' name ty (by simpa [h_lookup_eq name] using h_lookup)
    | lam _ param paramTy bodyTy body h_body =>
      exact HasType.lam env' param paramTy bodyTy body
        (hasType_lookup_congr (lookup_eq_cons h_lookup_eq param paramTy) h_body)
    | app _ fn arg paramTy _ h_fn h_arg =>
      exact HasType.app env' fn arg paramTy ty
        (hasType_lookup_congr h_lookup_eq h_fn)
        (hasType_lookup_congr h_lookup_eq h_arg)
    | letE _ name value body valueTy _ h_value h_body =>
      exact HasType.letE env' name value body valueTy ty
        (hasType_lookup_congr h_lookup_eq h_value)
        (hasType_lookup_congr (lookup_eq_cons h_lookup_eq name valueTy) h_body)
    | record _ fields rowFields h_fields =>
      exact HasType.record env' fields rowFields
        (hasFieldsType_lookup_congr h_lookup_eq h_fields)
    | proj _ e rowFields label ty h_e h_get =>
      exact HasType.proj env' e rowFields label ty
        (hasType_lookup_congr h_lookup_eq h_e) h_get

  /-- Field typing transport under lookup-equivalent environments. -/
  theorem hasFieldsType_lookup_congr
      {env env' : TermEnv} {fs : CoreFields} {rowFields : RowFields}
      (h_lookup_eq : ∀ n, TermEnv.lookup env n = TermEnv.lookup env' n) :
      HasFieldsType env fs rowFields → HasFieldsType env' fs rowFields := by
    intro h_fs
    cases h_fs with
    | nil _ =>
      exact HasFieldsType.nil env'
    | cons _ label e rest ty restFields h_head h_rest =>
      exact HasFieldsType.cons env' label e rest ty restFields
        (hasType_lookup_congr h_lookup_eq h_head)
        (hasFieldsType_lookup_congr h_lookup_eq h_rest)
end

/-- Algorithmic inference is preserved across lookup-equivalent environments. -/
theorem inferExpr_lookup_congr
    {env env' : TermEnv} {e : CoreExpr} {ty : Ty}
    (h_lookup_eq : ∀ n, TermEnv.lookup env n = TermEnv.lookup env' n) :
    inferExpr env e = some ty ↔ inferExpr env' e = some ty := by
  constructor
  · intro h
    have h_ty : HasType env e ty := (inferExpr_iff_hasType env e ty).1 h
    have h_ty' : HasType env' e ty := hasType_lookup_congr h_lookup_eq h_ty
    exact (inferExpr_iff_hasType env' e ty).2 h_ty'
  · intro h
    have h_lookup_eq_symm : ∀ n, TermEnv.lookup env' n = TermEnv.lookup env n := by
      intro n; symm; exact h_lookup_eq n
    have h_ty : HasType env' e ty := (inferExpr_iff_hasType env' e ty).1 h
    have h_ty' : HasType env e ty := hasType_lookup_congr h_lookup_eq_symm h_ty
    exact (inferExpr_iff_hasType env e ty).2 h_ty'

-- =========================================================================
-- Vertical slice: inference with threaded unification state
-- =========================================================================

/-- Result type for unification-backed expression inference. -/
inductive InferUnifyResult : Type where
  | ok  : UnifyState → Ty → InferUnifyResult
  | err : String → InferUnifyResult

mutual
  /--
  Algorithmic inference that threads `UnifyState` and delegates constraints to
  `unify` (fuel-bounded).
  -/
  def inferExprUnify (st : UnifyState) (fuel : Nat) (env : TermEnv) : CoreExpr → InferUnifyResult
    | .intLit _ => .ok st .int
    | .boolLit _ => .ok st .bool
    | .stringLit _ => .ok st .string
    | .var name =>
      match TermEnv.lookup env name with
      | some ty => .ok st ty
      | none => .err s!"unbound variable: {name}"
    | .lam param paramTy body =>
      match inferExprUnify st fuel ((param, paramTy) :: env) body with
      | .ok st' bodyTy => .ok st' (.function (.cons paramTy .nil) bodyTy)
      | .err e => .err e
    | .app fn arg =>
      match inferExprUnify st fuel env fn with
      | .err e => .err e
      | .ok stFn fnTy =>
        match inferExprUnify stFn fuel env arg with
        | .err e => .err e
        | .ok stArg argTy =>
          let (resVar, stRes) := stArg.freshTypeVar
          let expected := .function (.cons argTy .nil) (.var resVar)
          match unify stRes fuel fnTy expected with
          | .err e => .err e
          | .ok stU =>
            .ok stU (applySubstCompat stU.subst fuel (.var resVar))
    | .letE name value body =>
      match inferExprUnify st fuel env value with
      | .err e => .err e
      | .ok st' valueTy => inferExprUnify st' fuel ((name, valueTy) :: env) body
    | .record fields =>
      match inferFieldsUnify st fuel env fields with
      | .ok st' (.row (.mk rowFields none)) => .ok st' (.anonRecord (.mk rowFields none))
      | .ok _ _ => .err "internal error: expected row type from inferFieldsUnify"
      | .err e => .err e
    | .proj recv label =>
      match inferExprUnify st fuel env recv with
      | .err e => .err e
      | .ok stRecv recvTy =>
        let (fieldVar, stField) := stRecv.freshTypeVar
        let (restVar, stRest) := stField.freshRowVar
        let expected := .anonRecord (.mk (.cons label (.var fieldVar) .nil) (some restVar))
        match unify stRest fuel recvTy expected with
        | .err e => .err e
        | .ok stU =>
          .ok stU (applySubstCompat stU.subst fuel (.var fieldVar))

  /-- Unification-backed field inference (threads state through fields). -/
  def inferFieldsUnify (st : UnifyState) (fuel : Nat) (env : TermEnv) : CoreFields → InferUnifyResult
    | .nil => .ok st (.row (.mk .nil none))
    | .cons label e rest =>
      match inferExprUnify st fuel env e with
      | .err err => .err err
      | .ok stHead tyHead =>
        match inferFieldsUnify stHead fuel env rest with
        | .err err => .err err
        | .ok stRest (.row (.mk restFields none)) =>
          .ok stRest (.row (.mk (.cons label tyHead restFields) none))
        | .ok _ _ => .err "internal error: expected row type from inferFieldsUnify"
end

/-- Project a row-fields payload out of `inferFieldsUnify` results. -/
def inferFieldsUnifyRowFields
    (st : UnifyState) (fuel : Nat) (env : TermEnv) (fs : CoreFields) :
    Option (UnifyState × RowFields) :=
  match inferFieldsUnify st fuel env fs with
  | .ok st' (.row (.mk fields none)) => some (st', fields)
  | _ => none

/-- Soundness hook shape for app branches in `inferExprUnify`. -/
def AppUnifySoundHook : Prop :=
  ∀ env fn arg fnTy argTy stBefore stAfter fuel resVar,
    HasType env fn fnTy →
    HasType env arg argTy →
    unify stBefore fuel fnTy (.function (.cons argTy .nil) (.var resVar)) = .ok stAfter →
    HasType env (.app fn arg) (applySubstCompat stAfter.subst fuel (.var resVar))

/--
Empty-substitution specialization of `AppUnifySoundHook`.
Used to test whether hook closure is possible in the simplest starting state.
-/
def AppUnifySoundHookEmptySubst : Prop :=
  ∀ env fn arg fnTy argTy stBefore stAfter fuel resVar,
    stBefore.subst = Subst.empty →
    HasType env fn fnTy →
    HasType env arg argTy →
    unify stBefore fuel fnTy (.function (.cons argTy .nil) (.var resVar)) = .ok stAfter →
    HasType env (.app fn arg) (applySubstCompat stAfter.subst fuel (.var resVar))

/-- Soundness hook shape for projection branches in `inferExprUnify`. -/
def ProjUnifySoundHook : Prop :=
  ∀ env recv label recvTy stBefore stAfter fuel fieldVar restVar,
    HasType env recv recvTy →
    unify stBefore fuel recvTy (.anonRecord (.mk (.cons label (.var fieldVar) .nil) (some restVar))) = .ok stAfter →
    HasType env (.proj recv label) (applySubstCompat stAfter.subst fuel (.var fieldVar))

/-- `HasTypeU`-targeted app hook shape for `inferExprUnify`. -/
def AppUnifySoundHookU : Prop :=
  ∀ env fn arg fnTy argTy stBefore stAfter fuel resVar,
    HasTypeU env fn fnTy →
    HasTypeU env arg argTy →
    unify stBefore fuel fnTy (.function (.cons argTy .nil) (.var resVar)) = .ok stAfter →
    HasTypeU env (.app fn arg) (applySubstCompat stAfter.subst fuel (.var resVar))

/-- `HasTypeU`-targeted projection hook shape for `inferExprUnify`. -/
def ProjUnifySoundHookU : Prop :=
  ∀ env recv label recvTy stBefore stAfter fuel fieldVar restVar,
    HasTypeU env recv recvTy →
    unify stBefore fuel recvTy (.anonRecord (.mk (.cons label (.var fieldVar) .nil) (some restVar))) = .ok stAfter →
    HasTypeU env (.proj recv label) (applySubstCompat stAfter.subst fuel (.var fieldVar))

/--
Global app-branch resolved-shape premise: successful app unification determines
the resolved function shape at the same fuel.
-/
def AppResolvedShapeFromUnify : Prop :=
  ∀ env fn arg fnTy argTy stBefore stAfter fuel resVar,
    HasTypeU env fn fnTy →
    HasTypeU env arg argTy →
    unify stBefore fuel fnTy (.function (.cons argTy .nil) (.var resVar)) = .ok stAfter →
    applySubstCompat stAfter.subst fuel fnTy =
      .function
        (.cons (applySubstCompat stAfter.subst fuel argTy) .nil)
        (applySubstCompat stAfter.subst fuel (.var resVar))

/--
Global projection-branch resolved-shape premise: successful projection
unification determines a closed resolved receiver row and selected field type.
-/
def ProjResolvedShapeFromUnify : Prop :=
  ∀ env recv label recvTy stBefore stAfter fuel fieldVar restVar,
    HasTypeU env recv recvTy →
    unify stBefore fuel recvTy (.anonRecord (.mk (.cons label (.var fieldVar) .nil) (some restVar))) = .ok stAfter →
    ∃ rowFields,
      applySubstCompat stAfter.subst fuel recvTy = .anonRecord (.mk rowFields none)
      ∧ RowFields.get rowFields label = some (applySubstCompat stAfter.subst fuel (.var fieldVar))

/-- Packaged global resolved-shape premises for app and projection branches. -/
def UnifyResolvedShapePremises : Prop :=
  AppResolvedShapeFromUnify ∧ ProjResolvedShapeFromUnify

/-- Packaged `HasType` hook assumptions for recursive soundness. -/
def UnifyHookPremises : Prop :=
  AppUnifySoundHook ∧ ProjUnifySoundHook

/-- Packaged `HasTypeU` hook assumptions for recursive soundness. -/
def UnifyHookPremisesU : Prop :=
  AppUnifySoundHookU ∧ ProjUnifySoundHookU

/--
Empty-substitution specialization of `ProjUnifySoundHook`.
Used to test whether hook closure is possible in the simplest starting state.
-/
def ProjUnifySoundHookEmptySubst : Prop :=
  ∀ env recv label recvTy stBefore stAfter fuel fieldVar restVar,
    stBefore.subst = Subst.empty →
    HasType env recv recvTy →
    unify stBefore fuel recvTy (.anonRecord (.mk (.cons label (.var fieldVar) .nil) (some restVar))) = .ok stAfter →
    HasType env (.proj recv label) (applySubstCompat stAfter.subst fuel (.var fieldVar))

/--
`AppUnifySoundHook` is not derivable from the current declarative judgment:
unification can succeed by binding a variable-typed function position, while
`HasType.app` requires the function side to already have a function type.
-/
theorem not_AppUnifySoundHook : ¬ AppUnifySoundHook := by
  intro h_app
  let env : TermEnv := [("f", .var 0)]
  let fn : CoreExpr := .var "f"
  let arg : CoreExpr := .intLit 1
  let stBefore : UnifyState := { UnifyState.empty with nextTypeVar := 2 }
  let expected : Ty := .function (.cons .int .nil) (.var 1)
  let stAfter : UnifyState := { stBefore with subst := stBefore.subst.bindType 0 expected }
  have h_fn : HasType env fn (.var 0) := by
    exact HasType.var env "f" (.var 0) (by simp [env, TermEnv.lookup])
  have h_arg : HasType env arg .int := HasType.int env 1
  have h_unify : unify stBefore 1 (.var 0) expected = .ok stAfter := by
    have h_occ : occursInTyList 0 (TyList.cons Ty.int TyList.nil) = false := by
      simp [occursInTyList, occursIn]
    have h_neq1 : (Ty.var 0 == expected) = false := by
      native_decide
    have h_neq2 : (expected == Ty.var 0) = false := by
      native_decide
    simp [unify, bindTypeVar, stBefore, stAfter, expected, UnifyState.empty,
      applySubst, occursIn, h_occ, h_neq1, h_neq2]
  have h_typed :
      HasType env (.app fn arg) (applySubstCompat stAfter.subst 1 (.var 1)) :=
    h_app env fn arg (.var 0) .int stBefore stAfter 1 1 h_fn h_arg h_unify
  have h_alg :
      inferExpr env (.app fn arg) = some (applySubstCompat stAfter.subst 1 (.var 1)) :=
    inferExpr_complete env (.app fn arg) (applySubstCompat stAfter.subst 1 (.var 1)) h_typed
  simp [inferExpr, env, fn, arg, TermEnv.lookup] at h_alg

/--
Even requiring an empty starting substitution is not enough to derive the app
hook against the monomorphic declarative judgment.
-/
theorem not_AppUnifySoundHookEmptySubst : ¬ AppUnifySoundHookEmptySubst := by
  intro h_app
  let env : TermEnv := [("f", .var 0)]
  let fn : CoreExpr := .var "f"
  let arg : CoreExpr := .intLit 1
  let stBefore : UnifyState := { UnifyState.empty with nextTypeVar := 2 }
  let expected : Ty := .function (.cons .int .nil) (.var 1)
  let stAfter : UnifyState := { stBefore with subst := stBefore.subst.bindType 0 expected }
  have h_fn : HasType env fn (.var 0) := by
    exact HasType.var env "f" (.var 0) (by simp [env, TermEnv.lookup])
  have h_arg : HasType env arg .int := HasType.int env 1
  have h_unify : unify stBefore 1 (.var 0) expected = .ok stAfter := by
    have h_occ : occursInTyList 0 (TyList.cons Ty.int TyList.nil) = false := by
      simp [occursInTyList, occursIn]
    have h_neq1 : (Ty.var 0 == expected) = false := by
      native_decide
    have h_neq2 : (expected == Ty.var 0) = false := by
      native_decide
    simp [unify, bindTypeVar, stBefore, stAfter, expected, UnifyState.empty,
      applySubst, occursIn, h_occ, h_neq1, h_neq2]
  have h_empty : stBefore.subst = Subst.empty := by
    simp [stBefore, UnifyState.empty]
  have h_typed :
      HasType env (.app fn arg) (applySubstCompat stAfter.subst 1 (.var 1)) :=
    h_app env fn arg (.var 0) .int stBefore stAfter 1 1 h_empty h_fn h_arg h_unify
  have h_alg :
      inferExpr env (.app fn arg) = some (applySubstCompat stAfter.subst 1 (.var 1)) :=
    inferExpr_complete env (.app fn arg) (applySubstCompat stAfter.subst 1 (.var 1)) h_typed
  simp [inferExpr, env, fn, arg, TermEnv.lookup] at h_alg

/--
`ProjUnifySoundHook` is not derivable from the current declarative judgment:
unification can succeed by binding a variable-typed receiver position, while
`HasType.proj` requires the receiver to already have a closed anon-record type.
-/
theorem not_ProjUnifySoundHook : ¬ ProjUnifySoundHook := by
  intro h_proj
  let env : TermEnv := [("r", .var 0)]
  let recv : CoreExpr := .var "r"
  let label : Label := "a"
  let stBefore : UnifyState := { UnifyState.empty with nextTypeVar := 2 }
  let expected : Ty := .anonRecord (.mk (.cons label (.var 1) .nil) (some 0))
  let stAfter : UnifyState := { stBefore with subst := stBefore.subst.bindType 0 expected }
  have h_recv : HasType env recv (.var 0) := by
    exact HasType.var env "r" (.var 0) (by simp [env, TermEnv.lookup])
  have h_unify : unify stBefore 1 (.var 0) expected = .ok stAfter := by
    have h_occ : occursInRow 0 (.mk (.cons label (.var 1) .nil) (some 0)) = false := by
      simp [occursInRow, occursInRowFields, occursIn]
    have h_neq1 : (Ty.var 0 == expected) = false := by
      native_decide
    have h_neq2 : (expected == Ty.var 0) = false := by
      native_decide
    simp [unify, bindTypeVar, stBefore, stAfter, expected, UnifyState.empty,
      applySubst, occursIn, h_occ, h_neq1, h_neq2]
  have h_typed :
      HasType env (.proj recv label) (applySubstCompat stAfter.subst 1 (.var 1)) :=
    h_proj env recv label (.var 0) stBefore stAfter 1 1 0 h_recv h_unify
  have h_alg :
      inferExpr env (.proj recv label) = some (applySubstCompat stAfter.subst 1 (.var 1)) :=
    inferExpr_complete env (.proj recv label) (applySubstCompat stAfter.subst 1 (.var 1)) h_typed
  simp [inferExpr, env, recv, TermEnv.lookup] at h_alg

/--
Even requiring an empty starting substitution is not enough to derive the
projection hook against the monomorphic declarative judgment.
-/
theorem not_ProjUnifySoundHookEmptySubst : ¬ ProjUnifySoundHookEmptySubst := by
  intro h_proj
  let env : TermEnv := [("r", .var 0)]
  let recv : CoreExpr := .var "r"
  let label : Label := "a"
  let stBefore : UnifyState := { UnifyState.empty with nextTypeVar := 2 }
  let expected : Ty := .anonRecord (.mk (.cons label (.var 1) .nil) (some 0))
  let stAfter : UnifyState := { stBefore with subst := stBefore.subst.bindType 0 expected }
  have h_recv : HasType env recv (.var 0) := by
    exact HasType.var env "r" (.var 0) (by simp [env, TermEnv.lookup])
  have h_unify : unify stBefore 1 (.var 0) expected = .ok stAfter := by
    have h_occ : occursInRow 0 (.mk (.cons label (.var 1) .nil) (some 0)) = false := by
      simp [occursInRow, occursInRowFields, occursIn]
    have h_neq1 : (Ty.var 0 == expected) = false := by
      native_decide
    have h_neq2 : (expected == Ty.var 0) = false := by
      native_decide
    simp [unify, bindTypeVar, stBefore, stAfter, expected, UnifyState.empty,
      applySubst, occursIn, h_occ, h_neq1, h_neq2]
  have h_empty : stBefore.subst = Subst.empty := by
    simp [stBefore, UnifyState.empty]
  have h_typed :
      HasType env (.proj recv label) (applySubstCompat stAfter.subst 1 (.var 1)) :=
    h_proj env recv label (.var 0) stBefore stAfter 1 1 0 h_empty h_recv h_unify
  have h_alg :
      inferExpr env (.proj recv label) = some (applySubstCompat stAfter.subst 1 (.var 1)) :=
    inferExpr_complete env (.proj recv label) (applySubstCompat stAfter.subst 1 (.var 1)) h_typed
  simp [inferExpr, env, recv, TermEnv.lookup] at h_alg

/--
The global app resolved-shape premise is false in the fuel model: successful
app unification can produce a substitution where the resolved function side and
the "resolved argument + resolved result" shape diverge at the same fuel.
-/
theorem not_AppResolvedShapeFromUnify : ¬ AppResolvedShapeFromUnify := by
  intro h_app_resolved
  let env : TermEnv := [("f", .var 0), ("x", .var 0)]
  let fn : CoreExpr := .var "f"
  let arg : CoreExpr := .var "x"
  let fnTy : Ty := .var 0
  let argTy : Ty := .var 0
  let resVar : TypeVarId := 2
  let target : Ty := .function (.cons argTy .nil) (.var resVar)
  let s0 : Subst :=
    { typeMap := fun v => if v == 0 then some (.var 1) else none
      rowMap := fun _ => none }
  let stBefore : UnifyState :=
    { subst := s0, lacks := Lacks.empty, traitBounds := [], nextTypeVar := 3, nextRowVar := 0 }
  let stAfter : UnifyState := { stBefore with subst := stBefore.subst.bindType 1 target }
  have h_fn : HasTypeU env fn fnTy := by
    exact HasTypeU.var env "f" fnTy (by simp [env, fnTy, TermEnv.lookup])
  have h_arg : HasTypeU env arg argTy := by
    exact HasTypeU.var env "x" argTy (by simp [env, argTy, TermEnv.lookup])
  have h_unify : unify stBefore 2 fnTy target = .ok stAfter := by
    have h_left_ne :
        (Ty.var 1 == Ty.function (.cons argTy .nil) (.var resVar)) = false := by
      native_decide
    have h_right_ne :
        (Ty.function (.cons argTy .nil) (.var resVar) == Ty.var 1) = false := by
      native_decide
    have h_occ :
        occursInTyList 1 (.cons argTy .nil) = false := by
      native_decide
    have h_ne : (1 : Nat) ≠ resVar := by
      native_decide
    simp [unify, bindTypeVar, stBefore, stAfter, fnTy, target, s0, applySubst,
      applySubstTyList, occursIn, h_left_ne, h_right_ne, h_occ, h_ne]
  have h_resolved :
      applySubstCompat stAfter.subst 2 fnTy =
        .function
          (.cons (applySubstCompat stAfter.subst 2 argTy) .nil)
          (applySubstCompat stAfter.subst 2 (.var resVar)) :=
    h_app_resolved env fn arg fnTy argTy stBefore stAfter 2 resVar h_fn h_arg h_unify
  let lhs : Ty := applySubstCompat stAfter.subst 2 fnTy
  let rhs : Ty :=
    .function
      (.cons (applySubstCompat stAfter.subst 2 argTy) .nil)
      (applySubstCompat stAfter.subst 2 (.var resVar))
  have h_false :
      (lhs == rhs) = false := by
    native_decide
  have h_true :
      (lhs == rhs) = true := by
    have h_resolved' : lhs = rhs := by
      simpa [lhs, rhs] using h_resolved
    rw [h_resolved']
    exact beqTy_refl rhs
  rw [h_true] at h_false
  cases h_false

/--
The global projection resolved-shape premise is false in the fuel model:
successful projection unification can leave the receiver resolved to an open
row at the same fuel, so no closed-row witness exists.
-/
theorem not_ProjResolvedShapeFromUnify : ¬ ProjResolvedShapeFromUnify := by
  intro h_proj_resolved
  let env : TermEnv := [("r", .var 0)]
  let recv : CoreExpr := .var "r"
  let label : Label := "a"
  let recvTy : Ty := .var 0
  let fieldVar : TypeVarId := 2
  let restVar : RowVarId := 1
  let stBefore : UnifyState := { UnifyState.empty with nextTypeVar := 3, nextRowVar := 2 }
  let expected : Ty := .anonRecord (.mk (.cons label (.var fieldVar) .nil) (some restVar))
  let stAfter : UnifyState := { stBefore with subst := stBefore.subst.bindType 0 expected }
  have h_recv : HasTypeU env recv recvTy := by
    exact HasTypeU.var env "r" recvTy (by simp [env, recvTy, TermEnv.lookup])
  have h_unify : unify stBefore 1 recvTy expected = .ok stAfter := by
    have h_occ :
        occursInRow 0 (.mk (.cons label (.var fieldVar) .nil) (some restVar)) = false := by
      simp [occursInRow, occursInRowFields, occursIn, fieldVar]
    have h_neq1 : (recvTy == expected) = false := by
      native_decide
    have h_neq2 : (expected == recvTy) = false := by
      native_decide
    simp [unify, bindTypeVar, stBefore, stAfter, recvTy, expected, UnifyState.empty,
      applySubst, occursIn, h_occ, h_neq1, h_neq2]
  rcases h_proj_resolved env recv label recvTy stBefore stAfter 1 fieldVar restVar h_recv h_unify with
    ⟨rowFields, h_resolved, _h_get⟩
  have h_open :
      applySubstCompat stAfter.subst 1 recvTy =
        .anonRecord (.mk (.cons label (.var fieldVar) .nil) (some restVar)) := by
    simp [applySubstCompat, applySubst, stAfter, recvTy, expected, Subst.bindType]
  rw [h_open] at h_resolved
  cases rowFields <;> cases h_resolved

/-- Consequently, the bundled resolved-shape premise pair is also false. -/
theorem not_UnifyResolvedShapePremises : ¬ UnifyResolvedShapePremises := by
  intro h
  exact not_AppResolvedShapeFromUnify h.1

/--
Weaker app hook: derivable when the function side is already declaratively typed
as a single-argument function, and the unify result variable is known to resolve
to that return type.
-/
def AppUnifySoundHookWeak : Prop :=
  ∀ env fn arg argTy retTy stBefore stAfter fuel resVar,
    HasType env fn (.function (.cons argTy .nil) retTy) →
    HasType env arg argTy →
    unify stBefore fuel (.function (.cons argTy .nil) retTy) (.function (.cons argTy .nil) (.var resVar)) = .ok stAfter →
    applySubstCompat stAfter.subst fuel (.var resVar) = retTy →
    HasType env (.app fn arg) (applySubstCompat stAfter.subst fuel (.var resVar))

/-- `AppUnifySoundHookWeak` is derivable from declarative typing + result equality. -/
theorem appUnifySoundHookWeak_proved : AppUnifySoundHookWeak := by
  intro env fn arg argTy retTy stBefore stAfter fuel resVar h_fn h_arg _ h_res_eq
  rw [h_res_eq]
  exact HasType.app env fn arg argTy retTy h_fn h_arg

/--
Weaker projection hook: derivable when the receiver side is already
declaratively typed as a closed anonymous record carrying the selected field
at the substitution-resolved projection type.
-/
def ProjUnifySoundHookWeak : Prop :=
  ∀ env recv label recvTy stBefore stAfter fuel fieldVar restVar rowFields,
    HasType env recv recvTy →
    recvTy = .anonRecord (.mk rowFields none) →
    unify stBefore fuel recvTy (.anonRecord (.mk (.cons label (.var fieldVar) .nil) (some restVar))) = .ok stAfter →
    RowFields.get rowFields label = some (applySubstCompat stAfter.subst fuel (.var fieldVar)) →
    HasType env (.proj recv label) (applySubstCompat stAfter.subst fuel (.var fieldVar))

/-- `ProjUnifySoundHookWeak` is derivable from declarative projection typing. -/
theorem projUnifySoundHookWeak_proved : ProjUnifySoundHookWeak := by
  intro env recv label recvTy stBefore stAfter fuel fieldVar restVar rowFields
    h_recv h_shape _ h_get
  rw [h_shape] at h_recv
  exact HasType.proj env recv rowFields label
    (applySubstCompat stAfter.subst fuel (.var fieldVar)) h_recv h_get

/-- Any strong app hook witness implies the app weak-hook surface. -/
theorem appUnifySoundHookWeak_of_appUnifySoundHook
    (h_app : AppUnifySoundHook) :
    AppUnifySoundHookWeak := by
  intro env fn arg argTy retTy stBefore stAfter fuel resVar h_fn h_arg h_unify h_res_eq
  have h_app_step : HasType env (.app fn arg) (applySubstCompat stAfter.subst fuel (.var resVar)) :=
    h_app env fn arg (.function (.cons argTy .nil) retTy) argTy stBefore stAfter fuel resVar
      h_fn h_arg h_unify
  simpa [h_res_eq] using h_app_step

/-- Any strong projection hook witness implies the projection weak-hook surface. -/
theorem projUnifySoundHookWeak_of_projUnifySoundHook
    (h_proj : ProjUnifySoundHook) :
    ProjUnifySoundHookWeak := by
  intro env recv label recvTy stBefore stAfter fuel fieldVar restVar rowFields
    h_recv _ h_unify _
  exact h_proj env recv label recvTy stBefore stAfter fuel fieldVar restVar h_recv h_unify

/-- Packaged weak hook assumptions for app/projection branch reasoning. -/
def UnifyHookPremisesWeak : Prop :=
  AppUnifySoundHookWeak ∧ ProjUnifySoundHookWeak

/-- The weak hook package is derivable on both app and projection branches. -/
theorem unifyHookPremisesWeak_proved : UnifyHookPremisesWeak := by
  exact ⟨appUnifySoundHookWeak_proved, projUnifySoundHookWeak_proved⟩

/-- Any strong hook package implies the weak hook package. -/
theorem unifyHookPremisesWeak_of_unifyHookPremises
    (h_hooks : UnifyHookPremises) :
    UnifyHookPremisesWeak := by
  exact ⟨appUnifySoundHookWeak_of_appUnifySoundHook h_hooks.1,
    projUnifySoundHookWeak_of_projUnifySoundHook h_hooks.2⟩

/--
Canonical weak-boundary local-step bundle for `HasType`: packages app/proj
one-step soundness under resolved equality/row-shape premises.
-/
def UnifyStepSoundWeak : Prop :=
  (∀ env fn arg argTy retTy stBefore stAfter fuel resVar,
    HasType env fn (.function (.cons argTy .nil) retTy) →
    HasType env arg argTy →
    unify stBefore fuel (.function (.cons argTy .nil) retTy)
      (.function (.cons argTy .nil) (.var resVar)) = .ok stAfter →
    applySubstCompat stAfter.subst fuel (.var resVar) = retTy →
    HasType env (.app fn arg) (applySubstCompat stAfter.subst fuel (.var resVar)))
  ∧
  (∀ env recv label recvTy stBefore stAfter fuel fieldVar restVar rowFields,
    HasType env recv recvTy →
    recvTy = .anonRecord (.mk rowFields none) →
    unify stBefore fuel recvTy
      (.anonRecord (.mk (.cons label (.var fieldVar) .nil) (some restVar))) = .ok stAfter →
    RowFields.get rowFields label = some (applySubstCompat stAfter.subst fuel (.var fieldVar)) →
    HasType env (.proj recv label) (applySubstCompat stAfter.subst fuel (.var fieldVar)))

/-- Build the weak local-step bundle from weak hook premises. -/
theorem unifyStepSoundWeak_of_hookPremisesWeak
    (h_hooks : UnifyHookPremisesWeak) :
    UnifyStepSoundWeak := by
  exact ⟨h_hooks.1, h_hooks.2⟩

/-- Canonical witness for the weak local-step bundle. -/
theorem unifyStepSoundWeak_proved : UnifyStepSoundWeak := by
  exact unifyStepSoundWeak_of_hookPremisesWeak unifyHookPremisesWeak_proved

/-- Build the weak local-step bundle directly from strong hook premises. -/
theorem unifyStepSoundWeak_of_unifyHookPremises
    (h_hooks : UnifyHookPremises) :
    UnifyStepSoundWeak := by
  exact unifyStepSoundWeak_of_hookPremisesWeak
    (unifyHookPremisesWeak_of_unifyHookPremises h_hooks)

/--
Unification-aware app hook: if substitution-resolving `fnTy` yields a
single-argument function shape over the resolved argument type, app typing is
derivable directly in `HasTypeU`.
-/
def AppUnifySoundHookUResolved : Prop :=
  ∀ env fn arg fnTy argTy stBefore stAfter fuel resVar,
    HasTypeU env fn fnTy →
    HasTypeU env arg argTy →
    unify stBefore fuel fnTy (.function (.cons argTy .nil) (.var resVar)) = .ok stAfter →
    applySubstCompat stAfter.subst fuel fnTy =
      .function
        (.cons (applySubstCompat stAfter.subst fuel argTy) .nil)
        (applySubstCompat stAfter.subst fuel (.var resVar)) →
    HasTypeU env (.app fn arg) (applySubstCompat stAfter.subst fuel (.var resVar))

/--
`AppUnifySoundHookUResolved` is derivable from `HasTypeU.subst`: once the
resolved function-shape equation is available, no additional hook is needed.
-/
theorem appUnifySoundHookUResolved_proved : AppUnifySoundHookUResolved := by
  intro env fn arg fnTy argTy stBefore stAfter fuel resVar h_fn h_arg _ h_resolved
  have h_fn_resolved : HasTypeU env fn (applySubstCompat stAfter.subst fuel fnTy) :=
    HasTypeU.subst env fn fnTy stAfter.subst fuel h_fn
  have h_arg_resolved : HasTypeU env arg (applySubstCompat stAfter.subst fuel argTy) :=
    HasTypeU.subst env arg argTy stAfter.subst fuel h_arg
  rw [h_resolved] at h_fn_resolved
  exact HasTypeU.app env fn arg
    (applySubstCompat stAfter.subst fuel argTy)
    (applySubstCompat stAfter.subst fuel (.var resVar))
    h_fn_resolved h_arg_resolved

/--
Successor-fuel variant of `AppUnifySoundHookUResolved` matching the app-branch
shape exposed by `bindTypeVarConsistentIdempotent`-style lemmas.
-/
def AppUnifySoundHookUResolvedSucc : Prop :=
  ∀ env fn arg fnTy argTy stBefore stAfter fuel resVar,
    HasTypeU env fn fnTy →
    HasTypeU env arg argTy →
    unify stBefore fuel fnTy (.function (.cons argTy .nil) (.var resVar)) = .ok stAfter →
    applySubstCompat stAfter.subst (fuel + 1) fnTy =
      .function
        (.cons (applySubstCompat stAfter.subst fuel argTy) .nil)
        (applySubstCompat stAfter.subst (fuel + 1) (.var resVar)) →
    HasTypeU env (.app fn arg) (applySubstCompat stAfter.subst (fuel + 1) (.var resVar))

/-- `AppUnifySoundHookUResolvedSucc` is derivable from `HasTypeU.subst`. -/
theorem appUnifySoundHookUResolvedSucc_proved : AppUnifySoundHookUResolvedSucc := by
  intro env fn arg fnTy argTy stBefore stAfter fuel resVar h_fn h_arg _ h_resolved
  have h_fn_resolved : HasTypeU env fn (applySubstCompat stAfter.subst (fuel + 1) fnTy) :=
    HasTypeU.subst env fn fnTy stAfter.subst (fuel + 1) h_fn
  have h_arg_resolved : HasTypeU env arg (applySubstCompat stAfter.subst fuel argTy) :=
    HasTypeU.subst env arg argTy stAfter.subst fuel h_arg
  rw [h_resolved] at h_fn_resolved
  exact HasTypeU.app env fn arg
    (applySubstCompat stAfter.subst fuel argTy)
    (applySubstCompat stAfter.subst (fuel + 1) (.var resVar))
    h_fn_resolved h_arg_resolved

/--
Unification-aware projection hook: if substitution-resolving `recvTy` yields a
closed anon-record shape whose selected field is the resolved projection
variable, projection typing is derivable directly in `HasTypeU`.
-/
def ProjUnifySoundHookUResolved : Prop :=
  ∀ env recv label recvTy stBefore stAfter fuel fieldVar restVar rowFields,
    HasTypeU env recv recvTy →
    unify stBefore fuel recvTy (.anonRecord (.mk (.cons label (.var fieldVar) .nil) (some restVar))) = .ok stAfter →
    applySubstCompat stAfter.subst fuel recvTy = .anonRecord (.mk rowFields none) →
    RowFields.get rowFields label = some (applySubstCompat stAfter.subst fuel (.var fieldVar)) →
    HasTypeU env (.proj recv label) (applySubstCompat stAfter.subst fuel (.var fieldVar))

/-- `ProjUnifySoundHookUResolved` is derivable from `HasTypeU.subst`. -/
theorem projUnifySoundHookUResolved_proved : ProjUnifySoundHookUResolved := by
  intro env recv label recvTy stBefore stAfter fuel fieldVar restVar rowFields
    h_recv _ h_resolved h_get
  have h_recv_resolved : HasTypeU env recv (applySubstCompat stAfter.subst fuel recvTy) :=
    HasTypeU.subst env recv recvTy stAfter.subst fuel h_recv
  rw [h_resolved] at h_recv_resolved
  exact HasTypeU.proj env recv rowFields label
    (applySubstCompat stAfter.subst fuel (.var fieldVar))
    h_recv_resolved h_get

/--
Bridge lemma for the app weak-hook equality premise:
if the app unification success factors through a `bindTypeVar` step on the
result variable and the final substitution is idempotent, the needed equality
follows from `bindTypeVarConsistentIdempotent`.
-/
theorem app_unify_result_eq_of_bindTypeVar_idempotent
    (stBefore : UnifyState) (fuel : Nat) (retTy : Ty) (resVar : TypeVarId) (stAfter : UnifyState)
    (h_bind : bindTypeVar stBefore resVar retTy fuel = .ok stAfter)
    (h_idemp : stAfter.subst.Idempotent) :
    applySubst stAfter.subst (fuel + 1) (.var resVar) =
      applySubst stAfter.subst (fuel + 1) retTy := by
  have h :=
    bindTypeVarConsistentIdempotent stBefore resVar retTy fuel stAfter h_bind h_idemp
  simpa using h

/--
Function-app bridge slice: if the function-parameter phase is known successful
and the return-type phase is known to be a `bindTypeVar` success, idempotence
is sufficient to derive the weak-hook equality premise.
-/
theorem app_unify_result_eq_of_function_tail_bind_idempotent
    (st stTail stAfter : UnifyState) (fuel : Nat) (argTy retTy : Ty) (resVar : TypeVarId)
    (_h_params : unifyTyList st fuel (.cons argTy .nil) (.cons argTy .nil) = .ok stTail)
    (h_tail_bind : bindTypeVar stTail resVar retTy fuel = .ok stAfter)
    (h_idemp : stAfter.subst.Idempotent) :
    applySubst stAfter.subst (fuel + 1) (.var resVar) =
      applySubst stAfter.subst (fuel + 1) retTy :=
  app_unify_result_eq_of_bindTypeVar_idempotent stTail fuel retTy resVar stAfter h_tail_bind h_idemp

/--
Packaged app-branch bridge: expose exactly the equality premise needed by
`AppUnifySoundHookWeak`, assuming explicit function-branch shape witnesses.
-/
theorem app_unify_result_eq_of_unify_function_shape_idempotent
    (st stAfter : UnifyState) (fuel : Nat) (argTy retTy : Ty) (resVar : TypeVarId)
    (h_shape :
      ∃ stTail,
        unifyTyList st fuel (.cons argTy .nil) (.cons argTy .nil) = .ok stTail ∧
        bindTypeVar stTail resVar retTy fuel = .ok stAfter)
    (h_idemp : stAfter.subst.Idempotent) :
    applySubst stAfter.subst (fuel + 1) (.var resVar) =
      applySubst stAfter.subst (fuel + 1) retTy := by
  rcases h_shape with ⟨stTail, h_params, h_tail_bind⟩
  exact app_unify_result_eq_of_function_tail_bind_idempotent
    st stTail stAfter fuel argTy retTy resVar h_params h_tail_bind h_idemp

/--
Decompose app-branch unification success into parameter-list and return-tail
success, assuming the resolved heads are the expected function shapes and the
BEq fast-path is not taken.
-/
theorem app_unify_function_shape_witness_of_success_resolved_heads
    (st stAfter : UnifyState) (fuel : Nat) (argTy retTy : Ty) (resVar : TypeVarId)
    (h_head_l :
      applySubstCompat st.subst fuel (.function (.cons argTy .nil) retTy) =
        .function (.cons argTy .nil) retTy)
    (h_head_r :
      applySubstCompat st.subst fuel (.function (.cons argTy .nil) (.var resVar)) =
        .function (.cons argTy .nil) (.var resVar))
    (h_beq :
      (applySubstCompat st.subst fuel (.function (.cons argTy .nil) retTy)
        == applySubstCompat st.subst fuel (.function (.cons argTy .nil) (.var resVar))) = false)
    (h_unify :
      unify st (fuel + 1) (.function (.cons argTy .nil) retTy)
        (.function (.cons argTy .nil) (.var resVar)) = .ok stAfter) :
    ∃ stTail,
      unifyTyList st fuel (.cons argTy .nil) (.cons argTy .nil) = .ok stTail ∧
      unify stTail fuel retTy (.var resVar) = .ok stAfter := by
  have h_beq' :
      ((Ty.function (.cons argTy .nil) retTy) == (Ty.function (.cons argTy .nil) (.var resVar))) = false := by
    simpa [h_head_l, h_head_r] using h_beq
  have h_unify' :
      (match unifyTyList st fuel (.cons argTy .nil) (.cons argTy .nil) with
        | .ok st' => unify st' fuel retTy (.var resVar)
        | e => e) = .ok stAfter := by
    simpa [unify, h_head_l, h_head_r, h_beq'] using h_unify
  cases h_params : unifyTyList st fuel (.cons argTy .nil) (.cons argTy .nil) with
  | err e =>
    simp [h_params] at h_unify'
  | ok stTail =>
    refine ⟨stTail, ?_, ?_⟩
    · simp
    · simpa [h_params] using h_unify'

/--
Derive resolved app/function heads from no-op domain assumptions on the
argument type, return type, and result variable.
-/
theorem app_unify_resolved_heads_of_noop_domain
    (st : UnifyState) (fuel : Nat) (argTy retTy : Ty) (resVar : TypeVarId)
    (h_arg_type : ∀ v ∈ freeTypeVars argTy, st.subst.typeMap v = none)
    (h_arg_row : ∀ v ∈ freeRowVars argTy, st.subst.rowMap v = none)
    (h_ret_type : ∀ v ∈ freeTypeVars retTy, st.subst.typeMap v = none)
    (h_ret_row : ∀ v ∈ freeRowVars retTy, st.subst.rowMap v = none)
    (h_res_unbound : st.subst.typeMap resVar = none) :
    applySubstCompat st.subst fuel (.function (.cons argTy .nil) retTy) =
      .function (.cons argTy .nil) retTy
    ∧
    applySubstCompat st.subst fuel (.function (.cons argTy .nil) (.var resVar)) =
      .function (.cons argTy .nil) (.var resVar) := by
  obtain ⟨h_noop_ty, _, _, _⟩ := applySubst_noop st.subst fuel
  constructor
  · exact h_noop_ty (.function (.cons argTy .nil) retTy) (by
      intro v hv
      simp [freeTypeVars, freeTypeVarsTyList] at hv
      rcases hv with hv | hv
      · exact h_arg_type v hv
      · exact h_ret_type v hv
    ) (by
      intro v hv
      simp [freeRowVars, freeRowVarsTyList] at hv
      rcases hv with hv | hv
      · exact h_arg_row v hv
      · exact h_ret_row v hv
    )
  · exact h_noop_ty (.function (.cons argTy .nil) (.var resVar)) (by
      intro v hv
      simp [freeTypeVars, freeTypeVarsTyList] at hv
      rcases hv with hv | hv
      · exact h_arg_type v hv
      · have hv' : v = resVar := by simpa [freeTypeVars] using hv
        cases hv'
        exact h_res_unbound
    ) (by
      intro v hv
      simp [freeRowVars, freeRowVarsTyList] at hv
      exact h_arg_row v hv
    )

/-- Reusable no-op domain contract for app-branch bridge lemmas. -/
structure AppUnifyNoopDomain (st : UnifyState) (argTy retTy : Ty) (resVar : TypeVarId) : Prop where
  argTypeNone : ∀ v ∈ freeTypeVars argTy, st.subst.typeMap v = none
  argRowNone : ∀ v ∈ freeRowVars argTy, st.subst.rowMap v = none
  retTypeNone : ∀ v ∈ freeTypeVars retTy, st.subst.typeMap v = none
  retRowNone : ∀ v ∈ freeRowVars retTy, st.subst.rowMap v = none
  resUnbound : st.subst.typeMap resVar = none

/-- Type-level freshness invariant: variables at/above `nextTypeVar` are unbound. -/
def TypeVarsAboveNextUnbound (st : UnifyState) : Prop :=
  ∀ v, st.nextTypeVar ≤ v → st.subst.typeMap v = none

/-- Base state satisfies `TypeVarsAboveNextUnbound`. -/
theorem typeVarsAboveNextUnbound_empty : TypeVarsAboveNextUnbound UnifyState.empty := by
  intro v _
  simp [UnifyState.empty, Subst.empty]

/-- Any state with empty substitution satisfies the above-threshold invariant. -/
theorem typeVarsAboveNextUnbound_of_subst_empty
    (st : UnifyState) (h_empty : st.subst = Subst.empty) :
    TypeVarsAboveNextUnbound st := by
  intro v _
  simp [h_empty, Subst.empty]

/-- Raising only `nextTypeVar` preserves the above-threshold unbound invariant. -/
theorem typeVarsAboveNextUnbound_with_nextTypeVar
    (st : UnifyState) (next' : Nat)
    (h_inv : TypeVarsAboveNextUnbound st)
    (h_le : st.nextTypeVar ≤ next') :
    TypeVarsAboveNextUnbound { st with nextTypeVar := next' } := by
  intro v hv
  exact h_inv v (Nat.le_trans h_le hv)

/-- Empty substitution satisfies the app no-op domain contract for all types. -/
theorem appUnifyNoopDomain_of_subst_empty
    (st : UnifyState) (argTy retTy : Ty) (resVar : TypeVarId)
    (h_empty : st.subst = Subst.empty) :
    AppUnifyNoopDomain st argTy retTy resVar := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v _
    simp [h_empty, Subst.empty]
  · intro v _
    simp [h_empty, Subst.empty]
  · intro v _
    simp [h_empty, Subst.empty]
  · intro v _
    simp [h_empty, Subst.empty]
  · simp [h_empty, Subst.empty]

/--
Lift app no-op domain assumptions back through substitution extension:
if a final substitution extends the current substitution and has no bindings on
the relevant vars, then the current substitution also has none.
-/
theorem appUnifyNoopDomain_of_extends_final_none
    (st stFinal : UnifyState) (argTy retTy : Ty) (resVar : TypeVarId)
    (h_ext : Subst.Extends st.subst stFinal.subst)
    (h_arg_type_final : ∀ v ∈ freeTypeVars argTy, stFinal.subst.typeMap v = none)
    (h_arg_row_final : ∀ v ∈ freeRowVars argTy, stFinal.subst.rowMap v = none)
    (h_ret_type_final : ∀ v ∈ freeTypeVars retTy, stFinal.subst.typeMap v = none)
    (h_ret_row_final : ∀ v ∈ freeRowVars retTy, stFinal.subst.rowMap v = none)
    (h_res_unbound_final : stFinal.subst.typeMap resVar = none) :
    AppUnifyNoopDomain st argTy retTy resVar := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    have hnone := h_arg_type_final v hv
    cases hst : st.subst.typeMap v with
    | none => rfl
    | some ty =>
      have hsome : stFinal.subst.typeMap v = some ty := h_ext.typeExt v ty hst
      rw [hsome] at hnone
      contradiction
  · intro v hv
    have hnone := h_arg_row_final v hv
    cases hst : st.subst.rowMap v with
    | none => rfl
    | some r =>
      have hsome : stFinal.subst.rowMap v = some r := h_ext.rowExt v r hst
      rw [hsome] at hnone
      contradiction
  · intro v hv
    have hnone := h_ret_type_final v hv
    cases hst : st.subst.typeMap v with
    | none => rfl
    | some ty =>
      have hsome : stFinal.subst.typeMap v = some ty := h_ext.typeExt v ty hst
      rw [hsome] at hnone
      contradiction
  · intro v hv
    have hnone := h_ret_row_final v hv
    cases hst : st.subst.rowMap v with
    | none => rfl
    | some r =>
      have hsome : stFinal.subst.rowMap v = some r := h_ext.rowExt v r hst
      rw [hsome] at hnone
      contradiction
  · have hnone := h_res_unbound_final
    cases hst : st.subst.typeMap resVar with
    | none => rfl
    | some ty =>
      have hsome : stFinal.subst.typeMap resVar = some ty := h_ext.typeExt resVar ty hst
      rw [hsome] at hnone
      contradiction

/--
Variant of `appUnifyNoopDomain_of_extends_final_none` that does not require
final-state unboundness for `resVar`; the result-variable unboundness is
provided directly for the starting state.
-/
theorem appUnifyNoopDomain_of_extends_final_none_with_res_unbound
    (st stFinal : UnifyState) (argTy retTy : Ty) (resVar : TypeVarId)
    (h_ext : Subst.Extends st.subst stFinal.subst)
    (h_arg_type_final : ∀ v ∈ freeTypeVars argTy, stFinal.subst.typeMap v = none)
    (h_arg_row_final : ∀ v ∈ freeRowVars argTy, stFinal.subst.rowMap v = none)
    (h_ret_type_final : ∀ v ∈ freeTypeVars retTy, stFinal.subst.typeMap v = none)
    (h_ret_row_final : ∀ v ∈ freeRowVars retTy, stFinal.subst.rowMap v = none)
    (h_res_unbound_start : st.subst.typeMap resVar = none) :
    AppUnifyNoopDomain st argTy retTy resVar := by
  refine ⟨?_, ?_, ?_, ?_, h_res_unbound_start⟩
  · intro v hv
    have hnone := h_arg_type_final v hv
    cases hst : st.subst.typeMap v with
    | none => rfl
    | some ty =>
      have hsome : stFinal.subst.typeMap v = some ty := h_ext.typeExt v ty hst
      rw [hsome] at hnone
      contradiction
  · intro v hv
    have hnone := h_arg_row_final v hv
    cases hst : st.subst.rowMap v with
    | none => rfl
    | some r =>
      have hsome : stFinal.subst.rowMap v = some r := h_ext.rowExt v r hst
      rw [hsome] at hnone
      contradiction
  · intro v hv
    have hnone := h_ret_type_final v hv
    cases hst : st.subst.typeMap v with
    | none => rfl
    | some ty =>
      have hsome : stFinal.subst.typeMap v = some ty := h_ext.typeExt v ty hst
      rw [hsome] at hnone
      contradiction
  · intro v hv
    have hnone := h_ret_row_final v hv
    cases hst : st.subst.rowMap v with
    | none => rfl
    | some r =>
      have hsome : stFinal.subst.rowMap v = some r := h_ext.rowExt v r hst
      rw [hsome] at hnone
      contradiction

/-- Unboundness of all vars at/above `nextTypeVar` implies fresh var unbound. -/
theorem freshTypeVar_unbound_of_above_none
    (st : UnifyState)
    (h_above_none : ∀ v, st.nextTypeVar ≤ v → st.subst.typeMap v = none) :
    (st.freshTypeVar).2.subst.typeMap (st.freshTypeVar).1 = none := by
  simp [UnifyState.freshTypeVar]
  exact h_above_none st.nextTypeVar (Nat.le_refl _)

/-- Freshness projection from `TypeVarsAboveNextUnbound`. -/
theorem freshTypeVar_unbound_of_typeVarsAboveNextUnbound
    (st : UnifyState) (h_inv : TypeVarsAboveNextUnbound st) :
    (st.freshTypeVar).2.subst.typeMap (st.freshTypeVar).1 = none :=
  freshTypeVar_unbound_of_above_none st h_inv

/-- `freshTypeVar` preserves `TypeVarsAboveNextUnbound` on the resulting state. -/
theorem typeVarsAboveNextUnbound_after_freshTypeVar
    (st : UnifyState) (h_inv : TypeVarsAboveNextUnbound st) :
    TypeVarsAboveNextUnbound (st.freshTypeVar).2 := by
  simpa [UnifyState.freshTypeVar] using
    typeVarsAboveNextUnbound_with_nextTypeVar st (st.nextTypeVar + 1) h_inv
      (Nat.le_succ _)

/--
Binding a variable strictly below `nextTypeVar` preserves the above-threshold
unbound invariant.
-/
theorem typeVarsAboveNextUnbound_bindTypeVar_lt_next
    (st st' : UnifyState) (v : TypeVarId) (ty : Ty) (fuel : Nat)
    (h_inv : TypeVarsAboveNextUnbound st)
    (h_lt : v < st.nextTypeVar)
    (h_bind : bindTypeVar st v ty fuel = .ok st') :
    TypeVarsAboveNextUnbound st' := by
  unfold bindTypeVar at h_bind
  split at h_bind
  · simp [UnifyResult.ok.injEq] at h_bind
    subst h_bind
    exact h_inv
  · split at h_bind
    · exact absurd h_bind (by intro h'; exact UnifyResult.noConfusion h')
    · simp [UnifyResult.ok.injEq] at h_bind
      subst h_bind
      intro w hw
      have h_old : st.subst.typeMap w = none := h_inv w hw
      have hvw : v ≠ w := Nat.ne_of_lt (Nat.lt_of_lt_of_le h_lt hw)
      have hwv : w ≠ v := hvw.symm
      simpa [Subst.bindType, hwv] using h_old

/--
Specialized preservation step for the app fresh-result-variable shape:
after `freshTypeVar`, any successful `bindTypeVar` on that fresh variable
preserves above-threshold unboundness.
-/
theorem typeVarsAboveNextUnbound_after_bind_fresh
    (st st' : UnifyState) (ty : Ty) (fuel : Nat)
    (h_inv : TypeVarsAboveNextUnbound st)
    (h_bind :
      bindTypeVar (st.freshTypeVar).2 (st.freshTypeVar).1 ty fuel = .ok st') :
    TypeVarsAboveNextUnbound st' := by
  have h_inv_fresh : TypeVarsAboveNextUnbound (st.freshTypeVar).2 :=
    typeVarsAboveNextUnbound_after_freshTypeVar st h_inv
  have h_lt : (st.freshTypeVar).1 < (st.freshTypeVar).2.nextTypeVar := by
    simp [UnifyState.freshTypeVar]
  exact typeVarsAboveNextUnbound_bindTypeVar_lt_next
    (st := (st.freshTypeVar).2) (st' := st') (v := (st.freshTypeVar).1)
    (ty := ty) (fuel := fuel) h_inv_fresh h_lt h_bind

/--
Contract derivation for the common app case where `resVar` is chosen as the
fresh type variable from `st`.
-/
theorem appUnifyNoopDomain_of_extends_final_none_with_freshRes
    (st stFinal : UnifyState) (argTy retTy : Ty)
    (h_ext : Subst.Extends st.subst stFinal.subst)
    (h_arg_type_final : ∀ v ∈ freeTypeVars argTy, stFinal.subst.typeMap v = none)
    (h_arg_row_final : ∀ v ∈ freeRowVars argTy, stFinal.subst.rowMap v = none)
    (h_ret_type_final : ∀ v ∈ freeTypeVars retTy, stFinal.subst.typeMap v = none)
    (h_ret_row_final : ∀ v ∈ freeRowVars retTy, stFinal.subst.rowMap v = none)
    (h_inv : TypeVarsAboveNextUnbound st) :
    AppUnifyNoopDomain st argTy retTy (st.freshTypeVar).1 := by
  have h_res_unbound_start : st.subst.typeMap (st.freshTypeVar).1 = none := by
    simpa [UnifyState.freshTypeVar] using h_inv st.nextTypeVar (Nat.le_refl _)
  exact appUnifyNoopDomain_of_extends_final_none_with_res_unbound
    st stFinal argTy retTy (st.freshTypeVar).1
    h_ext h_arg_type_final h_arg_row_final h_ret_type_final h_ret_row_final h_res_unbound_start

/--
If argument/return types are closed (no free type/row vars), app no-op domain
reduces to unboundness of the result variable in the starting substitution.
-/
theorem appUnifyNoopDomain_of_closed_types
    (st : UnifyState) (argTy retTy : Ty) (resVar : TypeVarId)
    (h_arg_ftv : freeTypeVars argTy = [])
    (h_arg_frv : freeRowVars argTy = [])
    (h_ret_ftv : freeTypeVars retTy = [])
    (h_ret_frv : freeRowVars retTy = [])
    (h_res_unbound : st.subst.typeMap resVar = none) :
    AppUnifyNoopDomain st argTy retTy resVar := by
  refine ⟨?_, ?_, ?_, ?_, h_res_unbound⟩
  · intro v hv
    rw [h_arg_ftv] at hv
    cases hv
  · intro v hv
    rw [h_arg_frv] at hv
    cases hv
  · intro v hv
    rw [h_ret_ftv] at hv
    cases hv
  · intro v hv
    rw [h_ret_frv] at hv
    cases hv

/--
Convenience contract for app branches with fresh result variable and closed
argument/return types under the above-`nextTypeVar` unbound invariant.
-/
theorem appUnifyNoopDomain_of_closed_types_with_freshRes
    (st : UnifyState) (argTy retTy : Ty)
    (h_arg_ftv : freeTypeVars argTy = [])
    (h_arg_frv : freeRowVars argTy = [])
    (h_ret_ftv : freeTypeVars retTy = [])
    (h_ret_frv : freeRowVars retTy = [])
    (h_inv : TypeVarsAboveNextUnbound st) :
    AppUnifyNoopDomain st argTy retTy (st.freshTypeVar).1 := by
  have h_res_unbound : st.subst.typeMap (st.freshTypeVar).1 = none :=
    freshTypeVar_unbound_of_typeVarsAboveNextUnbound st h_inv
  exact appUnifyNoopDomain_of_closed_types st argTy retTy (st.freshTypeVar).1
    h_arg_ftv h_arg_frv h_ret_ftv h_ret_frv h_res_unbound

/--
Empty-substitution specialization of `appUnifyNoopDomain_of_closed_types_with_freshRes`.
-/
theorem appUnifyNoopDomain_of_closed_types_with_freshRes_of_subst_empty
    (st : UnifyState) (argTy retTy : Ty)
    (h_empty : st.subst = Subst.empty)
    (h_arg_ftv : freeTypeVars argTy = [])
    (h_arg_frv : freeRowVars argTy = [])
    (h_ret_ftv : freeTypeVars retTy = [])
    (h_ret_frv : freeRowVars retTy = []) :
    AppUnifyNoopDomain st argTy retTy (st.freshTypeVar).1 := by
  have h_inv : TypeVarsAboveNextUnbound st :=
    typeVarsAboveNextUnbound_of_subst_empty st h_empty
  exact appUnifyNoopDomain_of_closed_types_with_freshRes
    st argTy retTy h_arg_ftv h_arg_frv h_ret_ftv h_ret_frv h_inv

/-- A closed type (no free type vars) cannot be a type variable. -/
theorem closed_type_not_var
    (ty : Ty) (h_closed : freeTypeVars ty = []) :
    ∀ v, ty ≠ .var v := by
  intro v h_eq
  rw [h_eq, freeTypeVars] at h_closed
  simp at h_closed

/-- Closed types are fixed points of `applySubstCompat` at any fuel. -/
theorem applySubstCompat_closed
    (s : Subst) (fuel : Nat) (ty : Ty)
    (h_ftv : freeTypeVars ty = [])
    (h_frv : freeRowVars ty = []) :
    applySubstCompat s fuel ty = ty := by
  obtain ⟨h_noop_ty, _, _, _⟩ := applySubst_noop s fuel
  have h_type_none : ∀ v ∈ freeTypeVars ty, s.typeMap v = none := by
    intro v hv
    have : False := by simp [h_ftv] at hv
    exact False.elim this
  have h_row_none : ∀ rv ∈ freeRowVars ty, s.rowMap rv = none := by
    intro rv hv
    have : False := by simp [h_frv] at hv
    exact False.elim this
  simpa using h_noop_ty ty h_type_none h_row_none

/-- Contract wrapper for `app_unify_resolved_heads_of_noop_domain`. -/
theorem app_unify_resolved_heads_of_contract
    (st : UnifyState) (fuel : Nat) (argTy retTy : Ty) (resVar : TypeVarId)
    (h_dom : AppUnifyNoopDomain st argTy retTy resVar) :
    applySubstCompat st.subst fuel (.function (.cons argTy .nil) retTy) =
      .function (.cons argTy .nil) retTy
    ∧
    applySubstCompat st.subst fuel (.function (.cons argTy .nil) (.var resVar)) =
      .function (.cons argTy .nil) (.var resVar) :=
  app_unify_resolved_heads_of_noop_domain st fuel argTy retTy resVar
    h_dom.argTypeNone h_dom.argRowNone h_dom.retTypeNone h_dom.retRowNone h_dom.resUnbound

/--
Success decomposition variant that discharges resolved-head assumptions from
no-op domain conditions.
-/
theorem app_unify_function_shape_witness_of_success_noop_domain
    (st stAfter : UnifyState) (fuel : Nat) (argTy retTy : Ty) (resVar : TypeVarId)
    (h_arg_type : ∀ v ∈ freeTypeVars argTy, st.subst.typeMap v = none)
    (h_arg_row : ∀ v ∈ freeRowVars argTy, st.subst.rowMap v = none)
    (h_ret_type : ∀ v ∈ freeTypeVars retTy, st.subst.typeMap v = none)
    (h_ret_row : ∀ v ∈ freeRowVars retTy, st.subst.rowMap v = none)
    (h_res_unbound : st.subst.typeMap resVar = none)
    (h_beq_raw :
      ((Ty.function (.cons argTy .nil) retTy) == (Ty.function (.cons argTy .nil) (.var resVar))) = false)
    (h_unify :
      unify st (fuel + 1) (.function (.cons argTy .nil) retTy)
        (.function (.cons argTy .nil) (.var resVar)) = .ok stAfter) :
    ∃ stTail,
      unifyTyList st fuel (.cons argTy .nil) (.cons argTy .nil) = .ok stTail ∧
      unify stTail fuel retTy (.var resVar) = .ok stAfter := by
  have h_heads := app_unify_resolved_heads_of_noop_domain
    st fuel argTy retTy resVar h_arg_type h_arg_row h_ret_type h_ret_row h_res_unbound
  rcases h_heads with ⟨h_head_l, h_head_r⟩
  have h_beq :
      (applySubstCompat st.subst fuel (.function (.cons argTy .nil) retTy)
        == applySubstCompat st.subst fuel (.function (.cons argTy .nil) (.var resVar))) = false := by
    simpa [h_head_l, h_head_r] using h_beq_raw
  exact app_unify_function_shape_witness_of_success_resolved_heads
    st stAfter fuel argTy retTy resVar h_head_l h_head_r h_beq h_unify

/-- Contract wrapper for `app_unify_function_shape_witness_of_success_noop_domain`. -/
theorem app_unify_function_shape_witness_of_success_contract
    (st stAfter : UnifyState) (fuel : Nat) (argTy retTy : Ty) (resVar : TypeVarId)
    (h_dom : AppUnifyNoopDomain st argTy retTy resVar)
    (h_beq_raw :
      ((Ty.function (.cons argTy .nil) retTy) == (Ty.function (.cons argTy .nil) (.var resVar))) = false)
    (h_unify :
      unify st (fuel + 1) (.function (.cons argTy .nil) retTy)
        (.function (.cons argTy .nil) (.var resVar)) = .ok stAfter) :
    ∃ stTail,
      unifyTyList st fuel (.cons argTy .nil) (.cons argTy .nil) = .ok stTail ∧
      unify stTail fuel retTy (.var resVar) = .ok stAfter :=
  app_unify_function_shape_witness_of_success_noop_domain
    st stAfter fuel argTy retTy resVar
    h_dom.argTypeNone h_dom.argRowNone h_dom.retTypeNone h_dom.retRowNone h_dom.resUnbound
    h_beq_raw h_unify

/--
If singleton-parameter list unification succeeds against itself, the resulting
state is unchanged.
-/
theorem unifyTyList_singleton_self_success_state_eq
    (st stTail : UnifyState) (fuel : Nat) (argTy : Ty)
    (h_params :
      unifyTyList st fuel (.cons argTy .nil) (.cons argTy .nil) = .ok stTail) :
    stTail = st := by
  cases fuel with
  | zero =>
    simp [unifyTyList] at h_params
  | succ fuel' =>
    simp [unifyTyList] at h_params
    cases h_unify : unify st fuel' argTy argTy with
    | err e =>
      simp [h_unify] at h_params
    | ok stMid =>
      cases fuel' with
      | zero =>
        simp [h_unify, unifyTyList] at h_params
      | succ fuel'' =>
        simp [h_unify, unifyTyList] at h_params
        have h_refl : unify st (fuel'' + 1) argTy argTy = .ok st := by
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
            (unifyReflexive' st fuel'' argTy)
        rw [h_unify] at h_refl
        cases h_refl
        simpa using h_params.symm

/-- Closed singleton type-lists are fixed points of substitution at any fuel. -/
theorem applySubstTyList_nil (s : Subst) (fuel : Nat) :
    applySubstTyList s fuel .nil = .nil := by
  cases fuel with
  | zero =>
    simp [applySubstTyList]
  | succ fuel' =>
    simp [applySubstTyList]

/-- Closed singleton type-lists are fixed points of substitution at any fuel. -/
theorem applySubstTyList_singleton_closed
    (s : Subst) (fuel : Nat) (ty : Ty)
    (h_ftv : freeTypeVars ty = [])
    (h_frv : freeRowVars ty = []) :
    applySubstTyList s fuel (.cons ty .nil) = .cons ty .nil := by
  cases fuel with
  | zero =>
    simp [applySubstTyList]
  | succ fuel' =>
    have h_closed : applySubst s fuel' ty = ty := by
      simpa [applySubstCompat] using
        (applySubstCompat_closed s fuel' ty h_ftv h_frv)
    simp [applySubstTyList, applySubstTyList_nil, h_closed]

/-- For equal single-parameter function heads, BEq-false implies tail BEq-false. -/
theorem app_function_beq_false_implies_tail_beq_false
    (argTy retTy : Ty) (resVar : TypeVarId)
    (h_fn_beq :
      ((Ty.function (.cons argTy .nil) retTy) == (Ty.function (.cons argTy .nil) (.var resVar))) = false) :
    (retTy == .var resVar) = false := by
  have h_params_refl : (beqTyList (.cons argTy .nil) (.cons argTy .nil)) = true := by
    simpa using beqTyList_refl (.cons argTy .nil)
  cases h_tail : (retTy == .var resVar) with
  | false =>
    rfl
  | true =>
    have h_tail' : beqTy retTy (.var resVar) = true := by
      simpa [BEq.beq] using h_tail
    have h_fn_true :
        ((Ty.function (.cons argTy .nil) retTy) == (Ty.function (.cons argTy .nil) (.var resVar))) = true := by
      simp [BEq.beq, beqTy, h_params_refl, h_tail']
    rw [h_fn_true] at h_fn_beq
    contradiction

/-- If return type is not a variable, app-function BEq is false. -/
theorem app_function_beq_false_of_not_var
    (argTy retTy : Ty) (resVar : TypeVarId)
    (h_not_var : ∀ v, retTy ≠ .var v) :
    ((Ty.function (.cons argTy .nil) retTy) == (Ty.function (.cons argTy .nil) (.var resVar))) = false := by
  have h_params_refl : (beqTyList (.cons argTy .nil) (.cons argTy .nil)) = true := by
    simpa using beqTyList_refl (.cons argTy .nil)
  cases retTy with
  | var v =>
    exfalso
    exact h_not_var v rfl
  | int | intN _ _ | float | floatN _ | decimal _ _ | bool | string | html | markdown | atom | date | dateTime | unit | dynamic
    | list _ | map _ _ | set _ | option _ | result _ _ | existential _ _ | fixedSizeList _ _ | tensor _ _ | sum _ _ | «opaque» _ _
    | function _ _ | functionEff _ _ _ | «forall» _ _ | app _ _ | constructor _ _ _ | record _ _ | anonRecord _ | dataframe _ | groupedFrame _ _ | tagged _ _ | column _ | stream _ | task _ | actor _ | arc _
    | row _ | tuple _ =>
      simp [BEq.beq, beqTy, h_params_refl]

/--
Bridge from raw app unification success to result-variable equality: if the
function/function branch heads are resolved, BEq fast-path is excluded, and the
tail `unify` success can be reinterpreted as a `bindTypeVar` success, then the
idempotent equality premise follows.
-/
theorem app_unify_result_eq_of_unify_success_resolved_heads_tail_bind_idempotent
    (st stAfter : UnifyState) (fuel : Nat) (argTy retTy : Ty) (resVar : TypeVarId)
    (h_head_l :
      applySubstCompat st.subst fuel (.function (.cons argTy .nil) retTy) =
        .function (.cons argTy .nil) retTy)
    (h_head_r :
      applySubstCompat st.subst fuel (.function (.cons argTy .nil) (.var resVar)) =
        .function (.cons argTy .nil) (.var resVar))
    (h_beq :
      (applySubstCompat st.subst fuel (.function (.cons argTy .nil) retTy)
        == applySubstCompat st.subst fuel (.function (.cons argTy .nil) (.var resVar))) = false)
    (h_unify :
      unify st (fuel + 1) (.function (.cons argTy .nil) retTy)
        (.function (.cons argTy .nil) (.var resVar)) = .ok stAfter)
    (h_tail_to_bind :
      ∀ stTail,
        unify stTail fuel retTy (.var resVar) = .ok stAfter →
        bindTypeVar stTail resVar retTy fuel = .ok stAfter)
    (h_idemp : stAfter.subst.Idempotent) :
    applySubst stAfter.subst (fuel + 1) (.var resVar) =
      applySubst stAfter.subst (fuel + 1) retTy := by
  rcases app_unify_function_shape_witness_of_success_resolved_heads
      st stAfter fuel argTy retTy resVar h_head_l h_head_r h_beq h_unify with
    ⟨stTail, h_params, h_tail_unify⟩
  have h_tail_bind : bindTypeVar stTail resVar retTy fuel = .ok stAfter :=
    h_tail_to_bind stTail h_tail_unify
  exact app_unify_result_eq_of_function_tail_bind_idempotent
    st stTail stAfter fuel argTy retTy resVar h_params h_tail_bind h_idemp

/--
Tail-branch contract: when tail unification is run at successor fuel with
resolved heads and BEq fast-path excluded, success is exactly a `bindTypeVar`
success on the result variable.
-/
theorem tail_unify_to_bindTypeVar_of_success_resolved_heads_nonbeq
    (st stAfter : UnifyState) (fuel : Nat) (retTy : Ty) (resVar : TypeVarId)
    (h_not_var : ∀ v, retTy ≠ .var v)
    (h_head_l : applySubstCompat st.subst fuel retTy = retTy)
    (h_head_r : applySubstCompat st.subst fuel (.var resVar) = .var resVar)
    (h_beq :
      (applySubstCompat st.subst fuel retTy
        == applySubstCompat st.subst fuel (.var resVar)) = false)
    (h_unify : unify st (fuel + 1) retTy (.var resVar) = .ok stAfter) :
    bindTypeVar st resVar retTy fuel = .ok stAfter := by
  have h_beq' : (retTy == .var resVar) = false := by
    simpa [h_head_l, h_head_r] using h_beq
  cases retTy with
  | var v =>
    exfalso
    exact h_not_var v rfl
  | int | intN _ _ | float | floatN _ | decimal _ _ | bool | string | html | markdown | atom | date | dateTime | unit | dynamic
    | list _ | map _ _ | set _ | option _ | result _ _ | existential _ _ | fixedSizeList _ _ | tensor _ _ | sum _ _ | «opaque» _ _
    | function _ _ | functionEff _ _ _ | «forall» _ _ | app _ _ | constructor _ _ _ | record _ _ | anonRecord _ | dataframe _ | groupedFrame _ _ | tagged _ _ | column _ | stream _ | task _ | actor _ | arc _
    | row _ | tuple _ =>
      simpa [unify, h_head_l, h_head_r, h_beq'] using h_unify

/--
Tail-branch equality contract without return-shape restriction: under resolved
heads + non-BEq, successful tail unification yields the result-variable
equality directly (using idempotence in the variable-head case).
-/
theorem tail_unify_result_eq_of_success_resolved_heads_nonbeq_idempotent
    (st stAfter : UnifyState) (fuel : Nat) (retTy : Ty) (resVar : TypeVarId)
    (h_head_l : applySubstCompat st.subst fuel retTy = retTy)
    (h_head_r : applySubstCompat st.subst fuel (.var resVar) = .var resVar)
    (h_beq :
      (applySubstCompat st.subst fuel retTy
        == applySubstCompat st.subst fuel (.var resVar)) = false)
    (h_unify : unify st (fuel + 1) retTy (.var resVar) = .ok stAfter)
    (h_idemp : stAfter.subst.Idempotent) :
    applySubst stAfter.subst (fuel + 1) (.var resVar) =
      applySubst stAfter.subst (fuel + 1) retTy := by
  by_cases hvar : ∃ v, retTy = .var v
  · rcases hvar with ⟨v, rfl⟩
    have h_beq' : ((.var v : Ty) == (.var resVar : Ty)) = false := by
      simpa [h_head_l, h_head_r] using h_beq
    have h_bind : bindTypeVar st v (.var resVar) fuel = .ok stAfter := by
      simpa [unify, h_head_l, h_head_r, h_beq'] using h_unify
    have h_eq :=
      bindTypeVarConsistentIdempotent st v (.var resVar) fuel stAfter h_bind h_idemp
    simpa using h_eq.symm
  · have h_not_var : ∀ v, retTy ≠ .var v := by
      intro v hv
      exact hvar ⟨v, hv⟩
    have h_bind : bindTypeVar st resVar retTy fuel = .ok stAfter :=
      tail_unify_to_bindTypeVar_of_success_resolved_heads_nonbeq
        st stAfter fuel retTy resVar h_not_var h_head_l h_head_r h_beq h_unify
    exact app_unify_result_eq_of_bindTypeVar_idempotent
      st fuel retTy resVar stAfter h_bind h_idemp

/--
Shifted app bridge: with an outer app unification run at `fuel + 2`, no-op
domains and tail non-BEq/non-variable assumptions are enough to recover the
result-variable equality at `fuel + 1`.
-/
theorem app_unify_result_eq_of_unify_success_noop_domain_tail_nonbeq_idempotent_succ
    (st stAfter : UnifyState) (fuel : Nat) (argTy retTy : Ty) (resVar : TypeVarId)
    (h_arg_type : ∀ v ∈ freeTypeVars argTy, st.subst.typeMap v = none)
    (h_arg_row : ∀ v ∈ freeRowVars argTy, st.subst.rowMap v = none)
    (h_ret_type : ∀ v ∈ freeTypeVars retTy, st.subst.typeMap v = none)
    (h_ret_row : ∀ v ∈ freeRowVars retTy, st.subst.rowMap v = none)
    (h_res_unbound : st.subst.typeMap resVar = none)
    (h_fn_beq_raw :
      ((Ty.function (.cons argTy .nil) retTy) == (Ty.function (.cons argTy .nil) (.var resVar))) = false)
    (h_unify :
      unify st (fuel + 2) (.function (.cons argTy .nil) retTy)
        (.function (.cons argTy .nil) (.var resVar)) = .ok stAfter)
    (h_idemp : stAfter.subst.Idempotent) :
    applySubst stAfter.subst (fuel + 1) (.var resVar) =
      applySubst stAfter.subst (fuel + 1) retTy := by
  rcases app_unify_function_shape_witness_of_success_noop_domain
      st stAfter (fuel + 1) argTy retTy resVar
      h_arg_type h_arg_row h_ret_type h_ret_row h_res_unbound
      h_fn_beq_raw h_unify with
    ⟨stTail, h_params, h_tail_unify⟩
  have h_tail_eq : stTail = st :=
    unifyTyList_singleton_self_success_state_eq st stTail (fuel + 1) argTy h_params
  have h_tail_unify_st : unify st (fuel + 1) retTy (.var resVar) = .ok stAfter := by
    simpa [h_tail_eq] using h_tail_unify
  have h_head_l_tail : applySubstCompat st.subst fuel retTy = retTy := by
    obtain ⟨h_noop_ty, _, _, _⟩ := applySubst_noop st.subst fuel
    exact h_noop_ty retTy h_ret_type h_ret_row
  have h_head_r_tail : applySubstCompat st.subst fuel (.var resVar) = .var resVar := by
    cases fuel with
    | zero =>
      simp [applySubstCompat, applySubst]
    | succ fuel' =>
      simp [applySubstCompat, applySubst, h_res_unbound]
  have h_tail_beq :
      (applySubstCompat st.subst fuel retTy == applySubstCompat st.subst fuel (.var resVar)) = false := by
      have h_tail_beq_raw : (retTy == .var resVar) = false :=
        app_function_beq_false_implies_tail_beq_false argTy retTy resVar h_fn_beq_raw
      simpa [h_head_l_tail, h_head_r_tail] using h_tail_beq_raw
  exact tail_unify_result_eq_of_success_resolved_heads_nonbeq_idempotent
    st stAfter fuel retTy resVar h_head_l_tail h_head_r_tail h_tail_beq h_tail_unify_st h_idemp

/-- Contract wrapper for shifted app equality bridge. -/
theorem app_unify_result_eq_of_unify_success_contract_succ
    (st stAfter : UnifyState) (fuel : Nat) (argTy retTy : Ty) (resVar : TypeVarId)
    (h_dom : AppUnifyNoopDomain st argTy retTy resVar)
    (h_fn_beq_raw :
      ((Ty.function (.cons argTy .nil) retTy) == (Ty.function (.cons argTy .nil) (.var resVar))) = false)
    (h_unify :
      unify st (fuel + 2) (.function (.cons argTy .nil) retTy)
        (.function (.cons argTy .nil) (.var resVar)) = .ok stAfter)
    (h_idemp : stAfter.subst.Idempotent) :
    applySubst stAfter.subst (fuel + 1) (.var resVar) =
      applySubst stAfter.subst (fuel + 1) retTy :=
  app_unify_result_eq_of_unify_success_noop_domain_tail_nonbeq_idempotent_succ
    st stAfter fuel argTy retTy resVar
    h_dom.argTypeNone h_dom.argRowNone h_dom.retTypeNone h_dom.retRowNone h_dom.resUnbound
    h_fn_beq_raw h_unify h_idemp

/--
Shifted app bridge to tail binding only: from outer app-unify success at
`fuel+2`, no-op domain + tail non-BEq/non-variable assumptions recover the
tail `bindTypeVar` success at fuel.
-/
theorem app_unify_tail_bind_of_success_noop_domain_tail_nonbeq_succ
    (st stAfter : UnifyState) (fuel : Nat) (argTy retTy : Ty) (resVar : TypeVarId)
    (h_arg_type : ∀ v ∈ freeTypeVars argTy, st.subst.typeMap v = none)
    (h_arg_row : ∀ v ∈ freeRowVars argTy, st.subst.rowMap v = none)
    (h_ret_type : ∀ v ∈ freeTypeVars retTy, st.subst.typeMap v = none)
    (h_ret_row : ∀ v ∈ freeRowVars retTy, st.subst.rowMap v = none)
    (h_res_unbound : st.subst.typeMap resVar = none)
    (h_fn_beq_raw :
      ((Ty.function (.cons argTy .nil) retTy) == (Ty.function (.cons argTy .nil) (.var resVar))) = false)
    (h_not_var : ∀ v, retTy ≠ .var v)
    (h_unify :
      unify st (fuel + 2) (.function (.cons argTy .nil) retTy)
        (.function (.cons argTy .nil) (.var resVar)) = .ok stAfter) :
    bindTypeVar st resVar retTy fuel = .ok stAfter := by
  rcases app_unify_function_shape_witness_of_success_noop_domain
      st stAfter (fuel + 1) argTy retTy resVar
      h_arg_type h_arg_row h_ret_type h_ret_row h_res_unbound
      h_fn_beq_raw h_unify with
    ⟨stTail, h_params, h_tail_unify⟩
  have h_tail_eq : stTail = st :=
    unifyTyList_singleton_self_success_state_eq st stTail (fuel + 1) argTy h_params
  have h_tail_unify_st : unify st (fuel + 1) retTy (.var resVar) = .ok stAfter := by
    simpa [h_tail_eq] using h_tail_unify
  have h_head_l_tail : applySubstCompat st.subst fuel retTy = retTy := by
    obtain ⟨h_noop_ty, _, _, _⟩ := applySubst_noop st.subst fuel
    exact h_noop_ty retTy h_ret_type h_ret_row
  have h_head_r_tail : applySubstCompat st.subst fuel (.var resVar) = .var resVar := by
    cases fuel with
    | zero =>
      simp [applySubstCompat, applySubst]
    | succ fuel' =>
      simp [applySubstCompat, applySubst, h_res_unbound]
  have h_tail_beq :
      (applySubstCompat st.subst fuel retTy == applySubstCompat st.subst fuel (.var resVar)) = false := by
    have h_tail_beq_raw : (retTy == .var resVar) = false :=
      app_function_beq_false_implies_tail_beq_false argTy retTy resVar h_fn_beq_raw
    simpa [h_head_l_tail, h_head_r_tail] using h_tail_beq_raw
  exact tail_unify_to_bindTypeVar_of_success_resolved_heads_nonbeq
    st stAfter fuel retTy resVar h_not_var h_head_l_tail h_head_r_tail h_tail_beq h_tail_unify_st

/-- Contract wrapper for shifted app tail-bind bridge. -/
theorem app_unify_tail_bind_of_success_contract_succ
    (st stAfter : UnifyState) (fuel : Nat) (argTy retTy : Ty) (resVar : TypeVarId)
    (h_dom : AppUnifyNoopDomain st argTy retTy resVar)
    (h_fn_beq_raw :
      ((Ty.function (.cons argTy .nil) retTy) == (Ty.function (.cons argTy .nil) (.var resVar))) = false)
    (h_not_var : ∀ v, retTy ≠ .var v)
    (h_unify :
      unify st (fuel + 2) (.function (.cons argTy .nil) retTy)
        (.function (.cons argTy .nil) (.var resVar)) = .ok stAfter) :
    bindTypeVar st resVar retTy fuel = .ok stAfter :=
  app_unify_tail_bind_of_success_noop_domain_tail_nonbeq_succ
    st stAfter fuel argTy retTy resVar
    h_dom.argTypeNone h_dom.argRowNone h_dom.retTypeNone h_dom.retRowNone h_dom.resUnbound
    h_fn_beq_raw h_not_var h_unify

/--
App-tail-bind success preserves the above-threshold unbound invariant when the
bound result variable is known to be below `nextTypeVar`.
-/
theorem typeVarsAboveNextUnbound_after_app_unify_tail_bind_contract_succ
    (st stAfter : UnifyState) (fuel : Nat) (argTy retTy : Ty) (resVar : TypeVarId)
    (h_inv : TypeVarsAboveNextUnbound st)
    (h_lt : resVar < st.nextTypeVar)
    (h_dom : AppUnifyNoopDomain st argTy retTy resVar)
    (h_fn_beq_raw :
      ((Ty.function (.cons argTy .nil) retTy) == (Ty.function (.cons argTy .nil) (.var resVar))) = false)
    (h_not_var : ∀ v, retTy ≠ .var v)
    (h_unify :
      unify st (fuel + 2) (.function (.cons argTy .nil) retTy)
        (.function (.cons argTy .nil) (.var resVar)) = .ok stAfter) :
    TypeVarsAboveNextUnbound stAfter := by
  have h_bind :
      bindTypeVar st resVar retTy fuel = .ok stAfter :=
    app_unify_tail_bind_of_success_contract_succ
      st stAfter fuel argTy retTy resVar h_dom h_fn_beq_raw h_not_var h_unify
  exact typeVarsAboveNextUnbound_bindTypeVar_lt_next
    st stAfter resVar retTy fuel h_inv h_lt h_bind

/--
Fresh-result specialization of invariant transport across the app tail-bind
contract: after one `freshTypeVar` step, the contract result preserves the
above-threshold unbound invariant.
-/
theorem typeVarsAboveNextUnbound_after_app_unify_tail_bind_contract_succ_fresh
    (st stAfter : UnifyState) (fuel : Nat) (argTy retTy : Ty)
    (h_inv : TypeVarsAboveNextUnbound st)
    (h_dom : AppUnifyNoopDomain (st.freshTypeVar).2 argTy retTy (st.freshTypeVar).1)
    (h_fn_beq_raw :
      ((Ty.function (.cons argTy .nil) retTy) ==
        (Ty.function (.cons argTy .nil) (.var (st.freshTypeVar).1))) = false)
    (h_not_var : ∀ v, retTy ≠ .var v)
    (h_unify :
      unify (st.freshTypeVar).2 (fuel + 2) (.function (.cons argTy .nil) retTy)
        (.function (.cons argTy .nil) (.var (st.freshTypeVar).1)) = .ok stAfter) :
    TypeVarsAboveNextUnbound stAfter := by
  have h_inv_fresh : TypeVarsAboveNextUnbound (st.freshTypeVar).2 :=
    typeVarsAboveNextUnbound_after_freshTypeVar st h_inv
  have h_lt_fresh : (st.freshTypeVar).1 < (st.freshTypeVar).2.nextTypeVar := by
    simp [UnifyState.freshTypeVar]
  exact typeVarsAboveNextUnbound_after_app_unify_tail_bind_contract_succ
    (st := (st.freshTypeVar).2) (stAfter := stAfter) (fuel := fuel)
    (argTy := argTy) (retTy := retTy) (resVar := (st.freshTypeVar).1)
    h_inv_fresh h_lt_fresh h_dom h_fn_beq_raw h_not_var h_unify

/--
Shifted app tail-bind bridge specialized to closed arg/ret types and fresh
result variable under the above-`nextTypeVar` invariant.
-/
theorem app_unify_tail_bind_of_success_closed_fresh_succ
    (st stAfter : UnifyState) (fuel : Nat) (argTy retTy : Ty)
    (h_arg_ftv : freeTypeVars argTy = [])
    (h_arg_frv : freeRowVars argTy = [])
    (h_ret_ftv : freeTypeVars retTy = [])
    (h_ret_frv : freeRowVars retTy = [])
    (h_inv : TypeVarsAboveNextUnbound st)
    (h_unify :
      unify st (fuel + 2) (.function (.cons argTy .nil) retTy)
        (.function (.cons argTy .nil) (.var (st.freshTypeVar).1)) = .ok stAfter) :
    bindTypeVar st (st.freshTypeVar).1 retTy fuel = .ok stAfter := by
  let h_dom : AppUnifyNoopDomain st argTy retTy (st.freshTypeVar).1 :=
    appUnifyNoopDomain_of_closed_types_with_freshRes
      st argTy retTy h_arg_ftv h_arg_frv h_ret_ftv h_ret_frv h_inv
  have h_not_var : ∀ v, retTy ≠ .var v := closed_type_not_var retTy h_ret_ftv
  have h_fn_beq_raw :
      ((Ty.function (.cons argTy .nil) retTy) ==
        (Ty.function (.cons argTy .nil) (.var (st.freshTypeVar).1))) = false :=
    app_function_beq_false_of_not_var argTy retTy (st.freshTypeVar).1 h_not_var
  exact app_unify_tail_bind_of_success_contract_succ
    st stAfter fuel argTy retTy (st.freshTypeVar).1 h_dom h_fn_beq_raw h_not_var h_unify

/--
Empty-substitution specialization of the closed+fresh shifted app tail-bind
bridge.
-/
theorem app_unify_tail_bind_of_success_closed_fresh_succ_of_subst_empty
    (st stAfter : UnifyState) (fuel : Nat) (argTy retTy : Ty)
    (h_empty : st.subst = Subst.empty)
    (h_arg_ftv : freeTypeVars argTy = [])
    (h_arg_frv : freeRowVars argTy = [])
    (h_ret_ftv : freeTypeVars retTy = [])
    (h_ret_frv : freeRowVars retTy = [])
    (h_unify :
      unify st (fuel + 2) (.function (.cons argTy .nil) retTy)
        (.function (.cons argTy .nil) (.var (st.freshTypeVar).1)) = .ok stAfter) :
    bindTypeVar st (st.freshTypeVar).1 retTy fuel = .ok stAfter := by
  have h_inv : TypeVarsAboveNextUnbound st :=
    typeVarsAboveNextUnbound_of_subst_empty st h_empty
  exact app_unify_tail_bind_of_success_closed_fresh_succ
    st stAfter fuel argTy retTy
    h_arg_ftv h_arg_frv h_ret_ftv h_ret_frv h_inv h_unify

/--
Shifted app equality bridge specialized to closed arg/ret types and fresh
result variable under the above-`nextTypeVar` invariant.
-/
theorem app_unify_result_eq_of_success_closed_fresh_succ
    (st stAfter : UnifyState) (fuel : Nat) (argTy retTy : Ty)
    (h_arg_ftv : freeTypeVars argTy = [])
    (h_arg_frv : freeRowVars argTy = [])
    (h_ret_ftv : freeTypeVars retTy = [])
    (h_ret_frv : freeRowVars retTy = [])
    (h_inv : TypeVarsAboveNextUnbound st)
    (h_unify :
      unify st (fuel + 2) (.function (.cons argTy .nil) retTy)
        (.function (.cons argTy .nil) (.var (st.freshTypeVar).1)) = .ok stAfter)
    (h_idemp : stAfter.subst.Idempotent) :
    applySubst stAfter.subst (fuel + 1) (.var (st.freshTypeVar).1) =
      applySubst stAfter.subst (fuel + 1) retTy := by
  let h_dom : AppUnifyNoopDomain st argTy retTy (st.freshTypeVar).1 :=
    appUnifyNoopDomain_of_closed_types_with_freshRes
      st argTy retTy h_arg_ftv h_arg_frv h_ret_ftv h_ret_frv h_inv
  have h_not_var : ∀ v, retTy ≠ .var v := closed_type_not_var retTy h_ret_ftv
  have h_fn_beq_raw :
      ((Ty.function (.cons argTy .nil) retTy) ==
        (Ty.function (.cons argTy .nil) (.var (st.freshTypeVar).1))) = false :=
    app_function_beq_false_of_not_var argTy retTy (st.freshTypeVar).1 h_not_var
  exact app_unify_result_eq_of_unify_success_contract_succ
    st stAfter fuel argTy retTy (st.freshTypeVar).1 h_dom h_fn_beq_raw h_unify h_idemp

/--
Empty-substitution specialization of the closed+fresh shifted app result-eq
bridge.
-/
theorem app_unify_result_eq_of_success_closed_fresh_succ_of_subst_empty
    (st stAfter : UnifyState) (fuel : Nat) (argTy retTy : Ty)
    (h_empty : st.subst = Subst.empty)
    (h_arg_ftv : freeTypeVars argTy = [])
    (h_arg_frv : freeRowVars argTy = [])
    (h_ret_ftv : freeTypeVars retTy = [])
    (h_ret_frv : freeRowVars retTy = [])
    (h_unify :
      unify st (fuel + 2) (.function (.cons argTy .nil) retTy)
        (.function (.cons argTy .nil) (.var (st.freshTypeVar).1)) = .ok stAfter)
    (h_idemp : stAfter.subst.Idempotent) :
    applySubst stAfter.subst (fuel + 1) (.var (st.freshTypeVar).1) =
      applySubst stAfter.subst (fuel + 1) retTy := by
  have h_inv : TypeVarsAboveNextUnbound st :=
    typeVarsAboveNextUnbound_of_subst_empty st h_empty
  exact app_unify_result_eq_of_success_closed_fresh_succ
    st stAfter fuel argTy retTy
    h_arg_ftv h_arg_frv h_ret_ftv h_ret_frv h_inv h_unify h_idemp

/--
Closed-type app bridge in `HasTypeU`: when app unification succeeds against a
fresh result variable and the shifted result-equality contract holds, app
typing follows end-to-end without additional hooks.
-/
theorem app_unify_resolved_fn_shape_of_success_closed_fresh_succ
    (st stAfter : UnifyState) (fuel : Nat) (argTy retTy : Ty)
    (h_arg_ftv : freeTypeVars argTy = [])
    (h_arg_frv : freeRowVars argTy = [])
    (h_ret_ftv : freeTypeVars retTy = [])
    (h_ret_frv : freeRowVars retTy = [])
    (h_inv : TypeVarsAboveNextUnbound st)
    (h_unify :
      unify st (fuel + 2) (.function (.cons argTy .nil) retTy)
        (.function (.cons argTy .nil) (.var (st.freshTypeVar).1)) = .ok stAfter)
    (h_idemp : stAfter.subst.Idempotent) :
    applySubstCompat stAfter.subst (fuel + 1) (.function (.cons argTy .nil) retTy) =
      .function
        (.cons (applySubstCompat stAfter.subst fuel argTy) .nil)
        (applySubstCompat stAfter.subst (fuel + 1) (.var (st.freshTypeVar).1)) := by
  have h_res_eq :
      applySubstCompat stAfter.subst (fuel + 1) (.var (st.freshTypeVar).1) =
        applySubstCompat stAfter.subst (fuel + 1) retTy :=
    app_unify_result_eq_of_success_closed_fresh_succ
      st stAfter fuel argTy retTy h_arg_ftv h_arg_frv h_ret_ftv h_ret_frv h_inv h_unify h_idemp
  have h_ret_closed_fuel :
      applySubstCompat stAfter.subst fuel retTy = retTy :=
    applySubstCompat_closed stAfter.subst fuel retTy h_ret_ftv h_ret_frv
  have h_ret_closed_succ :
      applySubstCompat stAfter.subst (fuel + 1) retTy = retTy :=
    applySubstCompat_closed stAfter.subst (fuel + 1) retTy h_ret_ftv h_ret_frv
  have h_arg_closed :
      applySubstCompat stAfter.subst fuel argTy = argTy :=
    applySubstCompat_closed stAfter.subst fuel argTy h_arg_ftv h_arg_frv
  have h_resolved_ret :
      applySubstCompat stAfter.subst fuel retTy =
        applySubstCompat stAfter.subst (fuel + 1) (.var (st.freshTypeVar).1) := by
    calc
      applySubstCompat stAfter.subst fuel retTy = retTy := h_ret_closed_fuel
      _ = applySubstCompat stAfter.subst (fuel + 1) retTy := by
        symm
        exact h_ret_closed_succ
      _ = applySubstCompat stAfter.subst (fuel + 1) (.var (st.freshTypeVar).1) := by
        symm
        exact h_res_eq
  simp [applySubstCompat, applySubst, applySubstTyList_singleton_closed,
    h_arg_ftv, h_arg_frv, h_arg_closed, h_resolved_ret]

/--
Empty-substitution specialization of the closed+fresh successor-fuel app
resolved-shape bridge.
-/
theorem app_unify_resolved_fn_shape_of_success_closed_fresh_succ_of_subst_empty
    (st stAfter : UnifyState) (fuel : Nat) (argTy retTy : Ty)
    (h_empty : st.subst = Subst.empty)
    (h_arg_ftv : freeTypeVars argTy = [])
    (h_arg_frv : freeRowVars argTy = [])
    (h_ret_ftv : freeTypeVars retTy = [])
    (h_ret_frv : freeRowVars retTy = [])
    (h_unify :
      unify st (fuel + 2) (.function (.cons argTy .nil) retTy)
        (.function (.cons argTy .nil) (.var (st.freshTypeVar).1)) = .ok stAfter)
    (h_idemp : stAfter.subst.Idempotent) :
    applySubstCompat stAfter.subst (fuel + 1) (.function (.cons argTy .nil) retTy) =
      .function
        (.cons (applySubstCompat stAfter.subst fuel argTy) .nil)
        (applySubstCompat stAfter.subst (fuel + 1) (.var (st.freshTypeVar).1)) := by
  have h_inv : TypeVarsAboveNextUnbound st :=
    typeVarsAboveNextUnbound_of_subst_empty st h_empty
  exact app_unify_resolved_fn_shape_of_success_closed_fresh_succ
    st stAfter fuel argTy retTy
    h_arg_ftv h_arg_frv h_ret_ftv h_ret_frv h_inv h_unify h_idemp

/--
Packaged closed+fresh successor-fuel app resolved-shape premise.
This is the directly proved app-side premise fragment currently available for
resolved-shape-driven recursion in `HasTypeU`.
-/
def AppResolvedShapeFromUnifyClosedFreshSucc : Prop :=
  ∀ st stAfter fuel argTy retTy,
    freeTypeVars argTy = [] →
    freeRowVars argTy = [] →
    freeTypeVars retTy = [] →
    freeRowVars retTy = [] →
    TypeVarsAboveNextUnbound st →
    unify st (fuel + 2) (.function (.cons argTy .nil) retTy)
      (.function (.cons argTy .nil) (.var (st.freshTypeVar).1)) = .ok stAfter →
    stAfter.subst.Idempotent →
    applySubstCompat stAfter.subst (fuel + 1) (.function (.cons argTy .nil) retTy) =
      .function
        (.cons (applySubstCompat stAfter.subst fuel argTy) .nil)
        (applySubstCompat stAfter.subst (fuel + 1) (.var (st.freshTypeVar).1))

/-- Closed+fresh successor-fuel app resolved-shape premise is provable. -/
theorem appResolvedShapeFromUnifyClosedFreshSucc_proved :
    AppResolvedShapeFromUnifyClosedFreshSucc := by
  intro st stAfter fuel argTy retTy h_arg_ftv h_arg_frv h_ret_ftv h_ret_frv h_inv h_unify h_idemp
  exact app_unify_resolved_fn_shape_of_success_closed_fresh_succ
    st stAfter fuel argTy retTy h_arg_ftv h_arg_frv h_ret_ftv h_ret_frv h_inv h_unify h_idemp

/--
Closed-type app bridge in `HasTypeU`: when app unification succeeds against a
fresh result variable and the shifted result-equality contract holds, app
typing follows end-to-end without additional hooks.
-/
theorem inferExprUnify_app_step_sound_hasTypeU_closed_fresh_succ
    {env : TermEnv} {fn arg : CoreExpr} {argTy retTy : Ty}
    {st stAfter : UnifyState} {fuel : Nat}
    (h_fn : HasTypeU env fn (.function (.cons argTy .nil) retTy))
    (h_arg : HasTypeU env arg argTy)
    (h_arg_ftv : freeTypeVars argTy = [])
    (h_arg_frv : freeRowVars argTy = [])
    (h_ret_ftv : freeTypeVars retTy = [])
    (h_ret_frv : freeRowVars retTy = [])
    (h_inv : TypeVarsAboveNextUnbound st)
    (h_unify :
      unify st (fuel + 2) (.function (.cons argTy .nil) retTy)
        (.function (.cons argTy .nil) (.var (st.freshTypeVar).1)) = .ok stAfter)
    (h_idemp : stAfter.subst.Idempotent) :
    HasTypeU env (.app fn arg) (applySubstCompat stAfter.subst (fuel + 1) (.var (st.freshTypeVar).1)) := by
  have h_resolved :
      applySubstCompat stAfter.subst (fuel + 1) (.function (.cons argTy .nil) retTy) =
        .function
          (.cons (applySubstCompat stAfter.subst fuel argTy) .nil)
          (applySubstCompat stAfter.subst (fuel + 1) (.var (st.freshTypeVar).1)) :=
    app_unify_resolved_fn_shape_of_success_closed_fresh_succ
      st stAfter fuel argTy retTy
      h_arg_ftv h_arg_frv h_ret_ftv h_ret_frv h_inv h_unify h_idemp
  have h_fn_resolved :
      HasTypeU env fn
        (applySubstCompat stAfter.subst (fuel + 1) (.function (.cons argTy .nil) retTy)) :=
    HasTypeU.subst env fn (.function (.cons argTy .nil) retTy) stAfter.subst (fuel + 1) h_fn
  have h_arg_resolved :
      HasTypeU env arg (applySubstCompat stAfter.subst fuel argTy) :=
    HasTypeU.subst env arg argTy stAfter.subst fuel h_arg
  rw [h_resolved] at h_fn_resolved
  exact HasTypeU.app env fn arg
    (applySubstCompat stAfter.subst fuel argTy)
    (applySubstCompat stAfter.subst (fuel + 1) (.var (st.freshTypeVar).1))
    h_fn_resolved h_arg_resolved

/--
Empty-substitution specialization of the closed+fresh successor-fuel app step
soundness theorem in `HasTypeU`.
-/
theorem inferExprUnify_app_step_sound_hasTypeU_closed_fresh_succ_of_subst_empty
    {env : TermEnv} {fn arg : CoreExpr} {argTy retTy : Ty}
    {st stAfter : UnifyState} {fuel : Nat}
    (h_empty : st.subst = Subst.empty)
    (h_fn : HasTypeU env fn (.function (.cons argTy .nil) retTy))
    (h_arg : HasTypeU env arg argTy)
    (h_arg_ftv : freeTypeVars argTy = [])
    (h_arg_frv : freeRowVars argTy = [])
    (h_ret_ftv : freeTypeVars retTy = [])
    (h_ret_frv : freeRowVars retTy = [])
    (h_unify :
      unify st (fuel + 2) (.function (.cons argTy .nil) retTy)
        (.function (.cons argTy .nil) (.var (st.freshTypeVar).1)) = .ok stAfter)
    (h_idemp : stAfter.subst.Idempotent) :
    HasTypeU env (.app fn arg) (applySubstCompat stAfter.subst (fuel + 1) (.var (st.freshTypeVar).1)) := by
  have h_inv : TypeVarsAboveNextUnbound st :=
    typeVarsAboveNextUnbound_of_subst_empty st h_empty
  exact inferExprUnify_app_step_sound_hasTypeU_closed_fresh_succ
    h_fn h_arg h_arg_ftv h_arg_frv h_ret_ftv h_ret_frv h_inv h_unify h_idemp

/--
Specialized `HasTypeU` app-hook fragment for the closed+fresh successor-fuel
regime where the app-side resolved-shape bridge is fully discharged.
-/
def AppUnifySoundHookUClosedFreshSucc : Prop :=
  ∀ env fn arg st stAfter fuel argTy retTy,
    HasTypeU env fn (.function (.cons argTy .nil) retTy) →
    HasTypeU env arg argTy →
    freeTypeVars argTy = [] →
    freeRowVars argTy = [] →
    freeTypeVars retTy = [] →
    freeRowVars retTy = [] →
    TypeVarsAboveNextUnbound st →
    unify st (fuel + 2) (.function (.cons argTy .nil) retTy)
      (.function (.cons argTy .nil) (.var (st.freshTypeVar).1)) = .ok stAfter →
    stAfter.subst.Idempotent →
    HasTypeU env (.app fn arg) (applySubstCompat stAfter.subst (fuel + 1) (.var (st.freshTypeVar).1))

/-- Closed+fresh successor-fuel app-hook fragment is provable. -/
theorem appUnifySoundHookUClosedFreshSucc_proved :
    AppUnifySoundHookUClosedFreshSucc := by
  intro env fn arg st stAfter fuel argTy retTy
    h_fn h_arg h_arg_ftv h_arg_frv h_ret_ftv h_ret_frv h_inv h_unify h_idemp
  exact inferExprUnify_app_step_sound_hasTypeU_closed_fresh_succ
    h_fn h_arg h_arg_ftv h_arg_frv h_ret_ftv h_ret_frv h_inv h_unify h_idemp

/--
Empty-substitution specialization of the closed+fresh successor-fuel app-hook
fragment in `HasTypeU`.
-/
def AppUnifySoundHookUClosedFreshSuccEmptySubst : Prop :=
  ∀ env fn arg st stAfter fuel argTy retTy,
    st.subst = Subst.empty →
    HasTypeU env fn (.function (.cons argTy .nil) retTy) →
    HasTypeU env arg argTy →
    freeTypeVars argTy = [] →
    freeRowVars argTy = [] →
    freeTypeVars retTy = [] →
    freeRowVars retTy = [] →
    unify st (fuel + 2) (.function (.cons argTy .nil) retTy)
      (.function (.cons argTy .nil) (.var (st.freshTypeVar).1)) = .ok stAfter →
    stAfter.subst.Idempotent →
    HasTypeU env (.app fn arg) (applySubstCompat stAfter.subst (fuel + 1) (.var (st.freshTypeVar).1))

/-- Empty-substitution closed+fresh successor-fuel app-hook fragment is provable. -/
theorem appUnifySoundHookUClosedFreshSuccEmptySubst_proved :
    AppUnifySoundHookUClosedFreshSuccEmptySubst := by
  intro env fn arg st stAfter fuel argTy retTy
    h_empty h_fn h_arg h_arg_ftv h_arg_frv h_ret_ftv h_ret_frv h_unify h_idemp
  exact inferExprUnify_app_step_sound_hasTypeU_closed_fresh_succ_of_subst_empty
    h_empty h_fn h_arg h_arg_ftv h_arg_frv h_ret_ftv h_ret_frv h_unify h_idemp

/--
Specialized shifted app-equality bridge when the starting substitution is
empty; this discharges `AppUnifyNoopDomain` automatically.
-/
theorem app_unify_result_eq_of_unify_success_empty_subst_succ
    (st stAfter : UnifyState) (fuel : Nat) (argTy retTy : Ty) (resVar : TypeVarId)
    (h_empty : st.subst = Subst.empty)
    (h_fn_beq_raw :
      ((Ty.function (.cons argTy .nil) retTy) == (Ty.function (.cons argTy .nil) (.var resVar))) = false)
    (h_unify :
      unify st (fuel + 2) (.function (.cons argTy .nil) retTy)
        (.function (.cons argTy .nil) (.var resVar)) = .ok stAfter)
    (h_idemp : stAfter.subst.Idempotent) :
    applySubst stAfter.subst (fuel + 1) (.var resVar) =
      applySubst stAfter.subst (fuel + 1) retTy := by
  let h_dom : AppUnifyNoopDomain st argTy retTy resVar :=
    appUnifyNoopDomain_of_subst_empty st argTy retTy resVar h_empty
  exact app_unify_result_eq_of_unify_success_contract_succ
    st stAfter fuel argTy retTy resVar h_dom h_fn_beq_raw h_unify h_idemp

/--
Specialized shifted app-tail-bind bridge when the starting substitution is
empty; this discharges `AppUnifyNoopDomain` automatically.
-/
theorem app_unify_tail_bind_of_success_empty_subst_succ
    (st stAfter : UnifyState) (fuel : Nat) (argTy retTy : Ty) (resVar : TypeVarId)
    (h_empty : st.subst = Subst.empty)
    (h_fn_beq_raw :
      ((Ty.function (.cons argTy .nil) retTy) == (Ty.function (.cons argTy .nil) (.var resVar))) = false)
    (h_not_var : ∀ v, retTy ≠ .var v)
    (h_unify :
      unify st (fuel + 2) (.function (.cons argTy .nil) retTy)
        (.function (.cons argTy .nil) (.var resVar)) = .ok stAfter) :
    bindTypeVar st resVar retTy fuel = .ok stAfter := by
  let h_dom : AppUnifyNoopDomain st argTy retTy resVar :=
    appUnifyNoopDomain_of_subst_empty st argTy retTy resVar h_empty
  exact app_unify_tail_bind_of_success_contract_succ
    st stAfter fuel argTy retTy resVar h_dom h_fn_beq_raw h_not_var h_unify

-- Bounded witness: the non-variable-return premise in tail bind recovery is
-- necessary in the fuel model (variable-return branch binds the left variable,
-- not necessarily the designated result variable).
private def tailBindNonVarNecessaryCounterexample : Bool :=
  let st : UnifyState := { UnifyState.empty with nextTypeVar := 2 }
  let retTy : Ty := .var 0
  let resVar : TypeVarId := 1
  match unify st 2 retTy (.var resVar), bindTypeVar st resVar retTy 1 with
  | .ok stU, .ok stB => !(stU.subst.typeMap 0 == stB.subst.typeMap 0)
  | _, _ => false

private theorem tailBindNonVarNecessaryCounterexample_true :
    tailBindNonVarNecessaryCounterexample = true := by
  native_decide

-- Bounded witness: result-variable equality at `fuel + 1` does not by itself
-- force resolved function-shape equality with parameter substitution at `fuel`.
private def appResolvedShapeCounterexample : Bool :=
  let s : Subst :=
    { typeMap := fun v => if v == 0 then some (.var 1) else none
      rowMap := fun _ => none }
  let lhs :=
    applySubstCompat s 2 (.function (.cons (.var 0) .nil) (.var 2))
  let rhs :=
    .function
      (.cons (applySubstCompat s 1 (.var 0)) .nil)
      (applySubstCompat s 2 (.var 2))
  let retEq :=
    applySubstCompat s 2 (.var 2) == applySubstCompat s 2 (.var 2)
  retEq && !(lhs == rhs)

private theorem appResolvedShapeCounterexample_true :
    appResolvedShapeCounterexample = true := by
  native_decide

/--
One-step app soundness in `HasTypeU`, parameterized by an explicit resolved
function-shape equation produced by the unification side.
-/
theorem inferExprUnify_app_step_sound_hasTypeU_resolved
    {env : TermEnv} {fn arg : CoreExpr} {fnTy argTy : Ty}
    {stBefore stAfter : UnifyState} {fuel : Nat} {resVar : TypeVarId}
    (h_fn : HasTypeU env fn fnTy)
    (h_arg : HasTypeU env arg argTy)
    (h_unify :
      unify stBefore fuel fnTy (.function (.cons argTy .nil) (.var resVar)) = .ok stAfter)
    (h_resolved :
      applySubstCompat stAfter.subst fuel fnTy =
        .function
          (.cons (applySubstCompat stAfter.subst fuel argTy) .nil)
          (applySubstCompat stAfter.subst fuel (.var resVar))) :
    HasTypeU env (.app fn arg) (applySubstCompat stAfter.subst fuel (.var resVar)) :=
  appUnifySoundHookUResolved_proved env fn arg fnTy argTy stBefore stAfter fuel resVar
    h_fn h_arg h_unify h_resolved

/--
One-step projection soundness in `HasTypeU`, parameterized by an explicit
resolved receiver-row shape produced by the unification side.
-/
theorem inferExprUnify_proj_step_sound_hasTypeU_resolved
    {env : TermEnv} {recv : CoreExpr} {label : Label} {recvTy : Ty}
    {stBefore stAfter : UnifyState} {fuel : Nat} {fieldVar : TypeVarId} {restVar : RowVarId}
    {rowFields : RowFields}
    (h_recv : HasTypeU env recv recvTy)
    (h_unify :
      unify stBefore fuel recvTy
        (.anonRecord (.mk (.cons label (.var fieldVar) .nil) (some restVar))) = .ok stAfter)
    (h_resolved :
      applySubstCompat stAfter.subst fuel recvTy =
        .anonRecord (.mk rowFields none))
    (h_get :
      RowFields.get rowFields label =
        some (applySubstCompat stAfter.subst fuel (.var fieldVar))) :
    HasTypeU env (.proj recv label) (applySubstCompat stAfter.subst fuel (.var fieldVar)) :=
  projUnifySoundHookUResolved_proved
    env recv label recvTy stBefore stAfter fuel fieldVar restVar rowFields
    h_recv h_unify h_resolved h_get

/-- Build `AppUnifySoundHookU` from resolved-shape app premise. -/
theorem appUnifySoundHookU_of_resolved
    (h_resolved : AppResolvedShapeFromUnify) :
    AppUnifySoundHookU := by
  intro env fn arg fnTy argTy stBefore stAfter fuel resVar h_fn h_arg h_unify
  exact inferExprUnify_app_step_sound_hasTypeU_resolved
    h_fn h_arg h_unify (h_resolved env fn arg fnTy argTy stBefore stAfter fuel resVar h_fn h_arg h_unify)

/-- Build `ProjUnifySoundHookU` from resolved-shape projection premise. -/
theorem projUnifySoundHookU_of_resolved
    (h_resolved : ProjResolvedShapeFromUnify) :
    ProjUnifySoundHookU := by
  intro env recv label recvTy stBefore stAfter fuel fieldVar restVar h_recv h_unify
  rcases h_resolved env recv label recvTy stBefore stAfter fuel fieldVar restVar h_recv h_unify with
    ⟨rowFields, h_row, h_get⟩
  exact inferExprUnify_proj_step_sound_hasTypeU_resolved
    h_recv h_unify h_row h_get

/-- Build `HasTypeU` hook bundle from global resolved-shape premises. -/
theorem unifyHookPremisesU_of_resolved
    (h_resolved : UnifyResolvedShapePremises) :
    UnifyHookPremisesU := by
  exact ⟨
    appUnifySoundHookU_of_resolved h_resolved.1,
    projUnifySoundHookU_of_resolved h_resolved.2
  ⟩


/--
Hook-free local-step bundle in `HasTypeU`: both app and projection one-step
rules are discharged once resolved-shape witnesses are provided.
-/
def UnifyStepSoundHasTypeU : Prop :=
  AppUnifySoundHookUResolved ∧ ProjUnifySoundHookUResolved

/-- Canonical witness for `UnifyStepSoundHasTypeU`. -/
theorem unifyStepSoundHasTypeU_proved : UnifyStepSoundHasTypeU := by
  exact ⟨appUnifySoundHookUResolved_proved, projUnifySoundHookUResolved_proved⟩

/--
Resolved-shape-premise entrypoint to the local-step bundle. The bundle itself is
already dischargeable from substitution admissibility; this theorem exposes the
same entrypoint shape used by recursive resolved-premise theorems.
-/
theorem unifyStepSoundHasTypeU_of_resolved
    (h_resolved : UnifyResolvedShapePremises) :
    UnifyStepSoundHasTypeU := by
  cases h_resolved
  exact unifyStepSoundHasTypeU_proved

/-- Bundle-driven app local-step rule. -/
theorem inferExprUnify_app_step_sound_hasTypeU_from_bundle
    (h_steps : UnifyStepSoundHasTypeU)
    {env : TermEnv} {fn arg : CoreExpr} {fnTy argTy : Ty}
    {stBefore stAfter : UnifyState} {fuel : Nat} {resVar : TypeVarId}
    (h_fn : HasTypeU env fn fnTy)
    (h_arg : HasTypeU env arg argTy)
    (h_unify :
      unify stBefore fuel fnTy (.function (.cons argTy .nil) (.var resVar)) = .ok stAfter)
    (h_resolved :
      applySubstCompat stAfter.subst fuel fnTy =
        .function
          (.cons (applySubstCompat stAfter.subst fuel argTy) .nil)
          (applySubstCompat stAfter.subst fuel (.var resVar))) :
    HasTypeU env (.app fn arg) (applySubstCompat stAfter.subst fuel (.var resVar)) := by
  exact h_steps.1 env fn arg fnTy argTy stBefore stAfter fuel resVar h_fn h_arg h_unify h_resolved

/-- Bundle-driven projection local-step rule. -/
theorem inferExprUnify_proj_step_sound_hasTypeU_from_bundle
    (h_steps : UnifyStepSoundHasTypeU)
    {env : TermEnv} {recv : CoreExpr} {label : Label} {recvTy : Ty}
    {stBefore stAfter : UnifyState} {fuel : Nat} {fieldVar : TypeVarId} {restVar : RowVarId}
    {rowFields : RowFields}
    (h_recv : HasTypeU env recv recvTy)
    (h_unify :
      unify stBefore fuel recvTy
        (.anonRecord (.mk (.cons label (.var fieldVar) .nil) (some restVar))) = .ok stAfter)
    (h_resolved :
      applySubstCompat stAfter.subst fuel recvTy =
        .anonRecord (.mk rowFields none))
    (h_get :
      RowFields.get rowFields label =
        some (applySubstCompat stAfter.subst fuel (.var fieldVar))) :
    HasTypeU env (.proj recv label) (applySubstCompat stAfter.subst fuel (.var fieldVar)) := by
  exact h_steps.2
    env recv label recvTy stBefore stAfter fuel fieldVar restVar rowFields
    h_recv h_unify h_resolved h_get

/-- Admissibility in `HasTypeU` is built into the judgment. -/
theorem hasTypeU_subst_admissible
    {env : TermEnv} {e : CoreExpr} {ty : Ty} {s : Subst} {fuel : Nat}
    (h_ty : HasTypeU env e ty) :
    HasTypeU env e (applySubstCompat s fuel ty) :=
  HasTypeU.subst env e ty s fuel h_ty

/--
The app-hook counterexample becomes typable in the unification-aware judgment
because substitution admissibility can be applied to the function position.
-/
theorem app_counterexample_hasTypeU :
    let env : TermEnv := [("f", .var 0)]
    let fn : CoreExpr := .var "f"
    let arg : CoreExpr := .intLit 1
    let stBefore : UnifyState := { UnifyState.empty with nextTypeVar := 2 }
    let expected : Ty := .function (.cons .int .nil) (.var 1)
    let stAfter : UnifyState := { stBefore with subst := stBefore.subst.bindType 0 expected }
    unify stBefore 1 (.var 0) expected = .ok stAfter →
    HasTypeU env (.app fn arg) (applySubstCompat stAfter.subst 1 (.var 1)) := by
  intro env fn arg stBefore expected stAfter h_unify
  have h_var : HasTypeU env fn (.var 0) := by
    exact HasTypeU.var env "f" (.var 0) (by simp [env, TermEnv.lookup])
  have h_fn_sub :
      HasTypeU env fn (.function (.cons .int .nil) (.var 1)) := by
    have h_sub := hasTypeU_subst_admissible (s := stAfter.subst) (fuel := 1) h_var
    simpa [stAfter, expected, applySubstCompat, applySubst, Subst.bindType] using h_sub
  have h_arg : HasTypeU env arg .int := HasTypeU.int env 1
  have h_app_var1 : HasTypeU env (.app fn arg) (.var 1) :=
    HasTypeU.app env fn arg .int (.var 1) h_fn_sub h_arg
  have h_app_resolved := hasTypeU_subst_admissible (s := stAfter.subst) (fuel := 1) h_app_var1
  simpa [stAfter, applySubstCompat, applySubst, Subst.bindType] using h_app_resolved

/--
Projection-hook counterexample with variable-typed receiver becomes typable in
`HasTypeU` once substitution admissibility is available.
-/
theorem proj_counterexample_hasTypeU :
    let env : TermEnv := [("r", .var 0)]
    let recv : CoreExpr := .var "r"
    let label : Label := "a"
    let stBefore : UnifyState := { UnifyState.empty with nextTypeVar := 2 }
    let expected : Ty := .anonRecord (.mk (.cons label (.var 1) .nil) none)
    let stAfter : UnifyState := { stBefore with subst := stBefore.subst.bindType 0 expected }
    unify stBefore 1 (.var 0) expected = .ok stAfter →
    HasTypeU env (.proj recv label) (applySubstCompat stAfter.subst 1 (.var 1)) := by
  intro env recv label stBefore expected stAfter h_unify
  have h_var : HasTypeU env recv (.var 0) := by
    exact HasTypeU.var env "r" (.var 0) (by simp [env, TermEnv.lookup])
  have h_recv_sub :
      HasTypeU env recv (.anonRecord (.mk (.cons label (.var 1) .nil) none)) := by
    have h_sub := hasTypeU_subst_admissible (s := stAfter.subst) (fuel := 1) h_var
    simpa [stAfter, expected, applySubstCompat, applySubst, applySubstRow,
      applySubstRowFields, Subst.bindType] using h_sub
  have h_get : RowFields.get (.cons label (.var 1) .nil) label = some (.var 1) := by
    simp [RowFields.get]
  have h_proj_var1 : HasTypeU env (.proj recv label) (.var 1) :=
    HasTypeU.proj env recv (.cons label (.var 1) .nil) label (.var 1) h_recv_sub h_get
  have h_proj_resolved := hasTypeU_subst_admissible (s := stAfter.subst) (fuel := 1) h_proj_var1
  simpa [stAfter, applySubstCompat, applySubst, Subst.bindType] using h_proj_resolved

/-- One-step app soundness: app branch correctness from typed children + unify hook. -/
theorem inferExprUnify_app_step_sound
    (h_app : AppUnifySoundHook)
    {env fn arg fnTy argTy : _}
    {stBefore stAfter : UnifyState} {fuel : Nat} {resVar : TypeVarId}
    (h_fn : HasType env fn fnTy)
    (h_arg : HasType env arg argTy)
    (h_unify : unify stBefore fuel fnTy (.function (.cons argTy .nil) (.var resVar)) = .ok stAfter) :
    HasType env (.app fn arg) (applySubstCompat stAfter.subst fuel (.var resVar)) :=
  h_app env fn arg fnTy argTy stBefore stAfter fuel resVar h_fn h_arg h_unify

/--
One-step app soundness on the weak-hook boundary: app branch correctness from a
declaratively function-typed callee, typed argument, unification success, and
resolved result equality.
-/
theorem inferExprUnify_app_step_sound_weak
    (h_app : AppUnifySoundHookWeak)
    {env fn arg argTy retTy : _}
    {stBefore stAfter : UnifyState} {fuel : Nat} {resVar : TypeVarId}
    (h_fn : HasType env fn (.function (.cons argTy .nil) retTy))
    (h_arg : HasType env arg argTy)
    (h_unify : unify stBefore fuel
      (.function (.cons argTy .nil) retTy)
      (.function (.cons argTy .nil) (.var resVar)) = .ok stAfter)
    (h_res_eq : applySubstCompat stAfter.subst fuel (.var resVar) = retTy) :
    HasType env (.app fn arg) (applySubstCompat stAfter.subst fuel (.var resVar)) :=
  h_app env fn arg argTy retTy stBefore stAfter fuel resVar h_fn h_arg h_unify h_res_eq

/--
One-step app soundness on the weak-hook boundary, derived from any strong app
hook witness through the strong→weak adapter.
-/
theorem inferExprUnify_app_step_sound_weak_of_strong
    (h_app : AppUnifySoundHook)
    {env fn arg argTy retTy : _}
    {stBefore stAfter : UnifyState} {fuel : Nat} {resVar : TypeVarId}
    (h_fn : HasType env fn (.function (.cons argTy .nil) retTy))
    (h_arg : HasType env arg argTy)
    (h_unify : unify stBefore fuel
      (.function (.cons argTy .nil) retTy)
      (.function (.cons argTy .nil) (.var resVar)) = .ok stAfter)
    (h_res_eq : applySubstCompat stAfter.subst fuel (.var resVar) = retTy) :
    HasType env (.app fn arg) (applySubstCompat stAfter.subst fuel (.var resVar)) :=
  inferExprUnify_app_step_sound_weak
    (appUnifySoundHookWeak_of_appUnifySoundHook h_app) h_fn h_arg h_unify h_res_eq

/-- Bundle-driven app local-step rule on the weak-hook boundary. -/
theorem inferExprUnify_app_step_sound_weak_from_bundle
    (h_steps : UnifyHookPremisesWeak)
    {env fn arg argTy retTy : _}
    {stBefore stAfter : UnifyState} {fuel : Nat} {resVar : TypeVarId}
    (h_fn : HasType env fn (.function (.cons argTy .nil) retTy))
    (h_arg : HasType env arg argTy)
    (h_unify : unify stBefore fuel
      (.function (.cons argTy .nil) retTy)
      (.function (.cons argTy .nil) (.var resVar)) = .ok stAfter)
    (h_res_eq : applySubstCompat stAfter.subst fuel (.var resVar) = retTy) :
    HasType env (.app fn arg) (applySubstCompat stAfter.subst fuel (.var resVar)) := by
  exact h_steps.1 env fn arg argTy retTy stBefore stAfter fuel resVar
    h_fn h_arg h_unify h_res_eq

/--
Strong-hook-bundle entrypoint to the weak app-step theorem surface via the
strong→weak package adapter.
-/
theorem inferExprUnify_app_step_sound_weak_from_strong_bundle
    (h_hooks : UnifyHookPremises)
    {env fn arg argTy retTy : _}
    {stBefore stAfter : UnifyState} {fuel : Nat} {resVar : TypeVarId}
    (h_fn : HasType env fn (.function (.cons argTy .nil) retTy))
    (h_arg : HasType env arg argTy)
    (h_unify : unify stBefore fuel
      (.function (.cons argTy .nil) retTy)
      (.function (.cons argTy .nil) (.var resVar)) = .ok stAfter)
    (h_res_eq : applySubstCompat stAfter.subst fuel (.var resVar) = retTy) :
    HasType env (.app fn arg) (applySubstCompat stAfter.subst fuel (.var resVar)) := by
  exact inferExprUnify_app_step_sound_weak_from_bundle
    (unifyHookPremisesWeak_of_unifyHookPremises h_hooks) h_fn h_arg h_unify h_res_eq

/-- Step-bundle-driven app local-step rule on the weak-hook boundary. -/
theorem inferExprUnify_app_step_sound_weak_from_stepBundle
    (h_steps : UnifyStepSoundWeak)
    {env fn arg argTy retTy : _}
    {stBefore stAfter : UnifyState} {fuel : Nat} {resVar : TypeVarId}
    (h_fn : HasType env fn (.function (.cons argTy .nil) retTy))
    (h_arg : HasType env arg argTy)
    (h_unify : unify stBefore fuel
      (.function (.cons argTy .nil) retTy)
      (.function (.cons argTy .nil) (.var resVar)) = .ok stAfter)
    (h_res_eq : applySubstCompat stAfter.subst fuel (.var resVar) = retTy) :
    HasType env (.app fn arg) (applySubstCompat stAfter.subst fuel (.var resVar)) := by
  exact h_steps.1 env fn arg argTy retTy stBefore stAfter fuel resVar
    h_fn h_arg h_unify h_res_eq

/-- Proved app local-step rule on the weak-hook boundary. -/
theorem inferExprUnify_app_step_sound_weak_proved
    {env fn arg argTy retTy : _}
    {stBefore stAfter : UnifyState} {fuel : Nat} {resVar : TypeVarId}
    (h_fn : HasType env fn (.function (.cons argTy .nil) retTy))
    (h_arg : HasType env arg argTy)
    (h_unify : unify stBefore fuel
      (.function (.cons argTy .nil) retTy)
      (.function (.cons argTy .nil) (.var resVar)) = .ok stAfter)
    (h_res_eq : applySubstCompat stAfter.subst fuel (.var resVar) = retTy) :
    HasType env (.app fn arg) (applySubstCompat stAfter.subst fuel (.var resVar)) := by
  exact inferExprUnify_app_step_sound_weak_from_stepBundle
    unifyStepSoundWeak_proved h_fn h_arg h_unify h_res_eq

/--
Strong-hook-package entrypoint to the weak app local-step rule through the
canonical weak-step bundle.
-/
theorem inferExprUnify_app_step_sound_weak_from_unifyHookPremises
    (h_hooks : UnifyHookPremises)
    {env fn arg argTy retTy : _}
    {stBefore stAfter : UnifyState} {fuel : Nat} {resVar : TypeVarId}
    (h_fn : HasType env fn (.function (.cons argTy .nil) retTy))
    (h_arg : HasType env arg argTy)
    (h_unify : unify stBefore fuel
      (.function (.cons argTy .nil) retTy)
      (.function (.cons argTy .nil) (.var resVar)) = .ok stAfter)
    (h_res_eq : applySubstCompat stAfter.subst fuel (.var resVar) = retTy) :
    HasType env (.app fn arg) (applySubstCompat stAfter.subst fuel (.var resVar)) := by
  exact inferExprUnify_app_step_sound_weak_from_stepBundle
    (unifyStepSoundWeak_of_unifyHookPremises h_hooks) h_fn h_arg h_unify h_res_eq

/-- One-step projection soundness: proj branch correctness from typed receiver + unify hook. -/
theorem inferExprUnify_proj_step_sound
    (h_proj : ProjUnifySoundHook)
    {env recv : _} {label : Label} {recvTy : Ty}
    {stBefore stAfter : UnifyState} {fuel : Nat} {fieldVar : TypeVarId} {restVar : RowVarId}
    (h_recv : HasType env recv recvTy)
    (h_unify : unify stBefore fuel recvTy (.anonRecord (.mk (.cons label (.var fieldVar) .nil) (some restVar))) = .ok stAfter) :
    HasType env (.proj recv label) (applySubstCompat stAfter.subst fuel (.var fieldVar)) :=
  h_proj env recv label recvTy stBefore stAfter fuel fieldVar restVar h_recv h_unify

/--
One-step projection soundness on the weak-hook boundary: projection branch
correctness from a typed receiver, explicit closed-row receiver shape, and
selected-field lookup at the resolved projection type.
-/
theorem inferExprUnify_proj_step_sound_weak
    (h_proj : ProjUnifySoundHookWeak)
    {env recv : _} {label : Label} {recvTy : Ty}
    {stBefore stAfter : UnifyState} {fuel : Nat} {fieldVar : TypeVarId}
    {restVar : RowVarId} {rowFields : RowFields}
    (h_recv : HasType env recv recvTy)
    (h_recv_shape : recvTy = .anonRecord (.mk rowFields none))
    (h_unify : unify stBefore fuel recvTy
      (.anonRecord (.mk (.cons label (.var fieldVar) .nil) (some restVar))) = .ok stAfter)
    (h_get : RowFields.get rowFields label =
      some (applySubstCompat stAfter.subst fuel (.var fieldVar))) :
    HasType env (.proj recv label) (applySubstCompat stAfter.subst fuel (.var fieldVar)) :=
  h_proj env recv label recvTy stBefore stAfter fuel fieldVar restVar rowFields
    h_recv h_recv_shape h_unify h_get

/--
One-step projection soundness on the weak-hook boundary, derived from any
strong projection hook witness through the strong→weak adapter.
-/
theorem inferExprUnify_proj_step_sound_weak_of_strong
    (h_proj : ProjUnifySoundHook)
    {env recv : _} {label : Label} {recvTy : Ty}
    {stBefore stAfter : UnifyState} {fuel : Nat} {fieldVar : TypeVarId}
    {restVar : RowVarId} {rowFields : RowFields}
    (h_recv : HasType env recv recvTy)
    (h_recv_shape : recvTy = .anonRecord (.mk rowFields none))
    (h_unify : unify stBefore fuel recvTy
      (.anonRecord (.mk (.cons label (.var fieldVar) .nil) (some restVar))) = .ok stAfter)
    (h_get : RowFields.get rowFields label =
      some (applySubstCompat stAfter.subst fuel (.var fieldVar))) :
    HasType env (.proj recv label) (applySubstCompat stAfter.subst fuel (.var fieldVar)) :=
  inferExprUnify_proj_step_sound_weak
    (projUnifySoundHookWeak_of_projUnifySoundHook h_proj)
    h_recv h_recv_shape h_unify h_get

/-- Bundle-driven projection local-step rule on the weak-hook boundary. -/
theorem inferExprUnify_proj_step_sound_weak_from_bundle
    (h_steps : UnifyHookPremisesWeak)
    {env recv : _} {label : Label} {recvTy : Ty}
    {stBefore stAfter : UnifyState} {fuel : Nat} {fieldVar : TypeVarId}
    {restVar : RowVarId} {rowFields : RowFields}
    (h_recv : HasType env recv recvTy)
    (h_recv_shape : recvTy = .anonRecord (.mk rowFields none))
    (h_unify : unify stBefore fuel recvTy
      (.anonRecord (.mk (.cons label (.var fieldVar) .nil) (some restVar))) = .ok stAfter)
    (h_get : RowFields.get rowFields label =
      some (applySubstCompat stAfter.subst fuel (.var fieldVar))) :
    HasType env (.proj recv label) (applySubstCompat stAfter.subst fuel (.var fieldVar)) := by
  exact h_steps.2 env recv label recvTy stBefore stAfter fuel fieldVar restVar rowFields
    h_recv h_recv_shape h_unify h_get

/--
Strong-hook-bundle entrypoint to the weak projection-step theorem surface via
the strong→weak package adapter.
-/
theorem inferExprUnify_proj_step_sound_weak_from_strong_bundle
    (h_hooks : UnifyHookPremises)
    {env recv : _} {label : Label} {recvTy : Ty}
    {stBefore stAfter : UnifyState} {fuel : Nat} {fieldVar : TypeVarId}
    {restVar : RowVarId} {rowFields : RowFields}
    (h_recv : HasType env recv recvTy)
    (h_recv_shape : recvTy = .anonRecord (.mk rowFields none))
    (h_unify : unify stBefore fuel recvTy
      (.anonRecord (.mk (.cons label (.var fieldVar) .nil) (some restVar))) = .ok stAfter)
    (h_get : RowFields.get rowFields label =
      some (applySubstCompat stAfter.subst fuel (.var fieldVar))) :
    HasType env (.proj recv label) (applySubstCompat stAfter.subst fuel (.var fieldVar)) := by
  exact inferExprUnify_proj_step_sound_weak_from_bundle
    (unifyHookPremisesWeak_of_unifyHookPremises h_hooks)
    h_recv h_recv_shape h_unify h_get

/-- Step-bundle-driven projection local-step rule on the weak-hook boundary. -/
theorem inferExprUnify_proj_step_sound_weak_from_stepBundle
    (h_steps : UnifyStepSoundWeak)
    {env recv : _} {label : Label} {recvTy : Ty}
    {stBefore stAfter : UnifyState} {fuel : Nat} {fieldVar : TypeVarId}
    {restVar : RowVarId} {rowFields : RowFields}
    (h_recv : HasType env recv recvTy)
    (h_recv_shape : recvTy = .anonRecord (.mk rowFields none))
    (h_unify : unify stBefore fuel recvTy
      (.anonRecord (.mk (.cons label (.var fieldVar) .nil) (some restVar))) = .ok stAfter)
    (h_get : RowFields.get rowFields label =
      some (applySubstCompat stAfter.subst fuel (.var fieldVar))) :
    HasType env (.proj recv label) (applySubstCompat stAfter.subst fuel (.var fieldVar)) := by
  exact h_steps.2 env recv label recvTy stBefore stAfter fuel fieldVar restVar rowFields
    h_recv h_recv_shape h_unify h_get

/-- Proved projection local-step rule on the weak-hook boundary. -/
theorem inferExprUnify_proj_step_sound_weak_proved
    {env recv : _} {label : Label} {recvTy : Ty}
    {stBefore stAfter : UnifyState} {fuel : Nat} {fieldVar : TypeVarId}
    {restVar : RowVarId} {rowFields : RowFields}
    (h_recv : HasType env recv recvTy)
    (h_recv_shape : recvTy = .anonRecord (.mk rowFields none))
    (h_unify : unify stBefore fuel recvTy
      (.anonRecord (.mk (.cons label (.var fieldVar) .nil) (some restVar))) = .ok stAfter)
    (h_get : RowFields.get rowFields label =
      some (applySubstCompat stAfter.subst fuel (.var fieldVar))) :
    HasType env (.proj recv label) (applySubstCompat stAfter.subst fuel (.var fieldVar)) := by
  exact inferExprUnify_proj_step_sound_weak_from_stepBundle
    unifyStepSoundWeak_proved h_recv h_recv_shape h_unify h_get

/--
Strong-hook-package entrypoint to the weak projection local-step rule through
the canonical weak-step bundle.
-/
theorem inferExprUnify_proj_step_sound_weak_from_unifyHookPremises
    (h_hooks : UnifyHookPremises)
    {env recv : _} {label : Label} {recvTy : Ty}
    {stBefore stAfter : UnifyState} {fuel : Nat} {fieldVar : TypeVarId}
    {restVar : RowVarId} {rowFields : RowFields}
    (h_recv : HasType env recv recvTy)
    (h_recv_shape : recvTy = .anonRecord (.mk rowFields none))
    (h_unify : unify stBefore fuel recvTy
      (.anonRecord (.mk (.cons label (.var fieldVar) .nil) (some restVar))) = .ok stAfter)
    (h_get : RowFields.get rowFields label =
      some (applySubstCompat stAfter.subst fuel (.var fieldVar))) :
    HasType env (.proj recv label) (applySubstCompat stAfter.subst fuel (.var fieldVar)) := by
  exact inferExprUnify_proj_step_sound_weak_from_stepBundle
    (unifyStepSoundWeak_of_unifyHookPremises h_hooks)
    h_recv h_recv_shape h_unify h_get

mutual
  /-- Structural size of core expressions (for recursive proof termination). -/
  def exprSize : CoreExpr → Nat
    | .intLit _ => 1
    | .boolLit _ => 1
    | .stringLit _ => 1
    | .var _ => 1
    | .lam _ _ body => exprSize body + 1
    | .app fn arg => exprSize fn + exprSize arg + 1
    | .letE _ value body => exprSize value + exprSize body + 1
    | .record fields => fieldsSize fields + 1
    | .proj recv _ => exprSize recv + 1

  /-- Structural size of field lists (for recursive proof termination). -/
  def fieldsSize : CoreFields → Nat
    | .nil => 1
    | .cons _ e rest => exprSize e + fieldsSize rest + 1
end

mutual
  /-- Expressions whose `inferExprUnify` path never enters app/proj unification branches. -/
  inductive NoUnifyBranchesExpr : CoreExpr → Prop where
    | intLit (n : Int) : NoUnifyBranchesExpr (.intLit n)
    | boolLit (b : Bool) : NoUnifyBranchesExpr (.boolLit b)
    | stringLit (s : String) : NoUnifyBranchesExpr (.stringLit s)
    | var (name : String) : NoUnifyBranchesExpr (.var name)
    | lam (param : String) (paramTy : Ty) (body : CoreExpr)
        (h_body : NoUnifyBranchesExpr body) :
        NoUnifyBranchesExpr (.lam param paramTy body)
    | letE (name : String) (value body : CoreExpr)
        (h_value : NoUnifyBranchesExpr value)
        (h_body : NoUnifyBranchesExpr body) :
        NoUnifyBranchesExpr (.letE name value body)
    | record (fields : CoreFields)
        (h_fields : NoUnifyBranchesFields fields) :
        NoUnifyBranchesExpr (.record fields)

  /-- Field lists whose `inferFieldsUnify` path never enters app/proj unification branches. -/
  inductive NoUnifyBranchesFields : CoreFields → Prop where
    | nil : NoUnifyBranchesFields .nil
    | cons (label : Label) (e : CoreExpr) (rest : CoreFields)
        (h_head : NoUnifyBranchesExpr e)
        (h_rest : NoUnifyBranchesFields rest) :
        NoUnifyBranchesFields (.cons label e rest)
end

mutual
  /--
  Soundness of `inferExprUnify` on the fragment that never executes app/proj
  unification branches.
  -/
  theorem inferExprUnify_sound_no_unify_branches
      {e : CoreExpr}
      (h_no : NoUnifyBranchesExpr e) :
      ∀ st fuel env st' ty,
        inferExprUnify st fuel env e = .ok st' ty →
        HasType env e ty := by
    cases h_no with
    | intLit n =>
      intro st fuel env st' ty h
      simp [inferExprUnify] at h
      rcases h with ⟨_, hty⟩
      subst hty
      exact HasType.int env n
    | boolLit b =>
      intro st fuel env st' ty h
      simp [inferExprUnify] at h
      rcases h with ⟨_, hty⟩
      subst hty
      exact HasType.bool env b
    | stringLit s =>
      intro st fuel env st' ty h
      simp [inferExprUnify] at h
      rcases h with ⟨_, hty⟩
      subst hty
      exact HasType.string env s
    | var name =>
      intro st fuel env st' ty h
      cases h_lookup : TermEnv.lookup env name with
      | none =>
        simp [inferExprUnify, h_lookup] at h
      | some vty =>
        simp [inferExprUnify, h_lookup] at h
        rcases h with ⟨_, hty⟩
        subst hty
        exact HasType.var env name vty h_lookup
    | lam param paramTy body h_body =>
      intro st fuel env st' ty h
      simp [inferExprUnify] at h
      cases h_body_infer : inferExprUnify st fuel ((param, paramTy) :: env) body with
      | err e =>
        simp [h_body_infer] at h
      | ok stBody bodyTy =>
        simp [h_body_infer] at h
        rcases h with ⟨_, hty⟩
        subst hty
        exact HasType.lam env param paramTy bodyTy body
          (inferExprUnify_sound_no_unify_branches h_body st fuel ((param, paramTy) :: env) stBody bodyTy h_body_infer)
    | letE name value body h_value h_body =>
      intro st fuel env st' ty h
      simp [inferExprUnify] at h
      cases h_value_infer : inferExprUnify st fuel env value with
      | err e =>
        simp [h_value_infer] at h
      | ok stValue valueTy =>
        exact HasType.letE env name value body valueTy ty
          (inferExprUnify_sound_no_unify_branches h_value st fuel env stValue valueTy h_value_infer)
          (inferExprUnify_sound_no_unify_branches h_body stValue fuel ((name, valueTy) :: env) st' ty (by
            simpa [h_value_infer] using h))
    | record fields h_fields =>
      intro st fuel env st' ty h
      simp [inferExprUnify] at h
      cases h_fields_infer : inferFieldsUnify st fuel env fields with
      | err e =>
        simp [h_fields_infer] at h
      | ok stFields fieldsTy =>
        cases fieldsTy with
        | row rowTy =>
          cases rowTy with
          | mk rf rest =>
            cases rest with
            | some rv =>
              simp [h_fields_infer] at h
            | none =>
              simp [h_fields_infer] at h
              rcases h with ⟨_, hty⟩
              subst hty
              exact HasType.record env fields rf
                (inferFieldsUnify_sound_no_unify_branches h_fields st fuel env stFields rf (by
                  simp [h_fields_infer]))
        | int | intN _ _ | float | floatN _ | decimal _ _ | bool | string | html | markdown | atom | date | dateTime | unit =>
          simp [h_fields_infer] at h
        | list _ | map _ _ | set _ | option _ | result _ _ | existential _ _ | fixedSizeList _ _ | tensor _ _ | sum _ _ | «opaque» _ _
          | function _ _ | functionEff _ _ _ | «forall» _ _ | app _ _ | constructor _ _ _ | record _ _ | anonRecord _ | dataframe _ | groupedFrame _ _ | tagged _ _ | dynamic | column _ | stream _ | task _ | actor _ | arc _
          | var _ | tuple _ =>
          simp [h_fields_infer] at h

  /-- Field-level counterpart of `inferExprUnify_sound_no_unify_branches`. -/
  theorem inferFieldsUnify_sound_no_unify_branches
      {fs : CoreFields}
      (h_no : NoUnifyBranchesFields fs) :
      ∀ st fuel env st' rf,
        inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)) →
        HasFieldsType env fs rf := by
    cases h_no with
    | nil =>
      intro st fuel env st' rf h
      simp [inferFieldsUnify] at h
      rcases h with ⟨_, hrf⟩
      subst hrf
      exact HasFieldsType.nil env
    | cons label e rest h_head h_rest =>
      intro st fuel env st' rf h
      simp [inferFieldsUnify] at h
      cases h_head_infer : inferExprUnify st fuel env e with
      | err e =>
        simp [h_head_infer] at h
      | ok stHead tyHead =>
        cases h_rest_infer : inferFieldsUnify stHead fuel env rest with
        | err e =>
          simp [h_head_infer, h_rest_infer] at h
        | ok stRest restTy =>
          cases restTy with
          | row rowTy =>
            cases rowTy with
            | mk restFields restVar =>
              cases restVar with
              | some rv =>
                simp [h_head_infer, h_rest_infer] at h
              | none =>
                simp [h_head_infer, h_rest_infer] at h
                rcases h with ⟨_, hrf⟩
                subst hrf
                exact HasFieldsType.cons env label e rest tyHead restFields
                  (inferExprUnify_sound_no_unify_branches h_head st fuel env stHead tyHead h_head_infer)
                  (inferFieldsUnify_sound_no_unify_branches h_rest stHead fuel env stRest restFields (by
                    simp [h_rest_infer]))
          | int | intN _ _ | float | floatN _ | decimal _ _ | bool | string | html | markdown | atom | date | dateTime | unit =>
            simp [h_head_infer, h_rest_infer] at h
          | list _ | map _ _ | set _ | option _ | result _ _ | existential _ _ | fixedSizeList _ _ | tensor _ _ | sum _ _ | «opaque» _ _
            | function _ _ | functionEff _ _ _ | «forall» _ _ | app _ _ | constructor _ _ _ | record _ _ | anonRecord _ | dataframe _ | groupedFrame _ _ | tagged _ _ | dynamic | column _ | stream _ | task _ | actor _ | arc _
            | var _ | tuple _ =>
            simp [h_head_infer, h_rest_infer] at h
end

mutual
  /--
  Completeness of unification-threaded inference on the no-unify fragment:
  syntax-directed inference can be replayed with identical result type/state.
  -/
  theorem inferExprUnify_complete_no_unify_branches
      {e : CoreExpr}
      (h_no : NoUnifyBranchesExpr e) :
      ∀ st fuel env ty,
        inferExpr env e = some ty →
        inferExprUnify st fuel env e = .ok st ty := by
    cases h_no with
    | intLit n =>
      intro st fuel env ty h_inf
      simp [inferExpr] at h_inf
      subst h_inf
      simp [inferExprUnify]
    | boolLit b =>
      intro st fuel env ty h_inf
      simp [inferExpr] at h_inf
      subst h_inf
      simp [inferExprUnify]
    | stringLit s =>
      intro st fuel env ty h_inf
      simp [inferExpr] at h_inf
      subst h_inf
      simp [inferExprUnify]
    | var name =>
      intro st fuel env ty h_inf
      cases h_lookup : TermEnv.lookup env name with
      | none =>
        simp [inferExpr, h_lookup] at h_inf
      | some vty =>
        simp [inferExpr, h_lookup] at h_inf
        subst h_inf
        simp [inferExprUnify, h_lookup]
    | lam param paramTy body h_body =>
      intro st fuel env ty h_inf
      simp [inferExpr] at h_inf
      cases h_body_alg : inferExpr ((param, paramTy) :: env) body with
      | none =>
        simp [h_body_alg] at h_inf
      | some bodyTy =>
        simp [h_body_alg] at h_inf
        subst h_inf
        have h_body_unify :
            inferExprUnify st fuel ((param, paramTy) :: env) body = .ok st bodyTy :=
          inferExprUnify_complete_no_unify_branches
            h_body st fuel ((param, paramTy) :: env) bodyTy h_body_alg
        simp [inferExprUnify, h_body_unify]
    | letE name value body h_value h_body =>
      intro st fuel env ty h_inf
      simp [inferExpr] at h_inf
      cases h_value_alg : inferExpr env value with
      | none =>
        simp [h_value_alg] at h_inf
      | some valueTy =>
        have h_value_unify :
            inferExprUnify st fuel env value = .ok st valueTy :=
          inferExprUnify_complete_no_unify_branches
            h_value st fuel env valueTy h_value_alg
        have h_body_unify :
            inferExprUnify st fuel ((name, valueTy) :: env) body = .ok st ty :=
          inferExprUnify_complete_no_unify_branches
            h_body st fuel ((name, valueTy) :: env) ty (by
              simpa [h_value_alg] using h_inf)
        simpa [inferExprUnify, h_value_unify] using h_body_unify
    | record fields h_fields =>
      intro st fuel env ty h_inf
      simp [inferExpr] at h_inf
      cases h_fields_alg : inferFields env fields with
      | none =>
        simp [h_fields_alg] at h_inf
      | some rowFields =>
        simp [h_fields_alg] at h_inf
        subst h_inf
        have h_fields_unify :
            inferFieldsUnify st fuel env fields = .ok st (.row (.mk rowFields none)) :=
          inferFieldsUnify_complete_no_unify_branches
            h_fields st fuel env rowFields h_fields_alg
        simp [inferExprUnify, h_fields_unify]

  /--
  Field-level completeness counterpart on the no-unify fragment.
  -/
  theorem inferFieldsUnify_complete_no_unify_branches
      {fs : CoreFields}
      (h_no : NoUnifyBranchesFields fs) :
      ∀ st fuel env rf,
        inferFields env fs = some rf →
        inferFieldsUnify st fuel env fs = .ok st (.row (.mk rf none)) := by
    cases h_no with
    | nil =>
      intro st fuel env rf h_inf
      simp [inferFields] at h_inf
      subst h_inf
      simp [inferFieldsUnify]
    | cons label e rest h_head h_rest =>
      intro st fuel env rf h_inf
      simp [inferFields] at h_inf
      cases h_head_alg : inferExpr env e with
      | none =>
        simp [h_head_alg] at h_inf
      | some tyHead =>
        cases h_rest_alg : inferFields env rest with
        | none =>
          simp [h_head_alg, h_rest_alg] at h_inf
        | some restFields =>
          simp [h_head_alg, h_rest_alg] at h_inf
          subst h_inf
          have h_head_unify :
              inferExprUnify st fuel env e = .ok st tyHead :=
            inferExprUnify_complete_no_unify_branches
              h_head st fuel env tyHead h_head_alg
          have h_rest_unify :
              inferFieldsUnify st fuel env rest = .ok st (.row (.mk restFields none)) :=
            inferFieldsUnify_complete_no_unify_branches
              h_rest st fuel env restFields h_rest_alg
          simp [inferFieldsUnify, h_head_unify, h_rest_unify]
end

/--
On the no-unify fragment, successful expression inference preserves
`UnifyState`.
-/
theorem inferExprUnify_state_preserved_no_unify_branches
    {e : CoreExpr}
    (h_no : NoUnifyBranchesExpr e) :
    ∀ st fuel env st' ty,
      inferExprUnify st fuel env e = .ok st' ty →
      st' = st := by
  intro st fuel env st' ty h_ok
  have h_ty : HasType env e ty :=
    inferExprUnify_sound_no_unify_branches h_no st fuel env st' ty h_ok
  have h_inf : inferExpr env e = some ty := inferExpr_complete env e ty h_ty
  have h_ok_ref :
      inferExprUnify st fuel env e = .ok st ty :=
    inferExprUnify_complete_no_unify_branches h_no st fuel env ty h_inf
  rw [h_ok] at h_ok_ref
  cases h_ok_ref
  rfl

/--
On the no-unify fragment, successful field inference preserves `UnifyState`.
-/
theorem inferFieldsUnify_state_preserved_no_unify_branches
    {fs : CoreFields}
    (h_no : NoUnifyBranchesFields fs) :
    ∀ st fuel env st' rf,
      inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)) →
      st' = st := by
  intro st fuel env st' rf h_ok
  have h_rf : HasFieldsType env fs rf :=
    inferFieldsUnify_sound_no_unify_branches h_no st fuel env st' rf h_ok
  have h_inf : inferFields env fs = some rf := inferFields_complete env fs rf h_rf
  have h_ok_ref :
      inferFieldsUnify st fuel env fs = .ok st (.row (.mk rf none)) :=
    inferFieldsUnify_complete_no_unify_branches h_no st fuel env rf h_inf
  rw [h_ok] at h_ok_ref
  cases h_ok_ref
  rfl

/--
On the no-unify fragment, successful `inferExprUnify` runs are exactly
syntax-directed inference results with unchanged state.
-/
theorem inferExprUnify_ok_iff_inferExpr_no_unify_branches
    {e : CoreExpr}
    (h_no : NoUnifyBranchesExpr e) :
    ∀ st fuel env st' ty,
      inferExprUnify st fuel env e = .ok st' ty ↔
        st' = st ∧ inferExpr env e = some ty := by
  intro st fuel env st' ty
  constructor
  · intro h_ok
    have h_st :
        st' = st :=
      inferExprUnify_state_preserved_no_unify_branches
        h_no st fuel env st' ty h_ok
    have h_ty : HasType env e ty :=
      inferExprUnify_sound_no_unify_branches
        h_no st fuel env st' ty h_ok
    refine ⟨h_st, ?_⟩
    exact inferExpr_complete env e ty h_ty
  · intro h
    rcases h with ⟨h_st, h_inf⟩
    cases h_st
    exact inferExprUnify_complete_no_unify_branches h_no st fuel env ty h_inf

/--
Field-level counterpart of no-unify equivalence/state preservation.
-/
theorem inferFieldsUnify_ok_iff_inferFields_no_unify_branches
    {fs : CoreFields}
    (h_no : NoUnifyBranchesFields fs) :
    ∀ st fuel env st' rf,
      inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)) ↔
        st' = st ∧ inferFields env fs = some rf := by
  intro st fuel env st' rf
  constructor
  · intro h_ok
    have h_st :
        st' = st :=
      inferFieldsUnify_state_preserved_no_unify_branches
        h_no st fuel env st' rf h_ok
    have h_rf : HasFieldsType env fs rf :=
      inferFieldsUnify_sound_no_unify_branches h_no st fuel env st' rf h_ok
    refine ⟨h_st, ?_⟩
    exact inferFields_complete env fs rf h_rf
  · intro h
    rcases h with ⟨h_st, h_inf⟩
    cases h_st
    exact inferFieldsUnify_complete_no_unify_branches h_no st fuel env rf h_inf

/--
Bridge from successful no-unify `inferExprUnify` runs into the core principal
typing package.
-/
theorem principalTypingSliceCore_of_unify_success_no_unify
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalTypingSliceCore env e ty := by
  have h_inf : inferExpr env e = some ty :=
    (inferExprUnify_ok_iff_inferExpr_no_unify_branches h_no st fuel env st' ty).1 h_ok |>.2
  exact principalTypingSliceCore_of_infer h_inf

/--
Bridge from successful no-unify `inferFieldsUnify` runs into the core
principal field-typing package.
-/
theorem principalFieldTypingSliceCore_of_unify_success_no_unify
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalFieldTypingSliceCore env fs rf := by
  have h_inf : inferFields env fs = some rf :=
    (inferFieldsUnify_ok_iff_inferFields_no_unify_branches h_no st fuel env st' rf).1 h_ok |>.2
  exact principalFieldTypingSliceCore_of_infer h_inf

/-- Packaged hook-free principal/equivalence surface on the no-unify fragment. -/
def PrincipalTypingNoUnifySlice : Prop :=
  ∀ {e : CoreExpr},
    NoUnifyBranchesExpr e →
    ∀ st fuel env st' ty,
      inferExprUnify st fuel env e = .ok st' ty ↔
        st' = st ∧ inferExpr env e = some ty

/-- Field-level packaged hook-free principal/equivalence surface. -/
def PrincipalTypingNoUnifyFieldSlice : Prop :=
  ∀ {fs : CoreFields},
    NoUnifyBranchesFields fs →
    ∀ st fuel env st' rf,
      inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)) ↔
        st' = st ∧ inferFields env fs = some rf

/-- Combined expression+field no-unify principal/equivalence surface. -/
def PrincipalTypingNoUnifySlices : Prop :=
  PrincipalTypingNoUnifySlice ∧ PrincipalTypingNoUnifyFieldSlice

/-- The combined no-unify principal/equivalence surface is fully proved. -/
theorem principalTypingNoUnifySlices_proved : PrincipalTypingNoUnifySlices := by
  refine ⟨?_, ?_⟩
  · intro e h_no st fuel env st' ty
    exact inferExprUnify_ok_iff_inferExpr_no_unify_branches h_no st fuel env st' ty
  · intro fs h_no st fuel env st' rf
    exact inferFieldsUnify_ok_iff_inferFields_no_unify_branches h_no st fuel env st' rf

mutual
  /--
  Full preconditioned soundness for unification-threaded expression inference.
  App/proj branches are discharged via explicit unifier-soundness hooks.
  -/
  theorem inferExprUnify_sound_preconditioned
      (h_app : AppUnifySoundHook)
      (h_proj : ProjUnifySoundHook) :
      ∀ st fuel env e st' ty,
        inferExprUnify st fuel env e = .ok st' ty →
        HasType env e ty := by
    intro st fuel env e
    cases e with
    | intLit n =>
      intro st' ty h
      simp [inferExprUnify] at h
      rcases h with ⟨_, hty⟩
      subst hty
      exact HasType.int env n
    | boolLit b =>
      intro st' ty h
      simp [inferExprUnify] at h
      rcases h with ⟨_, hty⟩
      subst hty
      exact HasType.bool env b
    | stringLit s =>
      intro st' ty h
      simp [inferExprUnify] at h
      rcases h with ⟨_, hty⟩
      subst hty
      exact HasType.string env s
    | var name =>
      intro st' ty h
      cases h_lookup : TermEnv.lookup env name with
      | none =>
        simp [inferExprUnify, h_lookup] at h
      | some vty =>
        simp [inferExprUnify, h_lookup] at h
        rcases h with ⟨_, hty⟩
        subst hty
        exact HasType.var env name vty h_lookup
    | lam param paramTy body =>
      intro st' ty h
      simp [inferExprUnify] at h
      cases h_body : inferExprUnify st fuel ((param, paramTy) :: env) body with
      | err err =>
        simp [h_body] at h
      | ok stBody bodyTy =>
        simp [h_body] at h
        rcases h with ⟨_, hty⟩
        subst hty
        exact HasType.lam env param paramTy bodyTy body
          (inferExprUnify_sound_preconditioned h_app h_proj st fuel ((param, paramTy) :: env) body stBody bodyTy h_body)
    | app fn arg =>
      intro st' ty h
      simp [inferExprUnify] at h
      cases h_fn : inferExprUnify st fuel env fn with
      | err err =>
        simp [h_fn] at h
      | ok stFn fnTy =>
        cases h_arg : inferExprUnify stFn fuel env arg with
        | err err =>
          simp [h_fn, h_arg] at h
        | ok stArg argTy =>
          let fresh := stArg.freshTypeVar
          cases h_unify : unify fresh.2 fuel fnTy (Ty.function (.cons argTy .nil) (.var fresh.1)) with
          | err err =>
            have h_false : False := by
              simp [h_fn, h_arg, fresh, h_unify] at h
            exact False.elim h_false
          | ok stU =>
            simp [h_fn, h_arg, fresh, h_unify] at h
            rcases h with ⟨_, hty⟩
            subst hty
            exact h_app env fn arg fnTy argTy fresh.2 stU fuel fresh.1
              (inferExprUnify_sound_preconditioned h_app h_proj st fuel env fn stFn fnTy h_fn)
              (inferExprUnify_sound_preconditioned h_app h_proj stFn fuel env arg stArg argTy h_arg)
              h_unify
    | letE name value body =>
      intro st' ty h
      simp [inferExprUnify] at h
      cases h_value : inferExprUnify st fuel env value with
      | err err =>
        simp [h_value] at h
      | ok stValue valueTy =>
        exact HasType.letE env name value body valueTy ty
          (inferExprUnify_sound_preconditioned h_app h_proj st fuel env value stValue valueTy h_value)
          (inferExprUnify_sound_preconditioned h_app h_proj stValue fuel ((name, valueTy) :: env) body st' ty (by
            simpa [h_value] using h))
    | record fields =>
      intro st' ty h
      simp [inferExprUnify] at h
      cases h_fields : inferFieldsUnify st fuel env fields with
      | err err =>
        simp [h_fields] at h
      | ok stFields fieldsTy =>
        cases fieldsTy with
        | row rowTy =>
          cases rowTy with
          | mk rf rest =>
            cases rest with
            | some rv =>
              simp [h_fields] at h
            | none =>
              simp [h_fields] at h
              rcases h with ⟨_, hty⟩
              subst hty
              exact HasType.record env fields rf
                (inferFieldsUnify_sound_preconditioned h_app h_proj st fuel env fields stFields rf (by
                  simp [h_fields]))
        | int | intN _ _ | float | floatN _ | decimal _ _ | bool | string | html | markdown | atom | date | dateTime | unit =>
          simp [h_fields] at h
        | list _ | map _ _ | set _ | option _ | result _ _ | existential _ _ | fixedSizeList _ _ | tensor _ _ | sum _ _ | «opaque» _ _
          | function _ _ | functionEff _ _ _ | «forall» _ _ | app _ _ | constructor _ _ _ | record _ _ | anonRecord _ | dataframe _ | groupedFrame _ _ | tagged _ _ | dynamic | column _ | stream _ | task _ | actor _ | arc _
          | var _ | tuple _ =>
          simp [h_fields] at h
    | proj recv label =>
      intro st' ty h
      simp [inferExprUnify] at h
      cases h_recv : inferExprUnify st fuel env recv with
      | err err =>
        simp [h_recv] at h
      | ok stRecv recvTy =>
        let freshTy := stRecv.freshTypeVar
        let freshRow := freshTy.2.freshRowVar
        cases h_unify :
            unify freshRow.2 fuel recvTy
              (Ty.anonRecord (.mk (.cons label (.var freshTy.1) .nil) (some freshRow.1))) with
        | err err =>
          have h_false : False := by
            simp [h_recv, freshTy, freshRow, h_unify] at h
          exact False.elim h_false
        | ok stU =>
          simp [h_recv, freshTy, freshRow, h_unify] at h
          rcases h with ⟨_, hty⟩
          subst hty
          exact h_proj env recv label recvTy freshRow.2 stU fuel freshTy.1 freshRow.1
            (inferExprUnify_sound_preconditioned h_app h_proj st fuel env recv stRecv recvTy h_recv)
            h_unify

  /-- Field-level counterpart of `inferExprUnify_sound_preconditioned`. -/
  theorem inferFieldsUnify_sound_preconditioned
      (h_app : AppUnifySoundHook)
      (h_proj : ProjUnifySoundHook) :
      ∀ st fuel env fs st' rf,
        inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)) →
        HasFieldsType env fs rf := by
    intro st fuel env fs
    cases fs with
    | nil =>
      intro st' rf h
      simp [inferFieldsUnify] at h
      rcases h with ⟨_, hrf⟩
      subst hrf
      exact HasFieldsType.nil env
    | cons label e rest =>
      intro st' rf h
      simp [inferFieldsUnify] at h
      cases h_head : inferExprUnify st fuel env e with
      | err err =>
        simp [h_head] at h
      | ok stHead tyHead =>
        cases h_rest : inferFieldsUnify stHead fuel env rest with
        | err err =>
          simp [h_head, h_rest] at h
        | ok stRest restTy =>
          cases restTy with
          | row rowTy =>
            cases rowTy with
            | mk restFields restVar =>
              cases restVar with
              | some rv =>
                simp [h_head, h_rest] at h
              | none =>
                simp [h_head, h_rest] at h
                rcases h with ⟨_, hrf⟩
                subst hrf
                exact HasFieldsType.cons env label e rest tyHead restFields
                  (inferExprUnify_sound_preconditioned h_app h_proj st fuel env e stHead tyHead h_head)
                  (inferFieldsUnify_sound_preconditioned h_app h_proj stHead fuel env rest stRest restFields (by
                    simp [h_rest]))
          | int | intN _ _ | float | floatN _ | decimal _ _ | bool | string | html | markdown | atom | date | dateTime | unit =>
            simp [h_head, h_rest] at h
          | list _ | map _ _ | set _ | option _ | result _ _ | existential _ _ | fixedSizeList _ _ | tensor _ _ | sum _ _ | «opaque» _ _
            | function _ _ | functionEff _ _ _ | «forall» _ _ | app _ _ | constructor _ _ _ | record _ _ | anonRecord _ | dataframe _ | groupedFrame _ _ | tagged _ _ | dynamic | column _ | stream _ | task _ | actor _ | arc _
            | var _ | tuple _ =>
            simp [h_head, h_rest] at h
end

mutual
  /--
  Direct `HasTypeU` recursive soundness for unification-threaded inference.
  App/proj branches are discharged via `HasTypeU`-targeted hook interfaces.
  -/
  theorem inferExprUnify_sound_preconditioned_hasTypeU_direct
      (h_app : AppUnifySoundHookU)
      (h_proj : ProjUnifySoundHookU) :
      ∀ st fuel env e st' ty,
        inferExprUnify st fuel env e = .ok st' ty →
        HasTypeU env e ty := by
    intro st fuel env e
    cases e with
    | intLit n =>
      intro st' ty h
      simp [inferExprUnify] at h
      rcases h with ⟨_, hty⟩
      subst hty
      exact HasTypeU.int env n
    | boolLit b =>
      intro st' ty h
      simp [inferExprUnify] at h
      rcases h with ⟨_, hty⟩
      subst hty
      exact HasTypeU.bool env b
    | stringLit s =>
      intro st' ty h
      simp [inferExprUnify] at h
      rcases h with ⟨_, hty⟩
      subst hty
      exact HasTypeU.string env s
    | var name =>
      intro st' ty h
      cases h_lookup : TermEnv.lookup env name with
      | none =>
        simp [inferExprUnify, h_lookup] at h
      | some vty =>
        simp [inferExprUnify, h_lookup] at h
        rcases h with ⟨_, hty⟩
        subst hty
        exact HasTypeU.var env name vty h_lookup
    | lam param paramTy body =>
      intro st' ty h
      simp [inferExprUnify] at h
      cases h_body : inferExprUnify st fuel ((param, paramTy) :: env) body with
      | err err =>
        simp [h_body] at h
      | ok stBody bodyTy =>
        simp [h_body] at h
        rcases h with ⟨_, hty⟩
        subst hty
        exact HasTypeU.lam env param paramTy bodyTy body
          (inferExprUnify_sound_preconditioned_hasTypeU_direct h_app h_proj
            st fuel ((param, paramTy) :: env) body stBody bodyTy h_body)
    | app fn arg =>
      intro st' ty h
      simp [inferExprUnify] at h
      cases h_fn : inferExprUnify st fuel env fn with
      | err err =>
        simp [h_fn] at h
      | ok stFn fnTy =>
        cases h_arg : inferExprUnify stFn fuel env arg with
        | err err =>
          simp [h_fn, h_arg] at h
        | ok stArg argTy =>
          let fresh := stArg.freshTypeVar
          cases h_unify : unify fresh.2 fuel fnTy (Ty.function (.cons argTy .nil) (.var fresh.1)) with
          | err err =>
            have h_false : False := by
              simp [h_fn, h_arg, fresh, h_unify] at h
            exact False.elim h_false
          | ok stU =>
            simp [h_fn, h_arg, fresh, h_unify] at h
            rcases h with ⟨_, hty⟩
            subst hty
            exact h_app env fn arg fnTy argTy fresh.2 stU fuel fresh.1
              (inferExprUnify_sound_preconditioned_hasTypeU_direct h_app h_proj st fuel env fn stFn fnTy h_fn)
              (inferExprUnify_sound_preconditioned_hasTypeU_direct h_app h_proj stFn fuel env arg stArg argTy h_arg)
              h_unify
    | letE name value body =>
      intro st' ty h
      simp [inferExprUnify] at h
      cases h_value : inferExprUnify st fuel env value with
      | err err =>
        simp [h_value] at h
      | ok stValue valueTy =>
        exact HasTypeU.letE env name value body valueTy ty
          (inferExprUnify_sound_preconditioned_hasTypeU_direct h_app h_proj st fuel env value stValue valueTy h_value)
          (inferExprUnify_sound_preconditioned_hasTypeU_direct h_app h_proj stValue fuel ((name, valueTy) :: env) body st' ty (by
            simpa [h_value] using h))
    | record fields =>
      intro st' ty h
      simp [inferExprUnify] at h
      cases h_fields : inferFieldsUnify st fuel env fields with
      | err err =>
        simp [h_fields] at h
      | ok stFields fieldsTy =>
        cases fieldsTy with
        | row rowTy =>
          cases rowTy with
          | mk rf rest =>
            cases rest with
            | some rv =>
              simp [h_fields] at h
            | none =>
              simp [h_fields] at h
              rcases h with ⟨_, hty⟩
              subst hty
              exact HasTypeU.record env fields rf
                (inferFieldsUnify_sound_preconditioned_hasTypeU_direct h_app h_proj st fuel env fields stFields rf (by
                  simp [h_fields]))
        | int | intN _ _ | float | floatN _ | decimal _ _ | bool | string | html | markdown | atom | date | dateTime | unit =>
          simp [h_fields] at h
        | list _ | map _ _ | set _ | option _ | result _ _ | existential _ _ | fixedSizeList _ _ | tensor _ _ | sum _ _ | «opaque» _ _
          | function _ _ | functionEff _ _ _ | «forall» _ _ | app _ _ | constructor _ _ _ | record _ _ | anonRecord _ | dataframe _ | groupedFrame _ _ | tagged _ _ | dynamic | column _ | stream _ | task _ | actor _ | arc _
          | var _ | tuple _ =>
          simp [h_fields] at h
    | proj recv label =>
      intro st' ty h
      simp [inferExprUnify] at h
      cases h_recv : inferExprUnify st fuel env recv with
      | err err =>
        simp [h_recv] at h
      | ok stRecv recvTy =>
        let freshTy := stRecv.freshTypeVar
        let freshRow := freshTy.2.freshRowVar
        cases h_unify :
            unify freshRow.2 fuel recvTy
              (Ty.anonRecord (.mk (.cons label (.var freshTy.1) .nil) (some freshRow.1))) with
        | err err =>
          have h_false : False := by
            simp [h_recv, freshTy, freshRow, h_unify] at h
          exact False.elim h_false
        | ok stU =>
          simp [h_recv, freshTy, freshRow, h_unify] at h
          rcases h with ⟨_, hty⟩
          subst hty
          exact h_proj env recv label recvTy freshRow.2 stU fuel freshTy.1 freshRow.1
            (inferExprUnify_sound_preconditioned_hasTypeU_direct h_app h_proj st fuel env recv stRecv recvTy h_recv)
            h_unify

  theorem inferFieldsUnify_sound_preconditioned_hasTypeU_direct
      (h_app : AppUnifySoundHookU)
      (h_proj : ProjUnifySoundHookU) :
      ∀ st fuel env fs st' rf,
        inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)) →
        HasFieldsTypeU env fs rf := by
    intro st fuel env fs
    cases fs with
    | nil =>
      intro st' rf h
      simp [inferFieldsUnify] at h
      rcases h with ⟨_, hrf⟩
      subst hrf
      exact HasFieldsTypeU.nil env
    | cons label e rest =>
      intro st' rf h
      simp [inferFieldsUnify] at h
      cases h_head : inferExprUnify st fuel env e with
      | err err =>
        simp [h_head] at h
      | ok stHead tyHead =>
        cases h_rest : inferFieldsUnify stHead fuel env rest with
        | err err =>
          simp [h_head, h_rest] at h
        | ok stRest restTy =>
          cases restTy with
          | row rowTy =>
            cases rowTy with
            | mk restFields restVar =>
              cases restVar with
              | some rv =>
                simp [h_head, h_rest] at h
              | none =>
                simp [h_head, h_rest] at h
                rcases h with ⟨_, hrf⟩
                subst hrf
                exact HasFieldsTypeU.cons env label e rest tyHead restFields
                  (inferExprUnify_sound_preconditioned_hasTypeU_direct h_app h_proj st fuel env e stHead tyHead h_head)
                  (inferFieldsUnify_sound_preconditioned_hasTypeU_direct h_app h_proj stHead fuel env rest stRest restFields (by
                    simp [h_rest]))
          | int | intN _ _ | float | floatN _ | decimal _ _ | bool | string | html | markdown | atom | date | dateTime | unit =>
            simp [h_head, h_rest] at h
          | list _ | map _ _ | set _ | option _ | result _ _ | existential _ _ | fixedSizeList _ _ | tensor _ _ | sum _ _ | «opaque» _ _
            | function _ _ | functionEff _ _ _ | «forall» _ _ | app _ _ | constructor _ _ _ | record _ _ | anonRecord _ | dataframe _ | groupedFrame _ _ | tagged _ _ | dynamic | column _ | stream _ | task _ | actor _ | arc _
            | var _ | tuple _ =>
            simp [h_head, h_rest] at h
end

/--
Determinism of `inferExprUnify`: for fixed `(st, fuel, env, e)`, successful
results are unique in both state and type.
-/
theorem inferExprUnify_deterministic
    (st : UnifyState) (fuel : Nat) (env : TermEnv) (e : CoreExpr)
    {st₁ st₂ : UnifyState} {ty₁ ty₂ : Ty}
    (h₁ : inferExprUnify st fuel env e = .ok st₁ ty₁)
    (h₂ : inferExprUnify st fuel env e = .ok st₂ ty₂) :
    st₁ = st₂ ∧ ty₁ = ty₂ := by
  rw [h₁] at h₂
  cases h₂
  exact ⟨rfl, rfl⟩

/--
Type uniqueness from the full preconditioned theorem: once an `inferExprUnify`
run succeeds, any declarative typing derivation for the same expression has the
same type.
-/
theorem inferExprUnify_type_unique_preconditioned
    (h_app : AppUnifySoundHook)
    (h_proj : ProjUnifySoundHook)
    {st st' : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr} {ty ty' : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty)
    (h_ty' : HasType env e ty') :
    ty' = ty := by
  have h_ty : HasType env e ty :=
    inferExprUnify_sound_preconditioned h_app h_proj st fuel env e st' ty h_ok
  have h_alg : inferExpr env e = some ty := inferExpr_complete env e ty h_ty
  have h_alg' : inferExpr env e = some ty' := inferExpr_complete env e ty' h_ty'
  rw [h_alg] at h_alg'
  injection h_alg' with h_eq
  exact h_eq.symm

/--
Packaged principal-typing slice on the current preconditioned boundary.

Given one successful `inferExprUnify` run, this bundle exports:
- uniqueness of successful algorithmic outputs at the same input,
- uniqueness against any declarative typing derivation,
- and agreement with the syntax-directed `inferExpr` result.
-/
structure PrincipalTypingSlicePreconditioned
    (h_app : AppUnifySoundHook)
    (h_proj : ProjUnifySoundHook)
    (st : UnifyState) (fuel : Nat) (env : TermEnv) (e : CoreExpr)
    (st' : UnifyState) (ty : Ty) : Prop where
  deterministic :
    ∀ {st'' : UnifyState} {ty'' : Ty},
      inferExprUnify st fuel env e = .ok st'' ty'' →
      st'' = st' ∧ ty'' = ty
  declarativeUnique :
    ∀ {ty' : Ty}, HasType env e ty' → ty' = ty
  inferExprAgrees :
    inferExpr env e = some ty

theorem principalTypingSlicePreconditioned_of_success
    (h_app : AppUnifySoundHook)
    (h_proj : ProjUnifySoundHook)
    (st : UnifyState) (fuel : Nat) (env : TermEnv) (e : CoreExpr)
    (st' : UnifyState) (ty : Ty)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalTypingSlicePreconditioned h_app h_proj st fuel env e st' ty := by
  refine {
    deterministic := ?_
    declarativeUnique := ?_
    inferExprAgrees := ?_
  }
  · intro st'' ty'' h_ok'
    exact inferExprUnify_deterministic st fuel env e h_ok' h_ok
  · intro ty' h_ty'
    exact inferExprUnify_type_unique_preconditioned h_app h_proj h_ok h_ty'
  · have h_ty : HasType env e ty :=
      inferExprUnify_sound_preconditioned h_app h_proj st fuel env e st' ty h_ok
    exact inferExpr_complete env e ty h_ty

/--
Determinism of `inferFieldsUnify`: for fixed `(st, fuel, env, fs)`, successful
results are unique in both state and closed row-fields payload.
-/
theorem inferFieldsUnify_deterministic
    (st : UnifyState) (fuel : Nat) (env : TermEnv) (fs : CoreFields)
    {st₁ st₂ : UnifyState} {rf₁ rf₂ : RowFields}
    (h₁ : inferFieldsUnify st fuel env fs = .ok st₁ (.row (.mk rf₁ none)))
    (h₂ : inferFieldsUnify st fuel env fs = .ok st₂ (.row (.mk rf₂ none))) :
    st₁ = st₂ ∧ rf₁ = rf₂ := by
  rw [h₁] at h₂
  cases h₂
  exact ⟨rfl, rfl⟩

/--
Row-fields uniqueness from the full preconditioned theorem: once an
`inferFieldsUnify` run succeeds, any declarative field typing derivation for
the same field list has the same row-fields payload.
-/
theorem inferFieldsUnify_row_unique_preconditioned
    (h_app : AppUnifySoundHook)
    (h_proj : ProjUnifySoundHook)
    {st st' : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {rf rf' : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)))
    (h_rf' : HasFieldsType env fs rf') :
    rf' = rf := by
  have h_rf : HasFieldsType env fs rf :=
    inferFieldsUnify_sound_preconditioned h_app h_proj st fuel env fs st' rf h_ok
  exact hasFieldsType_unique h_rf' h_rf

/--
Packaged preconditioned principal-field-typing slice.

Given one successful `inferFieldsUnify` run, this bundle exports:
- uniqueness of successful algorithmic outputs at the same input,
- uniqueness against any declarative field typing derivation,
- and agreement with the syntax-directed `inferFields` result.
-/
structure PrincipalFieldTypingSlicePreconditioned
    (h_app : AppUnifySoundHook)
    (h_proj : ProjUnifySoundHook)
    (st : UnifyState) (fuel : Nat) (env : TermEnv) (fs : CoreFields)
    (st' : UnifyState) (rf : RowFields) : Prop where
  deterministic :
    ∀ {st'' : UnifyState} {rf'' : RowFields},
      inferFieldsUnify st fuel env fs = .ok st'' (.row (.mk rf'' none)) →
      st'' = st' ∧ rf'' = rf
  declarativeUnique :
    ∀ {rf' : RowFields}, HasFieldsType env fs rf' → rf' = rf
  inferFieldsAgrees :
    inferFields env fs = some rf

theorem principalFieldTypingSlicePreconditioned_of_success
    (h_app : AppUnifySoundHook)
    (h_proj : ProjUnifySoundHook)
    (st : UnifyState) (fuel : Nat) (env : TermEnv) (fs : CoreFields)
    (st' : UnifyState) (rf : RowFields)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalFieldTypingSlicePreconditioned h_app h_proj st fuel env fs st' rf := by
  refine {
    deterministic := ?_
    declarativeUnique := ?_
    inferFieldsAgrees := ?_
  }
  · intro st'' rf'' h_ok'
    exact inferFieldsUnify_deterministic st fuel env fs h_ok' h_ok
  · intro rf' h_rf'
    exact inferFieldsUnify_row_unique_preconditioned h_app h_proj h_ok h_rf'
  · have h_rf : HasFieldsType env fs rf :=
      inferFieldsUnify_sound_preconditioned h_app h_proj st fuel env fs st' rf h_ok
    exact inferFields_complete env fs rf h_rf

/--
Bundle-entry variant of `principalFieldTypingSlicePreconditioned_of_success`.
-/
theorem principalFieldTypingSlicePreconditioned_of_success_from_bundle
    (h_hooks : UnifyHookPremises)
    (st : UnifyState) (fuel : Nat) (env : TermEnv) (fs : CoreFields)
    (st' : UnifyState) (rf : RowFields)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalFieldTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env fs st' rf := by
  exact principalFieldTypingSlicePreconditioned_of_success
    h_hooks.1 h_hooks.2 st fuel env fs st' rf h_ok

/--
Successful preconditioned `inferFieldsUnify` runs induce the core principal
field-typing package on the same `(env, fs, rf)` surface.
-/
theorem principalFieldTypingSliceCore_of_preconditioned_success
    (h_app : AppUnifySoundHook)
    (h_proj : ProjUnifySoundHook)
    (st : UnifyState) (fuel : Nat) (env : TermEnv) (fs : CoreFields)
    (st' : UnifyState) (rf : RowFields)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalFieldTypingSliceCore env fs rf := by
  have h_pre :
      PrincipalFieldTypingSlicePreconditioned h_app h_proj st fuel env fs st' rf :=
    principalFieldTypingSlicePreconditioned_of_success h_app h_proj st fuel env fs st' rf h_ok
  exact principalFieldTypingSliceCore_of_infer h_pre.inferFieldsAgrees

/--
Bundle-entry variant of `principalFieldTypingSliceCore_of_preconditioned_success`.
-/
theorem principalFieldTypingSliceCore_of_preconditioned_success_from_bundle
    (h_hooks : UnifyHookPremises)
    (st : UnifyState) (fuel : Nat) (env : TermEnv) (fs : CoreFields)
    (st' : UnifyState) (rf : RowFields)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalFieldTypingSliceCore env fs rf := by
  exact principalFieldTypingSliceCore_of_preconditioned_success
    h_hooks.1 h_hooks.2 st fuel env fs st' rf h_ok

/--
If a core principal-field-typing package is already available for
`(env, fs, rf)`, any successful `inferFieldsUnify` run to that same row-fields
payload yields the full preconditioned principal field-typing bundle,
independent of hook assumptions.
-/
theorem principalFieldTypingSlicePreconditioned_of_success_of_core_principal
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_core : PrincipalFieldTypingSliceCore env fs rf)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    ∀ h_app h_proj,
      PrincipalFieldTypingSlicePreconditioned h_app h_proj st fuel env fs st' rf := by
  intro h_app h_proj
  refine {
    deterministic := ?_
    declarativeUnique := ?_
    inferFieldsAgrees := ?_
  }
  · intro st'' rf'' h_ok'
    exact inferFieldsUnify_deterministic st fuel env fs h_ok' h_ok
  · intro rf' h_rf'
    exact h_core.unique h_rf'
  · exact inferFields_complete env fs rf h_core.sound

/--
Hook-independent preconditioned principal field-typing bundle on the no-unify
fragment.
-/
theorem principalFieldTypingSlicePreconditioned_of_success_no_unify
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    ∀ h_app h_proj,
      PrincipalFieldTypingSlicePreconditioned h_app h_proj st fuel env fs st' rf := by
  have h_core : PrincipalFieldTypingSliceCore env fs rf :=
    principalFieldTypingSliceCore_of_unify_success_no_unify h_no h_ok
  exact principalFieldTypingSlicePreconditioned_of_success_of_core_principal
    h_core h_ok

/--
Bundle-entry variant of
`principalFieldTypingSlicePreconditioned_of_success_no_unify`.
-/
theorem principalFieldTypingSlicePreconditioned_of_success_no_unify_from_bundle
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)))
    (h_hooks : UnifyHookPremises) :
    PrincipalFieldTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env fs st' rf := by
  exact principalFieldTypingSlicePreconditioned_of_success_no_unify
    h_no h_ok h_hooks.1 h_hooks.2

/--
On successful field runs, the preconditioned principal field slice and core
principal field slice are equivalent.
-/
theorem principalFieldTypingSlicePreconditioned_iff_core_of_success
    (h_app : AppUnifySoundHook)
    (h_proj : ProjUnifySoundHook)
    (st : UnifyState) (fuel : Nat) (env : TermEnv) (fs : CoreFields)
    (st' : UnifyState) (rf : RowFields)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalFieldTypingSlicePreconditioned h_app h_proj st fuel env fs st' rf
      ↔ PrincipalFieldTypingSliceCore env fs rf := by
  constructor
  · intro h_pre
    exact principalFieldTypingSliceCore_of_infer h_pre.inferFieldsAgrees
  · intro h_core
    exact principalFieldTypingSlicePreconditioned_of_success_of_core_principal
      h_core h_ok h_app h_proj

/--
Bundle-entry variant of `principalFieldTypingSlicePreconditioned_iff_core_of_success`.
-/
theorem principalFieldTypingSlicePreconditioned_iff_core_of_success_from_bundle
    (h_hooks : UnifyHookPremises)
    (st : UnifyState) (fuel : Nat) (env : TermEnv) (fs : CoreFields)
    (st' : UnifyState) (rf : RowFields)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalFieldTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env fs st' rf
      ↔ PrincipalFieldTypingSliceCore env fs rf := by
  exact principalFieldTypingSlicePreconditioned_iff_core_of_success
    h_hooks.1 h_hooks.2 st fuel env fs st' rf h_ok

/--
Packaged no-unify field principal bridge: one successful hook-free
`inferFieldsUnify` run yields both the core principal field package and the
preconditioned principal field package.
-/
structure PrincipalFieldNoUnifyBridgeBundle
    (h_app : AppUnifySoundHook)
    (h_proj : ProjUnifySoundHook)
    (st : UnifyState) (fuel : Nat) (env : TermEnv) (fs : CoreFields)
    (st' : UnifyState) (rf : RowFields) : Prop where
  core : PrincipalFieldTypingSliceCore env fs rf
  preconditioned : PrincipalFieldTypingSlicePreconditioned h_app h_proj st fuel env fs st' rf

/--
Construct the no-unify field bridge bundle from one successful hook-free
`inferFieldsUnify` run.
-/
theorem principalFieldNoUnifyBridgeBundle_of_success
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    ∀ h_app h_proj,
      PrincipalFieldNoUnifyBridgeBundle h_app h_proj st fuel env fs st' rf := by
  intro h_app h_proj
  let h_core : PrincipalFieldTypingSliceCore env fs rf :=
    principalFieldTypingSliceCore_of_unify_success_no_unify h_no h_ok
  refine {
    core := h_core
    preconditioned := ?_
  }
  exact principalFieldTypingSlicePreconditioned_of_success_of_core_principal
    h_core h_ok h_app h_proj

/--
Bundle-entry variant of `principalFieldNoUnifyBridgeBundle_of_success`.
-/
theorem principalFieldNoUnifyBridgeBundle_of_success_from_hook_bundle
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)))
    (h_hooks : UnifyHookPremises) :
    PrincipalFieldNoUnifyBridgeBundle h_hooks.1 h_hooks.2 st fuel env fs st' rf := by
  exact principalFieldNoUnifyBridgeBundle_of_success h_no h_ok h_hooks.1 h_hooks.2

/--
Bundle-entry variant of `principalTypingSlicePreconditioned_of_success`.
-/
theorem principalTypingSlicePreconditioned_of_success_from_bundle
    (h_hooks : UnifyHookPremises)
    (st : UnifyState) (fuel : Nat) (env : TermEnv) (e : CoreExpr)
    (st' : UnifyState) (ty : Ty)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env e st' ty := by
  exact principalTypingSlicePreconditioned_of_success
    h_hooks.1 h_hooks.2 st fuel env e st' ty h_ok

/--
On successful expression runs, the preconditioned principal slice and core
principal slice are equivalent.
-/
theorem principalTypingSlicePreconditioned_iff_core_of_success
    (h_app : AppUnifySoundHook)
    (h_proj : ProjUnifySoundHook)
    (st : UnifyState) (fuel : Nat) (env : TermEnv) (e : CoreExpr)
    (st' : UnifyState) (ty : Ty)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalTypingSlicePreconditioned h_app h_proj st fuel env e st' ty
      ↔ PrincipalTypingSliceCore env e ty := by
  constructor
  · intro h_pre
    exact principalTypingSliceCore_of_infer h_pre.inferExprAgrees
  · intro h_core
    refine {
      deterministic := ?_
      declarativeUnique := ?_
      inferExprAgrees := ?_
    }
    · intro st'' ty'' h_ok'
      exact inferExprUnify_deterministic st fuel env e h_ok' h_ok
    · intro ty' h_ty'
      exact h_core.unique h_ty'
    · exact inferExpr_complete env e ty h_core.sound

/--
Bundle-entry variant of `principalTypingSlicePreconditioned_iff_core_of_success`.
-/
theorem principalTypingSlicePreconditioned_iff_core_of_success_from_bundle
    (h_hooks : UnifyHookPremises)
    (st : UnifyState) (fuel : Nat) (env : TermEnv) (e : CoreExpr)
    (st' : UnifyState) (ty : Ty)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env e st' ty
      ↔ PrincipalTypingSliceCore env e ty := by
  exact principalTypingSlicePreconditioned_iff_core_of_success
    h_hooks.1 h_hooks.2 st fuel env e st' ty h_ok

/--
Packaged successful-run preconditioned↔core principality slice for expressions.
-/
def PrincipalPreconditionedExprCoreIffSlice : Prop :=
  ∀ (h_hooks : UnifyHookPremises)
    (st : UnifyState) (fuel : Nat) (env : TermEnv) (e : CoreExpr)
    (st' : UnifyState) (ty : Ty),
    inferExprUnify st fuel env e = .ok st' ty →
    (PrincipalTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env e st' ty
      ↔ PrincipalTypingSliceCore env e ty)

/--
Packaged successful-run preconditioned↔core principality slice for fields.
-/
def PrincipalPreconditionedFieldCoreIffSlice : Prop :=
  ∀ (h_hooks : UnifyHookPremises)
    (st : UnifyState) (fuel : Nat) (env : TermEnv) (fs : CoreFields)
    (st' : UnifyState) (rf : RowFields),
    inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)) →
    (PrincipalFieldTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env fs st' rf
      ↔ PrincipalFieldTypingSliceCore env fs rf)

/-- Combined successful-run preconditioned↔core principality slice. -/
def PrincipalPreconditionedCoreIffSlices : Prop :=
  PrincipalPreconditionedExprCoreIffSlice ∧ PrincipalPreconditionedFieldCoreIffSlice

/-- The combined preconditioned↔core principality slice is fully proved. -/
theorem principalPreconditionedCoreIffSlices_proved : PrincipalPreconditionedCoreIffSlices := by
  refine ⟨?_, ?_⟩
  · intro h_hooks st fuel env e st' ty h_ok
    exact principalTypingSlicePreconditioned_iff_core_of_success_from_bundle
      h_hooks st fuel env e st' ty h_ok
  · intro h_hooks st fuel env fs st' rf h_ok
    exact principalFieldTypingSlicePreconditioned_iff_core_of_success_from_bundle
      h_hooks st fuel env fs st' rf h_ok

/--
One-hop projection: expression branch from combined preconditioned↔core slice.
-/
theorem principalPreconditionedCoreIffSlices_expr
    (h_slice : PrincipalPreconditionedCoreIffSlices)
    (h_hooks : UnifyHookPremises)
    (st : UnifyState) (fuel : Nat) (env : TermEnv) (e : CoreExpr)
    (st' : UnifyState) (ty : Ty)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    (PrincipalTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env e st' ty
      ↔ PrincipalTypingSliceCore env e ty) :=
  h_slice.1 h_hooks st fuel env e st' ty h_ok

/--
One-hop projection: field branch from combined preconditioned↔core slice.
-/
theorem principalPreconditionedCoreIffSlices_field
    (h_slice : PrincipalPreconditionedCoreIffSlices)
    (h_hooks : UnifyHookPremises)
    (st : UnifyState) (fuel : Nat) (env : TermEnv) (fs : CoreFields)
    (st' : UnifyState) (rf : RowFields)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    (PrincipalFieldTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env fs st' rf
      ↔ PrincipalFieldTypingSliceCore env fs rf) :=
  h_slice.2 h_hooks st fuel env fs st' rf h_ok

/--
Successful preconditioned `inferExprUnify` runs induce the core principal
typing package on the same `(env, e, ty)` surface.
-/
theorem principalTypingSliceCore_of_preconditioned_success
    (h_app : AppUnifySoundHook)
    (h_proj : ProjUnifySoundHook)
    (st : UnifyState) (fuel : Nat) (env : TermEnv) (e : CoreExpr)
    (st' : UnifyState) (ty : Ty)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalTypingSliceCore env e ty := by
  have h_pre :
      PrincipalTypingSlicePreconditioned h_app h_proj st fuel env e st' ty :=
    principalTypingSlicePreconditioned_of_success h_app h_proj st fuel env e st' ty h_ok
  exact principalTypingSliceCore_of_infer h_pre.inferExprAgrees

/--
Bundle-entry variant of `principalTypingSliceCore_of_preconditioned_success`.
-/
theorem principalTypingSliceCore_of_preconditioned_success_from_bundle
    (h_hooks : UnifyHookPremises)
    (st : UnifyState) (fuel : Nat) (env : TermEnv) (e : CoreExpr)
    (st' : UnifyState) (ty : Ty)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalTypingSliceCore env e ty := by
  exact principalTypingSliceCore_of_preconditioned_success
    h_hooks.1 h_hooks.2 st fuel env e st' ty h_ok

/--
If a core principal-typing package is already available for `(env, e, ty)`,
any successful `inferExprUnify` run to that same type yields the full
preconditioned principal bundle, independent of hook assumptions.
-/
theorem principalTypingSlicePreconditioned_of_success_of_core_principal
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_core : PrincipalTypingSliceCore env e ty)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    ∀ h_app h_proj,
      PrincipalTypingSlicePreconditioned h_app h_proj st fuel env e st' ty := by
  intro h_app h_proj
  refine {
    deterministic := ?_
    declarativeUnique := ?_
    inferExprAgrees := ?_
  }
  · intro st'' ty'' h_ok'
    exact inferExprUnify_deterministic st fuel env e h_ok' h_ok
  · intro ty' h_ty'
    exact h_core.unique h_ty'
  · exact inferExpr_complete env e ty h_core.sound

/--
Hook-independent principal-typing bundle on the no-unify fragment.

When `e` never executes app/proj unification branches, successful
`inferExprUnify` runs determine the same principal consequences as the
preconditioned bundle, independent of app/proj hook assumptions.
-/
theorem principalTypingSlicePreconditioned_of_success_no_unify
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    ∀ h_app h_proj,
      PrincipalTypingSlicePreconditioned h_app h_proj st fuel env e st' ty := by
  have h_core : PrincipalTypingSliceCore env e ty :=
    principalTypingSliceCore_of_unify_success_no_unify h_no h_ok
  exact principalTypingSlicePreconditioned_of_success_of_core_principal
    h_core h_ok

/--
Bundle-entry variant of `principalTypingSlicePreconditioned_of_success_no_unify`.
-/
theorem principalTypingSlicePreconditioned_of_success_no_unify_from_bundle
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty)
    (h_hooks : UnifyHookPremises) :
    PrincipalTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env e st' ty := by
  exact principalTypingSlicePreconditioned_of_success_no_unify
    h_no h_ok h_hooks.1 h_hooks.2

/--
Packaged no-unify principal bridge: one successful hook-free `inferExprUnify`
run yields both the core principal package and the preconditioned principal
package.
-/
structure PrincipalNoUnifyBridgeBundle
    (h_app : AppUnifySoundHook)
    (h_proj : ProjUnifySoundHook)
    (st : UnifyState) (fuel : Nat) (env : TermEnv) (e : CoreExpr)
    (st' : UnifyState) (ty : Ty) : Prop where
  core : PrincipalTypingSliceCore env e ty
  preconditioned : PrincipalTypingSlicePreconditioned h_app h_proj st fuel env e st' ty

/--
Construct the no-unify bridge bundle from one successful hook-free
`inferExprUnify` run.
-/
theorem principalNoUnifyBridgeBundle_of_success
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    ∀ h_app h_proj,
      PrincipalNoUnifyBridgeBundle h_app h_proj st fuel env e st' ty := by
  intro h_app h_proj
  let h_core : PrincipalTypingSliceCore env e ty :=
    principalTypingSliceCore_of_unify_success_no_unify h_no h_ok
  refine {
    core := h_core
    preconditioned := ?_
  }
  exact principalTypingSlicePreconditioned_of_success_of_core_principal
    h_core h_ok h_app h_proj

/--
Bundle-entry variant of `principalNoUnifyBridgeBundle_of_success`.
-/
theorem principalNoUnifyBridgeBundle_of_success_from_hook_bundle
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty)
    (h_hooks : UnifyHookPremises) :
    PrincipalNoUnifyBridgeBundle h_hooks.1 h_hooks.2 st fuel env e st' ty := by
  exact principalNoUnifyBridgeBundle_of_success h_no h_ok h_hooks.1 h_hooks.2

/-- Packaged no-unify expression principal bridge slice (bundle-entry form). -/
def PrincipalNoUnifyExprBridgeSlice : Prop :=
  ∀ {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty},
    NoUnifyBranchesExpr e →
    inferExprUnify st fuel env e = .ok st' ty →
    (h_hooks : UnifyHookPremises) →
    PrincipalNoUnifyBridgeBundle h_hooks.1 h_hooks.2 st fuel env e st' ty

/-- Packaged no-unify field principal bridge slice (bundle-entry form). -/
def PrincipalNoUnifyFieldBridgeSlice : Prop :=
  ∀ {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields},
    NoUnifyBranchesFields fs →
    inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)) →
    (h_hooks : UnifyHookPremises) →
    PrincipalFieldNoUnifyBridgeBundle h_hooks.1 h_hooks.2 st fuel env fs st' rf

/-- Combined no-unify principal bridge slice across expressions and fields. -/
def PrincipalNoUnifyBridgeSlices : Prop :=
  PrincipalNoUnifyExprBridgeSlice ∧ PrincipalNoUnifyFieldBridgeSlice

/-- The combined no-unify principal bridge slice is fully proved. -/
theorem principalNoUnifyBridgeSlices_proved : PrincipalNoUnifyBridgeSlices := by
  refine ⟨?_, ?_⟩
  · intro st fuel env e st' ty h_no h_ok h_hooks
    exact principalNoUnifyBridgeBundle_of_success_from_hook_bundle
      h_no h_ok h_hooks
  · intro st fuel env fs st' rf h_no h_ok h_hooks
    exact principalFieldNoUnifyBridgeBundle_of_success_from_hook_bundle
      h_no h_ok h_hooks

/-- One-hop projection: expression branch from combined no-unify bridge slice. -/
theorem principalNoUnifyBridgeSlices_expr
    (h_slice : PrincipalNoUnifyBridgeSlices)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty)
    (h_hooks : UnifyHookPremises) :
    PrincipalNoUnifyBridgeBundle h_hooks.1 h_hooks.2 st fuel env e st' ty :=
  h_slice.1 h_no h_ok h_hooks

/-- One-hop projection: field branch from combined no-unify bridge slice. -/
theorem principalNoUnifyBridgeSlices_field
    (h_slice : PrincipalNoUnifyBridgeSlices)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)))
    (h_hooks : UnifyHookPremises) :
    PrincipalFieldNoUnifyBridgeBundle h_hooks.1 h_hooks.2 st fuel env fs st' rf :=
  h_slice.2 h_no h_ok h_hooks

/--
Combined M4 principal boundary bridge suite.

This packages the two capstones needed at the current boundary:
- hook-free no-unify bridge slices, and
- successful-run preconditioned↔core equivalence slices.
-/
structure PrincipalBoundaryBridgeSuite : Prop where
  noUnify : PrincipalNoUnifyBridgeSlices
  preconditionedCoreIff : PrincipalPreconditionedCoreIffSlices

/-- The combined principal boundary bridge suite is fully proved. -/
theorem principalBoundaryBridgeSuite_proved : PrincipalBoundaryBridgeSuite := by
  refine {
    noUnify := principalNoUnifyBridgeSlices_proved
    preconditionedCoreIff := principalPreconditionedCoreIffSlices_proved
  }

/-- One-hop expression no-unify bridge projection from the suite. -/
theorem principalBoundaryBridgeSuite_noUnify_expr
    (h_suite : PrincipalBoundaryBridgeSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty)
    (h_hooks : UnifyHookPremises) :
    PrincipalNoUnifyBridgeBundle h_hooks.1 h_hooks.2 st fuel env e st' ty :=
  principalNoUnifyBridgeSlices_expr h_suite.noUnify h_no h_ok h_hooks

/-- One-hop field no-unify bridge projection from the suite. -/
theorem principalBoundaryBridgeSuite_noUnify_field
    (h_suite : PrincipalBoundaryBridgeSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)))
    (h_hooks : UnifyHookPremises) :
    PrincipalFieldNoUnifyBridgeBundle h_hooks.1 h_hooks.2 st fuel env fs st' rf :=
  principalNoUnifyBridgeSlices_field h_suite.noUnify h_no h_ok h_hooks

/-- One-hop expression preconditioned↔core equivalence projection from suite. -/
theorem principalBoundaryBridgeSuite_preconditionedCoreIff_expr
    (h_suite : PrincipalBoundaryBridgeSuite)
    (h_hooks : UnifyHookPremises)
    (st : UnifyState) (fuel : Nat) (env : TermEnv) (e : CoreExpr)
    (st' : UnifyState) (ty : Ty)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    (PrincipalTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env e st' ty
      ↔ PrincipalTypingSliceCore env e ty) :=
  principalPreconditionedCoreIffSlices_expr
    h_suite.preconditionedCoreIff h_hooks st fuel env e st' ty h_ok

/-- One-hop field preconditioned↔core equivalence projection from suite. -/
theorem principalBoundaryBridgeSuite_preconditionedCoreIff_field
    (h_suite : PrincipalBoundaryBridgeSuite)
    (h_hooks : UnifyHookPremises)
    (st : UnifyState) (fuel : Nat) (env : TermEnv) (fs : CoreFields)
    (st' : UnifyState) (rf : RowFields)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    (PrincipalFieldTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env fs st' rf
      ↔ PrincipalFieldTypingSliceCore env fs rf) :=
  principalPreconditionedCoreIffSlices_field
    h_suite.preconditionedCoreIff h_hooks st fuel env fs st' rf h_ok

/--
Convenience wrapper: derive core principality from successful no-unify
expression inference via the proved boundary suite.
-/
theorem principalNoUnifyCoreExpr_of_success_via_suite
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty)
    (h_hooks : UnifyHookPremises) :
    PrincipalTypingSliceCore env e ty := by
  exact (principalBoundaryBridgeSuite_noUnify_expr
      principalBoundaryBridgeSuite_proved h_no h_ok h_hooks).core

/--
Convenience wrapper: derive preconditioned principality from successful
no-unify expression inference via the proved boundary suite.
-/
theorem principalNoUnifyPreconditionedExpr_of_success_via_suite
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty)
    (h_hooks : UnifyHookPremises) :
    PrincipalTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env e st' ty := by
  exact (principalBoundaryBridgeSuite_noUnify_expr
      principalBoundaryBridgeSuite_proved h_no h_ok h_hooks).preconditioned

/--
Convenience wrapper: derive core field principality from successful no-unify
field inference via the proved boundary suite.
-/
theorem principalNoUnifyCoreField_of_success_via_suite
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)))
    (h_hooks : UnifyHookPremises) :
    PrincipalFieldTypingSliceCore env fs rf := by
  exact (principalBoundaryBridgeSuite_noUnify_field
      principalBoundaryBridgeSuite_proved h_no h_ok h_hooks).core

/--
Convenience wrapper: derive preconditioned field principality from successful
no-unify field inference via the proved boundary suite.
-/
theorem principalNoUnifyPreconditionedField_of_success_via_suite
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)))
    (h_hooks : UnifyHookPremises) :
    PrincipalFieldTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env fs st' rf := by
  exact (principalBoundaryBridgeSuite_noUnify_field
      principalBoundaryBridgeSuite_proved h_no h_ok h_hooks).preconditioned

/--
Convenience wrapper: convert preconditioned -> core principality on successful
expression runs via the proved boundary suite.
-/
theorem principalCoreExpr_of_preconditioned_success_via_suite
    (h_hooks : UnifyHookPremises)
    (st : UnifyState) (fuel : Nat) (env : TermEnv) (e : CoreExpr)
    (st' : UnifyState) (ty : Ty)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty)
    (h_pre : PrincipalTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env e st' ty) :
    PrincipalTypingSliceCore env e ty := by
  exact (principalBoundaryBridgeSuite_preconditionedCoreIff_expr
      principalBoundaryBridgeSuite_proved h_hooks st fuel env e st' ty h_ok).1 h_pre

/--
Convenience wrapper: convert core -> preconditioned principality on successful
expression runs via the proved boundary suite.
-/
theorem principalPreconditionedExpr_of_core_success_via_suite
    (h_hooks : UnifyHookPremises)
    (st : UnifyState) (fuel : Nat) (env : TermEnv) (e : CoreExpr)
    (st' : UnifyState) (ty : Ty)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty)
    (h_core : PrincipalTypingSliceCore env e ty) :
    PrincipalTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env e st' ty := by
  exact (principalBoundaryBridgeSuite_preconditionedCoreIff_expr
      principalBoundaryBridgeSuite_proved h_hooks st fuel env e st' ty h_ok).2 h_core

/--
Convenience wrapper: convert preconditioned -> core field principality on
successful field runs via the proved boundary suite.
-/
theorem principalCoreField_of_preconditioned_success_via_suite
    (h_hooks : UnifyHookPremises)
    (st : UnifyState) (fuel : Nat) (env : TermEnv) (fs : CoreFields)
    (st' : UnifyState) (rf : RowFields)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)))
    (h_pre : PrincipalFieldTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env fs st' rf) :
    PrincipalFieldTypingSliceCore env fs rf := by
  exact (principalBoundaryBridgeSuite_preconditionedCoreIff_field
      principalBoundaryBridgeSuite_proved h_hooks st fuel env fs st' rf h_ok).1 h_pre

/--
Convenience wrapper: convert core -> preconditioned field principality on
successful field runs via the proved boundary suite.
-/
theorem principalPreconditionedField_of_core_success_via_suite
    (h_hooks : UnifyHookPremises)
    (st : UnifyState) (fuel : Nat) (env : TermEnv) (fs : CoreFields)
    (st' : UnifyState) (rf : RowFields)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)))
    (h_core : PrincipalFieldTypingSliceCore env fs rf) :
    PrincipalFieldTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env fs st' rf := by
  exact (principalBoundaryBridgeSuite_preconditionedCoreIff_field
      principalBoundaryBridgeSuite_proved h_hooks st fuel env fs st' rf h_ok).2 h_core

/--
Coherence (expression): the suite's no-unify preconditioned witness implies the
suite's core witness through the suite's preconditioned↔core equivalence.
-/
theorem principalBoundaryBridgeSuite_noUnify_expr_coherent_core
    (h_suite : PrincipalBoundaryBridgeSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty)
    (h_hooks : UnifyHookPremises) :
    PrincipalTypingSliceCore env e ty := by
  exact (principalBoundaryBridgeSuite_preconditionedCoreIff_expr
      h_suite h_hooks st fuel env e st' ty h_ok).1
        ((principalBoundaryBridgeSuite_noUnify_expr
          h_suite h_no h_ok h_hooks).preconditioned)

/--
Coherence (expression): the suite's no-unify core witness implies the suite's
preconditioned witness through the suite's preconditioned↔core equivalence.
-/
theorem principalBoundaryBridgeSuite_noUnify_expr_coherent_preconditioned
    (h_suite : PrincipalBoundaryBridgeSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty)
    (h_hooks : UnifyHookPremises) :
    PrincipalTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env e st' ty := by
  exact (principalBoundaryBridgeSuite_preconditionedCoreIff_expr
      h_suite h_hooks st fuel env e st' ty h_ok).2
        ((principalBoundaryBridgeSuite_noUnify_expr
          h_suite h_no h_ok h_hooks).core)

/--
Coherence (field): the suite's no-unify preconditioned witness implies the
suite's core witness through the suite's preconditioned↔core equivalence.
-/
theorem principalBoundaryBridgeSuite_noUnify_field_coherent_core
    (h_suite : PrincipalBoundaryBridgeSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)))
    (h_hooks : UnifyHookPremises) :
    PrincipalFieldTypingSliceCore env fs rf := by
  exact (principalBoundaryBridgeSuite_preconditionedCoreIff_field
      h_suite h_hooks st fuel env fs st' rf h_ok).1
        ((principalBoundaryBridgeSuite_noUnify_field
          h_suite h_no h_ok h_hooks).preconditioned)

/--
Coherence (field): the suite's no-unify core witness implies the suite's
preconditioned witness through the suite's preconditioned↔core equivalence.
-/
theorem principalBoundaryBridgeSuite_noUnify_field_coherent_preconditioned
    (h_suite : PrincipalBoundaryBridgeSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)))
    (h_hooks : UnifyHookPremises) :
    PrincipalFieldTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env fs st' rf := by
  exact (principalBoundaryBridgeSuite_preconditionedCoreIff_field
      h_suite h_hooks st fuel env fs st' rf h_ok).2
        ((principalBoundaryBridgeSuite_noUnify_field
          h_suite h_no h_ok h_hooks).core)

/--
No-unify expression capstone from the principal boundary suite.

Packages the no-unify bridge witness and successful-run
preconditioned↔core equivalence in one theorem surface.
-/
structure PrincipalBoundaryNoUnifyExprCapstone
    (h_app : AppUnifySoundHook)
    (h_proj : ProjUnifySoundHook)
    (st : UnifyState) (fuel : Nat) (env : TermEnv) (e : CoreExpr)
    (st' : UnifyState) (ty : Ty) : Prop where
  noUnify : PrincipalNoUnifyBridgeBundle h_app h_proj st fuel env e st' ty
  preconditionedCoreIff :
    PrincipalTypingSlicePreconditioned h_app h_proj st fuel env e st' ty
      ↔ PrincipalTypingSliceCore env e ty

/--
Construct the no-unify expression capstone directly from successful no-unify
inference via the proved principal boundary suite.
-/
theorem principalBoundaryNoUnifyExprCapstone_of_success_via_suite
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty)
    (h_hooks : UnifyHookPremises) :
    PrincipalBoundaryNoUnifyExprCapstone
      h_hooks.1 h_hooks.2 st fuel env e st' ty := by
  refine {
    noUnify := principalBoundaryBridgeSuite_noUnify_expr
      principalBoundaryBridgeSuite_proved h_no h_ok h_hooks
    preconditionedCoreIff := principalBoundaryBridgeSuite_preconditionedCoreIff_expr
      principalBoundaryBridgeSuite_proved h_hooks st fuel env e st' ty h_ok
  }

/--
Unbundled-hook entrypoint for the no-unify expression capstone.
-/
theorem principalBoundaryNoUnifyExprCapstone_of_success
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    ∀ h_app h_proj,
      PrincipalBoundaryNoUnifyExprCapstone
        h_app h_proj st fuel env e st' ty := by
  intro h_app h_proj
  exact principalBoundaryNoUnifyExprCapstone_of_success_via_suite
    h_no h_ok ⟨h_app, h_proj⟩

/--
Bundle-entry variant of `principalBoundaryNoUnifyExprCapstone_of_success`.
-/
theorem principalBoundaryNoUnifyExprCapstone_of_success_from_hook_bundle
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty)
    (h_hooks : UnifyHookPremises) :
    PrincipalBoundaryNoUnifyExprCapstone
      h_hooks.1 h_hooks.2 st fuel env e st' ty := by
  exact principalBoundaryNoUnifyExprCapstone_of_success
    h_no h_ok h_hooks.1 h_hooks.2

/-- One-hop projection: core expression principality from the expression capstone. -/
theorem principalBoundaryNoUnifyExprCapstone_core
    {h_app : AppUnifySoundHook} {h_proj : ProjUnifySoundHook}
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_cap : PrincipalBoundaryNoUnifyExprCapstone
      h_app h_proj st fuel env e st' ty) :
    PrincipalTypingSliceCore env e ty :=
  h_cap.noUnify.core

/-- One-hop projection: preconditioned expression principality from the capstone. -/
theorem principalBoundaryNoUnifyExprCapstone_preconditioned
    {h_app : AppUnifySoundHook} {h_proj : ProjUnifySoundHook}
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_cap : PrincipalBoundaryNoUnifyExprCapstone
      h_app h_proj st fuel env e st' ty) :
    PrincipalTypingSlicePreconditioned h_app h_proj st fuel env e st' ty :=
  h_cap.noUnify.preconditioned

/--
Coherence (expression capstone): no-unify preconditioned witness implies the
core witness through the packaged successful-run equivalence.
-/
theorem principalBoundaryNoUnifyExprCapstone_coherent_core
    {h_app : AppUnifySoundHook} {h_proj : ProjUnifySoundHook}
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_cap : PrincipalBoundaryNoUnifyExprCapstone
      h_app h_proj st fuel env e st' ty) :
    PrincipalTypingSliceCore env e ty := by
  exact h_cap.preconditionedCoreIff.1 h_cap.noUnify.preconditioned

/--
Coherence (expression capstone): no-unify core witness implies the
preconditioned witness through the packaged successful-run equivalence.
-/
theorem principalBoundaryNoUnifyExprCapstone_coherent_preconditioned
    {h_app : AppUnifySoundHook} {h_proj : ProjUnifySoundHook}
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_cap : PrincipalBoundaryNoUnifyExprCapstone
      h_app h_proj st fuel env e st' ty) :
    PrincipalTypingSlicePreconditioned h_app h_proj st fuel env e st' ty := by
  exact h_cap.preconditionedCoreIff.2 h_cap.noUnify.core

/--
No-unify field capstone from the principal boundary suite.

Packages the field no-unify bridge witness and successful-run
preconditioned↔core equivalence in one theorem surface.
-/
structure PrincipalBoundaryNoUnifyFieldCapstone
    (h_app : AppUnifySoundHook)
    (h_proj : ProjUnifySoundHook)
    (st : UnifyState) (fuel : Nat) (env : TermEnv) (fs : CoreFields)
    (st' : UnifyState) (rf : RowFields) : Prop where
  noUnify : PrincipalFieldNoUnifyBridgeBundle h_app h_proj st fuel env fs st' rf
  preconditionedCoreIff :
    PrincipalFieldTypingSlicePreconditioned h_app h_proj st fuel env fs st' rf
      ↔ PrincipalFieldTypingSliceCore env fs rf

/--
Construct the no-unify field capstone directly from successful no-unify field
inference via the proved principal boundary suite.
-/
theorem principalBoundaryNoUnifyFieldCapstone_of_success_via_suite
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)))
    (h_hooks : UnifyHookPremises) :
    PrincipalBoundaryNoUnifyFieldCapstone
      h_hooks.1 h_hooks.2 st fuel env fs st' rf := by
  refine {
    noUnify := principalBoundaryBridgeSuite_noUnify_field
      principalBoundaryBridgeSuite_proved h_no h_ok h_hooks
    preconditionedCoreIff := principalBoundaryBridgeSuite_preconditionedCoreIff_field
      principalBoundaryBridgeSuite_proved h_hooks st fuel env fs st' rf h_ok
  }

/--
Unbundled-hook entrypoint for the no-unify field capstone.
-/
theorem principalBoundaryNoUnifyFieldCapstone_of_success
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    ∀ h_app h_proj,
      PrincipalBoundaryNoUnifyFieldCapstone
        h_app h_proj st fuel env fs st' rf := by
  intro h_app h_proj
  exact principalBoundaryNoUnifyFieldCapstone_of_success_via_suite
    h_no h_ok ⟨h_app, h_proj⟩

/--
Bundle-entry variant of `principalBoundaryNoUnifyFieldCapstone_of_success`.
-/
theorem principalBoundaryNoUnifyFieldCapstone_of_success_from_hook_bundle
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)))
    (h_hooks : UnifyHookPremises) :
    PrincipalBoundaryNoUnifyFieldCapstone
      h_hooks.1 h_hooks.2 st fuel env fs st' rf := by
  exact principalBoundaryNoUnifyFieldCapstone_of_success
    h_no h_ok h_hooks.1 h_hooks.2

/-- One-hop projection: core field principality from the field capstone. -/
theorem principalBoundaryNoUnifyFieldCapstone_core
    {h_app : AppUnifySoundHook} {h_proj : ProjUnifySoundHook}
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_cap : PrincipalBoundaryNoUnifyFieldCapstone
      h_app h_proj st fuel env fs st' rf) :
    PrincipalFieldTypingSliceCore env fs rf :=
  h_cap.noUnify.core

/-- One-hop projection: preconditioned field principality from the field capstone. -/
theorem principalBoundaryNoUnifyFieldCapstone_preconditioned
    {h_app : AppUnifySoundHook} {h_proj : ProjUnifySoundHook}
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_cap : PrincipalBoundaryNoUnifyFieldCapstone
      h_app h_proj st fuel env fs st' rf) :
    PrincipalFieldTypingSlicePreconditioned h_app h_proj st fuel env fs st' rf :=
  h_cap.noUnify.preconditioned

/--
Coherence (field capstone): no-unify preconditioned witness implies the
core witness through the packaged successful-run equivalence.
-/
theorem principalBoundaryNoUnifyFieldCapstone_coherent_core
    {h_app : AppUnifySoundHook} {h_proj : ProjUnifySoundHook}
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_cap : PrincipalBoundaryNoUnifyFieldCapstone
      h_app h_proj st fuel env fs st' rf) :
    PrincipalFieldTypingSliceCore env fs rf := by
  exact h_cap.preconditionedCoreIff.1 h_cap.noUnify.preconditioned

/--
Coherence (field capstone): no-unify core witness implies the
preconditioned witness through the packaged successful-run equivalence.
-/
theorem principalBoundaryNoUnifyFieldCapstone_coherent_preconditioned
    {h_app : AppUnifySoundHook} {h_proj : ProjUnifySoundHook}
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_cap : PrincipalBoundaryNoUnifyFieldCapstone
      h_app h_proj st fuel env fs st' rf) :
    PrincipalFieldTypingSlicePreconditioned h_app h_proj st fuel env fs st' rf := by
  exact h_cap.preconditionedCoreIff.2 h_cap.noUnify.core

/-- Packaged no-unify expression principal capstone slice. -/
def PrincipalBoundaryNoUnifyExprCapstoneSlice : Prop :=
  ∀ {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty},
    NoUnifyBranchesExpr e →
    inferExprUnify st fuel env e = .ok st' ty →
    (h_hooks : UnifyHookPremises) →
    PrincipalBoundaryNoUnifyExprCapstone
      h_hooks.1 h_hooks.2 st fuel env e st' ty

/-- Packaged no-unify field principal capstone slice. -/
def PrincipalBoundaryNoUnifyFieldCapstoneSlice : Prop :=
  ∀ {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields},
    NoUnifyBranchesFields fs →
    inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)) →
    (h_hooks : UnifyHookPremises) →
    PrincipalBoundaryNoUnifyFieldCapstone
      h_hooks.1 h_hooks.2 st fuel env fs st' rf

/-- Combined no-unify principal capstone slice across expressions and fields. -/
def PrincipalBoundaryNoUnifyCapstoneSlices : Prop :=
  PrincipalBoundaryNoUnifyExprCapstoneSlice ∧
    PrincipalBoundaryNoUnifyFieldCapstoneSlice

/-- The combined no-unify principal capstone slice is fully proved. -/
theorem principalBoundaryNoUnifyCapstoneSlices_proved :
    PrincipalBoundaryNoUnifyCapstoneSlices := by
  refine ⟨?_, ?_⟩
  · intro st fuel env e st' ty h_no h_ok h_hooks
    exact principalBoundaryNoUnifyExprCapstone_of_success_via_suite
      h_no h_ok h_hooks
  · intro st fuel env fs st' rf h_no h_ok h_hooks
    exact principalBoundaryNoUnifyFieldCapstone_of_success_via_suite
      h_no h_ok h_hooks

/--
One-hop projection: expression branch from combined no-unify principal capstone
slice.
-/
theorem principalBoundaryNoUnifyCapstoneSlices_expr
    (h_slice : PrincipalBoundaryNoUnifyCapstoneSlices)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty)
    (h_hooks : UnifyHookPremises) :
    PrincipalBoundaryNoUnifyExprCapstone
      h_hooks.1 h_hooks.2 st fuel env e st' ty :=
  h_slice.1 h_no h_ok h_hooks

/-- One-hop projection: field branch from combined no-unify principal capstone slice. -/
theorem principalBoundaryNoUnifyCapstoneSlices_field
    (h_slice : PrincipalBoundaryNoUnifyCapstoneSlices)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)))
    (h_hooks : UnifyHookPremises) :
    PrincipalBoundaryNoUnifyFieldCapstone
      h_hooks.1 h_hooks.2 st fuel env fs st' rf :=
  h_slice.2 h_no h_ok h_hooks

/--
One-hop projection: core expression principality from combined no-unify
principal capstone slices.
-/
theorem principalBoundaryNoUnifyCapstoneSlices_expr_core
    (h_slice : PrincipalBoundaryNoUnifyCapstoneSlices)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty)
    (h_hooks : UnifyHookPremises) :
    PrincipalTypingSliceCore env e ty :=
  (principalBoundaryNoUnifyCapstoneSlices_expr
    h_slice h_no h_ok h_hooks).noUnify.core

/--
One-hop projection: preconditioned expression principality from combined
no-unify principal capstone slices.
-/
theorem principalBoundaryNoUnifyCapstoneSlices_expr_preconditioned
    (h_slice : PrincipalBoundaryNoUnifyCapstoneSlices)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty)
    (h_hooks : UnifyHookPremises) :
    PrincipalTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env e st' ty :=
  (principalBoundaryNoUnifyCapstoneSlices_expr
    h_slice h_no h_ok h_hooks).noUnify.preconditioned

/--
One-hop projection: successful-run expression preconditioned↔core equivalence
from combined no-unify principal capstone slices.
-/
theorem principalBoundaryNoUnifyCapstoneSlices_expr_preconditionedCoreIff
    (h_slice : PrincipalBoundaryNoUnifyCapstoneSlices)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty)
    (h_hooks : UnifyHookPremises) :
    (PrincipalTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env e st' ty
      ↔ PrincipalTypingSliceCore env e ty) :=
  (principalBoundaryNoUnifyCapstoneSlices_expr
    h_slice h_no h_ok h_hooks).preconditionedCoreIff

/--
One-hop projection: core field principality from combined no-unify
principal capstone slices.
-/
theorem principalBoundaryNoUnifyCapstoneSlices_field_core
    (h_slice : PrincipalBoundaryNoUnifyCapstoneSlices)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)))
    (h_hooks : UnifyHookPremises) :
    PrincipalFieldTypingSliceCore env fs rf :=
  (principalBoundaryNoUnifyCapstoneSlices_field
    h_slice h_no h_ok h_hooks).noUnify.core

/--
One-hop projection: preconditioned field principality from combined
no-unify principal capstone slices.
-/
theorem principalBoundaryNoUnifyCapstoneSlices_field_preconditioned
    (h_slice : PrincipalBoundaryNoUnifyCapstoneSlices)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)))
    (h_hooks : UnifyHookPremises) :
    PrincipalFieldTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env fs st' rf :=
  (principalBoundaryNoUnifyCapstoneSlices_field
    h_slice h_no h_ok h_hooks).noUnify.preconditioned

/--
One-hop projection: successful-run field preconditioned↔core equivalence
from combined no-unify principal capstone slices.
-/
theorem principalBoundaryNoUnifyCapstoneSlices_field_preconditionedCoreIff
    (h_slice : PrincipalBoundaryNoUnifyCapstoneSlices)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)))
    (h_hooks : UnifyHookPremises) :
    (PrincipalFieldTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env fs st' rf
      ↔ PrincipalFieldTypingSliceCore env fs rf) :=
  (principalBoundaryNoUnifyCapstoneSlices_field
    h_slice h_no h_ok h_hooks).preconditionedCoreIff

/--
Transport preconditioned expression principality across hook witnesses on the
same successful `inferExprUnify` run.
-/
theorem principalTypingSlicePreconditioned_transport_hooks_of_success
    {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
    {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook}
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty)
    (h_pre : PrincipalTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env e st' ty) :
    PrincipalTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env e st' ty := by
  have h_core : PrincipalTypingSliceCore env e ty :=
    (principalTypingSlicePreconditioned_iff_core_of_success
      h_app₁ h_proj₁ st fuel env e st' ty h_ok).1 h_pre
  exact (principalTypingSlicePreconditioned_iff_core_of_success
      h_app₂ h_proj₂ st fuel env e st' ty h_ok).2 h_core

/--
Hook irrelevance (expression): on a fixed successful `inferExprUnify` run,
preconditioned principality is independent of which hook witnesses are used.
-/
theorem principalTypingSlicePreconditioned_hook_irrelevant_of_success
    {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
    {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook}
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    (PrincipalTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env e st' ty
      ↔ PrincipalTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env e st' ty) := by
  constructor
  · intro h_pre
    exact principalTypingSlicePreconditioned_transport_hooks_of_success h_ok h_pre
  · intro h_pre
    exact principalTypingSlicePreconditioned_transport_hooks_of_success h_ok h_pre

/--
Transport preconditioned field principality across hook witnesses on the same
successful `inferFieldsUnify` run.
-/
theorem principalFieldTypingSlicePreconditioned_transport_hooks_of_success
    {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
    {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook}
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)))
    (h_pre : PrincipalFieldTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env fs st' rf) :
    PrincipalFieldTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env fs st' rf := by
  have h_core : PrincipalFieldTypingSliceCore env fs rf :=
    (principalFieldTypingSlicePreconditioned_iff_core_of_success
      h_app₁ h_proj₁ st fuel env fs st' rf h_ok).1 h_pre
  exact (principalFieldTypingSlicePreconditioned_iff_core_of_success
      h_app₂ h_proj₂ st fuel env fs st' rf h_ok).2 h_core

/--
Hook irrelevance (field): on a fixed successful `inferFieldsUnify` run,
preconditioned field principality is independent of hook witnesses.
-/
theorem principalFieldTypingSlicePreconditioned_hook_irrelevant_of_success
    {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
    {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook}
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    (PrincipalFieldTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env fs st' rf
      ↔ PrincipalFieldTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env fs st' rf) := by
  constructor
  · intro h_pre
    exact principalFieldTypingSlicePreconditioned_transport_hooks_of_success h_ok h_pre
  · intro h_pre
    exact principalFieldTypingSlicePreconditioned_transport_hooks_of_success h_ok h_pre

/--
Packaged hook-irrelevance slice for expression principality on successful runs.
-/
def PrincipalPreconditionedHookIrrelevanceExprSlice : Prop :=
  ∀ {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
    {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook}
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty},
    inferExprUnify st fuel env e = .ok st' ty →
    (PrincipalTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env e st' ty
      ↔ PrincipalTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env e st' ty)

/--
Packaged hook-irrelevance slice for field principality on successful runs.
-/
def PrincipalPreconditionedHookIrrelevanceFieldSlice : Prop :=
  ∀ {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
    {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook}
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields},
    inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)) →
    (PrincipalFieldTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env fs st' rf
      ↔ PrincipalFieldTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env fs st' rf)

/-- Combined preconditioned-hook-irrelevance principal slice across expressions and fields. -/
def PrincipalPreconditionedHookIrrelevanceSlices : Prop :=
  PrincipalPreconditionedHookIrrelevanceExprSlice ∧
    PrincipalPreconditionedHookIrrelevanceFieldSlice

/-- The combined preconditioned-hook-irrelevance principal slice is fully proved. -/
theorem principalPreconditionedHookIrrelevanceSlices_proved :
    PrincipalPreconditionedHookIrrelevanceSlices := by
  refine ⟨?_, ?_⟩
  · intro h_app₁ h_proj₁ h_app₂ h_proj₂ st fuel env e st' ty h_ok
    exact principalTypingSlicePreconditioned_hook_irrelevant_of_success h_ok
  · intro h_app₁ h_proj₁ h_app₂ h_proj₂ st fuel env fs st' rf h_ok
    exact principalFieldTypingSlicePreconditioned_hook_irrelevant_of_success h_ok

/--
One-hop projection: expression branch from the combined preconditioned
hook-irrelevance principal slice.
-/
theorem principalPreconditionedHookIrrelevanceSlices_expr
    (h_slice : PrincipalPreconditionedHookIrrelevanceSlices)
    {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
    {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook}
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    (PrincipalTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env e st' ty
      ↔ PrincipalTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env e st' ty) :=
  h_slice.1 h_ok

/--
One-hop projection: field branch from the combined preconditioned
hook-irrelevance principal slice.
-/
theorem principalPreconditionedHookIrrelevanceSlices_field
    (h_slice : PrincipalPreconditionedHookIrrelevanceSlices)
    {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
    {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook}
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    (PrincipalFieldTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env fs st' rf
      ↔ PrincipalFieldTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env fs st' rf) :=
  h_slice.2 h_ok

/--
General successful-run all-hooks expression capstone.

Unlike the no-unify all-hooks capstone, this applies to arbitrary successful
`inferExprUnify` runs and is constructed from one hook witness pair.
-/
structure PrincipalPreconditionedExprAllHooksCapstone
    (st : UnifyState) (fuel : Nat) (env : TermEnv) (e : CoreExpr)
    (st' : UnifyState) (ty : Ty) : Prop where
  core : PrincipalTypingSliceCore env e ty
  preconditionedAny :
    ∀ h_app h_proj, PrincipalTypingSlicePreconditioned h_app h_proj st fuel env e st' ty
  preconditionedAnyIffCore :
    ∀ h_app h_proj,
      (PrincipalTypingSlicePreconditioned h_app h_proj st fuel env e st' ty
        ↔ PrincipalTypingSliceCore env e ty)

/--
Construct the general successful-run all-hooks expression capstone from one
hook witness pair.
-/
theorem principalPreconditionedExprAllHooksCapstone_of_success
    (h_app0 : AppUnifySoundHook)
    (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalPreconditionedExprAllHooksCapstone st fuel env e st' ty := by
  have h_pre0 :
      PrincipalTypingSlicePreconditioned h_app0 h_proj0 st fuel env e st' ty :=
    principalTypingSlicePreconditioned_of_success h_app0 h_proj0 st fuel env e st' ty h_ok
  have h_core : PrincipalTypingSliceCore env e ty :=
    (principalTypingSlicePreconditioned_iff_core_of_success
      h_app0 h_proj0 st fuel env e st' ty h_ok).1 h_pre0
  refine {
    core := h_core
    preconditionedAny := ?_
    preconditionedAnyIffCore := ?_
  }
  · intro h_app h_proj
    exact (principalTypingSlicePreconditioned_iff_core_of_success
      h_app h_proj st fuel env e st' ty h_ok).2 h_core
  · intro h_app h_proj
    exact principalTypingSlicePreconditioned_iff_core_of_success
      h_app h_proj st fuel env e st' ty h_ok

/--
General successful-run all-hooks field capstone.

Field-side analogue of `PrincipalPreconditionedExprAllHooksCapstone`.
-/
structure PrincipalPreconditionedFieldAllHooksCapstone
    (st : UnifyState) (fuel : Nat) (env : TermEnv) (fs : CoreFields)
    (st' : UnifyState) (rf : RowFields) : Prop where
  core : PrincipalFieldTypingSliceCore env fs rf
  preconditionedAny :
    ∀ h_app h_proj,
      PrincipalFieldTypingSlicePreconditioned h_app h_proj st fuel env fs st' rf
  preconditionedAnyIffCore :
    ∀ h_app h_proj,
      (PrincipalFieldTypingSlicePreconditioned h_app h_proj st fuel env fs st' rf
        ↔ PrincipalFieldTypingSliceCore env fs rf)

/--
Construct the general successful-run all-hooks field capstone from one hook
witness pair.
-/
theorem principalPreconditionedFieldAllHooksCapstone_of_success
    (h_app0 : AppUnifySoundHook)
    (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalPreconditionedFieldAllHooksCapstone st fuel env fs st' rf := by
  have h_pre0 :
      PrincipalFieldTypingSlicePreconditioned h_app0 h_proj0 st fuel env fs st' rf :=
    principalFieldTypingSlicePreconditioned_of_success
      h_app0 h_proj0 st fuel env fs st' rf h_ok
  have h_core : PrincipalFieldTypingSliceCore env fs rf :=
    (principalFieldTypingSlicePreconditioned_iff_core_of_success
      h_app0 h_proj0 st fuel env fs st' rf h_ok).1 h_pre0
  refine {
    core := h_core
    preconditionedAny := ?_
    preconditionedAnyIffCore := ?_
  }
  · intro h_app h_proj
    exact (principalFieldTypingSlicePreconditioned_iff_core_of_success
      h_app h_proj st fuel env fs st' rf h_ok).2 h_core
  · intro h_app h_proj
    exact principalFieldTypingSlicePreconditioned_iff_core_of_success
      h_app h_proj st fuel env fs st' rf h_ok

/-- Packaged general all-hooks expression capstone slice over successful runs. -/
def PrincipalPreconditionedAllHooksExprCapstoneSlice : Prop :=
  ∀ (_h_app0 : AppUnifySoundHook) (_h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty},
    inferExprUnify st fuel env e = .ok st' ty →
    PrincipalPreconditionedExprAllHooksCapstone st fuel env e st' ty

/-- Packaged general all-hooks field capstone slice over successful runs. -/
def PrincipalPreconditionedAllHooksFieldCapstoneSlice : Prop :=
  ∀ (_h_app0 : AppUnifySoundHook) (_h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields},
    inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)) →
    PrincipalPreconditionedFieldAllHooksCapstone st fuel env fs st' rf

/-- Combined general all-hooks capstone slices across expressions and fields. -/
def PrincipalPreconditionedAllHooksCapstoneSlices : Prop :=
  PrincipalPreconditionedAllHooksExprCapstoneSlice ∧
    PrincipalPreconditionedAllHooksFieldCapstoneSlice

/-- The combined general all-hooks capstone slices are fully proved. -/
theorem principalPreconditionedAllHooksCapstoneSlices_proved :
    PrincipalPreconditionedAllHooksCapstoneSlices := by
  refine ⟨?_, ?_⟩
  · intro h_app0 h_proj0 st fuel env e st' ty h_ok
    exact principalPreconditionedExprAllHooksCapstone_of_success
      h_app0 h_proj0 h_ok
  · intro h_app0 h_proj0 st fuel env fs st' rf h_ok
    exact principalPreconditionedFieldAllHooksCapstone_of_success
      h_app0 h_proj0 h_ok

/-- One-hop expression branch projection from general all-hooks capstone slices. -/
theorem principalPreconditionedAllHooksCapstoneSlices_expr
    (h_slice : PrincipalPreconditionedAllHooksCapstoneSlices)
    (h_app0 : AppUnifySoundHook) (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalPreconditionedExprAllHooksCapstone st fuel env e st' ty :=
  h_slice.1 h_app0 h_proj0 h_ok

/-- One-hop field branch projection from general all-hooks capstone slices. -/
theorem principalPreconditionedAllHooksCapstoneSlices_field
    (h_slice : PrincipalPreconditionedAllHooksCapstoneSlices)
    (h_app0 : AppUnifySoundHook) (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalPreconditionedFieldAllHooksCapstone st fuel env fs st' rf :=
  h_slice.2 h_app0 h_proj0 h_ok

/--
Coherence (general all-hooks expression capstone): any two hook witnesses yield
equivalent preconditioned principality on the same successful run.
-/
theorem principalPreconditionedExprAllHooksCapstone_hook_irrelevant
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_cap : PrincipalPreconditionedExprAllHooksCapstone st fuel env e st' ty)
    {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
    {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook} :
    (PrincipalTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env e st' ty
      ↔ PrincipalTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env e st' ty) := by
  constructor
  · intro h_pre
    have h_core : PrincipalTypingSliceCore env e ty :=
      (h_cap.preconditionedAnyIffCore h_app₁ h_proj₁).1 h_pre
    exact (h_cap.preconditionedAnyIffCore h_app₂ h_proj₂).2 h_core
  · intro h_pre
    have h_core : PrincipalTypingSliceCore env e ty :=
      (h_cap.preconditionedAnyIffCore h_app₂ h_proj₂).1 h_pre
    exact (h_cap.preconditionedAnyIffCore h_app₁ h_proj₁).2 h_core

/--
Coherence (general all-hooks field capstone): any two hook witnesses yield
equivalent preconditioned field principality on the same successful run.
-/
theorem principalPreconditionedFieldAllHooksCapstone_hook_irrelevant
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_cap : PrincipalPreconditionedFieldAllHooksCapstone st fuel env fs st' rf)
    {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
    {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook} :
    (PrincipalFieldTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env fs st' rf
      ↔ PrincipalFieldTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env fs st' rf) := by
  constructor
  · intro h_pre
    have h_core : PrincipalFieldTypingSliceCore env fs rf :=
      (h_cap.preconditionedAnyIffCore h_app₁ h_proj₁).1 h_pre
    exact (h_cap.preconditionedAnyIffCore h_app₂ h_proj₂).2 h_core
  · intro h_pre
    have h_core : PrincipalFieldTypingSliceCore env fs rf :=
      (h_cap.preconditionedAnyIffCore h_app₂ h_proj₂).1 h_pre
    exact (h_cap.preconditionedAnyIffCore h_app₁ h_proj₁).2 h_core

/--
Run-level expression bundle for arbitrary successful all-hooks principality.

This packages:
- the full all-hooks capstone consequences, and
- fixed-run preconditioned hook-irrelevance.
-/
structure PrincipalPreconditionedExprAllHooksRunBundle
    (st : UnifyState) (fuel : Nat) (env : TermEnv) (e : CoreExpr)
    (st' : UnifyState) (ty : Ty) : Prop where
  capstone : PrincipalPreconditionedExprAllHooksCapstone st fuel env e st' ty
  hookIrrelevant :
    ∀ {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
      {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook},
      (PrincipalTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env e st' ty
        ↔ PrincipalTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env e st' ty)

/--
Run-level field bundle for arbitrary successful all-hooks principality.

Field-side analogue of `PrincipalPreconditionedExprAllHooksRunBundle`.
-/
structure PrincipalPreconditionedFieldAllHooksRunBundle
    (st : UnifyState) (fuel : Nat) (env : TermEnv) (fs : CoreFields)
    (st' : UnifyState) (rf : RowFields) : Prop where
  capstone : PrincipalPreconditionedFieldAllHooksCapstone st fuel env fs st' rf
  hookIrrelevant :
    ∀ {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
      {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook},
      (PrincipalFieldTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env fs st' rf
        ↔ PrincipalFieldTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env fs st' rf)

/--
Construct an expression run-level all-hooks bundle from an existing capstone.
-/
theorem principalPreconditionedExprAllHooksRunBundle_of_capstone
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_cap : PrincipalPreconditionedExprAllHooksCapstone st fuel env e st' ty) :
    PrincipalPreconditionedExprAllHooksRunBundle st fuel env e st' ty := by
  refine {
    capstone := h_cap
    hookIrrelevant := ?_
  }
  intro h_app₁ h_proj₁ h_app₂ h_proj₂
  exact principalPreconditionedExprAllHooksCapstone_hook_irrelevant
    h_cap

/--
Construct a field run-level all-hooks bundle from an existing capstone.
-/
theorem principalPreconditionedFieldAllHooksRunBundle_of_capstone
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_cap : PrincipalPreconditionedFieldAllHooksCapstone st fuel env fs st' rf) :
    PrincipalPreconditionedFieldAllHooksRunBundle st fuel env fs st' rf := by
  refine {
    capstone := h_cap
    hookIrrelevant := ?_
  }
  intro h_app₁ h_proj₁ h_app₂ h_proj₂
  exact principalPreconditionedFieldAllHooksCapstone_hook_irrelevant
    h_cap

/--
Construct an expression run-level all-hooks bundle from one successful run and
one baseline hook pair.
-/
theorem principalPreconditionedExprAllHooksRunBundle_of_success
    (h_app0 : AppUnifySoundHook)
    (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalPreconditionedExprAllHooksRunBundle st fuel env e st' ty := by
  exact principalPreconditionedExprAllHooksRunBundle_of_capstone
    (principalPreconditionedExprAllHooksCapstone_of_success h_app0 h_proj0 h_ok)

/--
Construct a field run-level all-hooks bundle from one successful field run and
one baseline hook pair.
-/
theorem principalPreconditionedFieldAllHooksRunBundle_of_success
    (h_app0 : AppUnifySoundHook)
    (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalPreconditionedFieldAllHooksRunBundle st fuel env fs st' rf := by
  exact principalPreconditionedFieldAllHooksRunBundle_of_capstone
    (principalPreconditionedFieldAllHooksCapstone_of_success h_app0 h_proj0 h_ok)

/--
Bundle-entry variant of `principalPreconditionedExprAllHooksRunBundle_of_success`.
-/
theorem principalPreconditionedExprAllHooksRunBundle_of_success_from_bundle
    (h_seed : UnifyHookPremises)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalPreconditionedExprAllHooksRunBundle st fuel env e st' ty := by
  exact principalPreconditionedExprAllHooksRunBundle_of_success
    h_seed.1 h_seed.2 h_ok

/--
Bundle-entry variant of `principalPreconditionedFieldAllHooksRunBundle_of_success`.
-/
theorem principalPreconditionedFieldAllHooksRunBundle_of_success_from_bundle
    (h_seed : UnifyHookPremises)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalPreconditionedFieldAllHooksRunBundle st fuel env fs st' rf := by
  exact principalPreconditionedFieldAllHooksRunBundle_of_success
    h_seed.1 h_seed.2 h_ok

/--
Packaged arbitrary-success expression run-bundle slice for all-hooks principality.
-/
def PrincipalPreconditionedAllHooksRunBundleExprSlice : Prop :=
  ∀ (_h_app0 : AppUnifySoundHook) (_h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty},
    inferExprUnify st fuel env e = .ok st' ty →
    PrincipalPreconditionedExprAllHooksRunBundle st fuel env e st' ty

/--
Packaged arbitrary-success field run-bundle slice for all-hooks principality.
-/
def PrincipalPreconditionedAllHooksRunBundleFieldSlice : Prop :=
  ∀ (_h_app0 : AppUnifySoundHook) (_h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields},
    inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)) →
    PrincipalPreconditionedFieldAllHooksRunBundle st fuel env fs st' rf

/--
Combined arbitrary-success run-bundle slices across expressions and fields.
-/
def PrincipalPreconditionedAllHooksRunBundleSlices : Prop :=
  PrincipalPreconditionedAllHooksRunBundleExprSlice ∧
    PrincipalPreconditionedAllHooksRunBundleFieldSlice

/--
The combined arbitrary-success run-bundle slices are fully proved.
-/
theorem principalPreconditionedAllHooksRunBundleSlices_proved :
    PrincipalPreconditionedAllHooksRunBundleSlices := by
  refine ⟨?_, ?_⟩
  · intro h_app0 h_proj0 st fuel env e st' ty h_ok
    exact principalPreconditionedExprAllHooksRunBundle_of_success
      h_app0 h_proj0 h_ok
  · intro h_app0 h_proj0 st fuel env fs st' rf h_ok
    exact principalPreconditionedFieldAllHooksRunBundle_of_success
      h_app0 h_proj0 h_ok

/--
One-hop expression projection from combined arbitrary-success run-bundle slices.
-/
theorem principalPreconditionedAllHooksRunBundleSlices_expr
    (h_slice : PrincipalPreconditionedAllHooksRunBundleSlices)
    (h_app0 : AppUnifySoundHook) (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalPreconditionedExprAllHooksRunBundle st fuel env e st' ty :=
  h_slice.1 h_app0 h_proj0 h_ok

/--
One-hop field projection from combined arbitrary-success run-bundle slices.
-/
theorem principalPreconditionedAllHooksRunBundleSlices_field
    (h_slice : PrincipalPreconditionedAllHooksRunBundleSlices)
    (h_app0 : AppUnifySoundHook) (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalPreconditionedFieldAllHooksRunBundle st fuel env fs st' rf :=
  h_slice.2 h_app0 h_proj0 h_ok

/--
Derive the global preconditioned hook-irrelevance slices directly from general
all-hooks capstone slices.
-/
theorem principalPreconditionedHookIrrelevanceSlices_of_allHooksCapstones
    (h_caps : PrincipalPreconditionedAllHooksCapstoneSlices) :
    PrincipalPreconditionedHookIrrelevanceSlices := by
  refine ⟨?_, ?_⟩
  · intro h_app₁ h_proj₁ h_app₂ h_proj₂ st fuel env e st' ty h_ok
    exact principalPreconditionedExprAllHooksCapstone_hook_irrelevant
      (principalPreconditionedAllHooksCapstoneSlices_expr
        h_caps h_app₁ h_proj₁ h_ok)
  · intro h_app₁ h_proj₁ h_app₂ h_proj₂ st fuel env fs st' rf h_ok
    exact principalPreconditionedFieldAllHooksCapstone_hook_irrelevant
      (principalPreconditionedAllHooksCapstoneSlices_field
        h_caps h_app₁ h_proj₁ h_ok)

/--
Top-level suite for the general all-hooks successful-run layer.
-/
structure PrincipalPreconditionedAllHooksSuite : Prop where
  capstones : PrincipalPreconditionedAllHooksCapstoneSlices
  irrelevance : PrincipalPreconditionedHookIrrelevanceSlices
  runBundles : PrincipalPreconditionedAllHooksRunBundleSlices

/-- The general all-hooks successful-run suite is fully proved. -/
theorem principalPreconditionedAllHooksSuite_proved :
    PrincipalPreconditionedAllHooksSuite := by
  refine {
    capstones := principalPreconditionedAllHooksCapstoneSlices_proved
    irrelevance := principalPreconditionedHookIrrelevanceSlices_of_allHooksCapstones
      principalPreconditionedAllHooksCapstoneSlices_proved
    runBundles := principalPreconditionedAllHooksRunBundleSlices_proved
  }

/-- One-hop expression capstone projection from general all-hooks suite. -/
theorem principalPreconditionedAllHooksSuite_capstone_expr
    (h_suite : PrincipalPreconditionedAllHooksSuite)
    (h_app0 : AppUnifySoundHook) (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalPreconditionedExprAllHooksCapstone st fuel env e st' ty :=
  principalPreconditionedAllHooksCapstoneSlices_expr
    h_suite.capstones h_app0 h_proj0 h_ok

/-- One-hop field capstone projection from general all-hooks suite. -/
theorem principalPreconditionedAllHooksSuite_capstone_field
    (h_suite : PrincipalPreconditionedAllHooksSuite)
    (h_app0 : AppUnifySoundHook) (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalPreconditionedFieldAllHooksCapstone st fuel env fs st' rf :=
  principalPreconditionedAllHooksCapstoneSlices_field
    h_suite.capstones h_app0 h_proj0 h_ok

/-- One-hop expression irrelevance projection from general all-hooks suite. -/
theorem principalPreconditionedAllHooksSuite_irrelevance_expr
    (h_suite : PrincipalPreconditionedAllHooksSuite)
    {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
    {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook}
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    (PrincipalTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env e st' ty
      ↔ PrincipalTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env e st' ty) :=
  principalPreconditionedHookIrrelevanceSlices_expr h_suite.irrelevance h_ok

/-- One-hop field irrelevance projection from general all-hooks suite. -/
theorem principalPreconditionedAllHooksSuite_irrelevance_field
    (h_suite : PrincipalPreconditionedAllHooksSuite)
    {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
    {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook}
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    (PrincipalFieldTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env fs st' rf
      ↔ PrincipalFieldTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env fs st' rf) :=
  principalPreconditionedHookIrrelevanceSlices_field h_suite.irrelevance h_ok

/-- One-hop expression run-bundle projection from general all-hooks suite. -/
theorem principalPreconditionedAllHooksSuite_runBundle_expr
    (h_suite : PrincipalPreconditionedAllHooksSuite)
    (h_app0 : AppUnifySoundHook) (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalPreconditionedExprAllHooksRunBundle st fuel env e st' ty :=
  principalPreconditionedAllHooksRunBundleSlices_expr
    h_suite.runBundles h_app0 h_proj0 h_ok

/-- One-hop field run-bundle projection from general all-hooks suite. -/
theorem principalPreconditionedAllHooksSuite_runBundle_field
    (h_suite : PrincipalPreconditionedAllHooksSuite)
    (h_app0 : AppUnifySoundHook) (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalPreconditionedFieldAllHooksRunBundle st fuel env fs st' rf :=
  principalPreconditionedAllHooksRunBundleSlices_field
    h_suite.runBundles h_app0 h_proj0 h_ok

/--
General-all-hooks suite convenience wrapper: derive the expression run-bundle
surface from an arbitrary successful run.
-/
theorem principalGeneralAllHooksRunBundleExpr_of_success
    (h_suite : PrincipalPreconditionedAllHooksSuite)
    (h_app0 : AppUnifySoundHook)
    (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalPreconditionedExprAllHooksRunBundle st fuel env e st' ty :=
  principalPreconditionedAllHooksSuite_runBundle_expr
    h_suite h_app0 h_proj0 h_ok

/--
General-all-hooks suite convenience wrapper: derive the field run-bundle
surface from an arbitrary successful field run.
-/
theorem principalGeneralAllHooksRunBundleField_of_success
    (h_suite : PrincipalPreconditionedAllHooksSuite)
    (h_app0 : AppUnifySoundHook)
    (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalPreconditionedFieldAllHooksRunBundle st fuel env fs st' rf :=
  principalPreconditionedAllHooksSuite_runBundle_field
    h_suite h_app0 h_proj0 h_ok

/--
General-all-hooks suite convenience wrapper: derive core expression principality
from an arbitrary successful run.
-/
theorem principalGeneralAllHooksCoreExpr_of_success
    (h_suite : PrincipalPreconditionedAllHooksSuite)
    (h_app0 : AppUnifySoundHook)
    (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalTypingSliceCore env e ty :=
  (principalPreconditionedAllHooksSuite_capstone_expr
    h_suite h_app0 h_proj0 h_ok).core

/--
General-all-hooks suite convenience wrapper: derive preconditioned expression
principality for any hook witnesses from an arbitrary successful run.
-/
theorem principalGeneralAllHooksPreconditionedExpr_anyHooks_of_success
    (h_suite : PrincipalPreconditionedAllHooksSuite)
    (h_app0 : AppUnifySoundHook)
    (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    ∀ h_app h_proj,
      PrincipalTypingSlicePreconditioned h_app h_proj st fuel env e st' ty :=
  (principalPreconditionedAllHooksSuite_capstone_expr
    h_suite h_app0 h_proj0 h_ok).preconditionedAny

/--
General-all-hooks suite convenience wrapper: derive preconditioned expression
principality for a bundled hook witness from an arbitrary successful run.
-/
theorem principalGeneralAllHooksPreconditionedExpr_of_success
    (h_suite : PrincipalPreconditionedAllHooksSuite)
    (h_app0 : AppUnifySoundHook)
    (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty)
    (h_hooks : UnifyHookPremises) :
    PrincipalTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env e st' ty :=
  (principalGeneralAllHooksPreconditionedExpr_anyHooks_of_success
    h_suite h_app0 h_proj0 h_ok) h_hooks.1 h_hooks.2

/--
General-all-hooks suite convenience wrapper: derive fixed-run expression
preconditioned↔core equivalence for any hook witnesses.
-/
theorem principalGeneralAllHooksPreconditionedCoreIffExpr_anyHooks_of_success
    (h_suite : PrincipalPreconditionedAllHooksSuite)
    (h_app0 : AppUnifySoundHook)
    (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    ∀ h_app h_proj,
      (PrincipalTypingSlicePreconditioned h_app h_proj st fuel env e st' ty
        ↔ PrincipalTypingSliceCore env e ty) :=
  (principalPreconditionedAllHooksSuite_capstone_expr
    h_suite h_app0 h_proj0 h_ok).preconditionedAnyIffCore

/--
General-all-hooks suite convenience wrapper: derive fixed-run expression
preconditioned↔core equivalence for a bundled hook witness.
-/
theorem principalGeneralAllHooksPreconditionedCoreIffExpr_of_success
    (h_suite : PrincipalPreconditionedAllHooksSuite)
    (h_app0 : AppUnifySoundHook)
    (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty)
    (h_hooks : UnifyHookPremises) :
    (PrincipalTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env e st' ty
      ↔ PrincipalTypingSliceCore env e ty) :=
  (principalGeneralAllHooksPreconditionedCoreIffExpr_anyHooks_of_success
    h_suite h_app0 h_proj0 h_ok) h_hooks.1 h_hooks.2

/--
General-all-hooks suite convenience wrapper: derive fixed-run expression
hook-irrelevance from an arbitrary successful run.
-/
theorem principalGeneralAllHooksPreconditionedExpr_hookIrrelevant_of_success
    (h_suite : PrincipalPreconditionedAllHooksSuite)
    {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
    {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook}
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    (PrincipalTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env e st' ty
      ↔ PrincipalTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env e st' ty) :=
  principalPreconditionedAllHooksSuite_irrelevance_expr h_suite h_ok

/--
General-all-hooks suite convenience wrapper: derive core field principality
from an arbitrary successful field run.
-/
theorem principalGeneralAllHooksCoreField_of_success
    (h_suite : PrincipalPreconditionedAllHooksSuite)
    (h_app0 : AppUnifySoundHook)
    (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalFieldTypingSliceCore env fs rf :=
  (principalPreconditionedAllHooksSuite_capstone_field
    h_suite h_app0 h_proj0 h_ok).core

/--
General-all-hooks suite convenience wrapper: derive preconditioned field
principality for any hook witnesses from an arbitrary successful field run.
-/
theorem principalGeneralAllHooksPreconditionedField_anyHooks_of_success
    (h_suite : PrincipalPreconditionedAllHooksSuite)
    (h_app0 : AppUnifySoundHook)
    (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    ∀ h_app h_proj,
      PrincipalFieldTypingSlicePreconditioned h_app h_proj st fuel env fs st' rf :=
  (principalPreconditionedAllHooksSuite_capstone_field
    h_suite h_app0 h_proj0 h_ok).preconditionedAny

/--
General-all-hooks suite convenience wrapper: derive preconditioned field
principality for a bundled hook witness from an arbitrary successful field run.
-/
theorem principalGeneralAllHooksPreconditionedField_of_success
    (h_suite : PrincipalPreconditionedAllHooksSuite)
    (h_app0 : AppUnifySoundHook)
    (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)))
    (h_hooks : UnifyHookPremises) :
    PrincipalFieldTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env fs st' rf :=
  (principalGeneralAllHooksPreconditionedField_anyHooks_of_success
    h_suite h_app0 h_proj0 h_ok) h_hooks.1 h_hooks.2

/--
General-all-hooks suite convenience wrapper: derive fixed-run field
preconditioned↔core equivalence for any hook witnesses.
-/
theorem principalGeneralAllHooksPreconditionedCoreIffField_anyHooks_of_success
    (h_suite : PrincipalPreconditionedAllHooksSuite)
    (h_app0 : AppUnifySoundHook)
    (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    ∀ h_app h_proj,
      (PrincipalFieldTypingSlicePreconditioned h_app h_proj st fuel env fs st' rf
        ↔ PrincipalFieldTypingSliceCore env fs rf) :=
  (principalPreconditionedAllHooksSuite_capstone_field
    h_suite h_app0 h_proj0 h_ok).preconditionedAnyIffCore

/--
General-all-hooks suite convenience wrapper: derive fixed-run field
preconditioned↔core equivalence for a bundled hook witness.
-/
theorem principalGeneralAllHooksPreconditionedCoreIffField_of_success
    (h_suite : PrincipalPreconditionedAllHooksSuite)
    (h_app0 : AppUnifySoundHook)
    (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)))
    (h_hooks : UnifyHookPremises) :
    (PrincipalFieldTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env fs st' rf
      ↔ PrincipalFieldTypingSliceCore env fs rf) :=
  (principalGeneralAllHooksPreconditionedCoreIffField_anyHooks_of_success
    h_suite h_app0 h_proj0 h_ok) h_hooks.1 h_hooks.2

/--
General-all-hooks suite convenience wrapper: derive fixed-run field
hook-irrelevance from an arbitrary successful field run.
-/
theorem principalGeneralAllHooksPreconditionedField_hookIrrelevant_of_success
    (h_suite : PrincipalPreconditionedAllHooksSuite)
    {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
    {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook}
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    (PrincipalFieldTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env fs st' rf
      ↔ PrincipalFieldTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env fs st' rf) :=
  principalPreconditionedAllHooksSuite_irrelevance_field h_suite h_ok

/--
General-all-hooks-suite capstone wrapper: package the full expression
successful-run all-hooks principal boundary from one successful run and one
baseline hook witness pair.
-/
theorem principalPreconditionedExprAllHooksCapstone_of_success_via_generalAllHooksSuite
    (h_app0 : AppUnifySoundHook)
    (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalPreconditionedExprAllHooksCapstone st fuel env e st' ty :=
  principalPreconditionedAllHooksSuite_capstone_expr
    principalPreconditionedAllHooksSuite_proved h_app0 h_proj0 h_ok

/--
General-all-hooks-suite capstone wrapper: package the full field successful-run
all-hooks principal boundary from one successful field run and one baseline hook
witness pair.
-/
theorem principalPreconditionedFieldAllHooksCapstone_of_success_via_generalAllHooksSuite
    (h_app0 : AppUnifySoundHook)
    (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalPreconditionedFieldAllHooksCapstone st fuel env fs st' rf :=
  principalPreconditionedAllHooksSuite_capstone_field
    principalPreconditionedAllHooksSuite_proved h_app0 h_proj0 h_ok

/--
General-all-hooks-suite capstone wrapper: bundled-hook variant for expression
successful-run all-hooks principal boundary packaging.
-/
theorem principalPreconditionedExprAllHooksCapstone_of_success_via_generalAllHooksSuite_from_bundle
    (h_seed : UnifyHookPremises)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalPreconditionedExprAllHooksCapstone st fuel env e st' ty :=
  principalPreconditionedExprAllHooksCapstone_of_success_via_generalAllHooksSuite
    h_seed.1 h_seed.2 h_ok

/--
General-all-hooks-suite capstone wrapper: bundled-hook variant for field
successful-run all-hooks principal boundary packaging.
-/
theorem principalPreconditionedFieldAllHooksCapstone_of_success_via_generalAllHooksSuite_from_bundle
    (h_seed : UnifyHookPremises)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalPreconditionedFieldAllHooksCapstone st fuel env fs st' rf :=
  principalPreconditionedFieldAllHooksCapstone_of_success_via_generalAllHooksSuite
    h_seed.1 h_seed.2 h_ok

/--
General-all-hooks-suite run-bundle wrapper: package capstone + hook-irrelevance
for expression successful runs from one baseline hook witness pair.
-/
theorem principalPreconditionedExprAllHooksRunBundle_of_success_via_generalAllHooksSuite
    (h_app0 : AppUnifySoundHook)
    (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalPreconditionedExprAllHooksRunBundle st fuel env e st' ty :=
  principalGeneralAllHooksRunBundleExpr_of_success
    principalPreconditionedAllHooksSuite_proved h_app0 h_proj0 h_ok

/--
General-all-hooks-suite run-bundle wrapper: package capstone + hook-irrelevance
for successful field runs from one baseline hook witness pair.
-/
theorem principalPreconditionedFieldAllHooksRunBundle_of_success_via_generalAllHooksSuite
    (h_app0 : AppUnifySoundHook)
    (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalPreconditionedFieldAllHooksRunBundle st fuel env fs st' rf :=
  principalGeneralAllHooksRunBundleField_of_success
    principalPreconditionedAllHooksSuite_proved h_app0 h_proj0 h_ok

/--
Bundle-entry variant of
`principalPreconditionedExprAllHooksRunBundle_of_success_via_generalAllHooksSuite`.
-/
theorem principalPreconditionedExprAllHooksRunBundle_of_success_via_generalAllHooksSuite_from_bundle
    (h_seed : UnifyHookPremises)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalPreconditionedExprAllHooksRunBundle st fuel env e st' ty :=
  principalPreconditionedExprAllHooksRunBundle_of_success_via_generalAllHooksSuite
    h_seed.1 h_seed.2 h_ok

/--
Bundle-entry variant of
`principalPreconditionedFieldAllHooksRunBundle_of_success_via_generalAllHooksSuite`.
-/
theorem principalPreconditionedFieldAllHooksRunBundle_of_success_via_generalAllHooksSuite_from_bundle
    (h_seed : UnifyHookPremises)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalPreconditionedFieldAllHooksRunBundle st fuel env fs st' rf :=
  principalPreconditionedFieldAllHooksRunBundle_of_success_via_generalAllHooksSuite
    h_seed.1 h_seed.2 h_ok

/--
General-all-hooks-suite convenience wrapper: derive core expression principality
from an arbitrary successful `inferExprUnify` run.
-/
theorem principalCoreExpr_of_success_via_generalAllHooksSuite
    (h_app0 : AppUnifySoundHook)
    (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalTypingSliceCore env e ty :=
  principalGeneralAllHooksCoreExpr_of_success
    principalPreconditionedAllHooksSuite_proved h_app0 h_proj0 h_ok

/--
General-all-hooks-suite convenience wrapper: derive preconditioned expression
principality for any hook witnesses from an arbitrary successful run.
-/
theorem principalPreconditionedExpr_anyHooks_of_success_via_generalAllHooksSuite
    (h_app0 : AppUnifySoundHook)
    (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    ∀ h_app h_proj,
      PrincipalTypingSlicePreconditioned h_app h_proj st fuel env e st' ty :=
  principalGeneralAllHooksPreconditionedExpr_anyHooks_of_success
    principalPreconditionedAllHooksSuite_proved h_app0 h_proj0 h_ok

/--
General-all-hooks-suite convenience wrapper: derive preconditioned expression
principality for a bundled hook witness from an arbitrary successful run.
-/
theorem principalPreconditionedExpr_of_success_via_generalAllHooksSuite
    (h_app0 : AppUnifySoundHook)
    (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty)
    (h_hooks : UnifyHookPremises) :
    PrincipalTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env e st' ty :=
  principalGeneralAllHooksPreconditionedExpr_of_success
    principalPreconditionedAllHooksSuite_proved h_app0 h_proj0 h_ok h_hooks

/--
General-all-hooks-suite convenience wrapper: derive fixed-run expression
preconditioned↔core equivalence for any hook witnesses.
-/
theorem principalPreconditionedCoreIffExpr_anyHooks_of_success_via_generalAllHooksSuite
    (h_app0 : AppUnifySoundHook)
    (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    ∀ h_app h_proj,
      (PrincipalTypingSlicePreconditioned h_app h_proj st fuel env e st' ty
        ↔ PrincipalTypingSliceCore env e ty) :=
  principalGeneralAllHooksPreconditionedCoreIffExpr_anyHooks_of_success
    principalPreconditionedAllHooksSuite_proved h_app0 h_proj0 h_ok

/--
General-all-hooks-suite convenience wrapper: derive fixed-run expression
preconditioned↔core equivalence for a bundled hook witness.
-/
theorem principalPreconditionedCoreIffExpr_of_success_via_generalAllHooksSuite
    (h_app0 : AppUnifySoundHook)
    (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty)
    (h_hooks : UnifyHookPremises) :
    (PrincipalTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env e st' ty
      ↔ PrincipalTypingSliceCore env e ty) :=
  principalGeneralAllHooksPreconditionedCoreIffExpr_of_success
    principalPreconditionedAllHooksSuite_proved h_app0 h_proj0 h_ok h_hooks

/--
General-all-hooks-suite convenience wrapper: derive core field principality
from an arbitrary successful `inferFieldsUnify` run.
-/
theorem principalCoreField_of_success_via_generalAllHooksSuite
    (h_app0 : AppUnifySoundHook)
    (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalFieldTypingSliceCore env fs rf :=
  principalGeneralAllHooksCoreField_of_success
    principalPreconditionedAllHooksSuite_proved h_app0 h_proj0 h_ok

/--
General-all-hooks-suite convenience wrapper: derive preconditioned field
principality for any hook witnesses from an arbitrary successful run.
-/
theorem principalPreconditionedField_anyHooks_of_success_via_generalAllHooksSuite
    (h_app0 : AppUnifySoundHook)
    (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    ∀ h_app h_proj,
      PrincipalFieldTypingSlicePreconditioned h_app h_proj st fuel env fs st' rf :=
  principalGeneralAllHooksPreconditionedField_anyHooks_of_success
    principalPreconditionedAllHooksSuite_proved h_app0 h_proj0 h_ok

/--
General-all-hooks-suite convenience wrapper: derive preconditioned field
principality for a bundled hook witness from an arbitrary successful run.
-/
theorem principalPreconditionedField_of_success_via_generalAllHooksSuite
    (h_app0 : AppUnifySoundHook)
    (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)))
    (h_hooks : UnifyHookPremises) :
    PrincipalFieldTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env fs st' rf :=
  principalGeneralAllHooksPreconditionedField_of_success
    principalPreconditionedAllHooksSuite_proved h_app0 h_proj0 h_ok h_hooks

/--
General-all-hooks-suite convenience wrapper: derive fixed-run field
preconditioned↔core equivalence for any hook witnesses.
-/
theorem principalPreconditionedCoreIffField_anyHooks_of_success_via_generalAllHooksSuite
    (h_app0 : AppUnifySoundHook)
    (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    ∀ h_app h_proj,
      (PrincipalFieldTypingSlicePreconditioned h_app h_proj st fuel env fs st' rf
        ↔ PrincipalFieldTypingSliceCore env fs rf) :=
  principalGeneralAllHooksPreconditionedCoreIffField_anyHooks_of_success
    principalPreconditionedAllHooksSuite_proved h_app0 h_proj0 h_ok

/--
General-all-hooks-suite convenience wrapper: derive fixed-run field
preconditioned↔core equivalence for a bundled hook witness.
-/
theorem principalPreconditionedCoreIffField_of_success_via_generalAllHooksSuite
    (h_app0 : AppUnifySoundHook)
    (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)))
    (h_hooks : UnifyHookPremises) :
    (PrincipalFieldTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env fs st' rf
      ↔ PrincipalFieldTypingSliceCore env fs rf) :=
  principalGeneralAllHooksPreconditionedCoreIffField_of_success
    principalPreconditionedAllHooksSuite_proved h_app0 h_proj0 h_ok h_hooks

/--
General-all-hooks-suite convenience wrapper: bundled-baseline variant for core
expression principality from an arbitrary successful run.
-/
theorem principalCoreExpr_of_success_via_generalAllHooksSuite_from_bundle
    (h_seed : UnifyHookPremises)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalTypingSliceCore env e ty :=
  principalCoreExpr_of_success_via_generalAllHooksSuite h_seed.1 h_seed.2 h_ok

/--
General-all-hooks-suite convenience wrapper: bundled-baseline variant for
preconditioned expression principality (any target hooks) from an arbitrary
successful run.
-/
theorem principalPreconditionedExpr_anyHooks_of_success_via_generalAllHooksSuite_from_bundle
    (h_seed : UnifyHookPremises)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    ∀ h_app h_proj,
      PrincipalTypingSlicePreconditioned h_app h_proj st fuel env e st' ty :=
  principalPreconditionedExpr_anyHooks_of_success_via_generalAllHooksSuite
    h_seed.1 h_seed.2 h_ok

/--
General-all-hooks-suite convenience wrapper: bundled-baseline variant for
fixed-run expression preconditioned↔core equivalence (any target hooks) from an
arbitrary successful run.
-/
theorem principalPreconditionedCoreIffExpr_anyHooks_of_success_via_generalAllHooksSuite_from_bundle
    (h_seed : UnifyHookPremises)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    ∀ h_app h_proj,
      (PrincipalTypingSlicePreconditioned h_app h_proj st fuel env e st' ty
        ↔ PrincipalTypingSliceCore env e ty) :=
  principalPreconditionedCoreIffExpr_anyHooks_of_success_via_generalAllHooksSuite
    h_seed.1 h_seed.2 h_ok

/--
General-all-hooks-suite convenience wrapper: bundled-baseline variant for core
field principality from an arbitrary successful field run.
-/
theorem principalCoreField_of_success_via_generalAllHooksSuite_from_bundle
    (h_seed : UnifyHookPremises)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalFieldTypingSliceCore env fs rf :=
  principalCoreField_of_success_via_generalAllHooksSuite h_seed.1 h_seed.2 h_ok

/--
General-all-hooks-suite convenience wrapper: bundled-baseline variant for
preconditioned field principality (any target hooks) from an arbitrary
successful field run.
-/
theorem principalPreconditionedField_anyHooks_of_success_via_generalAllHooksSuite_from_bundle
    (h_seed : UnifyHookPremises)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    ∀ h_app h_proj,
      PrincipalFieldTypingSlicePreconditioned h_app h_proj st fuel env fs st' rf :=
  principalPreconditionedField_anyHooks_of_success_via_generalAllHooksSuite
    h_seed.1 h_seed.2 h_ok

/--
General-all-hooks-suite convenience wrapper: bundled-baseline variant for
fixed-run field preconditioned↔core equivalence (any target hooks) from an
arbitrary successful field run.
-/
theorem principalPreconditionedCoreIffField_anyHooks_of_success_via_generalAllHooksSuite_from_bundle
    (h_seed : UnifyHookPremises)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    ∀ h_app h_proj,
      (PrincipalFieldTypingSlicePreconditioned h_app h_proj st fuel env fs st' rf
        ↔ PrincipalFieldTypingSliceCore env fs rf) :=
  principalPreconditionedCoreIffField_anyHooks_of_success_via_generalAllHooksSuite
    h_seed.1 h_seed.2 h_ok

/--
General-all-hooks-suite convenience wrapper: bundled-baseline variant for
preconditioned expression principality under a bundled target-hook witness from
an arbitrary successful run.
-/
theorem principalPreconditionedExpr_of_success_via_generalAllHooksSuite_from_bundle
    (h_seed : UnifyHookPremises)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty)
    (h_hooks : UnifyHookPremises) :
    PrincipalTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env e st' ty :=
  principalPreconditionedExpr_of_success_via_generalAllHooksSuite
    h_seed.1 h_seed.2 h_ok h_hooks

/--
General-all-hooks-suite convenience wrapper: bundled-baseline variant for
fixed-run expression preconditioned↔core equivalence under a bundled
target-hook witness from an arbitrary successful run.
-/
theorem principalPreconditionedCoreIffExpr_of_success_via_generalAllHooksSuite_from_bundle
    (h_seed : UnifyHookPremises)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty)
    (h_hooks : UnifyHookPremises) :
    (PrincipalTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env e st' ty
      ↔ PrincipalTypingSliceCore env e ty) :=
  principalPreconditionedCoreIffExpr_of_success_via_generalAllHooksSuite
    h_seed.1 h_seed.2 h_ok h_hooks

/--
General-all-hooks-suite convenience wrapper: bundled-baseline variant for
preconditioned field principality under a bundled target-hook witness from an
arbitrary successful field run.
-/
theorem principalPreconditionedField_of_success_via_generalAllHooksSuite_from_bundle
    (h_seed : UnifyHookPremises)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)))
    (h_hooks : UnifyHookPremises) :
    PrincipalFieldTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env fs st' rf :=
  principalPreconditionedField_of_success_via_generalAllHooksSuite
    h_seed.1 h_seed.2 h_ok h_hooks

/--
General-all-hooks-suite convenience wrapper: bundled-baseline variant for
fixed-run field preconditioned↔core equivalence under a bundled target-hook
witness from an arbitrary successful field run.
-/
theorem principalPreconditionedCoreIffField_of_success_via_generalAllHooksSuite_from_bundle
    (h_seed : UnifyHookPremises)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)))
    (h_hooks : UnifyHookPremises) :
    (PrincipalFieldTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env fs st' rf
      ↔ PrincipalFieldTypingSliceCore env fs rf) :=
  principalPreconditionedCoreIffField_of_success_via_generalAllHooksSuite
    h_seed.1 h_seed.2 h_ok h_hooks

/--
General-all-hooks-suite convenience wrapper: derive fixed-run expression
hook-irrelevance from an arbitrary successful run.
-/
theorem principalPreconditionedExpr_hookIrrelevant_of_success_via_generalAllHooksSuite
    {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
    {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook}
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    (PrincipalTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env e st' ty
      ↔ PrincipalTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env e st' ty) :=
  principalGeneralAllHooksPreconditionedExpr_hookIrrelevant_of_success
    principalPreconditionedAllHooksSuite_proved h_ok

/--
General-all-hooks-suite convenience wrapper: derive fixed-run field
hook-irrelevance from an arbitrary successful field run.
-/
theorem principalPreconditionedField_hookIrrelevant_of_success_via_generalAllHooksSuite
    {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
    {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook}
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    (PrincipalFieldTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env fs st' rf
      ↔ PrincipalFieldTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env fs st' rf) :=
  principalGeneralAllHooksPreconditionedField_hookIrrelevant_of_success
    principalPreconditionedAllHooksSuite_proved h_ok

/--
Top-level M4 principal vacuity suite.

This packages:
- no-unify principal capstones (expression+field), and
- fixed-run hook-irrelevance for preconditioned principality.
-/
structure PrincipalBoundaryVacuitySuite : Prop where
  noUnifyCapstones : PrincipalBoundaryNoUnifyCapstoneSlices
  hookIrrelevance : PrincipalPreconditionedHookIrrelevanceSlices

/-- The principal vacuity suite is fully proved. -/
theorem principalBoundaryVacuitySuite_proved : PrincipalBoundaryVacuitySuite := by
  refine {
    noUnifyCapstones := principalBoundaryNoUnifyCapstoneSlices_proved
    hookIrrelevance := principalPreconditionedHookIrrelevanceSlices_proved
  }

/-- One-hop expression no-unify capstone projection from vacuity suite. -/
theorem principalBoundaryVacuitySuite_noUnify_expr
    (h_suite : PrincipalBoundaryVacuitySuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty)
    (h_hooks : UnifyHookPremises) :
    PrincipalBoundaryNoUnifyExprCapstone
      h_hooks.1 h_hooks.2 st fuel env e st' ty :=
  principalBoundaryNoUnifyCapstoneSlices_expr
    h_suite.noUnifyCapstones h_no h_ok h_hooks

/-- One-hop field no-unify capstone projection from vacuity suite. -/
theorem principalBoundaryVacuitySuite_noUnify_field
    (h_suite : PrincipalBoundaryVacuitySuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)))
    (h_hooks : UnifyHookPremises) :
    PrincipalBoundaryNoUnifyFieldCapstone
      h_hooks.1 h_hooks.2 st fuel env fs st' rf :=
  principalBoundaryNoUnifyCapstoneSlices_field
    h_suite.noUnifyCapstones h_no h_ok h_hooks

/--
One-hop expression hook-irrelevance projection from vacuity suite.
-/
theorem principalBoundaryVacuitySuite_hookIrrelevance_expr
    (h_suite : PrincipalBoundaryVacuitySuite)
    {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
    {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook}
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    (PrincipalTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env e st' ty
      ↔ PrincipalTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env e st' ty) :=
  principalPreconditionedHookIrrelevanceSlices_expr
    h_suite.hookIrrelevance h_ok

/--
One-hop field hook-irrelevance projection from vacuity suite.
-/
theorem principalBoundaryVacuitySuite_hookIrrelevance_field
    (h_suite : PrincipalBoundaryVacuitySuite)
    {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
    {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook}
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    (PrincipalFieldTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env fs st' rf
      ↔ PrincipalFieldTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env fs st' rf) :=
  principalPreconditionedHookIrrelevanceSlices_field
    h_suite.hookIrrelevance h_ok

/--
No-unify all-hooks expression capstone.

This removes explicit hook parameters from the capstone surface by exporting:
- core principality,
- preconditioned principality for any hook witnesses, and
- per-hook successful-run preconditioned↔core equivalence.
-/
structure PrincipalBoundaryNoUnifyExprAllHooksCapstone
    (st : UnifyState) (fuel : Nat) (env : TermEnv) (e : CoreExpr)
    (st' : UnifyState) (ty : Ty) : Prop where
  core : PrincipalTypingSliceCore env e ty
  preconditionedAny :
    ∀ h_app h_proj, PrincipalTypingSlicePreconditioned h_app h_proj st fuel env e st' ty
  preconditionedAnyIffCore :
    ∀ h_app h_proj,
      (PrincipalTypingSlicePreconditioned h_app h_proj st fuel env e st' ty
        ↔ PrincipalTypingSliceCore env e ty)

/--
Construct the no-unify all-hooks expression capstone from a successful no-unify
`inferExprUnify` run.
-/
theorem principalBoundaryNoUnifyExprAllHooksCapstone_of_success
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalBoundaryNoUnifyExprAllHooksCapstone st fuel env e st' ty := by
  have h_core : PrincipalTypingSliceCore env e ty :=
    principalTypingSliceCore_of_unify_success_no_unify h_no h_ok
  refine {
    core := h_core
    preconditionedAny := ?_
    preconditionedAnyIffCore := ?_
  }
  · intro h_app h_proj
    exact principalTypingSlicePreconditioned_of_success_no_unify
      h_no h_ok h_app h_proj
  · intro h_app h_proj
    exact principalTypingSlicePreconditioned_iff_core_of_success
      h_app h_proj st fuel env e st' ty h_ok

/--
No-unify all-hooks field capstone.

Field-side analogue of `PrincipalBoundaryNoUnifyExprAllHooksCapstone`.
-/
structure PrincipalBoundaryNoUnifyFieldAllHooksCapstone
    (st : UnifyState) (fuel : Nat) (env : TermEnv) (fs : CoreFields)
    (st' : UnifyState) (rf : RowFields) : Prop where
  core : PrincipalFieldTypingSliceCore env fs rf
  preconditionedAny :
    ∀ h_app h_proj,
      PrincipalFieldTypingSlicePreconditioned h_app h_proj st fuel env fs st' rf
  preconditionedAnyIffCore :
    ∀ h_app h_proj,
      (PrincipalFieldTypingSlicePreconditioned h_app h_proj st fuel env fs st' rf
        ↔ PrincipalFieldTypingSliceCore env fs rf)

/--
Construct the no-unify all-hooks field capstone from a successful no-unify
`inferFieldsUnify` run.
-/
theorem principalBoundaryNoUnifyFieldAllHooksCapstone_of_success
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalBoundaryNoUnifyFieldAllHooksCapstone st fuel env fs st' rf := by
  have h_core : PrincipalFieldTypingSliceCore env fs rf :=
    principalFieldTypingSliceCore_of_unify_success_no_unify h_no h_ok
  refine {
    core := h_core
    preconditionedAny := ?_
    preconditionedAnyIffCore := ?_
  }
  · intro h_app h_proj
    exact principalFieldTypingSlicePreconditioned_of_success_no_unify
      h_no h_ok h_app h_proj
  · intro h_app h_proj
    exact principalFieldTypingSlicePreconditioned_iff_core_of_success
      h_app h_proj st fuel env fs st' rf h_ok

/-- Packaged no-unify all-hooks expression capstone slice. -/
def PrincipalBoundaryNoUnifyExprAllHooksCapstoneSlice : Prop :=
  ∀ {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty},
    NoUnifyBranchesExpr e →
    inferExprUnify st fuel env e = .ok st' ty →
    PrincipalBoundaryNoUnifyExprAllHooksCapstone st fuel env e st' ty

/-- Packaged no-unify all-hooks field capstone slice. -/
def PrincipalBoundaryNoUnifyFieldAllHooksCapstoneSlice : Prop :=
  ∀ {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields},
    NoUnifyBranchesFields fs →
    inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)) →
    PrincipalBoundaryNoUnifyFieldAllHooksCapstone st fuel env fs st' rf

/-- Combined no-unify all-hooks capstone slices across expressions and fields. -/
def PrincipalBoundaryNoUnifyAllHooksCapstoneSlices : Prop :=
  PrincipalBoundaryNoUnifyExprAllHooksCapstoneSlice ∧
    PrincipalBoundaryNoUnifyFieldAllHooksCapstoneSlice

/-- The combined no-unify all-hooks capstone slices are fully proved. -/
theorem principalBoundaryNoUnifyAllHooksCapstoneSlices_proved :
    PrincipalBoundaryNoUnifyAllHooksCapstoneSlices := by
  refine ⟨?_, ?_⟩
  · intro st fuel env e st' ty h_no h_ok
    exact principalBoundaryNoUnifyExprAllHooksCapstone_of_success h_no h_ok
  · intro st fuel env fs st' rf h_no h_ok
    exact principalBoundaryNoUnifyFieldAllHooksCapstone_of_success h_no h_ok

/-- One-hop expression branch projection from all-hooks no-unify capstone slices. -/
theorem principalBoundaryNoUnifyAllHooksCapstoneSlices_expr
    (h_slice : PrincipalBoundaryNoUnifyAllHooksCapstoneSlices)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalBoundaryNoUnifyExprAllHooksCapstone st fuel env e st' ty :=
  h_slice.1 h_no h_ok

/-- One-hop field branch projection from all-hooks no-unify capstone slices. -/
theorem principalBoundaryNoUnifyAllHooksCapstoneSlices_field
    (h_slice : PrincipalBoundaryNoUnifyAllHooksCapstoneSlices)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalBoundaryNoUnifyFieldAllHooksCapstone st fuel env fs st' rf :=
  h_slice.2 h_no h_ok

/--
Coherence (all-hooks expression capstone): for any two hook witnesses, the
preconditioned principal slice is equivalent on the same successful run.
-/
theorem principalBoundaryNoUnifyExprAllHooksCapstone_hook_irrelevant
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_cap : PrincipalBoundaryNoUnifyExprAllHooksCapstone st fuel env e st' ty)
    {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
    {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook} :
    (PrincipalTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env e st' ty
      ↔ PrincipalTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env e st' ty) := by
  constructor
  · intro h_pre
    have h_core : PrincipalTypingSliceCore env e ty :=
      (h_cap.preconditionedAnyIffCore h_app₁ h_proj₁).1 h_pre
    exact (h_cap.preconditionedAnyIffCore h_app₂ h_proj₂).2 h_core
  · intro h_pre
    have h_core : PrincipalTypingSliceCore env e ty :=
      (h_cap.preconditionedAnyIffCore h_app₂ h_proj₂).1 h_pre
    exact (h_cap.preconditionedAnyIffCore h_app₁ h_proj₁).2 h_core

/--
Coherence (all-hooks field capstone): for any two hook witnesses, the
preconditioned field principal slice is equivalent on the same successful run.
-/
theorem principalBoundaryNoUnifyFieldAllHooksCapstone_hook_irrelevant
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_cap : PrincipalBoundaryNoUnifyFieldAllHooksCapstone st fuel env fs st' rf)
    {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
    {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook} :
    (PrincipalFieldTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env fs st' rf
      ↔ PrincipalFieldTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env fs st' rf) := by
  constructor
  · intro h_pre
    have h_core : PrincipalFieldTypingSliceCore env fs rf :=
      (h_cap.preconditionedAnyIffCore h_app₁ h_proj₁).1 h_pre
    exact (h_cap.preconditionedAnyIffCore h_app₂ h_proj₂).2 h_core
  · intro h_pre
    have h_core : PrincipalFieldTypingSliceCore env fs rf :=
      (h_cap.preconditionedAnyIffCore h_app₂ h_proj₂).1 h_pre
    exact (h_cap.preconditionedAnyIffCore h_app₁ h_proj₁).2 h_core

/--
Packaged no-unify expression hook-irrelevance obtained directly from the
all-hooks capstone slice.
-/
def PrincipalBoundaryNoUnifyExprAllHooksIrrelevanceSlice : Prop :=
  ∀ {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
    {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook},
    NoUnifyBranchesExpr e →
    inferExprUnify st fuel env e = .ok st' ty →
    (PrincipalTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env e st' ty
      ↔ PrincipalTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env e st' ty)

/--
Packaged no-unify field hook-irrelevance obtained directly from the all-hooks
capstone slice.
-/
def PrincipalBoundaryNoUnifyFieldAllHooksIrrelevanceSlice : Prop :=
  ∀ {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
    {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook},
    NoUnifyBranchesFields fs →
    inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)) →
    (PrincipalFieldTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env fs st' rf
      ↔ PrincipalFieldTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env fs st' rf)

/--
Combined no-unify all-hooks irrelevance slice across expressions and fields.
-/
def PrincipalBoundaryNoUnifyAllHooksIrrelevanceSlices : Prop :=
  PrincipalBoundaryNoUnifyExprAllHooksIrrelevanceSlice ∧
    PrincipalBoundaryNoUnifyFieldAllHooksIrrelevanceSlice

/--
The combined no-unify all-hooks irrelevance slices are fully proved.
-/
theorem principalBoundaryNoUnifyAllHooksIrrelevanceSlices_proved :
    PrincipalBoundaryNoUnifyAllHooksIrrelevanceSlices := by
  refine ⟨?_, ?_⟩
  · intro st fuel env e st' ty h_app₁ h_proj₁ h_app₂ h_proj₂ h_no h_ok
    exact principalBoundaryNoUnifyExprAllHooksCapstone_hook_irrelevant
      (principalBoundaryNoUnifyExprAllHooksCapstone_of_success h_no h_ok)
  · intro st fuel env fs st' rf h_app₁ h_proj₁ h_app₂ h_proj₂ h_no h_ok
    exact principalBoundaryNoUnifyFieldAllHooksCapstone_hook_irrelevant
      (principalBoundaryNoUnifyFieldAllHooksCapstone_of_success h_no h_ok)

/--
One-hop projection: expression branch from combined no-unify all-hooks
irrelevance slices.
-/
theorem principalBoundaryNoUnifyAllHooksIrrelevanceSlices_expr
    (h_slice : PrincipalBoundaryNoUnifyAllHooksIrrelevanceSlices)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
    {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    (PrincipalTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env e st' ty
      ↔ PrincipalTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env e st' ty) :=
  h_slice.1 h_no h_ok

/--
One-hop projection: field branch from combined no-unify all-hooks irrelevance
slices.
-/
theorem principalBoundaryNoUnifyAllHooksIrrelevanceSlices_field
    (h_slice : PrincipalBoundaryNoUnifyAllHooksIrrelevanceSlices)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
    {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    (PrincipalFieldTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env fs st' rf
      ↔ PrincipalFieldTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env fs st' rf) :=
  h_slice.2 h_no h_ok

/-- Packaged no-unify all-hooks expression run-bundle slice. -/
def PrincipalBoundaryNoUnifyExprAllHooksRunBundleSlice : Prop :=
  ∀ {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty},
    NoUnifyBranchesExpr e →
    inferExprUnify st fuel env e = .ok st' ty →
    PrincipalPreconditionedExprAllHooksRunBundle st fuel env e st' ty

/-- Packaged no-unify all-hooks field run-bundle slice. -/
def PrincipalBoundaryNoUnifyFieldAllHooksRunBundleSlice : Prop :=
  ∀ {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields},
    NoUnifyBranchesFields fs →
    inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)) →
    PrincipalPreconditionedFieldAllHooksRunBundle st fuel env fs st' rf

/-- Combined no-unify all-hooks run-bundle slices across expressions and fields. -/
def PrincipalBoundaryNoUnifyAllHooksRunBundleSlices : Prop :=
  PrincipalBoundaryNoUnifyExprAllHooksRunBundleSlice ∧
    PrincipalBoundaryNoUnifyFieldAllHooksRunBundleSlice

/-- The combined no-unify all-hooks run-bundle slices are fully proved. -/
theorem principalBoundaryNoUnifyAllHooksRunBundleSlices_proved :
    PrincipalBoundaryNoUnifyAllHooksRunBundleSlices := by
  refine ⟨?_, ?_⟩
  · intro st fuel env e st' ty h_no h_ok
    let h_cap_no : PrincipalBoundaryNoUnifyExprAllHooksCapstone st fuel env e st' ty :=
      principalBoundaryNoUnifyExprAllHooksCapstone_of_success h_no h_ok
    have h_cap_general : PrincipalPreconditionedExprAllHooksCapstone st fuel env e st' ty := by
      refine {
        core := h_cap_no.core
        preconditionedAny := h_cap_no.preconditionedAny
        preconditionedAnyIffCore := h_cap_no.preconditionedAnyIffCore
      }
    exact principalPreconditionedExprAllHooksRunBundle_of_capstone h_cap_general
  · intro st fuel env fs st' rf h_no h_ok
    let h_cap_no : PrincipalBoundaryNoUnifyFieldAllHooksCapstone st fuel env fs st' rf :=
      principalBoundaryNoUnifyFieldAllHooksCapstone_of_success h_no h_ok
    have h_cap_general : PrincipalPreconditionedFieldAllHooksCapstone st fuel env fs st' rf := by
      refine {
        core := h_cap_no.core
        preconditionedAny := h_cap_no.preconditionedAny
        preconditionedAnyIffCore := h_cap_no.preconditionedAnyIffCore
      }
    exact principalPreconditionedFieldAllHooksRunBundle_of_capstone h_cap_general

/-- One-hop expression projection from no-unify all-hooks run-bundle slices. -/
theorem principalBoundaryNoUnifyAllHooksRunBundleSlices_expr
    (h_slice : PrincipalBoundaryNoUnifyAllHooksRunBundleSlices)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalPreconditionedExprAllHooksRunBundle st fuel env e st' ty :=
  h_slice.1 h_no h_ok

/-- One-hop field projection from no-unify all-hooks run-bundle slices. -/
theorem principalBoundaryNoUnifyAllHooksRunBundleSlices_field
    (h_slice : PrincipalBoundaryNoUnifyAllHooksRunBundleSlices)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalPreconditionedFieldAllHooksRunBundle st fuel env fs st' rf :=
  h_slice.2 h_no h_ok

/--
Top-level no-unify all-hooks suite.

This packages:
- all-hooks no-unify capstones (expression+field), and
- no-unify hook-irrelevance derived from those all-hooks capstones.
-/
structure PrincipalBoundaryNoUnifyAllHooksSuite : Prop where
  capstones : PrincipalBoundaryNoUnifyAllHooksCapstoneSlices
  runBundles : PrincipalBoundaryNoUnifyAllHooksRunBundleSlices
  irrelevance : PrincipalBoundaryNoUnifyAllHooksIrrelevanceSlices

/-- The no-unify all-hooks suite is fully proved. -/
theorem principalBoundaryNoUnifyAllHooksSuite_proved :
    PrincipalBoundaryNoUnifyAllHooksSuite := by
  refine {
    capstones := principalBoundaryNoUnifyAllHooksCapstoneSlices_proved
    runBundles := principalBoundaryNoUnifyAllHooksRunBundleSlices_proved
    irrelevance := principalBoundaryNoUnifyAllHooksIrrelevanceSlices_proved
  }

/-- One-hop expression all-hooks capstone projection from all-hooks suite. -/
theorem principalBoundaryNoUnifyAllHooksSuite_capstone_expr
    (h_suite : PrincipalBoundaryNoUnifyAllHooksSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalBoundaryNoUnifyExprAllHooksCapstone st fuel env e st' ty :=
  principalBoundaryNoUnifyAllHooksCapstoneSlices_expr
    h_suite.capstones h_no h_ok

/-- One-hop field all-hooks capstone projection from all-hooks suite. -/
theorem principalBoundaryNoUnifyAllHooksSuite_capstone_field
    (h_suite : PrincipalBoundaryNoUnifyAllHooksSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalBoundaryNoUnifyFieldAllHooksCapstone st fuel env fs st' rf :=
  principalBoundaryNoUnifyAllHooksCapstoneSlices_field
    h_suite.capstones h_no h_ok

/-- One-hop expression run-bundle projection from all-hooks no-unify suite. -/
theorem principalBoundaryNoUnifyAllHooksSuite_runBundle_expr
    (h_suite : PrincipalBoundaryNoUnifyAllHooksSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalPreconditionedExprAllHooksRunBundle st fuel env e st' ty :=
  principalBoundaryNoUnifyAllHooksRunBundleSlices_expr
    h_suite.runBundles h_no h_ok

/-- One-hop field run-bundle projection from all-hooks no-unify suite. -/
theorem principalBoundaryNoUnifyAllHooksSuite_runBundle_field
    (h_suite : PrincipalBoundaryNoUnifyAllHooksSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalPreconditionedFieldAllHooksRunBundle st fuel env fs st' rf :=
  principalBoundaryNoUnifyAllHooksRunBundleSlices_field
    h_suite.runBundles h_no h_ok

/--
No-unify all-hooks suite convenience wrapper: derive the expression run-bundle
surface from a successful no-unify run.
-/
theorem principalBoundaryNoUnifyRunBundleExpr_of_success_via_allHooksSuite
    (h_suite : PrincipalBoundaryNoUnifyAllHooksSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalPreconditionedExprAllHooksRunBundle st fuel env e st' ty :=
  principalBoundaryNoUnifyAllHooksSuite_runBundle_expr h_suite h_no h_ok

/--
No-unify all-hooks suite convenience wrapper: derive the field run-bundle
surface from a successful no-unify field run.
-/
theorem principalBoundaryNoUnifyRunBundleField_of_success_via_allHooksSuite
    (h_suite : PrincipalBoundaryNoUnifyAllHooksSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalPreconditionedFieldAllHooksRunBundle st fuel env fs st' rf :=
  principalBoundaryNoUnifyAllHooksSuite_runBundle_field h_suite h_no h_ok

/--
All-hooks-suite convenience wrapper: derive the expression run-bundle surface
from a successful no-unify run.
-/
theorem principalNoUnifyRunBundleExpr_of_success_via_allHooksSuite
    (h_suite : PrincipalBoundaryNoUnifyAllHooksSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalPreconditionedExprAllHooksRunBundle st fuel env e st' ty :=
  principalBoundaryNoUnifyRunBundleExpr_of_success_via_allHooksSuite
    h_suite h_no h_ok

/--
All-hooks-suite convenience wrapper: derive the field run-bundle surface from a
successful no-unify field run.
-/
theorem principalNoUnifyRunBundleField_of_success_via_allHooksSuite
    (h_suite : PrincipalBoundaryNoUnifyAllHooksSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalPreconditionedFieldAllHooksRunBundle st fuel env fs st' rf :=
  principalBoundaryNoUnifyRunBundleField_of_success_via_allHooksSuite
    h_suite h_no h_ok

/-- One-hop expression irrelevance projection from all-hooks suite. -/
theorem principalBoundaryNoUnifyAllHooksSuite_irrelevance_expr
    (h_suite : PrincipalBoundaryNoUnifyAllHooksSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
    {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    (PrincipalTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env e st' ty
      ↔ PrincipalTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env e st' ty) :=
  principalBoundaryNoUnifyAllHooksIrrelevanceSlices_expr
    h_suite.irrelevance h_no h_ok

/-- One-hop field irrelevance projection from all-hooks suite. -/
theorem principalBoundaryNoUnifyAllHooksSuite_irrelevance_field
    (h_suite : PrincipalBoundaryNoUnifyAllHooksSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
    {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    (PrincipalFieldTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env fs st' rf
      ↔ PrincipalFieldTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env fs st' rf) :=
  principalBoundaryNoUnifyAllHooksIrrelevanceSlices_field
    h_suite.irrelevance h_no h_ok

/--
Convert a no-unify all-hooks expression capstone into the general successful-run
all-hooks expression capstone.
-/
theorem principalPreconditionedExprAllHooksCapstone_of_noUnifyAllHooks
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_cap : PrincipalBoundaryNoUnifyExprAllHooksCapstone st fuel env e st' ty) :
    PrincipalPreconditionedExprAllHooksCapstone st fuel env e st' ty := by
  refine {
    core := h_cap.core
    preconditionedAny := h_cap.preconditionedAny
    preconditionedAnyIffCore := h_cap.preconditionedAnyIffCore
  }

/--
Convert a no-unify all-hooks field capstone into the general successful-run
all-hooks field capstone.
-/
theorem principalPreconditionedFieldAllHooksCapstone_of_noUnifyAllHooks
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_cap : PrincipalBoundaryNoUnifyFieldAllHooksCapstone st fuel env fs st' rf) :
    PrincipalPreconditionedFieldAllHooksCapstone st fuel env fs st' rf := by
  refine {
    core := h_cap.core
    preconditionedAny := h_cap.preconditionedAny
    preconditionedAnyIffCore := h_cap.preconditionedAnyIffCore
  }

/--
One-hop expression projection: view a no-unify all-hooks suite capstone on a
successful no-unify run as a general successful-run all-hooks capstone.
-/
theorem principalBoundaryNoUnifyAllHooksSuite_capstone_expr_as_general
    (h_suite : PrincipalBoundaryNoUnifyAllHooksSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalPreconditionedExprAllHooksCapstone st fuel env e st' ty :=
  principalPreconditionedExprAllHooksCapstone_of_noUnifyAllHooks
    (principalBoundaryNoUnifyAllHooksSuite_capstone_expr h_suite h_no h_ok)

/--
One-hop field projection: view a no-unify all-hooks suite capstone on a
successful no-unify run as a general successful-run all-hooks capstone.
-/
theorem principalBoundaryNoUnifyAllHooksSuite_capstone_field_as_general
    (h_suite : PrincipalBoundaryNoUnifyAllHooksSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalPreconditionedFieldAllHooksCapstone st fuel env fs st' rf :=
  principalPreconditionedFieldAllHooksCapstone_of_noUnifyAllHooks
    (principalBoundaryNoUnifyAllHooksSuite_capstone_field h_suite h_no h_ok)

/--
Construct the general all-hooks expression capstone directly from a successful
no-unify expression run.
-/
theorem principalPreconditionedExprAllHooksCapstone_of_success_noUnify
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalPreconditionedExprAllHooksCapstone st fuel env e st' ty :=
  principalPreconditionedExprAllHooksCapstone_of_noUnifyAllHooks
    (principalBoundaryNoUnifyExprAllHooksCapstone_of_success h_no h_ok)

/--
Construct the general all-hooks field capstone directly from a successful
no-unify field run.
-/
theorem principalPreconditionedFieldAllHooksCapstone_of_success_noUnify
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalPreconditionedFieldAllHooksCapstone st fuel env fs st' rf :=
  principalPreconditionedFieldAllHooksCapstone_of_noUnifyAllHooks
    (principalBoundaryNoUnifyFieldAllHooksCapstone_of_success h_no h_ok)

/--
No-unify-to-general convenience wrapper: construct an expression run-bundle from
a successful no-unify run.
-/
theorem principalPreconditionedExprAllHooksRunBundle_of_success_noUnify_via_generalAllHooks
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalPreconditionedExprAllHooksRunBundle st fuel env e st' ty :=
  principalPreconditionedExprAllHooksRunBundle_of_capstone
    (principalPreconditionedExprAllHooksCapstone_of_success_noUnify h_no h_ok)

/--
No-unify-to-general convenience wrapper: construct a field run-bundle from a
successful no-unify field run.
-/
theorem principalPreconditionedFieldAllHooksRunBundle_of_success_noUnify_via_generalAllHooks
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalPreconditionedFieldAllHooksRunBundle st fuel env fs st' rf :=
  principalPreconditionedFieldAllHooksRunBundle_of_capstone
    (principalPreconditionedFieldAllHooksCapstone_of_success_noUnify h_no h_ok)

/--
No-unify-to-general convenience wrapper: derive core expression principality
from a successful no-unify run using the general all-hooks capstone surface.
-/
theorem principalCoreExpr_of_success_noUnify_via_generalAllHooks
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalTypingSliceCore env e ty :=
  (principalPreconditionedExprAllHooksCapstone_of_success_noUnify h_no h_ok).core

/--
No-unify-to-general convenience wrapper: derive preconditioned expression
principality for any hook witnesses from a successful no-unify run.
-/
theorem principalPreconditionedExpr_anyHooks_of_success_noUnify_via_generalAllHooks
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    ∀ h_app h_proj,
      PrincipalTypingSlicePreconditioned h_app h_proj st fuel env e st' ty :=
  (principalPreconditionedExprAllHooksCapstone_of_success_noUnify h_no h_ok).preconditionedAny

/--
No-unify-to-general convenience wrapper: derive preconditioned expression
principality for a bundled hook witness from a successful no-unify run.
-/
theorem principalPreconditionedExpr_of_success_noUnify_via_generalAllHooks
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty)
    (h_hooks : UnifyHookPremises) :
    PrincipalTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env e st' ty :=
  (principalPreconditionedExpr_anyHooks_of_success_noUnify_via_generalAllHooks
    h_no h_ok) h_hooks.1 h_hooks.2

/--
No-unify-to-general convenience wrapper: derive fixed-run expression
preconditioned↔core equivalence for any hook witnesses from a successful
no-unify run.
-/
theorem principalPreconditionedCoreIffExpr_anyHooks_of_success_noUnify_via_generalAllHooks
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    ∀ h_app h_proj,
      (PrincipalTypingSlicePreconditioned h_app h_proj st fuel env e st' ty
        ↔ PrincipalTypingSliceCore env e ty) :=
  (principalPreconditionedExprAllHooksCapstone_of_success_noUnify
    h_no h_ok).preconditionedAnyIffCore

/--
No-unify-to-general convenience wrapper: derive fixed-run expression
preconditioned↔core equivalence for a bundled hook witness from a successful
no-unify run.
-/
theorem principalPreconditionedCoreIffExpr_of_success_noUnify_via_generalAllHooks
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty)
    (h_hooks : UnifyHookPremises) :
    (PrincipalTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env e st' ty
      ↔ PrincipalTypingSliceCore env e ty) :=
  (principalPreconditionedCoreIffExpr_anyHooks_of_success_noUnify_via_generalAllHooks
    h_no h_ok) h_hooks.1 h_hooks.2

/--
No-unify-to-general convenience wrapper: derive fixed-run hook irrelevance for
expression principality from a successful no-unify run.
-/
theorem principalPreconditionedExpr_hookIrrelevant_of_success_noUnify_via_generalAllHooks
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
    {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    (PrincipalTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env e st' ty
      ↔ PrincipalTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env e st' ty) :=
  principalPreconditionedExprAllHooksCapstone_hook_irrelevant
    (principalPreconditionedExprAllHooksCapstone_of_success_noUnify h_no h_ok)

/--
No-unify-to-general convenience wrapper: derive core field principality from a
successful no-unify field run using the general all-hooks capstone surface.
-/
theorem principalCoreField_of_success_noUnify_via_generalAllHooks
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalFieldTypingSliceCore env fs rf :=
  (principalPreconditionedFieldAllHooksCapstone_of_success_noUnify h_no h_ok).core

/--
No-unify-to-general convenience wrapper: derive preconditioned field
principality for any hook witnesses from a successful no-unify field run.
-/
theorem principalPreconditionedField_anyHooks_of_success_noUnify_via_generalAllHooks
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    ∀ h_app h_proj,
      PrincipalFieldTypingSlicePreconditioned h_app h_proj st fuel env fs st' rf :=
  (principalPreconditionedFieldAllHooksCapstone_of_success_noUnify h_no h_ok).preconditionedAny

/--
No-unify-to-general convenience wrapper: derive preconditioned field
principality for a bundled hook witness from a successful no-unify field run.
-/
theorem principalPreconditionedField_of_success_noUnify_via_generalAllHooks
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)))
    (h_hooks : UnifyHookPremises) :
    PrincipalFieldTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env fs st' rf :=
  (principalPreconditionedField_anyHooks_of_success_noUnify_via_generalAllHooks
    h_no h_ok) h_hooks.1 h_hooks.2

/--
No-unify-to-general convenience wrapper: derive fixed-run field
preconditioned↔core equivalence for any hook witnesses from a successful
no-unify field run.
-/
theorem principalPreconditionedCoreIffField_anyHooks_of_success_noUnify_via_generalAllHooks
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    ∀ h_app h_proj,
      (PrincipalFieldTypingSlicePreconditioned h_app h_proj st fuel env fs st' rf
        ↔ PrincipalFieldTypingSliceCore env fs rf) :=
  (principalPreconditionedFieldAllHooksCapstone_of_success_noUnify
    h_no h_ok).preconditionedAnyIffCore

/--
No-unify-to-general convenience wrapper: derive fixed-run field
preconditioned↔core equivalence for a bundled hook witness from a successful
no-unify field run.
-/
theorem principalPreconditionedCoreIffField_of_success_noUnify_via_generalAllHooks
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)))
    (h_hooks : UnifyHookPremises) :
    (PrincipalFieldTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env fs st' rf
      ↔ PrincipalFieldTypingSliceCore env fs rf) :=
  (principalPreconditionedCoreIffField_anyHooks_of_success_noUnify_via_generalAllHooks
    h_no h_ok) h_hooks.1 h_hooks.2

/--
No-unify-to-general convenience wrapper: derive fixed-run hook irrelevance for
field principality from a successful no-unify run.
-/
theorem principalPreconditionedField_hookIrrelevant_of_success_noUnify_via_generalAllHooks
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
    {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    (PrincipalFieldTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env fs st' rf
      ↔ PrincipalFieldTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env fs st' rf) :=
  principalPreconditionedFieldAllHooksCapstone_hook_irrelevant
    (principalPreconditionedFieldAllHooksCapstone_of_success_noUnify h_no h_ok)

/--
Packaged no-unify-to-general expression all-hooks capstone slice.
-/
def PrincipalNoUnifyToGeneralAllHooksExprCapstoneSlice : Prop :=
  ∀ {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty},
    NoUnifyBranchesExpr e →
    inferExprUnify st fuel env e = .ok st' ty →
    PrincipalPreconditionedExprAllHooksCapstone st fuel env e st' ty

/--
Packaged no-unify-to-general field all-hooks capstone slice.
-/
def PrincipalNoUnifyToGeneralAllHooksFieldCapstoneSlice : Prop :=
  ∀ {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields},
    NoUnifyBranchesFields fs →
    inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)) →
    PrincipalPreconditionedFieldAllHooksCapstone st fuel env fs st' rf

/--
Combined no-unify-to-general all-hooks capstone slices across expressions and
fields.
-/
def PrincipalNoUnifyToGeneralAllHooksCapstoneSlices : Prop :=
  PrincipalNoUnifyToGeneralAllHooksExprCapstoneSlice ∧
    PrincipalNoUnifyToGeneralAllHooksFieldCapstoneSlice

/--
The combined no-unify-to-general all-hooks capstone slices are fully proved.
-/
theorem principalNoUnifyToGeneralAllHooksCapstoneSlices_proved :
    PrincipalNoUnifyToGeneralAllHooksCapstoneSlices := by
  refine ⟨?_, ?_⟩
  · intro st fuel env e st' ty h_no h_ok
    exact principalPreconditionedExprAllHooksCapstone_of_success_noUnify h_no h_ok
  · intro st fuel env fs st' rf h_no h_ok
    exact principalPreconditionedFieldAllHooksCapstone_of_success_noUnify h_no h_ok

/--
One-hop expression branch projection from no-unify-to-general all-hooks
capstone slices.
-/
theorem principalNoUnifyToGeneralAllHooksCapstoneSlices_expr
    (h_slice : PrincipalNoUnifyToGeneralAllHooksCapstoneSlices)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalPreconditionedExprAllHooksCapstone st fuel env e st' ty :=
  h_slice.1 h_no h_ok

/--
One-hop field branch projection from no-unify-to-general all-hooks capstone
slices.
-/
theorem principalNoUnifyToGeneralAllHooksCapstoneSlices_field
    (h_slice : PrincipalNoUnifyToGeneralAllHooksCapstoneSlices)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalPreconditionedFieldAllHooksCapstone st fuel env fs st' rf :=
  h_slice.2 h_no h_ok

/--
Packaged no-unify-to-general expression run-bundle slice.
-/
def PrincipalNoUnifyToGeneralAllHooksExprRunBundleSlice : Prop :=
  ∀ {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty},
    NoUnifyBranchesExpr e →
    inferExprUnify st fuel env e = .ok st' ty →
    PrincipalPreconditionedExprAllHooksRunBundle st fuel env e st' ty

/--
Packaged no-unify-to-general field run-bundle slice.
-/
def PrincipalNoUnifyToGeneralAllHooksFieldRunBundleSlice : Prop :=
  ∀ {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields},
    NoUnifyBranchesFields fs →
    inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)) →
    PrincipalPreconditionedFieldAllHooksRunBundle st fuel env fs st' rf

/--
Combined no-unify-to-general all-hooks run-bundle slices across expressions and
fields.
-/
def PrincipalNoUnifyToGeneralAllHooksRunBundleSlices : Prop :=
  PrincipalNoUnifyToGeneralAllHooksExprRunBundleSlice ∧
    PrincipalNoUnifyToGeneralAllHooksFieldRunBundleSlice

/--
The combined no-unify-to-general all-hooks run-bundle slices are fully proved.
-/
theorem principalNoUnifyToGeneralAllHooksRunBundleSlices_proved :
    PrincipalNoUnifyToGeneralAllHooksRunBundleSlices := by
  refine ⟨?_, ?_⟩
  · intro st fuel env e st' ty h_no h_ok
    exact principalPreconditionedExprAllHooksRunBundle_of_capstone
      (principalNoUnifyToGeneralAllHooksCapstoneSlices_expr
        principalNoUnifyToGeneralAllHooksCapstoneSlices_proved h_no h_ok)
  · intro st fuel env fs st' rf h_no h_ok
    exact principalPreconditionedFieldAllHooksRunBundle_of_capstone
      (principalNoUnifyToGeneralAllHooksCapstoneSlices_field
        principalNoUnifyToGeneralAllHooksCapstoneSlices_proved h_no h_ok)

/--
One-hop expression projection from no-unify-to-general all-hooks run-bundle
slices.
-/
theorem principalNoUnifyToGeneralAllHooksRunBundleSlices_expr
    (h_slice : PrincipalNoUnifyToGeneralAllHooksRunBundleSlices)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalPreconditionedExprAllHooksRunBundle st fuel env e st' ty :=
  h_slice.1 h_no h_ok

/--
One-hop field projection from no-unify-to-general all-hooks run-bundle slices.
-/
theorem principalNoUnifyToGeneralAllHooksRunBundleSlices_field
    (h_slice : PrincipalNoUnifyToGeneralAllHooksRunBundleSlices)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalPreconditionedFieldAllHooksRunBundle st fuel env fs st' rf :=
  h_slice.2 h_no h_ok

/--
Packaged no-unify-to-general expression hook-irrelevance slice.
-/
def PrincipalNoUnifyToGeneralAllHooksExprIrrelevanceSlice : Prop :=
  ∀ {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
    {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook},
    NoUnifyBranchesExpr e →
    inferExprUnify st fuel env e = .ok st' ty →
    (PrincipalTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env e st' ty
      ↔ PrincipalTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env e st' ty)

/--
Packaged no-unify-to-general field hook-irrelevance slice.
-/
def PrincipalNoUnifyToGeneralAllHooksFieldIrrelevanceSlice : Prop :=
  ∀ {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
    {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook},
    NoUnifyBranchesFields fs →
    inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)) →
    (PrincipalFieldTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env fs st' rf
      ↔ PrincipalFieldTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env fs st' rf)

/--
Combined no-unify-to-general all-hooks irrelevance slices across expressions and
fields.
-/
def PrincipalNoUnifyToGeneralAllHooksIrrelevanceSlices : Prop :=
  PrincipalNoUnifyToGeneralAllHooksExprIrrelevanceSlice ∧
    PrincipalNoUnifyToGeneralAllHooksFieldIrrelevanceSlice

/--
The combined no-unify-to-general all-hooks irrelevance slices are fully proved.
-/
theorem principalNoUnifyToGeneralAllHooksIrrelevanceSlices_proved :
    PrincipalNoUnifyToGeneralAllHooksIrrelevanceSlices := by
  refine ⟨?_, ?_⟩
  · intro st fuel env e st' ty h_app₁ h_proj₁ h_app₂ h_proj₂ h_no h_ok
    exact principalPreconditionedExpr_hookIrrelevant_of_success_noUnify_via_generalAllHooks
      h_no h_ok
  · intro st fuel env fs st' rf h_app₁ h_proj₁ h_app₂ h_proj₂ h_no h_ok
    exact principalPreconditionedField_hookIrrelevant_of_success_noUnify_via_generalAllHooks
      h_no h_ok

/--
One-hop projection: expression branch from no-unify-to-general all-hooks
irrelevance slices.
-/
theorem principalNoUnifyToGeneralAllHooksIrrelevanceSlices_expr
    (h_slice : PrincipalNoUnifyToGeneralAllHooksIrrelevanceSlices)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
    {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    (PrincipalTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env e st' ty
      ↔ PrincipalTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env e st' ty) :=
  h_slice.1 h_no h_ok

/--
One-hop projection: field branch from no-unify-to-general all-hooks irrelevance
slices.
-/
theorem principalNoUnifyToGeneralAllHooksIrrelevanceSlices_field
    (h_slice : PrincipalNoUnifyToGeneralAllHooksIrrelevanceSlices)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
    {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    (PrincipalFieldTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env fs st' rf
      ↔ PrincipalFieldTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env fs st' rf) :=
  h_slice.2 h_no h_ok

/--
Top-level no-unify-to-general all-hooks suite.
-/
structure PrincipalNoUnifyToGeneralAllHooksSuite : Prop where
  capstones : PrincipalNoUnifyToGeneralAllHooksCapstoneSlices
  runBundles : PrincipalNoUnifyToGeneralAllHooksRunBundleSlices
  irrelevance : PrincipalNoUnifyToGeneralAllHooksIrrelevanceSlices

/--
The no-unify-to-general all-hooks suite is fully proved.
-/
theorem principalNoUnifyToGeneralAllHooksSuite_proved :
    PrincipalNoUnifyToGeneralAllHooksSuite := by
  refine {
    capstones := principalNoUnifyToGeneralAllHooksCapstoneSlices_proved
    runBundles := principalNoUnifyToGeneralAllHooksRunBundleSlices_proved
    irrelevance := principalNoUnifyToGeneralAllHooksIrrelevanceSlices_proved
  }

/--
One-hop expression capstone projection from no-unify-to-general all-hooks
suite.
-/
theorem principalNoUnifyToGeneralAllHooksSuite_capstone_expr
    (h_suite : PrincipalNoUnifyToGeneralAllHooksSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalPreconditionedExprAllHooksCapstone st fuel env e st' ty :=
  principalNoUnifyToGeneralAllHooksCapstoneSlices_expr h_suite.capstones h_no h_ok

/--
One-hop field capstone projection from no-unify-to-general all-hooks suite.
-/
theorem principalNoUnifyToGeneralAllHooksSuite_capstone_field
    (h_suite : PrincipalNoUnifyToGeneralAllHooksSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalPreconditionedFieldAllHooksCapstone st fuel env fs st' rf :=
  principalNoUnifyToGeneralAllHooksCapstoneSlices_field h_suite.capstones h_no h_ok

/--
One-hop expression run-bundle projection from no-unify-to-general all-hooks
suite.
-/
theorem principalNoUnifyToGeneralAllHooksSuite_runBundle_expr
    (h_suite : PrincipalNoUnifyToGeneralAllHooksSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalPreconditionedExprAllHooksRunBundle st fuel env e st' ty :=
  principalNoUnifyToGeneralAllHooksRunBundleSlices_expr h_suite.runBundles h_no h_ok

/--
One-hop field run-bundle projection from no-unify-to-general all-hooks suite.
-/
theorem principalNoUnifyToGeneralAllHooksSuite_runBundle_field
    (h_suite : PrincipalNoUnifyToGeneralAllHooksSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalPreconditionedFieldAllHooksRunBundle st fuel env fs st' rf :=
  principalNoUnifyToGeneralAllHooksRunBundleSlices_field h_suite.runBundles h_no h_ok

/--
No-unify-to-general suite convenience wrapper: derive the expression run-bundle
surface from a successful no-unify run.
-/
theorem principalNoUnifyToGeneralRunBundleExpr_of_success
    (h_suite : PrincipalNoUnifyToGeneralAllHooksSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalPreconditionedExprAllHooksRunBundle st fuel env e st' ty :=
  principalNoUnifyToGeneralAllHooksSuite_runBundle_expr h_suite h_no h_ok

/--
No-unify-to-general suite convenience wrapper: derive the field run-bundle
surface from a successful no-unify field run.
-/
theorem principalNoUnifyToGeneralRunBundleField_of_success
    (h_suite : PrincipalNoUnifyToGeneralAllHooksSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalPreconditionedFieldAllHooksRunBundle st fuel env fs st' rf :=
  principalNoUnifyToGeneralAllHooksSuite_runBundle_field h_suite h_no h_ok

/--
One-hop expression irrelevance projection from no-unify-to-general all-hooks
suite.
-/
theorem principalNoUnifyToGeneralAllHooksSuite_irrelevance_expr
    (h_suite : PrincipalNoUnifyToGeneralAllHooksSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
    {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    (PrincipalTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env e st' ty
      ↔ PrincipalTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env e st' ty) :=
  principalNoUnifyToGeneralAllHooksIrrelevanceSlices_expr
    h_suite.irrelevance h_no h_ok

/--
One-hop field irrelevance projection from no-unify-to-general all-hooks suite.
-/
theorem principalNoUnifyToGeneralAllHooksSuite_irrelevance_field
    (h_suite : PrincipalNoUnifyToGeneralAllHooksSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
    {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    (PrincipalFieldTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env fs st' rf
      ↔ PrincipalFieldTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env fs st' rf) :=
  principalNoUnifyToGeneralAllHooksIrrelevanceSlices_field
    h_suite.irrelevance h_no h_ok

/--
No-unify-to-general suite convenience wrapper: derive core expression
principality from a successful no-unify expression run.
-/
theorem principalNoUnifyToGeneralCoreExpr_of_success
    (h_suite : PrincipalNoUnifyToGeneralAllHooksSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalTypingSliceCore env e ty :=
  (principalNoUnifyToGeneralAllHooksSuite_capstone_expr
    h_suite h_no h_ok).core

/--
No-unify-to-general suite convenience wrapper: derive preconditioned expression
principality for any hook witnesses from a successful no-unify run.
-/
theorem principalNoUnifyToGeneralPreconditionedExpr_anyHooks_of_success
    (h_suite : PrincipalNoUnifyToGeneralAllHooksSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    ∀ h_app h_proj,
      PrincipalTypingSlicePreconditioned h_app h_proj st fuel env e st' ty :=
  (principalNoUnifyToGeneralAllHooksSuite_capstone_expr
    h_suite h_no h_ok).preconditionedAny

/--
No-unify-to-general suite convenience wrapper: derive preconditioned expression
principality for a bundled hook witness from a successful no-unify run.
-/
theorem principalNoUnifyToGeneralPreconditionedExpr_of_success
    (h_suite : PrincipalNoUnifyToGeneralAllHooksSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty)
    (h_hooks : UnifyHookPremises) :
    PrincipalTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env e st' ty :=
  (principalNoUnifyToGeneralPreconditionedExpr_anyHooks_of_success
    h_suite h_no h_ok) h_hooks.1 h_hooks.2

/--
No-unify-to-general suite convenience wrapper: derive fixed-run expression
preconditioned↔core equivalence for any hook witnesses.
-/
theorem principalNoUnifyToGeneralPreconditionedCoreIffExpr_anyHooks_of_success
    (h_suite : PrincipalNoUnifyToGeneralAllHooksSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    ∀ h_app h_proj,
      (PrincipalTypingSlicePreconditioned h_app h_proj st fuel env e st' ty
        ↔ PrincipalTypingSliceCore env e ty) :=
  (principalNoUnifyToGeneralAllHooksSuite_capstone_expr
    h_suite h_no h_ok).preconditionedAnyIffCore

/--
No-unify-to-general suite convenience wrapper: derive fixed-run expression
preconditioned↔core equivalence for a bundled hook witness.
-/
theorem principalNoUnifyToGeneralPreconditionedCoreIffExpr_of_success
    (h_suite : PrincipalNoUnifyToGeneralAllHooksSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty)
    (h_hooks : UnifyHookPremises) :
    (PrincipalTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env e st' ty
      ↔ PrincipalTypingSliceCore env e ty) :=
  (principalNoUnifyToGeneralPreconditionedCoreIffExpr_anyHooks_of_success
    h_suite h_no h_ok) h_hooks.1 h_hooks.2

/--
No-unify-to-general suite convenience wrapper: derive fixed-run expression
hook-irrelevance from a successful no-unify run.
-/
theorem principalNoUnifyToGeneralPreconditionedExpr_hookIrrelevant_of_success
    (h_suite : PrincipalNoUnifyToGeneralAllHooksSuite)
    {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
    {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook}
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    (PrincipalTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env e st' ty
      ↔ PrincipalTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env e st' ty) :=
  principalNoUnifyToGeneralAllHooksSuite_irrelevance_expr
    h_suite h_no h_ok

/--
No-unify-to-general suite convenience wrapper: derive core field principality
from a successful no-unify field run.
-/
theorem principalNoUnifyToGeneralCoreField_of_success
    (h_suite : PrincipalNoUnifyToGeneralAllHooksSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalFieldTypingSliceCore env fs rf :=
  (principalNoUnifyToGeneralAllHooksSuite_capstone_field
    h_suite h_no h_ok).core

/--
No-unify-to-general suite convenience wrapper: derive preconditioned field
principality for any hook witnesses from a successful no-unify field run.
-/
theorem principalNoUnifyToGeneralPreconditionedField_anyHooks_of_success
    (h_suite : PrincipalNoUnifyToGeneralAllHooksSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    ∀ h_app h_proj,
      PrincipalFieldTypingSlicePreconditioned h_app h_proj st fuel env fs st' rf :=
  (principalNoUnifyToGeneralAllHooksSuite_capstone_field
    h_suite h_no h_ok).preconditionedAny

/--
No-unify-to-general suite convenience wrapper: derive preconditioned field
principality for a bundled hook witness from a successful no-unify field run.
-/
theorem principalNoUnifyToGeneralPreconditionedField_of_success
    (h_suite : PrincipalNoUnifyToGeneralAllHooksSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)))
    (h_hooks : UnifyHookPremises) :
    PrincipalFieldTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env fs st' rf :=
  (principalNoUnifyToGeneralPreconditionedField_anyHooks_of_success
    h_suite h_no h_ok) h_hooks.1 h_hooks.2

/--
No-unify-to-general suite convenience wrapper: derive fixed-run field
preconditioned↔core equivalence for any hook witnesses.
-/
theorem principalNoUnifyToGeneralPreconditionedCoreIffField_anyHooks_of_success
    (h_suite : PrincipalNoUnifyToGeneralAllHooksSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    ∀ h_app h_proj,
      (PrincipalFieldTypingSlicePreconditioned h_app h_proj st fuel env fs st' rf
        ↔ PrincipalFieldTypingSliceCore env fs rf) :=
  (principalNoUnifyToGeneralAllHooksSuite_capstone_field
    h_suite h_no h_ok).preconditionedAnyIffCore

/--
No-unify-to-general suite convenience wrapper: derive fixed-run field
preconditioned↔core equivalence for a bundled hook witness.
-/
theorem principalNoUnifyToGeneralPreconditionedCoreIffField_of_success
    (h_suite : PrincipalNoUnifyToGeneralAllHooksSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)))
    (h_hooks : UnifyHookPremises) :
    (PrincipalFieldTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env fs st' rf
      ↔ PrincipalFieldTypingSliceCore env fs rf) :=
  (principalNoUnifyToGeneralPreconditionedCoreIffField_anyHooks_of_success
    h_suite h_no h_ok) h_hooks.1 h_hooks.2

/--
No-unify-to-general suite convenience wrapper: derive fixed-run field
hook-irrelevance from a successful no-unify field run.
-/
theorem principalNoUnifyToGeneralPreconditionedField_hookIrrelevant_of_success
    (h_suite : PrincipalNoUnifyToGeneralAllHooksSuite)
    {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
    {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook}
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    (PrincipalFieldTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env fs st' rf
      ↔ PrincipalFieldTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env fs st' rf) :=
  principalNoUnifyToGeneralAllHooksSuite_irrelevance_field
    h_suite h_no h_ok

/--
Convert a general successful-run all-hooks expression capstone into the
no-unify all-hooks expression capstone shape.
-/
theorem principalBoundaryNoUnifyExprAllHooksCapstone_of_generalAllHooks
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_cap : PrincipalPreconditionedExprAllHooksCapstone st fuel env e st' ty) :
    PrincipalBoundaryNoUnifyExprAllHooksCapstone st fuel env e st' ty := by
  refine {
    core := h_cap.core
    preconditionedAny := h_cap.preconditionedAny
    preconditionedAnyIffCore := h_cap.preconditionedAnyIffCore
  }

/--
Convert a general successful-run all-hooks field capstone into the
no-unify all-hooks field capstone shape.
-/
theorem principalBoundaryNoUnifyFieldAllHooksCapstone_of_generalAllHooks
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_cap : PrincipalPreconditionedFieldAllHooksCapstone st fuel env fs st' rf) :
    PrincipalBoundaryNoUnifyFieldAllHooksCapstone st fuel env fs st' rf := by
  refine {
    core := h_cap.core
    preconditionedAny := h_cap.preconditionedAny
    preconditionedAnyIffCore := h_cap.preconditionedAnyIffCore
  }

/--
Derive no-unify-to-general run-bundle slices from a no-unify all-hooks suite.
-/
theorem principalNoUnifyToGeneralAllHooksRunBundleSlices_of_noUnifyAllHooksSuite
    (h_suite : PrincipalBoundaryNoUnifyAllHooksSuite) :
    PrincipalNoUnifyToGeneralAllHooksRunBundleSlices := by
  refine ⟨?_, ?_⟩
  · intro st fuel env e st' ty h_no h_ok
    exact principalBoundaryNoUnifyAllHooksSuite_runBundle_expr
      h_suite h_no h_ok
  · intro st fuel env fs st' rf h_no h_ok
    exact principalBoundaryNoUnifyAllHooksSuite_runBundle_field
      h_suite h_no h_ok

/--
Derive no-unify all-hooks run-bundle slices from a no-unify-to-general suite.
-/
theorem principalBoundaryNoUnifyAllHooksRunBundleSlices_of_noUnifyToGeneralAllHooksSuite
    (h_suite : PrincipalNoUnifyToGeneralAllHooksSuite) :
    PrincipalBoundaryNoUnifyAllHooksRunBundleSlices := by
  refine ⟨?_, ?_⟩
  · intro st fuel env e st' ty h_no h_ok
    exact principalNoUnifyToGeneralAllHooksSuite_runBundle_expr
      h_suite h_no h_ok
  · intro st fuel env fs st' rf h_no h_ok
    exact principalNoUnifyToGeneralAllHooksSuite_runBundle_field
      h_suite h_no h_ok

/--
Canonical no-unify-to-general run-bundle slices derived from the proved no-unify
all-hooks suite.
-/
theorem principalNoUnifyToGeneralAllHooksRunBundleSlices_proved_via_noUnifyAllHooks :
    PrincipalNoUnifyToGeneralAllHooksRunBundleSlices :=
  principalNoUnifyToGeneralAllHooksRunBundleSlices_of_noUnifyAllHooksSuite
    principalBoundaryNoUnifyAllHooksSuite_proved

/--
Canonical no-unify all-hooks run-bundle slices derived from the proved
no-unify-to-general all-hooks suite.
-/
theorem principalBoundaryNoUnifyAllHooksRunBundleSlices_proved_via_noUnifyToGeneral :
    PrincipalBoundaryNoUnifyAllHooksRunBundleSlices :=
  principalBoundaryNoUnifyAllHooksRunBundleSlices_of_noUnifyToGeneralAllHooksSuite
    principalNoUnifyToGeneralAllHooksSuite_proved

/--
Derive the no-unify-to-general all-hooks suite from a no-unify all-hooks suite.
-/
theorem principalNoUnifyToGeneralAllHooksSuite_of_noUnifyAllHooksSuite
    (h_suite : PrincipalBoundaryNoUnifyAllHooksSuite) :
    PrincipalNoUnifyToGeneralAllHooksSuite := by
  refine {
    capstones := ?_
    runBundles := ?_
    irrelevance := ?_
  }
  · refine ⟨?_, ?_⟩
    · intro st fuel env e st' ty h_no h_ok
      exact principalBoundaryNoUnifyAllHooksSuite_capstone_expr_as_general
        h_suite h_no h_ok
    · intro st fuel env fs st' rf h_no h_ok
      exact principalBoundaryNoUnifyAllHooksSuite_capstone_field_as_general
        h_suite h_no h_ok
  · refine ⟨?_, ?_⟩
    · intro st fuel env e st' ty h_no h_ok
      exact principalPreconditionedExprAllHooksRunBundle_of_capstone
        (principalBoundaryNoUnifyAllHooksSuite_capstone_expr_as_general
          h_suite h_no h_ok)
    · intro st fuel env fs st' rf h_no h_ok
      exact principalPreconditionedFieldAllHooksRunBundle_of_capstone
        (principalBoundaryNoUnifyAllHooksSuite_capstone_field_as_general
          h_suite h_no h_ok)
  · refine ⟨?_, ?_⟩
    · intro st fuel env e st' ty h_app₁ h_proj₁ h_app₂ h_proj₂ h_no h_ok
      exact principalBoundaryNoUnifyAllHooksSuite_irrelevance_expr
        h_suite h_no h_ok
    · intro st fuel env fs st' rf h_app₁ h_proj₁ h_app₂ h_proj₂ h_no h_ok
      exact principalBoundaryNoUnifyAllHooksSuite_irrelevance_field
        h_suite h_no h_ok

/--
Derive the no-unify all-hooks suite from a no-unify-to-general all-hooks suite.
-/
theorem principalBoundaryNoUnifyAllHooksSuite_of_noUnifyToGeneralAllHooksSuite
    (h_suite : PrincipalNoUnifyToGeneralAllHooksSuite) :
    PrincipalBoundaryNoUnifyAllHooksSuite := by
  refine {
    capstones := ?_
    runBundles := ?_
    irrelevance := ?_
  }
  · refine ⟨?_, ?_⟩
    · intro st fuel env e st' ty h_no h_ok
      exact principalBoundaryNoUnifyExprAllHooksCapstone_of_generalAllHooks
        (principalNoUnifyToGeneralAllHooksSuite_capstone_expr h_suite h_no h_ok)
    · intro st fuel env fs st' rf h_no h_ok
      exact principalBoundaryNoUnifyFieldAllHooksCapstone_of_generalAllHooks
        (principalNoUnifyToGeneralAllHooksSuite_capstone_field h_suite h_no h_ok)
  · refine ⟨?_, ?_⟩
    · intro st fuel env e st' ty h_no h_ok
      exact principalNoUnifyToGeneralAllHooksSuite_runBundle_expr
        h_suite h_no h_ok
    · intro st fuel env fs st' rf h_no h_ok
      exact principalNoUnifyToGeneralAllHooksSuite_runBundle_field
        h_suite h_no h_ok
  · refine ⟨?_, ?_⟩
    · intro st fuel env e st' ty h_app₁ h_proj₁ h_app₂ h_proj₂ h_no h_ok
      exact principalNoUnifyToGeneralAllHooksSuite_irrelevance_expr
        h_suite h_no h_ok
    · intro st fuel env fs st' rf h_app₁ h_proj₁ h_app₂ h_proj₂ h_no h_ok
      exact principalNoUnifyToGeneralAllHooksSuite_irrelevance_field
        h_suite h_no h_ok

/--
Canonical derived no-unify-to-general suite from the proved no-unify all-hooks
suite.
-/
theorem principalNoUnifyToGeneralAllHooksSuite_proved_via_noUnifyAllHooks :
    PrincipalNoUnifyToGeneralAllHooksSuite :=
  principalNoUnifyToGeneralAllHooksSuite_of_noUnifyAllHooksSuite
    principalBoundaryNoUnifyAllHooksSuite_proved

/--
Canonical derived no-unify all-hooks suite from the proved no-unify-to-general
suite.
-/
theorem principalBoundaryNoUnifyAllHooksSuite_proved_via_noUnifyToGeneral :
    PrincipalBoundaryNoUnifyAllHooksSuite :=
  principalBoundaryNoUnifyAllHooksSuite_of_noUnifyToGeneralAllHooksSuite
    principalNoUnifyToGeneralAllHooksSuite_proved

/--
Convert an all-hooks expression capstone into a hook-specific no-unify
expression capstone by selecting concrete hook witnesses.
-/
theorem principalBoundaryNoUnifyExprCapstone_of_allHooks
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_cap : PrincipalBoundaryNoUnifyExprAllHooksCapstone st fuel env e st' ty)
    (h_app : AppUnifySoundHook) (h_proj : ProjUnifySoundHook) :
    PrincipalBoundaryNoUnifyExprCapstone h_app h_proj st fuel env e st' ty := by
  refine {
    noUnify := ?_
    preconditionedCoreIff := h_cap.preconditionedAnyIffCore h_app h_proj
  }
  refine {
    core := h_cap.core
    preconditioned := h_cap.preconditionedAny h_app h_proj
  }

/--
Convert an all-hooks field capstone into a hook-specific no-unify field
capstone by selecting concrete hook witnesses.
-/
theorem principalBoundaryNoUnifyFieldCapstone_of_allHooks
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_cap : PrincipalBoundaryNoUnifyFieldAllHooksCapstone st fuel env fs st' rf)
    (h_app : AppUnifySoundHook) (h_proj : ProjUnifySoundHook) :
    PrincipalBoundaryNoUnifyFieldCapstone h_app h_proj st fuel env fs st' rf := by
  refine {
    noUnify := ?_
    preconditionedCoreIff := h_cap.preconditionedAnyIffCore h_app h_proj
  }
  refine {
    core := h_cap.core
    preconditioned := h_cap.preconditionedAny h_app h_proj
  }

/--
Derive the hook-specific no-unify capstone slices from the all-hooks no-unify
capstone slices.
-/
theorem principalBoundaryNoUnifyCapstoneSlices_of_allHooksCapstones
    (h_all : PrincipalBoundaryNoUnifyAllHooksCapstoneSlices) :
    PrincipalBoundaryNoUnifyCapstoneSlices := by
  refine ⟨?_, ?_⟩
  · intro st fuel env e st' ty h_no h_ok h_hooks
    exact principalBoundaryNoUnifyExprCapstone_of_allHooks
      (principalBoundaryNoUnifyAllHooksCapstoneSlices_expr h_all h_no h_ok)
      h_hooks.1 h_hooks.2
  · intro st fuel env fs st' rf h_no h_ok h_hooks
    exact principalBoundaryNoUnifyFieldCapstone_of_allHooks
      (principalBoundaryNoUnifyAllHooksCapstoneSlices_field h_all h_no h_ok)
      h_hooks.1 h_hooks.2

/--
Derive the hook-specific no-unify capstone slices directly from the proved
all-hooks suite.
-/
theorem principalBoundaryNoUnifyCapstoneSlices_of_allHooksSuite :
    PrincipalBoundaryNoUnifyCapstoneSlices :=
  principalBoundaryNoUnifyCapstoneSlices_of_allHooksCapstones
    principalBoundaryNoUnifyAllHooksSuite_proved.capstones

/--
Top-level principal boundary master suite.

This aggregates the current M4 theorem surfaces:
- successful-run bridge suite (core↔preconditioned and no-unify bundles),
- vacuity suite (no-unify + fixed-run hook-irrelevance), and
- general successful-run all-hooks suite, and
- no-unify all-hooks suite (+ compatibility back to hook-specific capstones),
- and no-unify-to-general all-hooks bridge suite.
-/
structure PrincipalBoundaryMasterSuite : Prop where
  bridge : PrincipalBoundaryBridgeSuite
  vacuity : PrincipalBoundaryVacuitySuite
  allHooks : PrincipalPreconditionedAllHooksSuite
  noUnifyAllHooks : PrincipalBoundaryNoUnifyAllHooksSuite
  noUnifyHookedFromAllHooks : PrincipalBoundaryNoUnifyCapstoneSlices
  noUnifyToGeneralAllHooks : PrincipalNoUnifyToGeneralAllHooksSuite

/-- The principal boundary master suite is fully proved. -/
theorem principalBoundaryMasterSuite_proved : PrincipalBoundaryMasterSuite := by
  refine {
    bridge := principalBoundaryBridgeSuite_proved
    vacuity := principalBoundaryVacuitySuite_proved
    allHooks := principalPreconditionedAllHooksSuite_proved
    noUnifyAllHooks := principalBoundaryNoUnifyAllHooksSuite_proved
    noUnifyHookedFromAllHooks := principalBoundaryNoUnifyCapstoneSlices_of_allHooksSuite
    noUnifyToGeneralAllHooks := principalNoUnifyToGeneralAllHooksSuite_proved_via_noUnifyAllHooks
  }

/--
One-hop expression successful-run preconditioned↔core equivalence from the
master suite.
-/
theorem principalBoundaryMasterSuite_preconditionedCoreIff_expr
    (h_suite : PrincipalBoundaryMasterSuite)
    (h_hooks : UnifyHookPremises)
    (st : UnifyState) (fuel : Nat) (env : TermEnv) (e : CoreExpr)
    (st' : UnifyState) (ty : Ty)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    (PrincipalTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env e st' ty
      ↔ PrincipalTypingSliceCore env e ty) :=
  principalBoundaryBridgeSuite_preconditionedCoreIff_expr
    h_suite.bridge h_hooks st fuel env e st' ty h_ok

/--
One-hop field successful-run preconditioned↔core equivalence from the master
suite.
-/
theorem principalBoundaryMasterSuite_preconditionedCoreIff_field
    (h_suite : PrincipalBoundaryMasterSuite)
    (h_hooks : UnifyHookPremises)
    (st : UnifyState) (fuel : Nat) (env : TermEnv) (fs : CoreFields)
    (st' : UnifyState) (rf : RowFields)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    (PrincipalFieldTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env fs st' rf
      ↔ PrincipalFieldTypingSliceCore env fs rf) :=
  principalBoundaryBridgeSuite_preconditionedCoreIff_field
    h_suite.bridge h_hooks st fuel env fs st' rf h_ok

/-- One-hop expression hook-irrelevance projection from master suite. -/
theorem principalBoundaryMasterSuite_hookIrrelevance_expr
    (h_suite : PrincipalBoundaryMasterSuite)
    {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
    {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook}
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    (PrincipalTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env e st' ty
      ↔ PrincipalTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env e st' ty) :=
  principalPreconditionedHookIrrelevanceSlices_expr
    h_suite.vacuity.hookIrrelevance h_ok

/-- One-hop field hook-irrelevance projection from master suite. -/
theorem principalBoundaryMasterSuite_hookIrrelevance_field
    (h_suite : PrincipalBoundaryMasterSuite)
    {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
    {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook}
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    (PrincipalFieldTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env fs st' rf
      ↔ PrincipalFieldTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env fs st' rf) :=
  principalPreconditionedHookIrrelevanceSlices_field
    h_suite.vacuity.hookIrrelevance h_ok

/-- One-hop expression general all-hooks capstone projection from master suite. -/
theorem principalBoundaryMasterSuite_allHooks_expr
    (h_suite : PrincipalBoundaryMasterSuite)
    (h_app0 : AppUnifySoundHook) (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalPreconditionedExprAllHooksCapstone st fuel env e st' ty :=
  principalPreconditionedAllHooksSuite_capstone_expr
    h_suite.allHooks h_app0 h_proj0 h_ok

/-- One-hop field general all-hooks capstone projection from master suite. -/
theorem principalBoundaryMasterSuite_allHooks_field
    (h_suite : PrincipalBoundaryMasterSuite)
    (h_app0 : AppUnifySoundHook) (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalPreconditionedFieldAllHooksCapstone st fuel env fs st' rf :=
  principalPreconditionedAllHooksSuite_capstone_field
    h_suite.allHooks h_app0 h_proj0 h_ok

/-- One-hop expression general all-hooks run-bundle projection from master suite. -/
theorem principalBoundaryMasterSuite_allHooks_runBundle_expr
    (h_suite : PrincipalBoundaryMasterSuite)
    (h_app0 : AppUnifySoundHook) (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalPreconditionedExprAllHooksRunBundle st fuel env e st' ty :=
  principalPreconditionedAllHooksSuite_runBundle_expr
    h_suite.allHooks h_app0 h_proj0 h_ok

/-- One-hop field general all-hooks run-bundle projection from master suite. -/
theorem principalBoundaryMasterSuite_allHooks_runBundle_field
    (h_suite : PrincipalBoundaryMasterSuite)
    (h_app0 : AppUnifySoundHook) (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalPreconditionedFieldAllHooksRunBundle st fuel env fs st' rf :=
  principalPreconditionedAllHooksSuite_runBundle_field
    h_suite.allHooks h_app0 h_proj0 h_ok

/-- One-hop expression all-hooks no-unify capstone projection from master suite. -/
theorem principalBoundaryMasterSuite_noUnifyAllHooks_expr
    (h_suite : PrincipalBoundaryMasterSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalBoundaryNoUnifyExprAllHooksCapstone st fuel env e st' ty :=
  principalBoundaryNoUnifyAllHooksSuite_capstone_expr
    h_suite.noUnifyAllHooks h_no h_ok

/-- One-hop field all-hooks no-unify capstone projection from master suite. -/
theorem principalBoundaryMasterSuite_noUnifyAllHooks_field
    (h_suite : PrincipalBoundaryMasterSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalBoundaryNoUnifyFieldAllHooksCapstone st fuel env fs st' rf :=
  principalBoundaryNoUnifyAllHooksSuite_capstone_field
    h_suite.noUnifyAllHooks h_no h_ok

/-- One-hop expression all-hooks no-unify run-bundle projection from master suite. -/
theorem principalBoundaryMasterSuite_noUnifyAllHooks_runBundle_expr
    (h_suite : PrincipalBoundaryMasterSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalPreconditionedExprAllHooksRunBundle st fuel env e st' ty :=
  principalBoundaryNoUnifyAllHooksSuite_runBundle_expr
    h_suite.noUnifyAllHooks h_no h_ok

/-- One-hop field all-hooks no-unify run-bundle projection from master suite. -/
theorem principalBoundaryMasterSuite_noUnifyAllHooks_runBundle_field
    (h_suite : PrincipalBoundaryMasterSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalPreconditionedFieldAllHooksRunBundle st fuel env fs st' rf :=
  principalBoundaryNoUnifyAllHooksSuite_runBundle_field
    h_suite.noUnifyAllHooks h_no h_ok

/--
One-hop expression no-unify-to-general all-hooks capstone projection from
master suite.
-/
theorem principalBoundaryMasterSuite_noUnifyToGeneralAllHooks_expr
    (h_suite : PrincipalBoundaryMasterSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalPreconditionedExprAllHooksCapstone st fuel env e st' ty :=
  principalNoUnifyToGeneralAllHooksSuite_capstone_expr
    h_suite.noUnifyToGeneralAllHooks h_no h_ok

/--
One-hop field no-unify-to-general all-hooks capstone projection from master
suite.
-/
theorem principalBoundaryMasterSuite_noUnifyToGeneralAllHooks_field
    (h_suite : PrincipalBoundaryMasterSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalPreconditionedFieldAllHooksCapstone st fuel env fs st' rf :=
  principalNoUnifyToGeneralAllHooksSuite_capstone_field
    h_suite.noUnifyToGeneralAllHooks h_no h_ok

/--
One-hop expression no-unify-to-general all-hooks run-bundle projection from
master suite.
-/
theorem principalBoundaryMasterSuite_noUnifyToGeneralAllHooks_runBundle_expr
    (h_suite : PrincipalBoundaryMasterSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalPreconditionedExprAllHooksRunBundle st fuel env e st' ty :=
  principalNoUnifyToGeneralAllHooksSuite_runBundle_expr
    h_suite.noUnifyToGeneralAllHooks h_no h_ok

/--
One-hop field no-unify-to-general all-hooks run-bundle projection from master
suite.
-/
theorem principalBoundaryMasterSuite_noUnifyToGeneralAllHooks_runBundle_field
    (h_suite : PrincipalBoundaryMasterSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalPreconditionedFieldAllHooksRunBundle st fuel env fs st' rf :=
  principalNoUnifyToGeneralAllHooksSuite_runBundle_field
    h_suite.noUnifyToGeneralAllHooks h_no h_ok

/--
One-hop expression no-unify-to-general all-hooks irrelevance projection from
master suite.
-/
theorem principalBoundaryMasterSuite_noUnifyToGeneralAllHooks_irrelevance_expr
    (h_suite : PrincipalBoundaryMasterSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
    {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    (PrincipalTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env e st' ty
      ↔ PrincipalTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env e st' ty) :=
  principalNoUnifyToGeneralAllHooksSuite_irrelevance_expr
    h_suite.noUnifyToGeneralAllHooks h_no h_ok

/--
One-hop field no-unify-to-general all-hooks irrelevance projection from master
suite.
-/
theorem principalBoundaryMasterSuite_noUnifyToGeneralAllHooks_irrelevance_field
    (h_suite : PrincipalBoundaryMasterSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
    {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    (PrincipalFieldTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env fs st' rf
      ↔ PrincipalFieldTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env fs st' rf) :=
  principalNoUnifyToGeneralAllHooksSuite_irrelevance_field
    h_suite.noUnifyToGeneralAllHooks h_no h_ok

/--
One-hop expression no-unify-as-general all-hooks projection from master suite.
-/
theorem principalBoundaryMasterSuite_noUnifyAllHooks_expr_as_general
    (h_suite : PrincipalBoundaryMasterSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalPreconditionedExprAllHooksCapstone st fuel env e st' ty :=
  principalBoundaryMasterSuite_noUnifyToGeneralAllHooks_expr h_suite h_no h_ok

/--
One-hop field no-unify-as-general all-hooks projection from master suite.
-/
theorem principalBoundaryMasterSuite_noUnifyAllHooks_field_as_general
    (h_suite : PrincipalBoundaryMasterSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalPreconditionedFieldAllHooksCapstone st fuel env fs st' rf :=
  principalBoundaryMasterSuite_noUnifyToGeneralAllHooks_field h_suite h_no h_ok

/--
One-hop expression no-unify-as-general all-hooks run-bundle projection from
master suite.
-/
theorem principalBoundaryMasterSuite_noUnifyAllHooks_runBundle_expr_as_general
    (h_suite : PrincipalBoundaryMasterSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalPreconditionedExprAllHooksRunBundle st fuel env e st' ty :=
  principalBoundaryMasterSuite_noUnifyToGeneralAllHooks_runBundle_expr h_suite h_no h_ok

/--
One-hop field no-unify-as-general all-hooks run-bundle projection from master
suite.
-/
theorem principalBoundaryMasterSuite_noUnifyAllHooks_runBundle_field_as_general
    (h_suite : PrincipalBoundaryMasterSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalPreconditionedFieldAllHooksRunBundle st fuel env fs st' rf :=
  principalBoundaryMasterSuite_noUnifyToGeneralAllHooks_runBundle_field h_suite h_no h_ok

/--
Top-level master run-bundle suite.

This packages all run-bundle entry surfaces currently exposed through
`PrincipalBoundaryMasterSuite`:
- arbitrary successful all-hooks runs,
- successful no-unify all-hooks runs,
- and successful no-unify-to-general all-hooks runs.
-/
structure PrincipalBoundaryMasterRunBundleSuite : Prop where
  allHooksExpr :
    ∀ (_h_app0 : AppUnifySoundHook) (_h_proj0 : ProjUnifySoundHook)
      {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
      {st' : UnifyState} {ty : Ty},
      inferExprUnify st fuel env e = .ok st' ty →
      PrincipalPreconditionedExprAllHooksRunBundle st fuel env e st' ty
  allHooksField :
    ∀ (_h_app0 : AppUnifySoundHook) (_h_proj0 : ProjUnifySoundHook)
      {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
      {st' : UnifyState} {rf : RowFields},
      inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)) →
      PrincipalPreconditionedFieldAllHooksRunBundle st fuel env fs st' rf
  noUnifyAllHooksExpr :
    ∀ {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
      {st' : UnifyState} {ty : Ty},
      NoUnifyBranchesExpr e →
      inferExprUnify st fuel env e = .ok st' ty →
      PrincipalPreconditionedExprAllHooksRunBundle st fuel env e st' ty
  noUnifyAllHooksField :
    ∀ {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
      {st' : UnifyState} {rf : RowFields},
      NoUnifyBranchesFields fs →
      inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)) →
      PrincipalPreconditionedFieldAllHooksRunBundle st fuel env fs st' rf
  noUnifyToGeneralExpr :
    ∀ {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
      {st' : UnifyState} {ty : Ty},
      NoUnifyBranchesExpr e →
      inferExprUnify st fuel env e = .ok st' ty →
      PrincipalPreconditionedExprAllHooksRunBundle st fuel env e st' ty
  noUnifyToGeneralField :
    ∀ {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
      {st' : UnifyState} {rf : RowFields},
      NoUnifyBranchesFields fs →
      inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)) →
      PrincipalPreconditionedFieldAllHooksRunBundle st fuel env fs st' rf

/--
Construct the master run-bundle suite from a master principal-boundary suite.
-/
theorem principalBoundaryMasterRunBundleSuite_of_master
    (h_suite : PrincipalBoundaryMasterSuite) :
    PrincipalBoundaryMasterRunBundleSuite := by
  refine {
    allHooksExpr := ?_
    allHooksField := ?_
    noUnifyAllHooksExpr := ?_
    noUnifyAllHooksField := ?_
    noUnifyToGeneralExpr := ?_
    noUnifyToGeneralField := ?_
  }
  · intro h_app0 h_proj0 st fuel env e st' ty h_ok
    exact principalBoundaryMasterSuite_allHooks_runBundle_expr
      h_suite h_app0 h_proj0 h_ok
  · intro h_app0 h_proj0 st fuel env fs st' rf h_ok
    exact principalBoundaryMasterSuite_allHooks_runBundle_field
      h_suite h_app0 h_proj0 h_ok
  · intro st fuel env e st' ty h_no h_ok
    exact principalBoundaryMasterSuite_noUnifyAllHooks_runBundle_expr
      h_suite h_no h_ok
  · intro st fuel env fs st' rf h_no h_ok
    exact principalBoundaryMasterSuite_noUnifyAllHooks_runBundle_field
      h_suite h_no h_ok
  · intro st fuel env e st' ty h_no h_ok
    exact principalBoundaryMasterSuite_noUnifyToGeneralAllHooks_runBundle_expr
      h_suite h_no h_ok
  · intro st fuel env fs st' rf h_no h_ok
    exact principalBoundaryMasterSuite_noUnifyToGeneralAllHooks_runBundle_field
      h_suite h_no h_ok

/-- The master run-bundle suite is fully proved. -/
theorem principalBoundaryMasterRunBundleSuite_proved :
    PrincipalBoundaryMasterRunBundleSuite :=
  principalBoundaryMasterRunBundleSuite_of_master principalBoundaryMasterSuite_proved

/--
One-hop projection: arbitrary-success all-hooks expression run-bundle from the
master run-bundle suite.
-/
theorem principalBoundaryMasterRunBundleSuite_allHooks_expr
    (h_suite : PrincipalBoundaryMasterRunBundleSuite)
    (h_app0 : AppUnifySoundHook) (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalPreconditionedExprAllHooksRunBundle st fuel env e st' ty :=
  h_suite.allHooksExpr h_app0 h_proj0 h_ok

/--
One-hop projection: arbitrary-success all-hooks field run-bundle from the
master run-bundle suite.
-/
theorem principalBoundaryMasterRunBundleSuite_allHooks_field
    (h_suite : PrincipalBoundaryMasterRunBundleSuite)
    (h_app0 : AppUnifySoundHook) (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalPreconditionedFieldAllHooksRunBundle st fuel env fs st' rf :=
  h_suite.allHooksField h_app0 h_proj0 h_ok

/--
One-hop projection: successful no-unify all-hooks expression run-bundle from
the master run-bundle suite.
-/
theorem principalBoundaryMasterRunBundleSuite_noUnifyAllHooks_expr
    (h_suite : PrincipalBoundaryMasterRunBundleSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalPreconditionedExprAllHooksRunBundle st fuel env e st' ty :=
  h_suite.noUnifyAllHooksExpr h_no h_ok

/--
One-hop projection: successful no-unify all-hooks field run-bundle from the
master run-bundle suite.
-/
theorem principalBoundaryMasterRunBundleSuite_noUnifyAllHooks_field
    (h_suite : PrincipalBoundaryMasterRunBundleSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalPreconditionedFieldAllHooksRunBundle st fuel env fs st' rf :=
  h_suite.noUnifyAllHooksField h_no h_ok

/--
One-hop projection: successful no-unify-to-general expression run-bundle from
the master run-bundle suite.
-/
theorem principalBoundaryMasterRunBundleSuite_noUnifyToGeneral_expr
    (h_suite : PrincipalBoundaryMasterRunBundleSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalPreconditionedExprAllHooksRunBundle st fuel env e st' ty :=
  h_suite.noUnifyToGeneralExpr h_no h_ok

/--
One-hop projection: successful no-unify-to-general field run-bundle from the
master run-bundle suite.
-/
theorem principalBoundaryMasterRunBundleSuite_noUnifyToGeneral_field
    (h_suite : PrincipalBoundaryMasterRunBundleSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalPreconditionedFieldAllHooksRunBundle st fuel env fs st' rf :=
  h_suite.noUnifyToGeneralField h_no h_ok

/--
Coherence wrapper: view the no-unify all-hooks expression run-bundle projection
through the no-unify-to-general projection path.
-/
theorem principalBoundaryMasterRunBundleSuite_noUnify_expr_as_general
    (h_suite : PrincipalBoundaryMasterRunBundleSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalPreconditionedExprAllHooksRunBundle st fuel env e st' ty :=
  principalBoundaryMasterRunBundleSuite_noUnifyToGeneral_expr h_suite h_no h_ok

/--
Coherence wrapper: view the no-unify all-hooks field run-bundle projection
through the no-unify-to-general projection path.
-/
theorem principalBoundaryMasterRunBundleSuite_noUnify_field_as_general
    (h_suite : PrincipalBoundaryMasterRunBundleSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalPreconditionedFieldAllHooksRunBundle st fuel env fs st' rf :=
  principalBoundaryMasterRunBundleSuite_noUnifyToGeneral_field h_suite h_no h_ok

/--
Master-run-bundle-suite convenience wrapper: derive the arbitrary-success
all-hooks expression run-bundle from a baseline hook pair.
-/
theorem principalPreconditionedExprAllHooksRunBundle_of_success_via_masterRunBundleSuite
    (h_app0 : AppUnifySoundHook) (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalPreconditionedExprAllHooksRunBundle st fuel env e st' ty :=
  principalBoundaryMasterRunBundleSuite_allHooks_expr
    principalBoundaryMasterRunBundleSuite_proved h_app0 h_proj0 h_ok

/--
Master-run-bundle-suite convenience wrapper: derive the arbitrary-success
all-hooks field run-bundle from a baseline hook pair.
-/
theorem principalPreconditionedFieldAllHooksRunBundle_of_success_via_masterRunBundleSuite
    (h_app0 : AppUnifySoundHook) (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalPreconditionedFieldAllHooksRunBundle st fuel env fs st' rf :=
  principalBoundaryMasterRunBundleSuite_allHooks_field
    principalBoundaryMasterRunBundleSuite_proved h_app0 h_proj0 h_ok

/--
Master-run-bundle-suite convenience wrapper: bundle-entry variant for arbitrary
successful expression run-bundles.
-/
theorem principalPreconditionedExprAllHooksRunBundle_of_success_via_masterRunBundleSuite_from_bundle
    (h_seed : UnifyHookPremises)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalPreconditionedExprAllHooksRunBundle st fuel env e st' ty :=
  principalPreconditionedExprAllHooksRunBundle_of_success_via_masterRunBundleSuite
    h_seed.1 h_seed.2 h_ok

/--
Master-run-bundle-suite convenience wrapper: bundle-entry variant for arbitrary
successful field run-bundles.
-/
theorem principalPreconditionedFieldAllHooksRunBundle_of_success_via_masterRunBundleSuite_from_bundle
    (h_seed : UnifyHookPremises)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalPreconditionedFieldAllHooksRunBundle st fuel env fs st' rf :=
  principalPreconditionedFieldAllHooksRunBundle_of_success_via_masterRunBundleSuite
    h_seed.1 h_seed.2 h_ok

/--
Master-run-bundle-suite convenience wrapper: derive the successful no-unify
expression run-bundle surface.
-/
theorem principalPreconditionedExprAllHooksRunBundle_of_success_noUnify_via_masterRunBundleSuite
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalPreconditionedExprAllHooksRunBundle st fuel env e st' ty :=
  principalBoundaryMasterRunBundleSuite_noUnify_expr_as_general
    principalBoundaryMasterRunBundleSuite_proved h_no h_ok

/--
Master-run-bundle-suite convenience wrapper: derive the successful no-unify
field run-bundle surface.
-/
theorem principalPreconditionedFieldAllHooksRunBundle_of_success_noUnify_via_masterRunBundleSuite
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalPreconditionedFieldAllHooksRunBundle st fuel env fs st' rf :=
  principalBoundaryMasterRunBundleSuite_noUnify_field_as_general
    principalBoundaryMasterRunBundleSuite_proved h_no h_ok

/--
One-hop expression hook-specific no-unify capstone projection (derived from
all-hooks compatibility) from the master suite.
-/
theorem principalBoundaryMasterSuite_noUnifyHookedFromAllHooks_expr
    (h_suite : PrincipalBoundaryMasterSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty)
    (h_hooks : UnifyHookPremises) :
    PrincipalBoundaryNoUnifyExprCapstone
      h_hooks.1 h_hooks.2 st fuel env e st' ty :=
  principalBoundaryNoUnifyCapstoneSlices_expr
    h_suite.noUnifyHookedFromAllHooks h_no h_ok h_hooks

/--
One-hop field hook-specific no-unify capstone projection (derived from
all-hooks compatibility) from the master suite.
-/
theorem principalBoundaryMasterSuite_noUnifyHookedFromAllHooks_field
    (h_suite : PrincipalBoundaryMasterSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)))
    (h_hooks : UnifyHookPremises) :
    PrincipalBoundaryNoUnifyFieldCapstone
      h_hooks.1 h_hooks.2 st fuel env fs st' rf :=
  principalBoundaryNoUnifyCapstoneSlices_field
    h_suite.noUnifyHookedFromAllHooks h_no h_ok h_hooks

/--
Master-suite capstone wrapper: package the full expression successful-run
all-hooks principal boundary from one successful run and one baseline hook
witness pair.
-/
theorem principalPreconditionedExprAllHooksCapstone_of_success_via_masterSuite
    (h_suite : PrincipalBoundaryMasterSuite)
    (h_app0 : AppUnifySoundHook)
    (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalPreconditionedExprAllHooksCapstone st fuel env e st' ty :=
  principalPreconditionedAllHooksSuite_capstone_expr
    h_suite.allHooks h_app0 h_proj0 h_ok

/--
Master-suite capstone wrapper: package the full field successful-run all-hooks
principal boundary from one successful field run and one baseline hook witness
pair.
-/
theorem principalPreconditionedFieldAllHooksCapstone_of_success_via_masterSuite
    (h_suite : PrincipalBoundaryMasterSuite)
    (h_app0 : AppUnifySoundHook)
    (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalPreconditionedFieldAllHooksCapstone st fuel env fs st' rf :=
  principalPreconditionedAllHooksSuite_capstone_field
    h_suite.allHooks h_app0 h_proj0 h_ok

/--
Master-suite capstone wrapper: bundled-hook variant for expression successful-run
all-hooks principal boundary packaging.
-/
theorem principalPreconditionedExprAllHooksCapstone_of_success_via_masterSuite_from_bundle
    (h_suite : PrincipalBoundaryMasterSuite)
    (h_seed : UnifyHookPremises)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalPreconditionedExprAllHooksCapstone st fuel env e st' ty :=
  principalPreconditionedExprAllHooksCapstone_of_success_via_masterSuite
    h_suite h_seed.1 h_seed.2 h_ok

/--
Master-suite capstone wrapper: bundled-hook variant for field successful-run
all-hooks principal boundary packaging.
-/
theorem principalPreconditionedFieldAllHooksCapstone_of_success_via_masterSuite_from_bundle
    (h_suite : PrincipalBoundaryMasterSuite)
    (h_seed : UnifyHookPremises)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalPreconditionedFieldAllHooksCapstone st fuel env fs st' rf :=
  principalPreconditionedFieldAllHooksCapstone_of_success_via_masterSuite
    h_suite h_seed.1 h_seed.2 h_ok

/--
Master-suite run-bundle wrapper: package capstone + hook-irrelevance for
expression successful runs from one baseline hook witness pair.
-/
theorem principalPreconditionedExprAllHooksRunBundle_of_success_via_masterSuite
    (h_suite : PrincipalBoundaryMasterSuite)
    (h_app0 : AppUnifySoundHook)
    (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalPreconditionedExprAllHooksRunBundle st fuel env e st' ty :=
  principalGeneralAllHooksRunBundleExpr_of_success
    h_suite.allHooks h_app0 h_proj0 h_ok

/--
Master-suite run-bundle wrapper: package capstone + hook-irrelevance for
successful field runs from one baseline hook witness pair.
-/
theorem principalPreconditionedFieldAllHooksRunBundle_of_success_via_masterSuite
    (h_suite : PrincipalBoundaryMasterSuite)
    (h_app0 : AppUnifySoundHook)
    (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalPreconditionedFieldAllHooksRunBundle st fuel env fs st' rf :=
  principalGeneralAllHooksRunBundleField_of_success
    h_suite.allHooks h_app0 h_proj0 h_ok

/--
Bundle-entry variant of
`principalPreconditionedExprAllHooksRunBundle_of_success_via_masterSuite`.
-/
theorem principalPreconditionedExprAllHooksRunBundle_of_success_via_masterSuite_from_bundle
    (h_suite : PrincipalBoundaryMasterSuite)
    (h_seed : UnifyHookPremises)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalPreconditionedExprAllHooksRunBundle st fuel env e st' ty :=
  principalPreconditionedExprAllHooksRunBundle_of_success_via_masterSuite
    h_suite h_seed.1 h_seed.2 h_ok

/--
Bundle-entry variant of
`principalPreconditionedFieldAllHooksRunBundle_of_success_via_masterSuite`.
-/
theorem principalPreconditionedFieldAllHooksRunBundle_of_success_via_masterSuite_from_bundle
    (h_suite : PrincipalBoundaryMasterSuite)
    (h_seed : UnifyHookPremises)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalPreconditionedFieldAllHooksRunBundle st fuel env fs st' rf :=
  principalPreconditionedFieldAllHooksRunBundle_of_success_via_masterSuite
    h_suite h_seed.1 h_seed.2 h_ok

/--
Master-suite convenience wrapper: derive core expression principality from an
arbitrary successful run via the embedded general all-hooks layer.
-/
theorem principalCoreExpr_of_success_via_masterSuite
    (h_suite : PrincipalBoundaryMasterSuite)
    (h_app0 : AppUnifySoundHook)
    (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalTypingSliceCore env e ty :=
  principalGeneralAllHooksCoreExpr_of_success
    h_suite.allHooks h_app0 h_proj0 h_ok

/--
Master-suite convenience wrapper: derive preconditioned expression principality
for any hook witnesses from an arbitrary successful run.
-/
theorem principalPreconditionedExpr_anyHooks_of_success_via_masterSuite
    (h_suite : PrincipalBoundaryMasterSuite)
    (h_app0 : AppUnifySoundHook)
    (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    ∀ h_app h_proj,
      PrincipalTypingSlicePreconditioned h_app h_proj st fuel env e st' ty :=
  principalGeneralAllHooksPreconditionedExpr_anyHooks_of_success
    h_suite.allHooks h_app0 h_proj0 h_ok

/--
Master-suite convenience wrapper: derive preconditioned expression principality
for a bundled hook witness from an arbitrary successful run.
-/
theorem principalPreconditionedExpr_of_success_via_masterSuite
    (h_suite : PrincipalBoundaryMasterSuite)
    (h_app0 : AppUnifySoundHook)
    (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty)
    (h_hooks : UnifyHookPremises) :
    PrincipalTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env e st' ty :=
  principalGeneralAllHooksPreconditionedExpr_of_success
    h_suite.allHooks h_app0 h_proj0 h_ok h_hooks

/--
Master-suite convenience wrapper: derive fixed-run expression preconditioned↔core
equivalence for any hook witnesses from an arbitrary successful run.
-/
theorem principalPreconditionedCoreIffExpr_anyHooks_of_success_via_masterSuite
    (h_suite : PrincipalBoundaryMasterSuite)
    (h_app0 : AppUnifySoundHook)
    (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    ∀ h_app h_proj,
      (PrincipalTypingSlicePreconditioned h_app h_proj st fuel env e st' ty
        ↔ PrincipalTypingSliceCore env e ty) :=
  principalGeneralAllHooksPreconditionedCoreIffExpr_anyHooks_of_success
    h_suite.allHooks h_app0 h_proj0 h_ok

/--
Master-suite convenience wrapper: derive fixed-run expression preconditioned↔core
equivalence for a bundled hook witness from an arbitrary successful run.
-/
theorem principalPreconditionedCoreIffExpr_of_success_via_masterSuite
    (h_suite : PrincipalBoundaryMasterSuite)
    (h_app0 : AppUnifySoundHook)
    (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty)
    (h_hooks : UnifyHookPremises) :
    (PrincipalTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env e st' ty
      ↔ PrincipalTypingSliceCore env e ty) :=
  principalGeneralAllHooksPreconditionedCoreIffExpr_of_success
    h_suite.allHooks h_app0 h_proj0 h_ok h_hooks

/--
Master-suite convenience wrapper: derive core field principality from an
arbitrary successful field run via the embedded general all-hooks layer.
-/
theorem principalCoreField_of_success_via_masterSuite
    (h_suite : PrincipalBoundaryMasterSuite)
    (h_app0 : AppUnifySoundHook)
    (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalFieldTypingSliceCore env fs rf :=
  principalGeneralAllHooksCoreField_of_success
    h_suite.allHooks h_app0 h_proj0 h_ok

/--
Master-suite convenience wrapper: derive preconditioned field principality for
any hook witnesses from an arbitrary successful field run.
-/
theorem principalPreconditionedField_anyHooks_of_success_via_masterSuite
    (h_suite : PrincipalBoundaryMasterSuite)
    (h_app0 : AppUnifySoundHook)
    (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    ∀ h_app h_proj,
      PrincipalFieldTypingSlicePreconditioned h_app h_proj st fuel env fs st' rf :=
  principalGeneralAllHooksPreconditionedField_anyHooks_of_success
    h_suite.allHooks h_app0 h_proj0 h_ok

/--
Master-suite convenience wrapper: derive preconditioned field principality for
a bundled hook witness from an arbitrary successful field run.
-/
theorem principalPreconditionedField_of_success_via_masterSuite
    (h_suite : PrincipalBoundaryMasterSuite)
    (h_app0 : AppUnifySoundHook)
    (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)))
    (h_hooks : UnifyHookPremises) :
    PrincipalFieldTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env fs st' rf :=
  principalGeneralAllHooksPreconditionedField_of_success
    h_suite.allHooks h_app0 h_proj0 h_ok h_hooks

/--
Master-suite convenience wrapper: derive fixed-run field preconditioned↔core
equivalence for any hook witnesses from an arbitrary successful field run.
-/
theorem principalPreconditionedCoreIffField_anyHooks_of_success_via_masterSuite
    (h_suite : PrincipalBoundaryMasterSuite)
    (h_app0 : AppUnifySoundHook)
    (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    ∀ h_app h_proj,
      (PrincipalFieldTypingSlicePreconditioned h_app h_proj st fuel env fs st' rf
        ↔ PrincipalFieldTypingSliceCore env fs rf) :=
  principalGeneralAllHooksPreconditionedCoreIffField_anyHooks_of_success
    h_suite.allHooks h_app0 h_proj0 h_ok

/--
Master-suite convenience wrapper: derive fixed-run field preconditioned↔core
equivalence for a bundled hook witness from an arbitrary successful field run.
-/
theorem principalPreconditionedCoreIffField_of_success_via_masterSuite
    (h_suite : PrincipalBoundaryMasterSuite)
    (h_app0 : AppUnifySoundHook)
    (h_proj0 : ProjUnifySoundHook)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)))
    (h_hooks : UnifyHookPremises) :
    (PrincipalFieldTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env fs st' rf
      ↔ PrincipalFieldTypingSliceCore env fs rf) :=
  principalGeneralAllHooksPreconditionedCoreIffField_of_success
    h_suite.allHooks h_app0 h_proj0 h_ok h_hooks

/--
Master-suite convenience wrapper: bundled-baseline variant for core expression
principality from an arbitrary successful run.
-/
theorem principalCoreExpr_of_success_via_masterSuite_from_bundle
    (h_suite : PrincipalBoundaryMasterSuite)
    (h_seed : UnifyHookPremises)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalTypingSliceCore env e ty :=
  principalCoreExpr_of_success_via_masterSuite h_suite h_seed.1 h_seed.2 h_ok

/--
Master-suite convenience wrapper: bundled-baseline variant for preconditioned
expression principality (any target hooks) from an arbitrary successful run.
-/
theorem principalPreconditionedExpr_anyHooks_of_success_via_masterSuite_from_bundle
    (h_suite : PrincipalBoundaryMasterSuite)
    (h_seed : UnifyHookPremises)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    ∀ h_app h_proj,
      PrincipalTypingSlicePreconditioned h_app h_proj st fuel env e st' ty :=
  principalPreconditionedExpr_anyHooks_of_success_via_masterSuite
    h_suite h_seed.1 h_seed.2 h_ok

/--
Master-suite convenience wrapper: bundled-baseline variant for fixed-run
expression preconditioned↔core equivalence (any target hooks) from an arbitrary
successful run.
-/
theorem principalPreconditionedCoreIffExpr_anyHooks_of_success_via_masterSuite_from_bundle
    (h_suite : PrincipalBoundaryMasterSuite)
    (h_seed : UnifyHookPremises)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    ∀ h_app h_proj,
      (PrincipalTypingSlicePreconditioned h_app h_proj st fuel env e st' ty
        ↔ PrincipalTypingSliceCore env e ty) :=
  principalPreconditionedCoreIffExpr_anyHooks_of_success_via_masterSuite
    h_suite h_seed.1 h_seed.2 h_ok

/--
Master-suite convenience wrapper: bundled-baseline variant for core field
principality from an arbitrary successful field run.
-/
theorem principalCoreField_of_success_via_masterSuite_from_bundle
    (h_suite : PrincipalBoundaryMasterSuite)
    (h_seed : UnifyHookPremises)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalFieldTypingSliceCore env fs rf :=
  principalCoreField_of_success_via_masterSuite h_suite h_seed.1 h_seed.2 h_ok

/--
Master-suite convenience wrapper: bundled-baseline variant for preconditioned
field principality (any target hooks) from an arbitrary successful field run.
-/
theorem principalPreconditionedField_anyHooks_of_success_via_masterSuite_from_bundle
    (h_suite : PrincipalBoundaryMasterSuite)
    (h_seed : UnifyHookPremises)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    ∀ h_app h_proj,
      PrincipalFieldTypingSlicePreconditioned h_app h_proj st fuel env fs st' rf :=
  principalPreconditionedField_anyHooks_of_success_via_masterSuite
    h_suite h_seed.1 h_seed.2 h_ok

/--
Master-suite convenience wrapper: bundled-baseline variant for fixed-run field
preconditioned↔core equivalence (any target hooks) from an arbitrary successful
field run.
-/
theorem principalPreconditionedCoreIffField_anyHooks_of_success_via_masterSuite_from_bundle
    (h_suite : PrincipalBoundaryMasterSuite)
    (h_seed : UnifyHookPremises)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    ∀ h_app h_proj,
      (PrincipalFieldTypingSlicePreconditioned h_app h_proj st fuel env fs st' rf
        ↔ PrincipalFieldTypingSliceCore env fs rf) :=
  principalPreconditionedCoreIffField_anyHooks_of_success_via_masterSuite
    h_suite h_seed.1 h_seed.2 h_ok

/--
Master-suite convenience wrapper: bundled-baseline variant for preconditioned
expression principality under a bundled target-hook witness from an arbitrary
successful run.
-/
theorem principalPreconditionedExpr_of_success_via_masterSuite_from_bundle
    (h_suite : PrincipalBoundaryMasterSuite)
    (h_seed : UnifyHookPremises)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty)
    (h_hooks : UnifyHookPremises) :
    PrincipalTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env e st' ty :=
  principalPreconditionedExpr_of_success_via_masterSuite
    h_suite h_seed.1 h_seed.2 h_ok h_hooks

/--
Master-suite convenience wrapper: bundled-baseline variant for fixed-run
expression preconditioned↔core equivalence under a bundled target-hook witness
from an arbitrary successful run.
-/
theorem principalPreconditionedCoreIffExpr_of_success_via_masterSuite_from_bundle
    (h_suite : PrincipalBoundaryMasterSuite)
    (h_seed : UnifyHookPremises)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_ok : inferExprUnify st fuel env e = .ok st' ty)
    (h_hooks : UnifyHookPremises) :
    (PrincipalTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env e st' ty
      ↔ PrincipalTypingSliceCore env e ty) :=
  principalPreconditionedCoreIffExpr_of_success_via_masterSuite
    h_suite h_seed.1 h_seed.2 h_ok h_hooks

/--
Master-suite convenience wrapper: bundled-baseline variant for preconditioned
field principality under a bundled target-hook witness from an arbitrary
successful field run.
-/
theorem principalPreconditionedField_of_success_via_masterSuite_from_bundle
    (h_suite : PrincipalBoundaryMasterSuite)
    (h_seed : UnifyHookPremises)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)))
    (h_hooks : UnifyHookPremises) :
    PrincipalFieldTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env fs st' rf :=
  principalPreconditionedField_of_success_via_masterSuite
    h_suite h_seed.1 h_seed.2 h_ok h_hooks

/--
Master-suite convenience wrapper: bundled-baseline variant for fixed-run field
preconditioned↔core equivalence under a bundled target-hook witness from an
arbitrary successful field run.
-/
theorem principalPreconditionedCoreIffField_of_success_via_masterSuite_from_bundle
    (h_suite : PrincipalBoundaryMasterSuite)
    (h_seed : UnifyHookPremises)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)))
    (h_hooks : UnifyHookPremises) :
    (PrincipalFieldTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env fs st' rf
      ↔ PrincipalFieldTypingSliceCore env fs rf) :=
  principalPreconditionedCoreIffField_of_success_via_masterSuite
    h_suite h_seed.1 h_seed.2 h_ok h_hooks

/--
Master-suite no-unify convenience wrapper: derive core expression principality
from a successful no-unify expression run.
-/
theorem principalNoUnifyCoreExpr_of_success_via_masterSuite
    (h_suite : PrincipalBoundaryMasterSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalTypingSliceCore env e ty :=
  principalNoUnifyToGeneralCoreExpr_of_success
    h_suite.noUnifyToGeneralAllHooks h_no h_ok

/--
Master-suite no-unify convenience wrapper: derive preconditioned expression
principality for any hook witnesses from a successful no-unify run.
-/
theorem principalNoUnifyPreconditionedExpr_anyHooks_of_success_via_masterSuite
    (h_suite : PrincipalBoundaryMasterSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    ∀ h_app h_proj,
      PrincipalTypingSlicePreconditioned h_app h_proj st fuel env e st' ty :=
  principalNoUnifyToGeneralPreconditionedExpr_anyHooks_of_success
    h_suite.noUnifyToGeneralAllHooks h_no h_ok

/--
Master-suite no-unify convenience wrapper: derive preconditioned expression
principality for a bundled hook witness from a successful no-unify run.
-/
theorem principalNoUnifyPreconditionedExpr_of_success_via_masterSuite
    (h_suite : PrincipalBoundaryMasterSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty)
    (h_hooks : UnifyHookPremises) :
    PrincipalTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env e st' ty :=
  principalNoUnifyToGeneralPreconditionedExpr_of_success
    h_suite.noUnifyToGeneralAllHooks h_no h_ok h_hooks

/--
Master-suite no-unify-to-general convenience wrapper: derive core expression
principality from a successful no-unify run.
-/
theorem principalCoreExpr_of_success_noUnify_via_masterSuite
    (h_suite : PrincipalBoundaryMasterSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalTypingSliceCore env e ty :=
  principalNoUnifyCoreExpr_of_success_via_masterSuite h_suite h_no h_ok

/--
Master-suite convenience wrapper: derive the expression run-bundle surface from
a successful no-unify run.
-/
theorem principalNoUnifyRunBundleExpr_of_success_via_masterSuite
    (h_suite : PrincipalBoundaryMasterSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalPreconditionedExprAllHooksRunBundle st fuel env e st' ty :=
  principalNoUnifyToGeneralRunBundleExpr_of_success
    h_suite.noUnifyToGeneralAllHooks h_no h_ok

/--
Master-suite no-unify-to-general convenience wrapper: derive the expression
run-bundle surface from a successful no-unify run.
-/
theorem principalPreconditionedExprAllHooksRunBundle_of_success_noUnify_via_masterSuite
    (h_suite : PrincipalBoundaryMasterSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalPreconditionedExprAllHooksRunBundle st fuel env e st' ty :=
  principalNoUnifyRunBundleExpr_of_success_via_masterSuite h_suite h_no h_ok

/--
Master-suite no-unify-to-general convenience wrapper: derive preconditioned
expression principality for any hook witnesses from a successful no-unify run.
-/
theorem principalPreconditionedExpr_anyHooks_of_success_noUnify_via_masterSuite
    (h_suite : PrincipalBoundaryMasterSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    ∀ h_app h_proj,
      PrincipalTypingSlicePreconditioned h_app h_proj st fuel env e st' ty :=
  principalNoUnifyPreconditionedExpr_anyHooks_of_success_via_masterSuite
    h_suite h_no h_ok

/--
Master-suite no-unify-to-general convenience wrapper: derive preconditioned
expression principality for a bundled hook witness from a successful no-unify
run.
-/
theorem principalPreconditionedExpr_of_success_noUnify_via_masterSuite
    (h_suite : PrincipalBoundaryMasterSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty)
    (h_hooks : UnifyHookPremises) :
    PrincipalTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env e st' ty :=
  principalNoUnifyPreconditionedExpr_of_success_via_masterSuite
    h_suite h_no h_ok h_hooks

/--
Master-suite no-unify convenience wrapper: derive fixed-run expression
preconditioned↔core equivalence for any hook witnesses.
-/
theorem principalNoUnifyPreconditionedCoreIffExpr_anyHooks_of_success_via_masterSuite
    (h_suite : PrincipalBoundaryMasterSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    ∀ h_app h_proj,
      (PrincipalTypingSlicePreconditioned h_app h_proj st fuel env e st' ty
        ↔ PrincipalTypingSliceCore env e ty) :=
  principalNoUnifyToGeneralPreconditionedCoreIffExpr_anyHooks_of_success
    h_suite.noUnifyToGeneralAllHooks h_no h_ok

/--
Master-suite no-unify convenience wrapper: derive fixed-run expression
preconditioned↔core equivalence for a bundled hook witness.
-/
theorem principalNoUnifyPreconditionedCoreIffExpr_of_success_via_masterSuite
    (h_suite : PrincipalBoundaryMasterSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty)
    (h_hooks : UnifyHookPremises) :
    (PrincipalTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env e st' ty
      ↔ PrincipalTypingSliceCore env e ty) :=
  (principalNoUnifyPreconditionedCoreIffExpr_anyHooks_of_success_via_masterSuite
    h_suite h_no h_ok) h_hooks.1 h_hooks.2

/--
Master-suite no-unify-to-general convenience wrapper: derive fixed-run
expression preconditioned↔core equivalence for any hook witnesses.
-/
theorem principalPreconditionedCoreIffExpr_anyHooks_of_success_noUnify_via_masterSuite
    (h_suite : PrincipalBoundaryMasterSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    ∀ h_app h_proj,
      (PrincipalTypingSlicePreconditioned h_app h_proj st fuel env e st' ty
        ↔ PrincipalTypingSliceCore env e ty) :=
  principalNoUnifyPreconditionedCoreIffExpr_anyHooks_of_success_via_masterSuite
    h_suite h_no h_ok

/--
Master-suite no-unify-to-general convenience wrapper: derive fixed-run
expression preconditioned↔core equivalence for a bundled hook witness.
-/
theorem principalPreconditionedCoreIffExpr_of_success_noUnify_via_masterSuite
    (h_suite : PrincipalBoundaryMasterSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty)
    (h_hooks : UnifyHookPremises) :
    (PrincipalTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env e st' ty
      ↔ PrincipalTypingSliceCore env e ty) :=
  principalNoUnifyPreconditionedCoreIffExpr_of_success_via_masterSuite
    h_suite h_no h_ok h_hooks

/--
Master-suite no-unify convenience wrapper: derive core field principality from
a successful no-unify field run.
-/
theorem principalNoUnifyCoreField_of_success_via_masterSuite
    (h_suite : PrincipalBoundaryMasterSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalFieldTypingSliceCore env fs rf :=
  principalNoUnifyToGeneralCoreField_of_success
    h_suite.noUnifyToGeneralAllHooks h_no h_ok

/--
Master-suite no-unify convenience wrapper: derive preconditioned field
principality for any hook witnesses from a successful no-unify run.
-/
theorem principalNoUnifyPreconditionedField_anyHooks_of_success_via_masterSuite
    (h_suite : PrincipalBoundaryMasterSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    ∀ h_app h_proj,
      PrincipalFieldTypingSlicePreconditioned h_app h_proj st fuel env fs st' rf :=
  principalNoUnifyToGeneralPreconditionedField_anyHooks_of_success
    h_suite.noUnifyToGeneralAllHooks h_no h_ok

/--
Master-suite no-unify convenience wrapper: derive preconditioned field
principality for a bundled hook witness from a successful no-unify run.
-/
theorem principalNoUnifyPreconditionedField_of_success_via_masterSuite
    (h_suite : PrincipalBoundaryMasterSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)))
    (h_hooks : UnifyHookPremises) :
    PrincipalFieldTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env fs st' rf :=
  principalNoUnifyToGeneralPreconditionedField_of_success
    h_suite.noUnifyToGeneralAllHooks h_no h_ok h_hooks

/--
Master-suite no-unify-to-general convenience wrapper: derive core field
principality from a successful no-unify field run.
-/
theorem principalCoreField_of_success_noUnify_via_masterSuite
    (h_suite : PrincipalBoundaryMasterSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalFieldTypingSliceCore env fs rf :=
  principalNoUnifyCoreField_of_success_via_masterSuite h_suite h_no h_ok

/--
Master-suite convenience wrapper: derive the field run-bundle surface from a
successful no-unify field run.
-/
theorem principalNoUnifyRunBundleField_of_success_via_masterSuite
    (h_suite : PrincipalBoundaryMasterSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalPreconditionedFieldAllHooksRunBundle st fuel env fs st' rf :=
  principalNoUnifyToGeneralRunBundleField_of_success
    h_suite.noUnifyToGeneralAllHooks h_no h_ok

/--
Master-suite no-unify-to-general convenience wrapper: derive the field
run-bundle surface from a successful no-unify field run.
-/
theorem principalPreconditionedFieldAllHooksRunBundle_of_success_noUnify_via_masterSuite
    (h_suite : PrincipalBoundaryMasterSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalPreconditionedFieldAllHooksRunBundle st fuel env fs st' rf :=
  principalNoUnifyRunBundleField_of_success_via_masterSuite h_suite h_no h_ok

/--
Master-suite no-unify-to-general convenience wrapper: derive preconditioned
field principality for any hook witnesses from a successful no-unify run.
-/
theorem principalPreconditionedField_anyHooks_of_success_noUnify_via_masterSuite
    (h_suite : PrincipalBoundaryMasterSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    ∀ h_app h_proj,
      PrincipalFieldTypingSlicePreconditioned h_app h_proj st fuel env fs st' rf :=
  principalNoUnifyPreconditionedField_anyHooks_of_success_via_masterSuite
    h_suite h_no h_ok

/--
Master-suite no-unify-to-general convenience wrapper: derive preconditioned
field principality for a bundled hook witness from a successful no-unify run.
-/
theorem principalPreconditionedField_of_success_noUnify_via_masterSuite
    (h_suite : PrincipalBoundaryMasterSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)))
    (h_hooks : UnifyHookPremises) :
    PrincipalFieldTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env fs st' rf :=
  principalNoUnifyPreconditionedField_of_success_via_masterSuite
    h_suite h_no h_ok h_hooks

/--
Master-suite no-unify convenience wrapper: derive fixed-run field
preconditioned↔core equivalence for any hook witnesses.
-/
theorem principalNoUnifyPreconditionedCoreIffField_anyHooks_of_success_via_masterSuite
    (h_suite : PrincipalBoundaryMasterSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    ∀ h_app h_proj,
      (PrincipalFieldTypingSlicePreconditioned h_app h_proj st fuel env fs st' rf
        ↔ PrincipalFieldTypingSliceCore env fs rf) :=
  principalNoUnifyToGeneralPreconditionedCoreIffField_anyHooks_of_success
    h_suite.noUnifyToGeneralAllHooks h_no h_ok

/--
Master-suite no-unify convenience wrapper: derive fixed-run field
preconditioned↔core equivalence for a bundled hook witness.
-/
theorem principalNoUnifyPreconditionedCoreIffField_of_success_via_masterSuite
    (h_suite : PrincipalBoundaryMasterSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)))
    (h_hooks : UnifyHookPremises) :
    (PrincipalFieldTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env fs st' rf
      ↔ PrincipalFieldTypingSliceCore env fs rf) :=
  (principalNoUnifyPreconditionedCoreIffField_anyHooks_of_success_via_masterSuite
    h_suite h_no h_ok) h_hooks.1 h_hooks.2

/--
Master-suite no-unify-to-general convenience wrapper: derive fixed-run field
preconditioned↔core equivalence for any hook witnesses.
-/
theorem principalPreconditionedCoreIffField_anyHooks_of_success_noUnify_via_masterSuite
    (h_suite : PrincipalBoundaryMasterSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    ∀ h_app h_proj,
      (PrincipalFieldTypingSlicePreconditioned h_app h_proj st fuel env fs st' rf
        ↔ PrincipalFieldTypingSliceCore env fs rf) :=
  principalNoUnifyPreconditionedCoreIffField_anyHooks_of_success_via_masterSuite
    h_suite h_no h_ok

/--
Master-suite no-unify-to-general convenience wrapper: derive fixed-run field
preconditioned↔core equivalence for a bundled hook witness.
-/
theorem principalPreconditionedCoreIffField_of_success_noUnify_via_masterSuite
    (h_suite : PrincipalBoundaryMasterSuite)
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)))
    (h_hooks : UnifyHookPremises) :
    (PrincipalFieldTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env fs st' rf
      ↔ PrincipalFieldTypingSliceCore env fs rf) :=
  principalNoUnifyPreconditionedCoreIffField_of_success_via_masterSuite
    h_suite h_no h_ok h_hooks

/--
Master-suite no-unify convenience wrapper: derive fixed-run expression
hook-irrelevance from a successful no-unify run.
-/
theorem principalNoUnifyPreconditionedExpr_hookIrrelevant_of_success_via_masterSuite
    (h_suite : PrincipalBoundaryMasterSuite)
    {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
    {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook}
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    (PrincipalTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env e st' ty
      ↔ PrincipalTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env e st' ty) :=
  principalNoUnifyToGeneralPreconditionedExpr_hookIrrelevant_of_success
    h_suite.noUnifyToGeneralAllHooks h_no h_ok

/--
Master-suite no-unify convenience wrapper: derive fixed-run field
hook-irrelevance from a successful no-unify field run.
-/
theorem principalNoUnifyPreconditionedField_hookIrrelevant_of_success_via_masterSuite
    (h_suite : PrincipalBoundaryMasterSuite)
    {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
    {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook}
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    (PrincipalFieldTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env fs st' rf
      ↔ PrincipalFieldTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env fs st' rf) :=
  principalNoUnifyToGeneralPreconditionedField_hookIrrelevant_of_success
    h_suite.noUnifyToGeneralAllHooks h_no h_ok

/--
Master-suite no-unify-to-general convenience wrapper: derive fixed-run
expression hook-irrelevance from a successful no-unify run.
-/
theorem principalPreconditionedExpr_hookIrrelevant_of_success_noUnify_via_masterSuite
    (h_suite : PrincipalBoundaryMasterSuite)
    {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
    {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook}
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    (PrincipalTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env e st' ty
      ↔ PrincipalTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env e st' ty) :=
  principalNoUnifyPreconditionedExpr_hookIrrelevant_of_success_via_masterSuite
    h_suite h_no h_ok

/--
Master-suite no-unify-to-general convenience wrapper: derive fixed-run field
hook-irrelevance from a successful no-unify field run.
-/
theorem principalPreconditionedField_hookIrrelevant_of_success_noUnify_via_masterSuite
    (h_suite : PrincipalBoundaryMasterSuite)
    {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
    {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook}
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    (PrincipalFieldTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env fs st' rf
      ↔ PrincipalFieldTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env fs st' rf) :=
  principalNoUnifyPreconditionedField_hookIrrelevant_of_success_via_masterSuite
    h_suite h_no h_ok

/--
All-hooks-suite convenience wrapper: derive core expression principality from a
successful no-unify expression run.
-/
theorem principalNoUnifyCoreExpr_of_success_via_allHooksSuite
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalTypingSliceCore env e ty :=
  principalNoUnifyToGeneralCoreExpr_of_success
    principalNoUnifyToGeneralAllHooksSuite_proved_via_noUnifyAllHooks h_no h_ok

/--
All-hooks-suite convenience wrapper: derive preconditioned expression
principality for any hook witnesses from a successful no-unify run.
-/
theorem principalNoUnifyPreconditionedExpr_anyHooks_of_success_via_allHooksSuite
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    ∀ h_app h_proj,
      PrincipalTypingSlicePreconditioned h_app h_proj st fuel env e st' ty :=
  principalNoUnifyToGeneralPreconditionedExpr_anyHooks_of_success
    principalNoUnifyToGeneralAllHooksSuite_proved_via_noUnifyAllHooks h_no h_ok

/--
All-hooks-suite convenience wrapper: derive preconditioned expression
principality for a bundled hook witness from a successful no-unify run.
-/
theorem principalNoUnifyPreconditionedExpr_of_success_via_allHooksSuite
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty)
    (h_hooks : UnifyHookPremises) :
    PrincipalTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env e st' ty :=
  principalNoUnifyToGeneralPreconditionedExpr_of_success
    principalNoUnifyToGeneralAllHooksSuite_proved_via_noUnifyAllHooks h_no h_ok h_hooks

/--
All-hooks-suite no-unify-to-general convenience wrapper: derive core
expression principality from a successful no-unify run.
-/
theorem principalCoreExpr_of_success_noUnify_via_allHooksSuite
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalTypingSliceCore env e ty :=
  principalNoUnifyCoreExpr_of_success_via_allHooksSuite h_no h_ok

/--
All-hooks-suite no-unify-to-general convenience wrapper: derive the expression
run-bundle surface from a successful no-unify run.
-/
theorem principalPreconditionedExprAllHooksRunBundle_of_success_noUnify_via_allHooksSuite
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    PrincipalPreconditionedExprAllHooksRunBundle st fuel env e st' ty :=
  principalNoUnifyToGeneralRunBundleExpr_of_success
    principalNoUnifyToGeneralAllHooksSuite_proved_via_noUnifyAllHooks h_no h_ok

/--
All-hooks-suite no-unify-to-general convenience wrapper: derive preconditioned
expression principality for any hook witnesses from a successful no-unify run.
-/
theorem principalPreconditionedExpr_anyHooks_of_success_noUnify_via_allHooksSuite
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    ∀ h_app h_proj,
      PrincipalTypingSlicePreconditioned h_app h_proj st fuel env e st' ty :=
  principalNoUnifyPreconditionedExpr_anyHooks_of_success_via_allHooksSuite
    h_no h_ok

/--
All-hooks-suite no-unify-to-general convenience wrapper: derive preconditioned
expression principality for a bundled hook witness from a successful no-unify
run.
-/
theorem principalPreconditionedExpr_of_success_noUnify_via_allHooksSuite
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty)
    (h_hooks : UnifyHookPremises) :
    PrincipalTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env e st' ty :=
  principalNoUnifyPreconditionedExpr_of_success_via_allHooksSuite h_no h_ok h_hooks

/--
All-hooks-suite convenience wrapper: derive fixed-run expression
preconditioned↔core equivalence for any hook witnesses.
-/
theorem principalNoUnifyPreconditionedCoreIffExpr_anyHooks_of_success_via_allHooksSuite
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    ∀ h_app h_proj,
      (PrincipalTypingSlicePreconditioned h_app h_proj st fuel env e st' ty
        ↔ PrincipalTypingSliceCore env e ty) :=
  principalNoUnifyToGeneralPreconditionedCoreIffExpr_anyHooks_of_success
    principalNoUnifyToGeneralAllHooksSuite_proved_via_noUnifyAllHooks h_no h_ok

/--
All-hooks-suite convenience wrapper: derive fixed-run expression
preconditioned↔core equivalence for a bundled hook witness.
-/
theorem principalNoUnifyPreconditionedCoreIffExpr_of_success_via_allHooksSuite
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty)
    (h_hooks : UnifyHookPremises) :
    (PrincipalTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env e st' ty
      ↔ PrincipalTypingSliceCore env e ty) :=
  (principalNoUnifyPreconditionedCoreIffExpr_anyHooks_of_success_via_allHooksSuite
    h_no h_ok) h_hooks.1 h_hooks.2

/--
All-hooks-suite no-unify-to-general convenience wrapper: derive fixed-run
expression preconditioned↔core equivalence for any hook witnesses.
-/
theorem principalPreconditionedCoreIffExpr_anyHooks_of_success_noUnify_via_allHooksSuite
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    ∀ h_app h_proj,
      (PrincipalTypingSlicePreconditioned h_app h_proj st fuel env e st' ty
        ↔ PrincipalTypingSliceCore env e ty) :=
  principalNoUnifyPreconditionedCoreIffExpr_anyHooks_of_success_via_allHooksSuite
    h_no h_ok

/--
All-hooks-suite no-unify-to-general convenience wrapper: derive fixed-run
expression preconditioned↔core equivalence for a bundled hook witness.
-/
theorem principalPreconditionedCoreIffExpr_of_success_noUnify_via_allHooksSuite
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty)
    (h_hooks : UnifyHookPremises) :
    (PrincipalTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env e st' ty
      ↔ PrincipalTypingSliceCore env e ty) :=
  principalNoUnifyPreconditionedCoreIffExpr_of_success_via_allHooksSuite
    h_no h_ok h_hooks

/--
All-hooks-suite convenience wrapper: derive core field principality from a
successful no-unify field run.
-/
theorem principalNoUnifyCoreField_of_success_via_allHooksSuite
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalFieldTypingSliceCore env fs rf :=
  principalNoUnifyToGeneralCoreField_of_success
    principalNoUnifyToGeneralAllHooksSuite_proved_via_noUnifyAllHooks h_no h_ok

/--
All-hooks-suite convenience wrapper: derive preconditioned field principality
for any hook witnesses from a successful no-unify run.
-/
theorem principalNoUnifyPreconditionedField_anyHooks_of_success_via_allHooksSuite
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    ∀ h_app h_proj,
      PrincipalFieldTypingSlicePreconditioned h_app h_proj st fuel env fs st' rf :=
  principalNoUnifyToGeneralPreconditionedField_anyHooks_of_success
    principalNoUnifyToGeneralAllHooksSuite_proved_via_noUnifyAllHooks h_no h_ok

/--
All-hooks-suite convenience wrapper: derive preconditioned field principality
for a bundled hook witness from a successful no-unify run.
-/
theorem principalNoUnifyPreconditionedField_of_success_via_allHooksSuite
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)))
    (h_hooks : UnifyHookPremises) :
    PrincipalFieldTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env fs st' rf :=
  principalNoUnifyToGeneralPreconditionedField_of_success
    principalNoUnifyToGeneralAllHooksSuite_proved_via_noUnifyAllHooks h_no h_ok h_hooks

/--
All-hooks-suite no-unify-to-general convenience wrapper: derive core field
principality from a successful no-unify field run.
-/
theorem principalCoreField_of_success_noUnify_via_allHooksSuite
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalFieldTypingSliceCore env fs rf :=
  principalNoUnifyCoreField_of_success_via_allHooksSuite h_no h_ok

/--
All-hooks-suite no-unify-to-general convenience wrapper: derive the field
run-bundle surface from a successful no-unify field run.
-/
theorem principalPreconditionedFieldAllHooksRunBundle_of_success_noUnify_via_allHooksSuite
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    PrincipalPreconditionedFieldAllHooksRunBundle st fuel env fs st' rf :=
  principalNoUnifyToGeneralRunBundleField_of_success
    principalNoUnifyToGeneralAllHooksSuite_proved_via_noUnifyAllHooks h_no h_ok

/--
All-hooks-suite no-unify-to-general convenience wrapper: derive preconditioned
field principality for any hook witnesses from a successful no-unify run.
-/
theorem principalPreconditionedField_anyHooks_of_success_noUnify_via_allHooksSuite
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    ∀ h_app h_proj,
      PrincipalFieldTypingSlicePreconditioned h_app h_proj st fuel env fs st' rf :=
  principalNoUnifyPreconditionedField_anyHooks_of_success_via_allHooksSuite
    h_no h_ok

/--
All-hooks-suite no-unify-to-general convenience wrapper: derive preconditioned
field principality for a bundled hook witness from a successful no-unify run.
-/
theorem principalPreconditionedField_of_success_noUnify_via_allHooksSuite
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)))
    (h_hooks : UnifyHookPremises) :
    PrincipalFieldTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env fs st' rf :=
  principalNoUnifyPreconditionedField_of_success_via_allHooksSuite h_no h_ok h_hooks

/--
All-hooks-suite convenience wrapper: derive fixed-run field preconditioned↔core
equivalence for any hook witnesses.
-/
theorem principalNoUnifyPreconditionedCoreIffField_anyHooks_of_success_via_allHooksSuite
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    ∀ h_app h_proj,
      (PrincipalFieldTypingSlicePreconditioned h_app h_proj st fuel env fs st' rf
        ↔ PrincipalFieldTypingSliceCore env fs rf) :=
  principalNoUnifyToGeneralPreconditionedCoreIffField_anyHooks_of_success
    principalNoUnifyToGeneralAllHooksSuite_proved_via_noUnifyAllHooks h_no h_ok

/--
All-hooks-suite convenience wrapper: derive fixed-run field preconditioned↔core
equivalence for a bundled hook witness.
-/
theorem principalNoUnifyPreconditionedCoreIffField_of_success_via_allHooksSuite
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)))
    (h_hooks : UnifyHookPremises) :
    (PrincipalFieldTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env fs st' rf
      ↔ PrincipalFieldTypingSliceCore env fs rf) :=
  (principalNoUnifyPreconditionedCoreIffField_anyHooks_of_success_via_allHooksSuite
    h_no h_ok) h_hooks.1 h_hooks.2

/--
All-hooks-suite no-unify-to-general convenience wrapper: derive fixed-run field
preconditioned↔core equivalence for any hook witnesses.
-/
theorem principalPreconditionedCoreIffField_anyHooks_of_success_noUnify_via_allHooksSuite
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    ∀ h_app h_proj,
      (PrincipalFieldTypingSlicePreconditioned h_app h_proj st fuel env fs st' rf
        ↔ PrincipalFieldTypingSliceCore env fs rf) :=
  principalNoUnifyPreconditionedCoreIffField_anyHooks_of_success_via_allHooksSuite
    h_no h_ok

/--
All-hooks-suite no-unify-to-general convenience wrapper: derive fixed-run field
preconditioned↔core equivalence for a bundled hook witness.
-/
theorem principalPreconditionedCoreIffField_of_success_noUnify_via_allHooksSuite
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)))
    (h_hooks : UnifyHookPremises) :
    (PrincipalFieldTypingSlicePreconditioned h_hooks.1 h_hooks.2 st fuel env fs st' rf
      ↔ PrincipalFieldTypingSliceCore env fs rf) :=
  principalNoUnifyPreconditionedCoreIffField_of_success_via_allHooksSuite
    h_no h_ok h_hooks

/--
All-hooks-suite convenience wrapper: derive fixed-run expression
hook-irrelevance from a successful no-unify run.
-/
theorem principalNoUnifyPreconditionedExpr_hookIrrelevant_of_success_via_allHooksSuite
    {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
    {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook}
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    (PrincipalTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env e st' ty
      ↔ PrincipalTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env e st' ty) :=
  principalNoUnifyToGeneralPreconditionedExpr_hookIrrelevant_of_success
    principalNoUnifyToGeneralAllHooksSuite_proved_via_noUnifyAllHooks h_no h_ok

/--
All-hooks-suite convenience wrapper: derive fixed-run field hook-irrelevance
from a successful no-unify field run.
-/
theorem principalNoUnifyPreconditionedField_hookIrrelevant_of_success_via_allHooksSuite
    {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
    {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook}
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    (PrincipalFieldTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env fs st' rf
      ↔ PrincipalFieldTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env fs st' rf) :=
  principalNoUnifyToGeneralPreconditionedField_hookIrrelevant_of_success
    principalNoUnifyToGeneralAllHooksSuite_proved_via_noUnifyAllHooks h_no h_ok

/--
All-hooks-suite no-unify-to-general convenience wrapper: derive fixed-run
expression hook-irrelevance from a successful no-unify run.
-/
theorem principalPreconditionedExpr_hookIrrelevant_of_success_noUnify_via_allHooksSuite
    {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
    {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook}
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {e : CoreExpr}
    {st' : UnifyState} {ty : Ty}
    (h_no : NoUnifyBranchesExpr e)
    (h_ok : inferExprUnify st fuel env e = .ok st' ty) :
    (PrincipalTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env e st' ty
      ↔ PrincipalTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env e st' ty) :=
  principalNoUnifyPreconditionedExpr_hookIrrelevant_of_success_via_allHooksSuite
    h_no h_ok

/--
All-hooks-suite no-unify-to-general convenience wrapper: derive fixed-run field
hook-irrelevance from a successful no-unify field run.
-/
theorem principalPreconditionedField_hookIrrelevant_of_success_noUnify_via_allHooksSuite
    {h_app₁ : AppUnifySoundHook} {h_proj₁ : ProjUnifySoundHook}
    {h_app₂ : AppUnifySoundHook} {h_proj₂ : ProjUnifySoundHook}
    {st : UnifyState} {fuel : Nat} {env : TermEnv} {fs : CoreFields}
    {st' : UnifyState} {rf : RowFields}
    (h_no : NoUnifyBranchesFields fs)
    (h_ok : inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none))) :
    (PrincipalFieldTypingSlicePreconditioned h_app₁ h_proj₁ st fuel env fs st' rf
      ↔ PrincipalFieldTypingSlicePreconditioned h_app₂ h_proj₂ st fuel env fs st' rf) :=
  principalNoUnifyPreconditionedField_hookIrrelevant_of_success_via_allHooksSuite
    h_no h_ok

/--
`HasTypeU` lift of non-app/proj recursive soundness: on the fragment that never
executes unification branches, algorithmic inference results are declaratively
typable in the unification-aware judgment as well.
-/
theorem inferExprUnify_sound_no_unify_branches_hasTypeU
    {e : CoreExpr}
    (h_no : NoUnifyBranchesExpr e) :
    ∀ st fuel env st' ty,
      inferExprUnify st fuel env e = .ok st' ty →
      HasTypeU env e ty := by
  intro st fuel env st' ty h_ok
  exact hasType_to_hasTypeU
    (inferExprUnify_sound_no_unify_branches h_no st fuel env st' ty h_ok)

/--
Vertical app slice (hook-free): when both app children are inferred on the
no-unify fragment and the app unification step satisfies the closed+fresh
empty-substitution regime, the app expression is declaratively typable in
`HasTypeU` without any global app/proj hook assumptions.
-/
theorem inferExprUnify_app_vertical_closed_fresh_empty_subst
    {env : TermEnv} {fn arg : CoreExpr}
    {st stFn stArg stAfter : UnifyState}
    {fuel : Nat} {argTy retTy : Ty}
    (h_fn_no : NoUnifyBranchesExpr fn)
    (h_arg_no : NoUnifyBranchesExpr arg)
    (h_fn_infer :
      inferExprUnify st (fuel + 2) env fn = .ok stFn (.function (.cons argTy .nil) retTy))
    (h_arg_infer :
      inferExprUnify stFn (fuel + 2) env arg = .ok stArg argTy)
    (h_empty : stArg.subst = Subst.empty)
    (h_arg_ftv : freeTypeVars argTy = [])
    (h_arg_frv : freeRowVars argTy = [])
    (h_ret_ftv : freeTypeVars retTy = [])
    (h_ret_frv : freeRowVars retTy = [])
    (h_unify :
      unify stArg (fuel + 2) (.function (.cons argTy .nil) retTy)
        (.function (.cons argTy .nil) (.var (stArg.freshTypeVar).1)) = .ok stAfter)
    (h_idemp : stAfter.subst.Idempotent) :
    HasTypeU env (.app fn arg)
      (applySubstCompat stAfter.subst (fuel + 1) (.var (stArg.freshTypeVar).1)) := by
  have h_fn_typed : HasTypeU env fn (.function (.cons argTy .nil) retTy) :=
    inferExprUnify_sound_no_unify_branches_hasTypeU h_fn_no
      st (fuel + 2) env stFn (.function (.cons argTy .nil) retTy) h_fn_infer
  have h_arg_typed : HasTypeU env arg argTy :=
    inferExprUnify_sound_no_unify_branches_hasTypeU h_arg_no
      stFn (fuel + 2) env stArg argTy h_arg_infer
  exact inferExprUnify_app_step_sound_hasTypeU_closed_fresh_succ_of_subst_empty
    h_empty h_fn_typed h_arg_typed h_arg_ftv h_arg_frv h_ret_ftv h_ret_frv h_unify h_idemp

/--
Vertical projection slice (hook-free): when the receiver is inferred on the
no-unify fragment and the projection unification step supplies an explicit
resolved closed-row witness, the projection expression is declaratively typable
in `HasTypeU` without global hook assumptions.
-/
theorem inferExprUnify_proj_vertical_resolved
    {env : TermEnv} {recv : CoreExpr} {label : Label}
    {st stRecv stAfter : UnifyState}
    {fuel : Nat} {recvTy : Ty} {rowFields : RowFields}
    (h_recv_no : NoUnifyBranchesExpr recv)
    (h_recv_infer :
      inferExprUnify st fuel env recv = .ok stRecv recvTy)
    (h_unify :
      unify (stRecv.freshTypeVar).2.freshRowVar.2 fuel recvTy
        (.anonRecord
          (.mk
            (.cons label (.var (stRecv.freshTypeVar).1) .nil)
            (some (stRecv.freshTypeVar).2.freshRowVar.1))) = .ok stAfter)
    (h_resolved :
      applySubstCompat stAfter.subst fuel recvTy =
        .anonRecord (.mk rowFields none))
    (h_get :
      RowFields.get rowFields label =
        some (applySubstCompat stAfter.subst fuel (.var (stRecv.freshTypeVar).1))) :
    HasTypeU env (.proj recv label)
      (applySubstCompat stAfter.subst fuel (.var (stRecv.freshTypeVar).1)) := by
  have h_recv_typed : HasTypeU env recv recvTy :=
    inferExprUnify_sound_no_unify_branches_hasTypeU h_recv_no
      st fuel env stRecv recvTy h_recv_infer
  exact inferExprUnify_proj_step_sound_hasTypeU_resolved
    (env := env) (recv := recv) (label := label) (recvTy := recvTy)
    (stBefore := (stRecv.freshTypeVar).2.freshRowVar.2)
    (stAfter := stAfter) (fuel := fuel)
    (fieldVar := (stRecv.freshTypeVar).1) (restVar := (stRecv.freshTypeVar).2.freshRowVar.1)
    (rowFields := rowFields)
    h_recv_typed h_unify h_resolved h_get

/--
Top-level projection corollary for the hook-free vertical fragment: if the
algorithmic projection inference result matches the resolved-witness branch
shape, the inferred projection type is declaratively valid in `HasTypeU`.
-/
theorem inferExprUnify_proj_vertical_resolved_of_infer
    {env : TermEnv} {recv : CoreExpr} {label : Label}
    {st stRecv stAfter : UnifyState}
    {fuel : Nat} {recvTy ty : Ty} {rowFields : RowFields}
    (h_recv_no : NoUnifyBranchesExpr recv)
    (h_recv_infer :
      inferExprUnify st fuel env recv = .ok stRecv recvTy)
    (h_unify :
      unify (stRecv.freshTypeVar).2.freshRowVar.2 fuel recvTy
        (.anonRecord
          (.mk
            (.cons label (.var (stRecv.freshTypeVar).1) .nil)
            (some (stRecv.freshTypeVar).2.freshRowVar.1))) = .ok stAfter)
    (h_resolved :
      applySubstCompat stAfter.subst fuel recvTy =
        .anonRecord (.mk rowFields none))
    (h_get :
      RowFields.get rowFields label =
        some (applySubstCompat stAfter.subst fuel (.var (stRecv.freshTypeVar).1)))
    (h_proj_infer :
      inferExprUnify st fuel env (.proj recv label) = .ok stAfter ty) :
    HasTypeU env (.proj recv label) ty := by
  have h_ty :
      applySubstCompat stAfter.subst fuel (.var (stRecv.freshTypeVar).1) = ty := by
    simpa [inferExprUnify, h_recv_infer, h_unify] using h_proj_infer
  have h_ty' :
      ty = applySubstCompat stAfter.subst fuel (.var (stRecv.freshTypeVar).1) := by
    symm
    exact h_ty
  rw [h_ty']
  exact inferExprUnify_proj_vertical_resolved
    h_recv_no h_recv_infer h_unify h_resolved h_get

/-- Packaged hook-free app vertical slice theorem shape. -/
def VerticalHookFreeAppSlice : Prop :=
  ∀ {env : TermEnv} {fn arg : CoreExpr}
    {st stFn stArg stAfter : UnifyState}
    {fuel : Nat} {argTy retTy : Ty},
    NoUnifyBranchesExpr fn →
    NoUnifyBranchesExpr arg →
    inferExprUnify st (fuel + 2) env fn = .ok stFn (.function (.cons argTy .nil) retTy) →
    inferExprUnify stFn (fuel + 2) env arg = .ok stArg argTy →
    stArg.subst = Subst.empty →
    freeTypeVars argTy = [] →
    freeRowVars argTy = [] →
    freeTypeVars retTy = [] →
    freeRowVars retTy = [] →
    unify stArg (fuel + 2) (.function (.cons argTy .nil) retTy)
      (.function (.cons argTy .nil) (.var (stArg.freshTypeVar).1)) = .ok stAfter →
    stAfter.subst.Idempotent →
    HasTypeU env (.app fn arg)
      (applySubstCompat stAfter.subst (fuel + 1) (.var (stArg.freshTypeVar).1))

/-- Packaged hook-free projection vertical slice theorem shape. -/
def VerticalHookFreeProjSlice : Prop :=
  ∀ {env : TermEnv} {recv : CoreExpr} {label : Label}
    {st stRecv stAfter : UnifyState}
    {fuel : Nat} {recvTy : Ty} {rowFields : RowFields},
    NoUnifyBranchesExpr recv →
    inferExprUnify st fuel env recv = .ok stRecv recvTy →
    unify (stRecv.freshTypeVar).2.freshRowVar.2 fuel recvTy
      (.anonRecord
        (.mk
          (.cons label (.var (stRecv.freshTypeVar).1) .nil)
          (some (stRecv.freshTypeVar).2.freshRowVar.1))) = .ok stAfter →
    applySubstCompat stAfter.subst fuel recvTy =
      .anonRecord (.mk rowFields none) →
    RowFields.get rowFields label =
      some (applySubstCompat stAfter.subst fuel (.var (stRecv.freshTypeVar).1)) →
    HasTypeU env (.proj recv label)
      (applySubstCompat stAfter.subst fuel (.var (stRecv.freshTypeVar).1))

/-- Combined hook-free vertical theorem surface for app and projection slices. -/
def VerticalHookFreeUnifySlices : Prop :=
  VerticalHookFreeAppSlice ∧ VerticalHookFreeProjSlice

/-- The combined hook-free vertical theorem surface is fully proved. -/
theorem verticalHookFreeUnifySlices_proved : VerticalHookFreeUnifySlices := by
  refine ⟨?_, ?_⟩
  · intro env fn arg st stFn stArg stAfter fuel argTy retTy
      h_fn_no h_arg_no h_fn_infer h_arg_infer h_empty
      h_arg_ftv h_arg_frv h_ret_ftv h_ret_frv h_unify h_idemp
    exact inferExprUnify_app_vertical_closed_fresh_empty_subst
      h_fn_no h_arg_no h_fn_infer h_arg_infer h_empty
      h_arg_ftv h_arg_frv h_ret_ftv h_ret_frv h_unify h_idemp
  · intro env recv label st stRecv stAfter fuel recvTy rowFields
      h_recv_no h_recv_infer h_unify h_resolved h_get
    exact inferExprUnify_proj_vertical_resolved
      h_recv_no h_recv_infer h_unify h_resolved h_get

/-- Field-level `HasTypeU` lift of `inferFieldsUnify_sound_no_unify_branches`. -/
theorem inferFieldsUnify_sound_no_unify_branches_hasTypeU
    {fs : CoreFields}
    (h_no : NoUnifyBranchesFields fs) :
    ∀ st fuel env st' rf,
      inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)) →
      HasFieldsTypeU env fs rf := by
  intro st fuel env st' rf h_ok
  exact hasFieldsType_to_hasFieldsTypeU
    (inferFieldsUnify_sound_no_unify_branches h_no st fuel env st' rf h_ok)

/--
`HasTypeU` lift of full preconditioned recursive soundness. This keeps the
monomorphic theorem as the proof core while exposing the result in the
unification-aware declarative layer.
-/
theorem inferExprUnify_sound_preconditioned_hasTypeU
    (h_app : AppUnifySoundHook)
    (h_proj : ProjUnifySoundHook) :
    ∀ st fuel env e st' ty,
      inferExprUnify st fuel env e = .ok st' ty →
      HasTypeU env e ty := by
  intro st fuel env e st' ty h_ok
  exact hasType_to_hasTypeU
    (inferExprUnify_sound_preconditioned h_app h_proj st fuel env e st' ty h_ok)

/-- Field-level `HasTypeU` lift of `inferFieldsUnify_sound_preconditioned`. -/
theorem inferFieldsUnify_sound_preconditioned_hasTypeU
    (h_app : AppUnifySoundHook)
    (h_proj : ProjUnifySoundHook) :
    ∀ st fuel env fs st' rf,
      inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)) →
      HasFieldsTypeU env fs rf := by
  intro st fuel env fs st' rf h_ok
  exact hasFieldsType_to_hasFieldsTypeU
    (inferFieldsUnify_sound_preconditioned h_app h_proj st fuel env fs st' rf h_ok)

/--
Direct recursive `HasTypeU` soundness instantiated from global resolved-shape
premises for app/proj unification branches.
-/
theorem inferExprUnify_sound_preconditioned_hasTypeU_resolved
    (h_app_resolved : AppResolvedShapeFromUnify)
    (h_proj_resolved : ProjResolvedShapeFromUnify) :
    ∀ st fuel env e st' ty,
      inferExprUnify st fuel env e = .ok st' ty →
      HasTypeU env e ty := by
  intro st fuel env e st' ty h_ok
  exact inferExprUnify_sound_preconditioned_hasTypeU_direct
    (appUnifySoundHookU_of_resolved h_app_resolved)
    (projUnifySoundHookU_of_resolved h_proj_resolved)
    st fuel env e st' ty h_ok

/-- Field-level resolved-shape instantiation counterpart. -/
theorem inferFieldsUnify_sound_preconditioned_hasTypeU_resolved
    (h_app_resolved : AppResolvedShapeFromUnify)
    (h_proj_resolved : ProjResolvedShapeFromUnify) :
    ∀ st fuel env fs st' rf,
      inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)) →
      HasFieldsTypeU env fs rf := by
  intro st fuel env fs st' rf h_ok
  exact inferFieldsUnify_sound_preconditioned_hasTypeU_direct
    (appUnifySoundHookU_of_resolved h_app_resolved)
    (projUnifySoundHookU_of_resolved h_proj_resolved)
    st fuel env fs st' rf h_ok

/-- Resolved-shape bundle instantiation for expression-level recursion. -/
theorem inferExprUnify_sound_preconditioned_hasTypeU_from_resolved_bundle
    (h_resolved : UnifyResolvedShapePremises) :
    ∀ st fuel env e st' ty,
      inferExprUnify st fuel env e = .ok st' ty →
      HasTypeU env e ty := by
  intro st fuel env e st' ty h_ok
  let h_hooks : UnifyHookPremisesU := unifyHookPremisesU_of_resolved h_resolved
  exact inferExprUnify_sound_preconditioned_hasTypeU_direct
    h_hooks.1 h_hooks.2 st fuel env e st' ty h_ok

/-- Resolved-shape bundle instantiation for field-level recursion. -/
theorem inferFieldsUnify_sound_preconditioned_hasTypeU_from_resolved_bundle
    (h_resolved : UnifyResolvedShapePremises) :
    ∀ st fuel env fs st' rf,
      inferFieldsUnify st fuel env fs = .ok st' (.row (.mk rf none)) →
      HasFieldsTypeU env fs rf := by
  intro st fuel env fs st' rf h_ok
  let h_hooks : UnifyHookPremisesU := unifyHookPremisesU_of_resolved h_resolved
  exact inferFieldsUnify_sound_preconditioned_hasTypeU_direct
    h_hooks.1 h_hooks.2 st fuel env fs st' rf h_ok
