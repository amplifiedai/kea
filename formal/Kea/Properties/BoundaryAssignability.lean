import Kea.Typing

/-!
  Kea.Properties.BoundaryAssignability

  Shared language-level boundary assignability abstraction used by typing
  bridge modules.
-/

/-- Generic boundary assignability judgment:
    expression `e` can inhabit `expected` if it has some actual type accepted
    by the boundary relation `allows`. -/
abbrev HasTypeAtBoundary
    (allows : Ty → Ty → Prop)
    (env : TermEnv) (e : CoreExpr) (expected : Ty) : Prop :=
  HasTypeAtCoreBoundary allows env e expected

/-- Lift a boolean boundary predicate into a proposition-valued boundary
    relation. -/
def allowsByBool
    (allows : Ty → Ty → Bool) : Ty → Ty → Prop :=
  fun expected actual => allows expected actual = true

/-- Lift a boolean boundary predicate and an explicit unifier-success check
    into a proposition-valued boundary relation. -/
def allowsByBoolAndUnify
    (allows : Ty → Ty → Bool)
    (st : UnifyState)
    (fuel : Nat) : Ty → Ty → Prop :=
  fun expected actual =>
    allows expected actual = true
    ∧ ∃ st', unify st fuel expected actual = .ok st'

/-- `HasTypeAtBoundary` is invariant under pointwise-equivalent boundary
    relations. -/
theorem hasTypeAtBoundary_congr
    (allows₁ allows₂ : Ty → Ty → Prop)
    (env : TermEnv) (e : CoreExpr) (expected : Ty)
    (h_rel : ∀ exp act, allows₁ exp act ↔ allows₂ exp act) :
    HasTypeAtBoundary allows₁ env e expected
      ↔ HasTypeAtBoundary allows₂ env e expected := by
  constructor
  · intro h
    rcases h with ⟨actual, h_ty, h_allow⟩
    exact ⟨actual, h_ty, (h_rel expected actual).1 h_allow⟩
  · intro h
    rcases h with ⟨actual, h_ty, h_allow⟩
    exact ⟨actual, h_ty, (h_rel expected actual).2 h_allow⟩
