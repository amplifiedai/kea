import Kea.Ty

/-!
  Kea.Properties.ResumeLinearity — Phase 2 resume-at-most-once scaffold.

  This file introduces an abstract summary model for resume usage counts.
  It does not yet formalize full handler syntax/typing judgments; instead it
  provides a compositional contract surface that can be connected to handler
  typing in later Phase-2 steps.
-/

/-- Abstract resume-use cardinality summary. -/
inductive ResumeUse : Type where
  | zero
  | one
  | many
  deriving DecidableEq, BEq

/-- Predicate for the linearity contract: zero or one resume usage. -/
def ResumeUse.atMostOnce : ResumeUse → Prop
  | .zero => True
  | .one => True
  | .many => False

/-- Saturating composition of resume-use summaries. -/
def ResumeUse.combine : ResumeUse → ResumeUse → ResumeUse
  | .zero, u => u
  | u, .zero => u
  | .one, .one => .many
  | .one, .many => .many
  | .many, .one => .many
  | .many, .many => .many

@[simp] theorem resume_atMostOnce_zero : ResumeUse.atMostOnce .zero := trivial
@[simp] theorem resume_atMostOnce_one : ResumeUse.atMostOnce .one := trivial
@[simp] theorem resume_not_atMostOnce_many : ¬ ResumeUse.atMostOnce .many := by
  simp [ResumeUse.atMostOnce]

@[simp] theorem resume_combine_zero_left (u : ResumeUse) :
    ResumeUse.combine .zero u = u := by
  cases u <;> rfl

@[simp] theorem resume_combine_zero_right (u : ResumeUse) :
    ResumeUse.combine u .zero = u := by
  cases u <;> rfl

@[simp] theorem resume_combine_comm (a b : ResumeUse) :
    ResumeUse.combine a b = ResumeUse.combine b a := by
  cases a <;> cases b <;> rfl

/--
If one side is proven zero-resume and the other is at-most-once, the composed
summary remains at-most-once.
-/
theorem resume_combine_preserves_atMostOnce_of_left_zero
    (a b : ResumeUse)
    (h_left : a = .zero)
    (h_right : ResumeUse.atMostOnce b) :
    ResumeUse.atMostOnce (ResumeUse.combine a b) := by
  subst h_left
  simpa [ResumeUse.combine] using h_right

/-- Symmetric zero-side variant. -/
theorem resume_combine_preserves_atMostOnce_of_right_zero
    (a b : ResumeUse)
    (h_left : ResumeUse.atMostOnce a)
    (h_right : b = .zero) :
    ResumeUse.atMostOnce (ResumeUse.combine a b) := by
  subst h_right
  cases a with
  | zero => trivial
  | one => trivial
  | many =>
      cases h_left

/--
Branch-style composition rule:
if each branch is at-most-once and execution is exclusive (one branch has
zero summary in the merged path), the merged summary is at-most-once.
-/
theorem resume_combine_preserves_atMostOnce_of_exclusive
    (a b : ResumeUse)
    (h_a : ResumeUse.atMostOnce a)
    (h_b : ResumeUse.atMostOnce b)
    (h_exclusive : a = .zero ∨ b = .zero) :
    ResumeUse.atMostOnce (ResumeUse.combine a b) := by
  cases h_exclusive with
  | inl h_zero =>
      exact resume_combine_preserves_atMostOnce_of_left_zero a b h_zero h_b
  | inr h_zero =>
      exact resume_combine_preserves_atMostOnce_of_right_zero a b h_a h_zero

/--
Exact characterization of linearity for composed summaries:
the composition is at-most-once iff one side is zero and the other side
is itself at-most-once.
-/
theorem resume_combine_atMostOnce_iff
    (a b : ResumeUse) :
    ResumeUse.atMostOnce (ResumeUse.combine a b) ↔
      (a = .zero ∧ ResumeUse.atMostOnce b) ∨
      (b = .zero ∧ ResumeUse.atMostOnce a) := by
  cases a <;> cases b <;> simp [ResumeUse.combine, ResumeUse.atMostOnce]

/--
Corollary: if a composed summary is at-most-once, at least one side is zero.
This is the abstract branch-exclusivity signal used by resume-linearity checks.
-/
theorem resume_combine_atMostOnce_implies_one_side_zero
    (a b : ResumeUse)
    (h : ResumeUse.atMostOnce (ResumeUse.combine a b)) :
    a = .zero ∨ b = .zero := by
  have h_iff := (resume_combine_atMostOnce_iff a b).mp h
  cases h_iff with
  | inl h_left => exact Or.inl h_left.1
  | inr h_right => exact Or.inr h_right.1

/-- Two definitely-resuming sides cannot compose to at-most-once. -/
theorem resume_combine_one_one_not_atMostOnce :
    ¬ ResumeUse.atMostOnce (ResumeUse.combine .one .one) := by
  simp [ResumeUse.combine, ResumeUse.atMostOnce]

/--
Phase-2 named contract surface for the resume linearity theorem family.
-/
def resume_at_most_once (u : ResumeUse) : Prop :=
  ResumeUse.atMostOnce u

theorem resume_at_most_once_sound
    (u : ResumeUse) (h : ResumeUse.atMostOnce u) :
    resume_at_most_once u := h
