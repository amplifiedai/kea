import Kea.Generalize
import Kea.WellFormed
import Kea.Properties.SubstIdempotent

/-
  Kea.Properties.WfGeneralize — WF lemmas for generalize/instantiate.

  Phase-1 baseline contracts:
  - generalization preserves WF when substitution is a no-op on the type
  - empty-substitution generalization preserves WF
  - monomorphic instantiation preserves WF
-/

theorem generalize_preserves_wf_of_no_domain_vars
    (ty : Ty) (env : TypeEnv) (s : Subst) (lc : Lacks) (traitBounds : TraitBounds) (fuel : Nat)
    (kctx : KindCtx) (rctx : RowCtx)
    (h_wf : Ty.WellFormed kctx rctx ty)
    (htv : ∀ v ∈ freeTypeVars ty, s.typeMap v = none)
    (hrv : ∀ v ∈ freeRowVars ty, s.rowMap v = none) :
    Ty.WellFormed kctx rctx (generalize ty env s lc traitBounds fuel).ty := by
  unfold generalize
  rw [(applySubst_noop s fuel).1 ty htv hrv]
  exact h_wf

theorem generalize_empty_preserves_wf
    (ty : Ty) (env : TypeEnv) (lc : Lacks) (traitBounds : TraitBounds) (fuel : Nat)
    (kctx : KindCtx) (rctx : RowCtx)
    (h_wf : Ty.WellFormed kctx rctx ty) :
    Ty.WellFormed kctx rctx (generalize ty env Subst.empty lc traitBounds fuel).ty := by
  apply generalize_preserves_wf_of_no_domain_vars ty env Subst.empty lc traitBounds fuel kctx rctx h_wf
  · intro _ _; rfl
  · intro _ _; rfl

theorem instantiate_mono_eq
    (scheme : TypeScheme) (st : UnifyState)
    (h_mono : scheme.isMono = true) :
    instantiate scheme st = (scheme.ty, st) := by
  unfold instantiate
  simp [h_mono]

theorem instantiate_mono_preserves_wf
    (scheme : TypeScheme) (st : UnifyState) (kctx : KindCtx) (rctx : RowCtx)
    (h_mono : scheme.isMono = true)
    (h_wf : Ty.WellFormed kctx rctx scheme.ty) :
    Ty.WellFormed kctx rctx (instantiate scheme st).1 := by
  rw [instantiate_mono_eq scheme st h_mono]
  simpa using h_wf
