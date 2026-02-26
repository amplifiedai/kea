import Kea.Generalize
import Kea.WellFormed
import Kea.Properties.SubstIdempotent
import Kea.Properties.WfRename

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

theorem instantiate_preserves_wf_of_mapping_respects_ctx
    (scheme : TypeScheme) (st : UnifyState) (kctx : KindCtx) (rctx : RowCtx)
    (h_wf : Ty.WellFormed kctx rctx scheme.ty)
    (h_respects :
      let typeMapping :=
        (scheme.typeVars.foldl
          (fun (acc, st) tv =>
            let (fresh, st') := st.freshTypeVar
            ((tv, fresh) :: acc, st'))
          ([], st)).1
      let stAfterType :=
        (scheme.typeVars.foldl
          (fun (acc, st) tv =>
            let (fresh, st') := st.freshTypeVar
            ((tv, fresh) :: acc, st'))
          ([], st)).2
      let rowMapping :=
        (scheme.rowVars.foldl
          (fun (acc, st) rv =>
            let (fresh, st') := st.freshRowVar
            ((rv, fresh) :: acc, st'))
          ([], stAfterType)).1
      ({ typeMap := typeMapping, rowMap := rowMapping } : VarMapping).RespectsCtx kctx rctx) :
    Ty.WellFormed kctx rctx (instantiate scheme st).1 := by
  unfold instantiate
  by_cases h_mono : scheme.isMono
  · simp [h_mono] at *
    simpa using h_wf
  · simp [h_mono]
    exact renameType_preserves_wf
      ({ typeMap :=
          (scheme.typeVars.foldl
            (fun (acc, st) tv =>
              let (fresh, st') := st.freshTypeVar
              ((tv, fresh) :: acc, st'))
            ([], st)).1,
         rowMap :=
          (scheme.rowVars.foldl
            (fun (acc, st) rv =>
              let (fresh, st') := st.freshRowVar
              ((rv, fresh) :: acc, st'))
            ([],
              (scheme.typeVars.foldl
                (fun (acc, st) tv =>
                  let (fresh, st') := st.freshTypeVar
                  ((tv, fresh) :: acc, st'))
                ([], st)).2)).1 })
      kctx rctx h_respects scheme.ty h_wf
