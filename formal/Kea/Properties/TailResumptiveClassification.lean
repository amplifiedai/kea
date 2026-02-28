import Kea.Properties.HandlerClosedAwareContracts

/-!
  Kea.Properties.TailResumptiveClassification

  Phase-2 classification surface for tail-resumptive handler clauses.

  This module classifies clause-level resume summaries and exposes a contract
  surface for the "tail-resumptive compiles like a direct call" slice.
-/

namespace Kea
namespace TailResumptiveClassification

/-- Resume-shape classification used by the tail-resumptive fast path. -/
inductive TailResumptiveClass : Type where
  | nonResumptive
  | tailResumptive
  | invalid
  deriving DecidableEq, BEq

/-- Classify abstract resume use into non/tail/invalid categories. -/
def classifyResumeUse : ResumeUse → TailResumptiveClass
  | .zero => .nonResumptive
  | .one => .tailResumptive
  | .many => .invalid

/-- Clause-level classifier derived from `resumeUse`. -/
def classifyClause (c : HandleClauseContract) : TailResumptiveClass :=
  classifyResumeUse c.resumeUse

/--
Eligibility contract for tail-resumptive lowering:
- exactly-one resume summary
- no `then` post-processing effects
-/
def tailResumptiveEligible (c : HandleClauseContract) : Prop :=
  classifyClause c = .tailResumptive ∧ c.thenEffects = none

theorem classifyResumeUse_tailResumptive_iff
    (u : ResumeUse) :
    classifyResumeUse u = .tailResumptive ↔ u = .one := by
  cases u <;> simp [classifyResumeUse]

theorem classifyResumeUse_nonResumptive_iff
    (u : ResumeUse) :
    classifyResumeUse u = .nonResumptive ↔ u = .zero := by
  cases u <;> simp [classifyResumeUse]

theorem classifyResumeUse_invalid_iff
    (u : ResumeUse) :
    classifyResumeUse u = .invalid ↔ u = .many := by
  cases u <;> simp [classifyResumeUse]

theorem classifyResumeUse_not_invalid_of_atMostOnce
    (u : ResumeUse)
    (h_lin : ResumeUse.atMostOnce u) :
    classifyResumeUse u ≠ .invalid := by
  cases u with
  | zero =>
      simp [classifyResumeUse]
  | one =>
      simp [classifyResumeUse]
  | many =>
      simp [ResumeUse.atMostOnce] at h_lin

/--
Phase-2 target theorem surface:
well-typed clauses classify as either non-resumptive or tail-resumptive
(never invalid-many).
-/
theorem tail_resumptive_classification
    (c : HandleClauseContract)
    (h_wellTyped : HandleClauseContract.wellTypedSlice c) :
    classifyClause c = .nonResumptive ∨
      classifyClause c = .tailResumptive := by
  have h_prov := HandleClauseContract.wellTypedSlice_implies_resumeProvenance c h_wellTyped
  cases h_prov with
  | inl h_zero =>
      left
      simp [classifyClause, classifyResumeUse, h_zero]
  | inr h_one =>
      right
      simp [classifyClause, classifyResumeUse, h_one]

/-- Direct-call equivalence contract for the tail-resumptive lowering path. -/
def directCallEquivalent (c : HandleClauseContract) : Prop :=
  HandleClauseContract.resultEffects c =
    HandleClauseContract.resultEffectsCore c

/-- Closed-aware direct-call equivalence contract for the tail-resumptive path. -/
def directCallEquivalentClosedAware (c : HandleClauseContract) : Prop :=
  HandlerClosedAwareContracts.resultEffectsClosedAware c =
    HandlerClosedAwareContracts.resultEffectsCoreClosedAware c

/--
Soundness of the tail-resumptive fast path:
if a clause is tail-resumptive-eligible, result effects reduce to core
handler effects (no extra `then` transformation).
-/
theorem tail_resumptive_direct_call_sound
    (c : HandleClauseContract)
    (h_eligible : tailResumptiveEligible c) :
    directCallEquivalent c := by
  rcases h_eligible with ⟨_h_class, h_then_none⟩
  unfold directCallEquivalent HandleClauseContract.resultEffects
  simp [h_then_none]

theorem tail_resumptive_direct_call_sound_closedAware
    (c : HandleClauseContract)
    (h_eligible : tailResumptiveEligible c) :
    directCallEquivalentClosedAware c := by
  rcases h_eligible with ⟨_h_class, h_then_none⟩
  unfold directCallEquivalentClosedAware HandlerClosedAwareContracts.resultEffectsClosedAware
  simp [h_then_none]

theorem tail_resumptive_wellTyped_direct_call_sound
    (c : HandleClauseContract)
    (h_wellTyped : HandleClauseContract.wellTypedSlice c)
    (h_eligible : tailResumptiveEligible c) :
    directCallEquivalent c := by
  have h_lin : ResumeUse.atMostOnce c.resumeUse :=
    HandleClauseContract.wellTypedSlice_linearity c h_wellTyped
  have _h_not_invalid : classifyClause c ≠ .invalid := by
    simpa [classifyClause] using
      (classifyResumeUse_not_invalid_of_atMostOnce c.resumeUse h_lin)
  exact tail_resumptive_direct_call_sound c h_eligible

theorem tail_resumptive_eligible_implies_resume_one
    (c : HandleClauseContract)
    (h_eligible : tailResumptiveEligible c) :
    c.resumeUse = .one := by
  rcases h_eligible with ⟨h_class, _h_then⟩
  exact (classifyResumeUse_tailResumptive_iff c.resumeUse).mp
    (by simpa [classifyClause] using h_class)

theorem tail_resumptive_eligible_implies_atMostOnce
    (c : HandleClauseContract)
    (h_eligible : tailResumptiveEligible c) :
    ResumeUse.atMostOnce c.resumeUse := by
  have h_one := tail_resumptive_eligible_implies_resume_one c h_eligible
  rw [h_one]
  exact resume_atMostOnce_one

/-- Named bundle for clause-level tail-resumptive classification outcomes. -/
structure TailResumptiveBundle (c : HandleClauseContract) where
  classification :
    classifyClause c = .nonResumptive ∨
      classifyClause c = .tailResumptive
  resumeProvenance : HandleClauseContract.resumeProvenance c
  notInvalid : classifyClause c ≠ .invalid
  directCallEquivalent_of_eligible :
    tailResumptiveEligible c →
      directCallEquivalent c

/-- Structural decomposition for tail-resumptive bundle. -/
theorem tailResumptiveBundle_iff_components
    (c : HandleClauseContract) :
    TailResumptiveBundle c
      ↔
      (classifyClause c = .nonResumptive ∨ classifyClause c = .tailResumptive)
      ∧ HandleClauseContract.resumeProvenance c
      ∧ classifyClause c ≠ .invalid
      ∧ (tailResumptiveEligible c → directCallEquivalent c) := by
  constructor
  · intro h_bundle
    exact ⟨
      h_bundle.classification,
      h_bundle.resumeProvenance,
      h_bundle.notInvalid,
      h_bundle.directCallEquivalent_of_eligible
    ⟩
  · intro h_comp
    exact {
      classification := h_comp.1
      resumeProvenance := h_comp.2.1
      notInvalid := h_comp.2.2.1
      directCallEquivalent_of_eligible := h_comp.2.2.2
    }

/-- Constructor helper for tail-resumptive bundle decomposition. -/
theorem tailResumptiveBundle_of_components
    (c : HandleClauseContract)
    (h_comp :
      (classifyClause c = .nonResumptive ∨ classifyClause c = .tailResumptive)
      ∧ HandleClauseContract.resumeProvenance c
      ∧ classifyClause c ≠ .invalid
      ∧ (tailResumptiveEligible c → directCallEquivalent c)) :
    TailResumptiveBundle c :=
  (tailResumptiveBundle_iff_components c).2 h_comp

theorem tailResumptiveBundle_as_components_of_components
    (c : HandleClauseContract)
    (h_comp :
      (classifyClause c = .nonResumptive ∨ classifyClause c = .tailResumptive)
      ∧ HandleClauseContract.resumeProvenance c
      ∧ classifyClause c ≠ .invalid
      ∧ (tailResumptiveEligible c → directCallEquivalent c)) :
    (classifyClause c = .nonResumptive ∨ classifyClause c = .tailResumptive)
    ∧ HandleClauseContract.resumeProvenance c
    ∧ classifyClause c ≠ .invalid
    ∧ (tailResumptiveEligible c → directCallEquivalent c) :=
  (tailResumptiveBundle_iff_components c).1
    (tailResumptiveBundle_of_components c h_comp)

/-- One-hop decomposition of tail-resumptive bundle. -/
theorem tailResumptiveBundle_as_components
    (c : HandleClauseContract)
    (h_bundle : TailResumptiveBundle c) :
    (classifyClause c = .nonResumptive ∨ classifyClause c = .tailResumptive)
    ∧ HandleClauseContract.resumeProvenance c
    ∧ classifyClause c ≠ .invalid
    ∧ (tailResumptiveEligible c → directCallEquivalent c) :=
  (tailResumptiveBundle_iff_components c).1 h_bundle

theorem tail_resumptive_bundle_of_wellTyped
    (c : HandleClauseContract)
    (h_wellTyped : HandleClauseContract.wellTypedSlice c) :
    TailResumptiveBundle c := by
  have h_class := tail_resumptive_classification c h_wellTyped
  have h_prov := HandleClauseContract.wellTypedSlice_implies_resumeProvenance c h_wellTyped
  have h_lin : ResumeUse.atMostOnce c.resumeUse :=
    HandleClauseContract.wellTypedSlice_linearity c h_wellTyped
  have h_not_invalid : classifyClause c ≠ .invalid := by
    simpa [classifyClause] using
      (classifyResumeUse_not_invalid_of_atMostOnce c.resumeUse h_lin)
  exact {
    classification := h_class
    resumeProvenance := h_prov
    notInvalid := h_not_invalid
    directCallEquivalent_of_eligible := by
      intro h_eligible
      exact tail_resumptive_direct_call_sound c h_eligible
  }

theorem tail_resumptive_bundle_as_components_of_wellTyped
    (c : HandleClauseContract)
    (h_wellTyped : HandleClauseContract.wellTypedSlice c) :
    (classifyClause c = .nonResumptive ∨ classifyClause c = .tailResumptive)
    ∧ HandleClauseContract.resumeProvenance c
    ∧ classifyClause c ≠ .invalid
    ∧ (tailResumptiveEligible c → directCallEquivalent c) :=
  tailResumptiveBundle_as_components c
    (tail_resumptive_bundle_of_wellTyped c h_wellTyped)

theorem tail_resumptive_bundle_classification_of_wellTyped
    (c : HandleClauseContract)
    (h_wellTyped : HandleClauseContract.wellTypedSlice c) :
    classifyClause c = .nonResumptive ∨ classifyClause c = .tailResumptive :=
  (tail_resumptive_bundle_of_wellTyped c h_wellTyped).classification

theorem tail_resumptive_bundle_resumeProvenance_of_wellTyped
    (c : HandleClauseContract)
    (h_wellTyped : HandleClauseContract.wellTypedSlice c) :
    HandleClauseContract.resumeProvenance c :=
  (tail_resumptive_bundle_of_wellTyped c h_wellTyped).resumeProvenance

theorem tail_resumptive_bundle_notInvalid
    (c : HandleClauseContract)
    (h_wellTyped : HandleClauseContract.wellTypedSlice c) :
    classifyClause c ≠ .invalid :=
  (tail_resumptive_bundle_of_wellTyped c h_wellTyped).notInvalid

structure TailResumptiveClosedAwareBundle (c : HandleClauseContract) where
  classification :
    classifyClause c = .nonResumptive ∨
      classifyClause c = .tailResumptive
  notInvalid : classifyClause c ≠ .invalid
  directCallEquivalentClosedAware_of_eligible :
    tailResumptiveEligible c →
      directCallEquivalentClosedAware c

/-- Structural decomposition for closed-aware tail-resumptive bundle. -/
theorem tailResumptiveClosedAwareBundle_iff_components
    (c : HandleClauseContract) :
    TailResumptiveClosedAwareBundle c
      ↔
      (classifyClause c = .nonResumptive ∨ classifyClause c = .tailResumptive)
      ∧ (classifyClause c ≠ .invalid)
      ∧ (tailResumptiveEligible c → directCallEquivalentClosedAware c) := by
  constructor
  · intro h_bundle
    exact ⟨
      h_bundle.classification,
      h_bundle.notInvalid,
      h_bundle.directCallEquivalentClosedAware_of_eligible
    ⟩
  · intro h_comp
    exact {
      classification := h_comp.1
      notInvalid := h_comp.2.1
      directCallEquivalentClosedAware_of_eligible := h_comp.2.2
    }

/-- Constructor helper for closed-aware tail-resumptive bundle decomposition. -/
theorem tailResumptiveClosedAwareBundle_of_components
    (c : HandleClauseContract)
    (h_comp :
      (classifyClause c = .nonResumptive ∨ classifyClause c = .tailResumptive)
      ∧ (classifyClause c ≠ .invalid)
      ∧ (tailResumptiveEligible c → directCallEquivalentClosedAware c)) :
    TailResumptiveClosedAwareBundle c :=
  (tailResumptiveClosedAwareBundle_iff_components c).2 h_comp

theorem tailResumptiveClosedAwareBundle_as_components_of_components
    (c : HandleClauseContract)
    (h_comp :
      (classifyClause c = .nonResumptive ∨ classifyClause c = .tailResumptive)
      ∧ (classifyClause c ≠ .invalid)
      ∧ (tailResumptiveEligible c → directCallEquivalentClosedAware c)) :
    (classifyClause c = .nonResumptive ∨ classifyClause c = .tailResumptive)
    ∧ (classifyClause c ≠ .invalid)
    ∧ (tailResumptiveEligible c → directCallEquivalentClosedAware c) :=
  (tailResumptiveClosedAwareBundle_iff_components c).1
    (tailResumptiveClosedAwareBundle_of_components c h_comp)

/-- One-hop decomposition of closed-aware tail-resumptive bundle. -/
theorem tailResumptiveClosedAwareBundle_as_components
    (c : HandleClauseContract)
    (h_bundle : TailResumptiveClosedAwareBundle c) :
    (classifyClause c = .nonResumptive ∨ classifyClause c = .tailResumptive)
    ∧ (classifyClause c ≠ .invalid)
    ∧ (tailResumptiveEligible c → directCallEquivalentClosedAware c) :=
  (tailResumptiveClosedAwareBundle_iff_components c).1 h_bundle

theorem tail_resumptive_closedAware_bundle_of_wellTyped
    (c : HandleClauseContract)
    (h_wellTyped : HandleClauseContract.wellTypedSlice c) :
    TailResumptiveClosedAwareBundle c := by
  have h_base := tail_resumptive_bundle_of_wellTyped c h_wellTyped
  exact {
    classification := h_base.classification
    notInvalid := h_base.notInvalid
    directCallEquivalentClosedAware_of_eligible := by
      intro h_eligible
      exact tail_resumptive_direct_call_sound_closedAware c h_eligible
  }

theorem tail_resumptive_closedAware_bundle_as_components_of_wellTyped
    (c : HandleClauseContract)
    (h_wellTyped : HandleClauseContract.wellTypedSlice c) :
    (classifyClause c = .nonResumptive ∨ classifyClause c = .tailResumptive)
    ∧ (classifyClause c ≠ .invalid)
    ∧ (tailResumptiveEligible c → directCallEquivalentClosedAware c) :=
  tailResumptiveClosedAwareBundle_as_components c
    (tail_resumptive_closedAware_bundle_of_wellTyped c h_wellTyped)

theorem tail_resumptive_closedAware_bundle_classification_of_wellTyped
    (c : HandleClauseContract)
    (h_wellTyped : HandleClauseContract.wellTypedSlice c) :
    classifyClause c = .nonResumptive ∨ classifyClause c = .tailResumptive :=
  (tail_resumptive_closedAware_bundle_of_wellTyped c h_wellTyped).classification

theorem tail_resumptive_closedAware_bundle_notInvalid_of_wellTyped
    (c : HandleClauseContract)
    (h_wellTyped : HandleClauseContract.wellTypedSlice c) :
    classifyClause c ≠ .invalid :=
  (tail_resumptive_closedAware_bundle_of_wellTyped c h_wellTyped).notInvalid

theorem tail_resumptive_closedAware_bundle_direct_call_of_eligible
    (c : HandleClauseContract)
    (h_wellTyped : HandleClauseContract.wellTypedSlice c)
    (h_eligible : tailResumptiveEligible c) :
    directCallEquivalentClosedAware c :=
  (tail_resumptive_closedAware_bundle_of_wellTyped c h_wellTyped).directCallEquivalentClosedAware_of_eligible
    h_eligible

theorem tail_resumptive_bundle_direct_call_of_eligible
    (c : HandleClauseContract)
    (h_wellTyped : HandleClauseContract.wellTypedSlice c)
    (h_eligible : tailResumptiveEligible c) :
    directCallEquivalent c :=
  (tail_resumptive_bundle_of_wellTyped c h_wellTyped).directCallEquivalent_of_eligible
    h_eligible

end TailResumptiveClassification
end Kea
