(**
  Atomic adequacy of rerooted native aligned evidence.

  An aligned predecessor carries genuine three-substitution traces from its
  successor global predicates to the current Sigma and Pi evidence codes.
  Consequently both current evidence codes are atomically adequate: this is
  a property of the operation trace itself, not an extra admissibility
  premise.

  Strong-step structural alignment identifies those native outputs with the
  canonical direct-template evidence leaves.  The generic direct ternary
  application theorem can then move either leaf to arbitrary rule-local
  formula and assignment terms while preserving atomic adequacy.  The main
  results below deliberately quantify over those three terms; the final
  Imp-I corollary is only their [#6,#9,#8] specialization.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedFixedLevelTruthTotality
  RawCodedTemplateSyntax
  RawCodedTemplateDirectStructuralTranslation
  RawCodedRestrictedPATemplateTernaryApplicationCompilation
  RawCodedDirectTemplateTernaryApplicationCongruence
  RawCodedDynamicTruthNativeCrossLevelLeafRootCompilation
  RawCodedDynamicTruthNativeLocalStagedCallbackCompilation
  RawCodedDynamicTruthNativeAlignedStrongStepLogicalRootsCompilation
  RawCodedDynamicTruthNativeAlignedRootApplicationIdentification.

Module PABoundedRawCodedDynamicTruthNativeAlignedRootAtomicAdequacy.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import
  PABoundedRawCodedRestrictedPATemplateTernaryApplicationCompilation.
Import PABoundedRawCodedDirectTemplateTernaryApplicationCongruence.
Import PABoundedRawCodedDynamicTruthNativeCrossLevelLeafRootCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeLocalStagedCallbackCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeAlignedStrongStepLogicalRootsCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeAlignedRootApplicationIdentification.

(** The native application traces already certify their output syntax.
    These two lemmas use only the aligned predecessor, before choosing any
    direct structural translation. *)
Theorem
    raw_dynamicTruthNativeLocalAligned_currentSigmaEvidence_atomically_adequate :
    forall (M : RawPAModel), RawPASatisfies M -> forall
    (tail : nat -> M) predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi
    (aligned : RawDynamicTruthNativeLocalAlignedPredecessorAt M tail
      predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi),
  RawCodedFormulaAtomicallyAdequate M
    (rawDynamicTruthNativeLocalAligned_currentSigmaEvidence M tail
      predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned).
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned.
  exact (raw_dynamicTruthLocalTernaryApplication_target_atomically_adequate
    M hPA nextInputGlobalSigma
    (rawDynamicTruthNativeLocalAligned_currentSigmaEvidence M tail
      predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned)
    (rawDynamicTruthNativeLocalAligned_sigmaApplication M tail
      predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned)).
Qed.

Theorem
    raw_dynamicTruthNativeLocalAligned_currentPiEvidence_atomically_adequate :
    forall (M : RawPAModel), RawPASatisfies M -> forall
    (tail : nat -> M) predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi
    (aligned : RawDynamicTruthNativeLocalAlignedPredecessorAt M tail
      predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi),
  RawCodedFormulaAtomicallyAdequate M
    (rawDynamicTruthNativeLocalAligned_currentPiEvidence M tail
      predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned).
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned.
  exact (raw_dynamicTruthLocalTernaryApplication_target_atomically_adequate
    M hPA nextInputGlobalPi
    (rawDynamicTruthNativeLocalAligned_currentPiEvidence M tail
      predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned)
    (rawDynamicTruthNativeLocalAligned_piApplication M tail
      predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned)).
Qed.

(** Sequential ternary opening of the reversed evidence leaves is literally
    their simultaneous rule-local rerooting.  Keeping these syntax facts
    separate makes the adequacy proofs below pure operation-trace transport. *)
Lemma
    coqDynamicTruthNativeAlignedSigmaEvidenceConclusionTemplate_reroot :
    forall rootFormula rootAssignmentCode rootAssignmentStep,
  coqRestrictedPATemplateTernaryApplication
      coqDynamicTruthNativeAlignedSigmaEvidenceConclusionTemplate
      rootAssignmentStep rootAssignmentCode rootFormula =
    coqDynamicTruthNativeAlignedSigmaEvidenceAtRootTerms
      rootFormula rootAssignmentCode rootAssignmentStep.
Proof.
  intros rootFormula rootAssignmentCode rootAssignmentStep.
  rewrite <-
    coqDynamicTruthNativeAlignedSigmaEvidenceConclusionTemplate_reverse.
  rewrite (coqDirectTemplateTernaryApplication_reverse_reroot
    coqDynamicTruthNativeAlignedSigmaEvidencePredicateTemplate
    rootFormula rootAssignmentCode rootAssignmentStep
    coqDynamicTruthNativeAlignedSigmaEvidencePredicate_scoped_three).
  reflexivity.
Qed.

Lemma
    coqDynamicTruthNativeAlignedPiEvidenceConclusionTemplate_reroot :
    forall rootFormula rootAssignmentCode rootAssignmentStep,
  coqRestrictedPATemplateTernaryApplication
      coqDynamicTruthNativeAlignedPiEvidenceConclusionTemplate
      rootAssignmentStep rootAssignmentCode rootFormula =
    coqDynamicTruthNativeAlignedPiEvidenceAtRootTerms
      rootFormula rootAssignmentCode rootAssignmentStep.
Proof.
  intros rootFormula rootAssignmentCode rootAssignmentStep.
  rewrite <-
    coqDynamicTruthNativeAlignedPiEvidenceConclusionTemplate_reverse.
  rewrite (coqDirectTemplateTernaryApplication_reverse_reroot
    coqDynamicTruthNativeAlignedPiEvidencePredicateTemplate
    rootFormula rootAssignmentCode rootAssignmentStep
    coqDynamicTruthNativeAlignedPiEvidencePredicate_scoped_three).
  reflexivity.
Qed.

(** Minimal-identification versions of arbitrary-root adequacy.  They ask
    only that the chosen direct evidence leaf is the native aligned output;
    callers that already possess this one equality need not construct the
    larger strong-step structural package. *)
Theorem
    raw_dynamicTruthNativeAlignedSigmaEvidenceAtRootTerms_atomically_adequate_of_identification :
    forall (M : RawPAModel), RawPASatisfies M -> forall
    (tail : nat -> M) predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi
    (aligned : RawDynamicTruthNativeLocalAlignedPredecessorAt M tail
      predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  rawDirectTemplateFormula inputs
      coqDynamicTruthNativeAlignedSigmaEvidenceConclusionTemplate =
    rawDynamicTruthNativeLocalAligned_currentSigmaEvidence M tail
      predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned ->
  forall rootFormula rootAssignmentCode rootAssignmentStep,
  RawCodedFormulaAtomicallyAdequate M
    (rawDirectTemplateFormula inputs
      (coqDynamicTruthNativeAlignedSigmaEvidenceAtRootTerms
        rootFormula rootAssignmentCode rootAssignmentStep)).
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputs
    hidentification rootFormula rootAssignmentCode rootAssignmentStep.
  rewrite <-
    coqDynamicTruthNativeAlignedSigmaEvidenceConclusionTemplate_reroot.
  apply (raw_directTemplateTernaryApplication_target_atomically_adequate
    M hPA inputs
    coqDynamicTruthNativeAlignedSigmaEvidenceConclusionTemplate
    rootAssignmentStep rootAssignmentCode rootFormula).
  rewrite hidentification.
  exact
    (raw_dynamicTruthNativeLocalAligned_currentSigmaEvidence_atomically_adequate
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned).
Qed.

Theorem
    raw_dynamicTruthNativeAlignedPiEvidenceAtRootTerms_atomically_adequate_of_identification :
    forall (M : RawPAModel), RawPASatisfies M -> forall
    (tail : nat -> M) predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi
    (aligned : RawDynamicTruthNativeLocalAlignedPredecessorAt M tail
      predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  rawDirectTemplateFormula inputs
      coqDynamicTruthNativeAlignedPiEvidenceConclusionTemplate =
    rawDynamicTruthNativeLocalAligned_currentPiEvidence M tail
      predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned ->
  forall rootFormula rootAssignmentCode rootAssignmentStep,
  RawCodedFormulaAtomicallyAdequate M
    (rawDirectTemplateFormula inputs
      (coqDynamicTruthNativeAlignedPiEvidenceAtRootTerms
        rootFormula rootAssignmentCode rootAssignmentStep)).
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputs
    hidentification rootFormula rootAssignmentCode rootAssignmentStep.
  rewrite <-
    coqDynamicTruthNativeAlignedPiEvidenceConclusionTemplate_reroot.
  apply (raw_directTemplateTernaryApplication_target_atomically_adequate
    M hPA inputs
    coqDynamicTruthNativeAlignedPiEvidenceConclusionTemplate
    rootAssignmentStep rootAssignmentCode rootFormula).
  rewrite hidentification.
  exact
    (raw_dynamicTruthNativeLocalAligned_currentPiEvidence_atomically_adequate
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned).
Qed.

(** The ordinary structural package contains exactly the two minimal
    identification equalities required above. *)
Theorem
    raw_dynamicTruthNativeAligned_evidenceAtRootTerms_atomically_adequate :
    forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (tail : nat -> M) predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi
    (aligned : RawDynamicTruthNativeLocalAlignedPredecessorAt M tail
      predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi)
    inputLevelNumeral
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawDynamicTruthNativeAlignedStrongStepStructuralInputsAt
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned
      inputLevelNumeral inputs ->
  (forall rootFormula rootAssignmentCode rootAssignmentStep,
    RawCodedFormulaAtomicallyAdequate M
      (rawDirectTemplateFormula inputs
        (coqDynamicTruthNativeAlignedSigmaEvidenceAtRootTerms
          rootFormula rootAssignmentCode rootAssignmentStep))) /\
  (forall rootFormula rootAssignmentCode rootAssignmentStep,
    RawCodedFormulaAtomicallyAdequate M
      (rawDirectTemplateFormula inputs
        (coqDynamicTruthNativeAlignedPiEvidenceAtRootTerms
          rootFormula rootAssignmentCode rootAssignmentStep))).
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hstructural.
  destruct hstructural as
    (localSigmaRow & localPiRow & _hwrapper & _hlower & _hsigmaRow &
     _hpiRow & hsigmaIdentification & hpiIdentification &
     _hsigmaGlobal & _hpiGlobal).
  split.
  - exact
      (raw_dynamicTruthNativeAlignedSigmaEvidenceAtRootTerms_atomically_adequate_of_identification
        M hPA tail predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned inputs
        hsigmaIdentification).
  - exact
      (raw_dynamicTruthNativeAlignedPiEvidenceAtRootTerms_atomically_adequate_of_identification
        M hPA tail predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned inputs
        hpiIdentification).
Qed.

(** Exact Imp-I specialization: [piLeft] is the native Pi evidence rerooted
    at antecedent [#6] and the current assignment coordinates [#9,#8]. *)
Corollary
    raw_dynamicTruthNativeAligned_impIntroduction_piLeft_atomically_adequate :
    forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (tail : nat -> M) predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi
    (aligned : RawDynamicTruthNativeLocalAlignedPredecessorAt M tail
      predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi)
    inputLevelNumeral
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawDynamicTruthNativeAlignedStrongStepStructuralInputsAt
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned
      inputLevelNumeral inputs ->
  let piLeft := rawDirectTemplateFormula inputs
    (coqDynamicTruthNativeAlignedPiEvidenceAtRootTerms
      (ttVar 6) (ttVar 9) (ttVar 8)) in
  RawCodedFormulaAtomicallyAdequate M piLeft.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hstructural piLeft.
  exact (proj2
    (raw_dynamicTruthNativeAligned_evidenceAtRootTerms_atomically_adequate
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
      inputs hstructural)
    (ttVar 6) (ttVar 9) (ttVar 8)).
Qed.

End PABoundedRawCodedDynamicTruthNativeAlignedRootAtomicAdequacy.
