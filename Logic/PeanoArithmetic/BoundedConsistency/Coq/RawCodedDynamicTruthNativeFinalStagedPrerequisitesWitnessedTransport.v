(**
  Transport all eleven final-stage prerequisite roots together.

  The prerequisite package records one witnessed PA base and eleven local
  proofs in that literal context.  Later arithmetic or list lemmas may extend
  the base by a finite standard PA prefix.  Since witnessed-context inclusion
  weakening is already proved for arbitrary represented derivations, one
  uniform transport operation moves every root while preserving the exact
  staged targets.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPALocalProofWitnessedContextMergeTransportComplete
  RawCodedDynamicTruthNativeAxiomStagedRootCompilation
  RawCodedDynamicTruthNativeFinalStagedRootCompilation.

Module
  PABoundedRawCodedDynamicTruthNativeFinalStagedPrerequisitesWitnessedTransport.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedPALocalProofWitnessedContextMergeTransportComplete.
Import PABoundedRawCodedDynamicTruthNativeAxiomStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeFinalStagedRootCompilation.

Theorem
    raw_dynamicTruthNativeFinalStagedPrerequisites_witnessed_context_transport
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      oldWitnessList oldBase newWitnessList newBase
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness,
  RawDynamicTruthNativeFinalStagedPrerequisitesOn M
    oldWitnessList oldBase
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution
    nextAxiomSoundness ->
  RawCodedPAAxiomWitnessContext M newWitnessList newBase ->
  RawContextListIncluded M oldBase newBase ->
  RawDynamicTruthNativeFinalStagedPrerequisitesOn M
    newWitnessList newBase
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution
    nextAxiomSoundness.
Proof.
  intros M hPA oldWitnessList oldBase newWitnessList newBase
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution
    nextAxiomSoundness hprerequisites hnewWitnessed hincluded.
  destruct hprerequisites as
    (currentLocalRoot & currentCrossLevelRoot & currentShiftRoot &
      currentSubstitutionRoot & currentAxiomSoundnessRoot &
      currentFinalRoot & nextLocalRoot & nextCrossLevelRoot &
      nextShiftRoot & nextSubstitutionRoot & nextAxiomSoundnessRoot &
      [hprefix hnextAxiomSoundness]).
  destruct hprefix as
    [holdWitnessed hcurrentLocal hcurrentCrossLevel hcurrentShift
      hcurrentSubstitution hcurrentAxiomSoundness hcurrentFinal
      hnextLocal hnextCrossLevel hnextShift hnextSubstitution].
  assert (htransport : RawCodedPALocalProofContextTransport
      M oldBase newBase).
  {
    intros conclusion root hroot.
    exact
      (raw_codedPALocalProofWitnessedContextInclusionWeakening_complete
        M hPA oldWitnessList oldBase newWitnessList newBase
        conclusion root holdWitnessed hnewWitnessed hincluded hroot).
  }
  destruct (htransport currentLocal currentLocalRoot hcurrentLocal)
    as [currentLocalRoot' hcurrentLocal'].
  destruct (htransport currentCrossLevel currentCrossLevelRoot
    hcurrentCrossLevel) as [currentCrossLevelRoot' hcurrentCrossLevel'].
  destruct (htransport currentShift currentShiftRoot hcurrentShift)
    as [currentShiftRoot' hcurrentShift'].
  destruct (htransport currentSubstitution currentSubstitutionRoot
    hcurrentSubstitution)
    as [currentSubstitutionRoot' hcurrentSubstitution'].
  destruct (htransport currentAxiomSoundness currentAxiomSoundnessRoot
    hcurrentAxiomSoundness)
    as [currentAxiomSoundnessRoot' hcurrentAxiomSoundness'].
  destruct (htransport currentFinal currentFinalRoot hcurrentFinal)
    as [currentFinalRoot' hcurrentFinal'].
  destruct (htransport nextLocal nextLocalRoot hnextLocal)
    as [nextLocalRoot' hnextLocal'].
  destruct (htransport nextCrossLevel nextCrossLevelRoot hnextCrossLevel)
    as [nextCrossLevelRoot' hnextCrossLevel'].
  destruct (htransport nextShift nextShiftRoot hnextShift)
    as [nextShiftRoot' hnextShift'].
  destruct (htransport nextSubstitution nextSubstitutionRoot
    hnextSubstitution)
    as [nextSubstitutionRoot' hnextSubstitution'].
  destruct (htransport nextAxiomSoundness nextAxiomSoundnessRoot
    hnextAxiomSoundness)
    as [nextAxiomSoundnessRoot' hnextAxiomSoundness'].
  exists currentLocalRoot', currentCrossLevelRoot', currentShiftRoot',
    currentSubstitutionRoot', currentAxiomSoundnessRoot', currentFinalRoot',
    nextLocalRoot', nextCrossLevelRoot', nextShiftRoot',
    nextSubstitutionRoot', nextAxiomSoundnessRoot'.
  constructor.
  - constructor; assumption.
  - exact hnextAxiomSoundness'.
Qed.

End
  PABoundedRawCodedDynamicTruthNativeFinalStagedPrerequisitesWitnessedTransport.
