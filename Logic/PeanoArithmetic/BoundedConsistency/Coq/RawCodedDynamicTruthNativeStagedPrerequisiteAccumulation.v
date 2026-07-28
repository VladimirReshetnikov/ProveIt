(**
  Common-context accumulation for dependency-ordered native stages.

  The current six-field master already supplies six local proof roots in one
  witnessed PA-axiom context.  Each positive successor callback then returns
  an ordinary certificate whose own witnessed context is existentially
  hidden.  Before a later field can use that certificate as a premise, its
  root must be synchronized with every root accumulated so far.

  This file performs that synchronization one field at a time.  It uses the
  completed ordinary-proof accumulation theorem, transports every old root
  into the returned merged context, and constructs the exact prerequisite
  record consumed by the next staged compiler.  No conclusion changes, no
  context is identified by proof irrelevance, and no nonempty context is
  replaced by the empty context.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedPAProvability
  RawCodedTruthCertificateMasterBaseBridge
  RawCodedPAOrdinaryProofWitnessedContextAccumulation
  RawCodedDynamicTruthNativeCrossLevelGuardRootCompilation
  RawCodedDynamicTruthNativeShiftStagedRootCompilation
  RawCodedDynamicTruthNativeSubstitutionStagedRootCompilation
  RawCodedDynamicTruthNativeAxiomStagedRootCompilation.

Module PABoundedRawCodedDynamicTruthNativeStagedPrerequisiteAccumulation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedTruthCertificateMasterBaseBridge.
Import PABoundedRawCodedPAOrdinaryProofWitnessedContextAccumulation.
Import PABoundedRawCodedDynamicTruthNativeCrossLevelGuardRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeShiftStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeSubstitutionStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeAxiomStagedRootCompilation.

(** Add the first successor certificate to the current master context. *)
Theorem
    raw_dynamicTruthNativeCrossLevelStagedPrerequisites_of_current_and_local :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal localCertificate,
  RawSixFieldMasterCommonContextProofsOf M
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal ->
  RawCodedPAProofOf M nextLocal localCertificate ->
  exists witnessList baseContext
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot : M,
    RawDynamicTruthNativeCrossLevelStagedPrerequisitesAt M
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot.
Proof.
  intros M hPA
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal nextLocal localCertificate
    hcurrent hlocal.
  unfold RawSixFieldMasterCommonContextProofsOf in hcurrent.
  destruct hcurrent as
    (currentWitnessList & currentContext &
      currentLocalRoot & currentCrossLevelRoot & currentShiftRoot &
      currentSubstitutionRoot & currentAxiomSoundnessRoot & currentFinalRoot &
      hcurrentWitnessed & hcurrentLocal & hcurrentCrossLevel & hcurrentShift &
      hcurrentSubstitution & hcurrentAxiomSoundness & hcurrentFinal).
  destruct (raw_codedPAProofOf_add_to_witnessed_context_complete
    M hPA nextLocal localCertificate
    currentWitnessList currentContext hlocal hcurrentWitnessed) as
    (mergedWitnessList & mergedContext & mergedNextLocalRoot &
      hmergedWitnessed & htransport & hmergedNextLocal).
  destruct (htransport currentLocal currentLocalRoot hcurrentLocal) as
    [mergedCurrentLocalRoot hmergedCurrentLocal].
  destruct (htransport currentCrossLevel currentCrossLevelRoot
    hcurrentCrossLevel) as
    [mergedCurrentCrossLevelRoot hmergedCurrentCrossLevel].
  destruct (htransport currentShift currentShiftRoot hcurrentShift) as
    [mergedCurrentShiftRoot hmergedCurrentShift].
  destruct (htransport currentSubstitution currentSubstitutionRoot
    hcurrentSubstitution) as
    [mergedCurrentSubstitutionRoot hmergedCurrentSubstitution].
  destruct (htransport currentAxiomSoundness currentAxiomSoundnessRoot
    hcurrentAxiomSoundness) as
    [mergedCurrentAxiomSoundnessRoot hmergedCurrentAxiomSoundness].
  destruct (htransport currentFinal currentFinalRoot hcurrentFinal) as
    [mergedCurrentFinalRoot hmergedCurrentFinal].
  exists mergedWitnessList, mergedContext,
    mergedCurrentLocalRoot, mergedCurrentCrossLevelRoot,
    mergedCurrentShiftRoot, mergedCurrentSubstitutionRoot,
    mergedCurrentAxiomSoundnessRoot, mergedCurrentFinalRoot,
    mergedNextLocalRoot.
  constructor; assumption.
Qed.

(** Add the selected cross-level certificate and retain the first seven
    roots. *)
Theorem
    raw_dynamicTruthNativeShiftStagedPrerequisites_add_crossLevel :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal nextCrossLevel
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot crossLevelCertificate,
  RawDynamicTruthNativeCrossLevelStagedPrerequisitesAt M
    witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal nextLocal
    currentLocalRoot currentCrossLevelRoot currentShiftRoot
    currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
    nextLocalRoot ->
  RawCodedPAProofOf M nextCrossLevel crossLevelCertificate ->
  exists mergedWitnessList mergedContext
      mergedCurrentLocalRoot mergedCurrentCrossLevelRoot
      mergedCurrentShiftRoot mergedCurrentSubstitutionRoot
      mergedCurrentAxiomSoundnessRoot mergedCurrentFinalRoot
      mergedNextLocalRoot mergedNextCrossLevelRoot : M,
    RawDynamicTruthNativeShiftStagedPrerequisitesAt M
      mergedWitnessList mergedContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal nextCrossLevel
      mergedCurrentLocalRoot mergedCurrentCrossLevelRoot
      mergedCurrentShiftRoot mergedCurrentSubstitutionRoot
      mergedCurrentAxiomSoundnessRoot mergedCurrentFinalRoot
      mergedNextLocalRoot mergedNextCrossLevelRoot.
Proof.
  intros M hPA witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal nextLocal nextCrossLevel
    currentLocalRoot currentCrossLevelRoot currentShiftRoot
    currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
    nextLocalRoot crossLevelCertificate hprefix hcrossCertificate.
  destruct hprefix as
    [hwitnessed hcurrentLocal hcurrentCrossLevel hcurrentShift
      hcurrentSubstitution hcurrentAxiomSoundness hcurrentFinal hnextLocal].
  destruct (raw_codedPAProofOf_add_to_witnessed_context_complete
    M hPA nextCrossLevel crossLevelCertificate
    witnessList baseContext hcrossCertificate hwitnessed) as
    (mergedWitnessList & mergedContext & mergedNextCrossLevelRoot &
      hmergedWitnessed & htransport & hmergedNextCrossLevel).
  destruct (htransport currentLocal currentLocalRoot hcurrentLocal) as
    [mergedCurrentLocalRoot hmergedCurrentLocal].
  destruct (htransport currentCrossLevel currentCrossLevelRoot
    hcurrentCrossLevel) as
    [mergedCurrentCrossLevelRoot hmergedCurrentCrossLevel].
  destruct (htransport currentShift currentShiftRoot hcurrentShift) as
    [mergedCurrentShiftRoot hmergedCurrentShift].
  destruct (htransport currentSubstitution currentSubstitutionRoot
    hcurrentSubstitution) as
    [mergedCurrentSubstitutionRoot hmergedCurrentSubstitution].
  destruct (htransport currentAxiomSoundness currentAxiomSoundnessRoot
    hcurrentAxiomSoundness) as
    [mergedCurrentAxiomSoundnessRoot hmergedCurrentAxiomSoundness].
  destruct (htransport currentFinal currentFinalRoot hcurrentFinal) as
    [mergedCurrentFinalRoot hmergedCurrentFinal].
  destruct (htransport nextLocal nextLocalRoot hnextLocal) as
    [mergedNextLocalRoot hmergedNextLocal].
  exists mergedWitnessList, mergedContext,
    mergedCurrentLocalRoot, mergedCurrentCrossLevelRoot,
    mergedCurrentShiftRoot, mergedCurrentSubstitutionRoot,
    mergedCurrentAxiomSoundnessRoot, mergedCurrentFinalRoot,
    mergedNextLocalRoot, mergedNextCrossLevelRoot.
  constructor; assumption.
Qed.

(** Add the selected shift certificate and retain the first eight roots. *)
Theorem
    raw_dynamicTruthNativeSubstitutionStagedPrerequisites_add_shift :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal nextCrossLevel nextShift
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot shiftCertificate,
  RawDynamicTruthNativeShiftStagedPrerequisitesAt M
    witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal nextLocal nextCrossLevel
    currentLocalRoot currentCrossLevelRoot currentShiftRoot
    currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
    nextLocalRoot nextCrossLevelRoot ->
  RawCodedPAProofOf M nextShift shiftCertificate ->
  exists mergedWitnessList mergedContext
      mergedCurrentLocalRoot mergedCurrentCrossLevelRoot
      mergedCurrentShiftRoot mergedCurrentSubstitutionRoot
      mergedCurrentAxiomSoundnessRoot mergedCurrentFinalRoot
      mergedNextLocalRoot mergedNextCrossLevelRoot mergedNextShiftRoot : M,
    RawDynamicTruthNativeSubstitutionStagedPrerequisitesAt M
      mergedWitnessList mergedContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal nextCrossLevel nextShift
      mergedCurrentLocalRoot mergedCurrentCrossLevelRoot
      mergedCurrentShiftRoot mergedCurrentSubstitutionRoot
      mergedCurrentAxiomSoundnessRoot mergedCurrentFinalRoot
      mergedNextLocalRoot mergedNextCrossLevelRoot mergedNextShiftRoot.
Proof.
  intros M hPA witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal nextLocal nextCrossLevel nextShift
    currentLocalRoot currentCrossLevelRoot currentShiftRoot
    currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
    nextLocalRoot nextCrossLevelRoot shiftCertificate
    hprefix hshiftCertificate.
  destruct hprefix as
    [hwitnessed hcurrentLocal hcurrentCrossLevel hcurrentShift
      hcurrentSubstitution hcurrentAxiomSoundness hcurrentFinal
      hnextLocal hnextCrossLevel].
  destruct (raw_codedPAProofOf_add_to_witnessed_context_complete
    M hPA nextShift shiftCertificate
    witnessList baseContext hshiftCertificate hwitnessed) as
    (mergedWitnessList & mergedContext & mergedNextShiftRoot &
      hmergedWitnessed & htransport & hmergedNextShift).
  destruct (htransport currentLocal currentLocalRoot hcurrentLocal) as
    [mergedCurrentLocalRoot hmergedCurrentLocal].
  destruct (htransport currentCrossLevel currentCrossLevelRoot
    hcurrentCrossLevel) as
    [mergedCurrentCrossLevelRoot hmergedCurrentCrossLevel].
  destruct (htransport currentShift currentShiftRoot hcurrentShift) as
    [mergedCurrentShiftRoot hmergedCurrentShift].
  destruct (htransport currentSubstitution currentSubstitutionRoot
    hcurrentSubstitution) as
    [mergedCurrentSubstitutionRoot hmergedCurrentSubstitution].
  destruct (htransport currentAxiomSoundness currentAxiomSoundnessRoot
    hcurrentAxiomSoundness) as
    [mergedCurrentAxiomSoundnessRoot hmergedCurrentAxiomSoundness].
  destruct (htransport currentFinal currentFinalRoot hcurrentFinal) as
    [mergedCurrentFinalRoot hmergedCurrentFinal].
  destruct (htransport nextLocal nextLocalRoot hnextLocal) as
    [mergedNextLocalRoot hmergedNextLocal].
  destruct (htransport nextCrossLevel nextCrossLevelRoot hnextCrossLevel) as
    [mergedNextCrossLevelRoot hmergedNextCrossLevel].
  exists mergedWitnessList, mergedContext,
    mergedCurrentLocalRoot, mergedCurrentCrossLevelRoot,
    mergedCurrentShiftRoot, mergedCurrentSubstitutionRoot,
    mergedCurrentAxiomSoundnessRoot, mergedCurrentFinalRoot,
    mergedNextLocalRoot, mergedNextCrossLevelRoot, mergedNextShiftRoot.
  constructor; assumption.
Qed.

(** Add the selected substitution certificate and retain the first nine
    roots for the axiom-soundness stage. *)
Theorem
    raw_dynamicTruthNativeAxiomStagedPrerequisites_add_substitution :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot nextShiftRoot
      substitutionCertificate,
  RawDynamicTruthNativeSubstitutionStagedPrerequisitesAt M
    witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal nextLocal nextCrossLevel nextShift
    currentLocalRoot currentCrossLevelRoot currentShiftRoot
    currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
    nextLocalRoot nextCrossLevelRoot nextShiftRoot ->
  RawCodedPAProofOf M nextSubstitution substitutionCertificate ->
  exists mergedWitnessList mergedContext
      mergedCurrentLocalRoot mergedCurrentCrossLevelRoot
      mergedCurrentShiftRoot mergedCurrentSubstitutionRoot
      mergedCurrentAxiomSoundnessRoot mergedCurrentFinalRoot
      mergedNextLocalRoot mergedNextCrossLevelRoot mergedNextShiftRoot
      mergedNextSubstitutionRoot : M,
    RawDynamicTruthNativeAxiomStagedPrerequisitesAt M
      mergedWitnessList mergedContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      mergedCurrentLocalRoot mergedCurrentCrossLevelRoot
      mergedCurrentShiftRoot mergedCurrentSubstitutionRoot
      mergedCurrentAxiomSoundnessRoot mergedCurrentFinalRoot
      mergedNextLocalRoot mergedNextCrossLevelRoot mergedNextShiftRoot
      mergedNextSubstitutionRoot.
Proof.
  intros M hPA witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution
    currentLocalRoot currentCrossLevelRoot currentShiftRoot
    currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
    nextLocalRoot nextCrossLevelRoot nextShiftRoot
    substitutionCertificate hprefix hsubstitutionCertificate.
  destruct hprefix as
    [hwitnessed hcurrentLocal hcurrentCrossLevel hcurrentShift
      hcurrentSubstitution hcurrentAxiomSoundness hcurrentFinal
      hnextLocal hnextCrossLevel hnextShift].
  destruct (raw_codedPAProofOf_add_to_witnessed_context_complete
    M hPA nextSubstitution substitutionCertificate
    witnessList baseContext hsubstitutionCertificate hwitnessed) as
    (mergedWitnessList & mergedContext & mergedNextSubstitutionRoot &
      hmergedWitnessed & htransport & hmergedNextSubstitution).
  destruct (htransport currentLocal currentLocalRoot hcurrentLocal) as
    [mergedCurrentLocalRoot hmergedCurrentLocal].
  destruct (htransport currentCrossLevel currentCrossLevelRoot
    hcurrentCrossLevel) as
    [mergedCurrentCrossLevelRoot hmergedCurrentCrossLevel].
  destruct (htransport currentShift currentShiftRoot hcurrentShift) as
    [mergedCurrentShiftRoot hmergedCurrentShift].
  destruct (htransport currentSubstitution currentSubstitutionRoot
    hcurrentSubstitution) as
    [mergedCurrentSubstitutionRoot hmergedCurrentSubstitution].
  destruct (htransport currentAxiomSoundness currentAxiomSoundnessRoot
    hcurrentAxiomSoundness) as
    [mergedCurrentAxiomSoundnessRoot hmergedCurrentAxiomSoundness].
  destruct (htransport currentFinal currentFinalRoot hcurrentFinal) as
    [mergedCurrentFinalRoot hmergedCurrentFinal].
  destruct (htransport nextLocal nextLocalRoot hnextLocal) as
    [mergedNextLocalRoot hmergedNextLocal].
  destruct (htransport nextCrossLevel nextCrossLevelRoot hnextCrossLevel) as
    [mergedNextCrossLevelRoot hmergedNextCrossLevel].
  destruct (htransport nextShift nextShiftRoot hnextShift) as
    [mergedNextShiftRoot hmergedNextShift].
  exists mergedWitnessList, mergedContext,
    mergedCurrentLocalRoot, mergedCurrentCrossLevelRoot,
    mergedCurrentShiftRoot, mergedCurrentSubstitutionRoot,
    mergedCurrentAxiomSoundnessRoot, mergedCurrentFinalRoot,
    mergedNextLocalRoot, mergedNextCrossLevelRoot, mergedNextShiftRoot,
    mergedNextSubstitutionRoot.
  constructor; assumption.
Qed.

End PABoundedRawCodedDynamicTruthNativeStagedPrerequisiteAccumulation.
