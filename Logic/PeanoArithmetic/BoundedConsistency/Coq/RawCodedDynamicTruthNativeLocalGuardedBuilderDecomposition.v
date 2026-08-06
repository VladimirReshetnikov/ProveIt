(**
  Decompose the growing guarded local builder into its two honest residues.

  The public guarded callback formerly requested the complete reduced staged
  package in one opaque operation.  That package mixes two independent kinds
  of work:

  - the constructor-sensitive Boolean diagonal pair and guarded implication
    predecessor; and
  - the predecessor-free case, row, and inherited-kernel remainder.

  Keeping them separate matters.  The first component may enlarge the
  witnessed PA context while compiling branch-local evidence.  Once that
  target is fixed, the second component can build the structural remainder
  directly there.  The existing remainder bridge then reuses the inherited
  three-root kernel tail and assembles the corrected guarded matrix.

  No legacy unconditional predecessor root occurs in either new interface.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedRestrictedPAProof
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTemplateProofCompiler
  RawCodedTemplatePAEmbedding
  RawCodedTruthCertificateMasterFixedHelperBatchExtension
  RawCodedDynamicTruthLocalCollisionMatrixAssembly
  RawCodedDynamicTruthImpGuardedBranchExclusivity
  RawCodedDynamicTruthMixedQFOpaqueQuantifierCellCompilation
  RawCodedDynamicTruthNativeLocalProofCompilation
  RawCodedDynamicTruthNativeLocalStagedRootCompilation
  RawCodedDynamicTruthNativeLocalStagedCallbackCompilation
  RawCodedDynamicTruthNativeLocalGrowingStagedCallbackCompilation
  RawCodedDynamicTruthNativeLocalGrowingPredecessorStagedCallbackCompilation
  RawCodedDynamicTruthNativeLocalGuardedMatrixCompilation
  RawCodedDynamicTruthNativeLocalGuardedNonImpPairCompilation
  RawCodedDynamicTruthNativeLocalHelperBatchGeneralization
  RawCodedDynamicTruthNativeLocalGuardedReducedStagedCompilation
  RawCodedDynamicTruthNativeLocalGuardedGrowingStagedCallbackCompilation
  RawCodedDynamicTruthNativeLocalGuardedRemainderBridge.

Module
  PABoundedRawCodedDynamicTruthNativeLocalGuardedBuilderDecomposition.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTruthCertificateMasterFixedHelperBatchExtension.
Import PABoundedRawCodedDynamicTruthLocalCollisionMatrixAssembly.
Import PABoundedRawCodedDynamicTruthImpGuardedBranchExclusivity.
Import PABoundedRawCodedDynamicTruthMixedQFOpaqueQuantifierCellCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalStagedCallbackCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeLocalGrowingStagedCallbackCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeLocalGrowingPredecessorStagedCallbackCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalGuardedMatrixCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeLocalGuardedNonImpPairCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeLocalHelperBatchGeneralization.
Import
  PABoundedRawCodedDynamicTruthNativeLocalGuardedReducedStagedCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeLocalGuardedGrowingStagedCallbackCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeLocalGuardedRemainderBridge.

(** The constructor-sensitive half may grow the guarded helper context.  Its
    two products already live on one literal target, so the later assembler
    never has to guess how independently selected witness batches align. *)
Definition
    RawDynamicTruthNativeLocalCurrentGrowingGuardedCollisionRootsBuilder
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M) : Prop :=
  forall (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      witnessList baseContext (helperRoots : list M)
      inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalCurrentGuardedHelperContextAt M translation
      tail level currentLocal currentCrossLevel currentShift
      currentSubstitution currentAxiomSoundness currentFinal
      witnessList baseContext helperRoots ->
    RawDynamicTruthNativeLocalProofTraceAt M tail level
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence ->
    forall sigmaRowDomain piRowDomain
        lowerPiApplication lowerSigmaApplication,
      RawDynamicTruthNativeLocalExactRowParametersAt M level
        inputGlobalSigma inputGlobalPi sigmaEvidence piEvidence
        sigmaRowDomain piRowDomain
        lowerPiApplication lowerSigmaApplication ->
      exists targetWitnessList targetContext,
        RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
        RawContextListIncluded M baseContext targetContext /\
        RawDynamicTruthLocalBooleanDiagonalPairRootsAt M targetContext /\
        RawDynamicTruthLocalRootAt M targetContext
          (rawDynamicTruthImpGuardedPredecessorStateExclusivityCode M).

Arguments
  RawDynamicTruthNativeLocalCurrentGrowingGuardedCollisionRootsBuilder
  M translation : clear implicits.

(** The structural remainder is deliberately independent of every
    predecessor formula.  It is requested only after a consumer has selected
    a witnessed target context, which avoids all later transport of its row
    roots through the inserted local-exclusive context. *)
Definition
    RawDynamicTruthNativeLocalCurrentNonConditionalReducedStagedRemainderBuilder
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M) : Prop :=
  forall (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      witnessList baseContext (helperRoots : list M)
      inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalCurrentHelperContextAt M translation
      tail level currentLocal currentCrossLevel currentShift
      currentSubstitution currentAxiomSoundness currentFinal
      witnessList baseContext helperRoots ->
    RawDynamicTruthNativeLocalProofTraceAt M tail level
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence ->
    forall sigmaRowDomain piRowDomain
        lowerPiApplication lowerSigmaApplication,
      RawDynamicTruthNativeLocalExactRowParametersAt M level
        inputGlobalSigma inputGlobalPi sigmaEvidence piEvidence
        sigmaRowDomain piRowDomain
        lowerPiApplication lowerSigmaApplication ->
    forall targetWitnessList targetContext,
      RawCodedPAAxiomWitnessContext M targetWitnessList targetContext ->
      RawContextListIncluded M baseContext targetContext ->
      RawDynamicTruthNativeLocalReducedStagedRootsWithoutPredecessorAt M
        targetContext sigmaDomain piDomain sigmaEvidence piEvidence
        sigmaRowDomain piRowDomain
        lowerPiApplication lowerSigmaApplication.

Arguments
  RawDynamicTruthNativeLocalCurrentNonConditionalReducedStagedRemainderBuilder
  M translation : clear implicits.

(** Forgetting the predecessor argument recovers the historical remainder
    interface.  This compatibility result also documents that the old input
    was not represented in its output type. *)
Theorem
    raw_dynamicTruthNativeLocalCurrentGrowingReducedStagedRemainderBuilder_of_nonconditional :
    forall (M : RawPAModel)
      (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeLocalCurrentNonConditionalReducedStagedRemainderBuilder
    M translation ->
  RawDynamicTruthNativeLocalCurrentGrowingReducedStagedRemainderBuilder
    M translation.
Proof.
  intros M translation hremainder tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal witnessList baseContext helperRoots
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain sigmaEvidence
    piEvidence hcurrent htrace sigmaRowDomain piRowDomain
    lowerPiApplication lowerSigmaApplication hrows
    targetWitnessList targetContext htargetWitnessed hincluded
    _hlegacyPredecessor.
  exact (hremainder tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal witnessList baseContext helperRoots
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain sigmaEvidence
    piEvidence hcurrent htrace sigmaRowDomain piRowDomain
    lowerPiApplication lowerSigmaApplication hrows
    targetWitnessList targetContext htargetWitnessed hincluded).
Qed.

(** Assemble the public guarded builder from the two split producers.  The
    guarded helper batch is transported only after the collision producer
    chooses its target.  The predecessor-free remainder is then built at that
    same target and the inherited kernel-tail bridge performs the final
    record assembly. *)
Theorem
    raw_dynamicTruthNativeLocalCurrentGrowingGuardedReducedStagedRootBuilder_of_collision_and_nonconditional_remainder :
    forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  RawDynamicTruthNativeLocalCurrentGrowingGuardedCollisionRootsBuilder
    M translation ->
  RawDynamicTruthNativeLocalCurrentNonConditionalReducedStagedRemainderBuilder
    M translation ->
  RawDynamicTruthNativeLocalCurrentGrowingGuardedReducedStagedRootBuilder
    M translation.
Proof.
  intros M hPA translation hagreement hcollision hremainder
    tail level currentLocal currentCrossLevel currentShift
    currentSubstitution currentAxiomSoundness currentFinal
    witnessList baseContext helperRoots inputGlobalSigma inputGlobalPi
    sigmaDomain piDomain sigmaEvidence piEvidence hcurrent htrace
    sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication
    hrows.
  destruct (hcollision tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal witnessList baseContext helperRoots
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain sigmaEvidence
    piEvidence hcurrent htrace sigmaRowDomain piRowDomain
    lowerPiApplication lowerSigmaApplication hrows) as
    (targetWitnessList & targetContext & htargetWitnessed & hincluded &
      hboolean & hguardedPredecessor).
  set (legacyHelperRoots :=
    firstn (length rawDynamicTruthReadyAndAllMixedQFPAHelpers) helperRoots).
  assert (hlegacyCurrent :
      RawDynamicTruthNativeLocalCurrentHelperContextAt M translation
        tail level currentLocal currentCrossLevel currentShift
        currentSubstitution currentAxiomSoundness currentFinal
        witnessList baseContext legacyHelperRoots).
  {
    unfold legacyHelperRoots.
    exact
      (raw_dynamicTruthNativeLocalCurrentHelperContextAt_of_guarded
        M translation tail level currentLocal currentCrossLevel currentShift
        currentSubstitution currentAxiomSoundness currentFinal
        witnessList baseContext helperRoots hcurrent).
  }
  pose proof (hremainder tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal witnessList baseContext
    legacyHelperRoots inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence hlegacyCurrent htrace
    sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication
    hrows targetWitnessList targetContext htargetWitnessed hincluded)
    as hstructuralRemainder.
  pose proof hcurrent as hguardedFields.
  unfold RawDynamicTruthNativeLocalCurrentGuardedHelperContextAt,
    RawDynamicTruthNativeLocalCurrentHelperBatchContextAt
    in hguardedFields.
  destruct hguardedFields as
    [_ (currentLocalRoot & currentCrossLevelRoot & currentShiftRoot &
      currentSubstitutionRoot & currentAxiomSoundnessRoot &
      currentFinalRoot & hbaseWitnessed & hcurrentLocal &
      hcurrentCrossLevel & hcurrentShift & hcurrentSubstitution &
      hcurrentAxiomSoundness & hcurrentFinal & hhelpers)].
  destruct
    (raw_fixedPAHelperBatchLocalProofs_witnessed_inclusion
      M hPA translation rawDynamicTruthReadyAndGuardedMixedQFPAHelpers
      helperRoots witnessList baseContext targetWitnessList targetContext
      hbaseWitnessed htargetWitnessed hincluded hhelpers)
    as [targetHelperRoots htargetHelpers].
  exists targetWitnessList, targetContext.
  split; [exact htargetWitnessed |].
  split; [exact hincluded |].
  exact
    (raw_dynamicTruthNativeLocalGuardedReducedStagedRootsAt_of_reduced_staged_without_predecessor_and_boolean_and_guarded_predecessor
      M hPA translation targetWitnessList targetContext targetHelperRoots
      tail level inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication
      hagreement htargetWitnessed htargetHelpers htrace hrows
      hstructuralRemainder hboolean hguardedPredecessor).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeLocalGuardedBuilderDecomposition.
