(**
  Assemble guarded collision roots by the native zero/successor split.

  Rank zero and positive rank use genuinely different proof resources.  The
  former is normalized to the canonical bottom trace; the latter carries an
  aligned predecessor record.  This module keeps those producers separate and
  performs only the structural case analysis already proved for a native local
  callback.  Both branches may grow their witnessed PA tails.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedRestrictedPAProof
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTemplateProofCompiler
  RawCodedDynamicTruthLocalCollisionMatrixAssembly
  RawCodedDynamicTruthMixedQFOpaqueQuantifierCellCompilation
  RawCodedDynamicTruthImpGuardedBranchExclusivity
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthNativeLocalProofCompilation
  RawCodedDynamicTruthNativeLocalStagedCallbackCompilation
  RawCodedDynamicTruthNativeLocalHelperBatchGeneralization
  RawCodedDynamicTruthNativeLocalGuardedNonImpPairCompilation
  RawCodedDynamicTruthNativeLocalGrowingPredecessorStagedCallbackCompilation
  RawCodedDynamicTruthNativeLocalGuardedBuilderDecomposition.

Module
  PABoundedRawCodedDynamicTruthNativeLocalGuardedCollisionCaseSplit.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedDynamicTruthLocalCollisionMatrixAssembly.
Import PABoundedRawCodedDynamicTruthMixedQFOpaqueQuantifierCellCompilation.
Import PABoundedRawCodedDynamicTruthImpGuardedBranchExclusivity.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeLocalProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalStagedCallbackCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeLocalHelperBatchGeneralization.
Import
  PABoundedRawCodedDynamicTruthNativeLocalGuardedNonImpPairCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeLocalGrowingPredecessorStagedCallbackCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeLocalGuardedBuilderDecomposition.

(** Rank-zero producer at the literal guarded callback interface. *)
Definition
    RawDynamicTruthNativeLocalZeroGrowingGuardedCollisionRootsCompilerOnCurrentGuardedHelperContext
    (M : RawPAModel) (hPA : RawPASatisfies M)
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
    level = raw_zero M ->
    exists targetWitnessList targetContext,
      RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
      RawContextListIncluded M baseContext targetContext /\
      RawDynamicTruthLocalBooleanDiagonalPairRootsAt M targetContext /\
      RawDynamicTruthLocalRootAt M targetContext
        (rawDynamicTruthImpGuardedPredecessorStateExclusivityCode M).

Arguments
  RawDynamicTruthNativeLocalZeroGrowingGuardedCollisionRootsCompilerOnCurrentGuardedHelperContext
  M hPA translation : clear implicits.

(** Positive-rank producer after the native trace has selected and aligned its
    predecessor.  Passing the existing witness list is weaker than asking the
    producer to rediscover a witness for [baseContext]. *)
Definition
    RawDynamicTruthNativeLocalAlignedGrowingGuardedCollisionRootsCompilerOnWitnessedBase
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi
      (aligned : RawDynamicTruthNativeLocalAlignedPredecessorAt M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi)
      sourceWitnessList,
    RawCodedPAAxiomWitnessContext M sourceWitnessList baseContext ->
    exists targetWitnessList targetContext,
      RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
      RawContextListIncluded M baseContext targetContext /\
      RawDynamicTruthLocalBooleanDiagonalPairRootsAt M targetContext /\
      RawDynamicTruthLocalRootAt M targetContext
        (rawDynamicTruthImpGuardedPredecessorStateExclusivityCode M).

Arguments
  RawDynamicTruthNativeLocalAlignedGrowingGuardedCollisionRootsCompilerOnWitnessedBase
  M : clear implicits.

(** Structural assembly into the public collision builder.  No collision
    formula is proved here; the theorem only routes the exact zero or aligned
    successor resources to the corresponding producer. *)
Theorem
    raw_dynamicTruthNativeLocalCurrentGrowingGuardedCollisionRootsBuilder_of_zero_and_witnessed_aligned :
    forall (M : RawPAModel) (hPA : RawPASatisfies M),
  forall (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeLocalZeroGrowingGuardedCollisionRootsCompilerOnCurrentGuardedHelperContext
    M hPA translation ->
  RawDynamicTruthNativeLocalAlignedGrowingGuardedCollisionRootsCompilerOnWitnessedBase
    M ->
  RawDynamicTruthNativeLocalCurrentGrowingGuardedCollisionRootsBuilder
    M translation.
Proof.
  intros M hPA translation hzero haligned tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal witnessList baseContext helperRoots
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain sigmaEvidence
    piEvidence hcurrent htrace sigmaRowDomain piRowDomain
    lowerPiApplication lowerSigmaApplication hrows.
  pose proof
    (raw_dynamicTruthNativeLocalCurrentHelperContextAt_of_guarded
      M translation tail level currentLocal currentCrossLevel currentShift
      currentSubstitution currentAxiomSoundness currentFinal
      witnessList baseContext helperRoots hcurrent) as hlegacyCurrent.
  destruct
    (raw_dynamicTruthNativeLocalCurrentHelperContextAt_exact_cases_aligned_with_next
      M hPA translation tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal witnessList baseContext
      (firstn (length rawDynamicTruthReadyAndAllMixedQFPAHelpers)
        helperRoots)
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain sigmaEvidence
      piEvidence hlegacyCurrent htrace) as
    [(_currentLocalRoot & hlevel & _hfield & _hcurrentRoot) |
      (predecessorLevel & _hlevel & aligned & _halignedRows)].
  - exact
      (hzero tail level
        currentLocal currentCrossLevel currentShift currentSubstitution
        currentAxiomSoundness currentFinal witnessList baseContext helperRoots
        inputGlobalSigma inputGlobalPi sigmaDomain piDomain sigmaEvidence
        piEvidence hcurrent htrace hlevel).
  - pose proof hcurrent as hfields.
    unfold RawDynamicTruthNativeLocalCurrentGuardedHelperContextAt,
      RawDynamicTruthNativeLocalCurrentHelperBatchContextAt in hfields.
    destruct hfields as
      [_ (_ & _ & _ & _ & _ & _ & hbaseWitnessed & _)].
    exact
      (haligned tail predecessorLevel baseContext currentLocal
        inputGlobalSigma inputGlobalPi aligned witnessList hbaseWitnessed).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeLocalGuardedCollisionCaseSplit.
