(**
  Bridge the historical predecessor-free remainder to the guarded matrix.

  The older staged decomposition already carries the three non-conditional
  kernel roots (two cross-level quantifier roots and mixed-QF replay).  A
  later guarded matrix interface accidentally repackaged those same roots as
  an additional residual.  The adapters below make the identity explicit and
  assemble the corrected guarded reduced package without requesting any new
  proof-producing premise.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedRestrictedPAProof
  RawCodedTemplateProofCompiler
  RawCodedTemplatePAEmbedding
  RawCodedTruthCertificateMasterFixedHelperBatchExtension
  RawCodedDynamicTruthLocalCollisionMatrixAssembly
  RawCodedDynamicTruthNativeLocalProofCompilation
  RawCodedDynamicTruthNativeLocalStagedRootCompilation
  RawCodedDynamicTruthNativeLocalRowProjectionCompilation
  RawCodedDynamicTruthNativeLocalGrowingPredecessorStagedCallbackCompilation
  RawCodedDynamicTruthNativeLocalGuardedMatrixCompilation
  RawCodedDynamicTruthImpGuardedBranchExclusivity
  RawCodedDynamicTruthNativeLocalGuardedNonImpPairCompilation
  RawCodedDynamicTruthNativeLocalGuardedReducedStagedCompilation.

Module
  PABoundedRawCodedDynamicTruthNativeLocalGuardedRemainderBridge.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTruthCertificateMasterFixedHelperBatchExtension.
Import PABoundedRawCodedDynamicTruthLocalCollisionMatrixAssembly.
Import PABoundedRawCodedDynamicTruthNativeLocalProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalRowProjectionCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeLocalGrowingPredecessorStagedCallbackCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalGuardedMatrixCompilation.
Import PABoundedRawCodedDynamicTruthImpGuardedBranchExclusivity.
Import
  PABoundedRawCodedDynamicTruthNativeLocalGuardedNonImpPairCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeLocalGuardedReducedStagedCompilation.

(** The two records are field-for-field identical.  This projection closes
    the apparent three-root residual without compiling any formula. *)
Definition
    raw_dynamicTruthNativeLocalNonConditionalReducedKernelInputsAt_of_current_kernel_tail
    (M : RawPAModel) context lowerPiApplication lowerSigmaApplication
    (tail : RawDynamicTruthNativeLocalReducedCurrentKernelTailInputsAt
      M context lowerPiApplication lowerSigmaApplication) :
  RawDynamicTruthNativeLocalNonConditionalReducedKernelInputsAt M
    context lowerPiApplication lowerSigmaApplication :=
  {| rawDynamicTruthNativeLocalNonConditionalReducedKernel_sigmaExCrossRoot :=
       rawDynamicTruthNativeLocalReducedKernelTail_sigmaExCrossRoot
         M context lowerPiApplication lowerSigmaApplication tail;
     rawDynamicTruthNativeLocalNonConditionalReducedKernel_sigmaAllCrossRoot :=
       rawDynamicTruthNativeLocalReducedKernelTail_sigmaAllCrossRoot
         M context lowerPiApplication lowerSigmaApplication tail;
     rawDynamicTruthNativeLocalNonConditionalReducedKernel_mixedReplayRoot :=
       rawDynamicTruthNativeLocalReducedKernelTail_mixedReplayRoot
         M context lowerPiApplication lowerSigmaApplication tail |}.

(** Extract the same reduced kernel directly from the predecessor-free staged
    remainder. *)
Theorem
    raw_dynamicTruthNativeLocalNonConditionalReducedKernelInputsAt_of_reduced_staged_without_predecessor :
    forall (M : RawPAModel) baseContext
      sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication,
  RawDynamicTruthNativeLocalReducedStagedRootsWithoutPredecessorAt M
    baseContext sigmaDomain piDomain sigmaEvidence piEvidence
    sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthNativeLocalNonConditionalReducedKernelInputsAt M
    baseContext lowerPiApplication lowerSigmaApplication.
Proof.
  intros M baseContext sigmaDomain piDomain sigmaEvidence piEvidence
    sigmaRowDomain piRowDomain lowerPi lowerSigma
    (_ & _ & _ & kernelTail & _).
  exact
    (raw_dynamicTruthNativeLocalNonConditionalReducedKernelInputsAt_of_current_kernel_tail
      M baseContext lowerPi lowerSigma kernelTail).
Qed.

(** Assemble the guarded reduced package.  Exact rows and the fixed helper
    batch compile all non-implication cells from the inherited kernel tail;
    the corrected guarded predecessor is inserted only in the final field. *)
Theorem
    raw_dynamicTruthNativeLocalGuardedReducedStagedRootsAt_of_reduced_staged_without_predecessor_and_boolean_and_guarded_predecessor :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      translation witnessList baseContext helperRoots
      (tail : nat -> M) predecessorLevel inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication,
  RawCodedTemplatePAAgreement M translation ->
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawFixedPAHelperBatchLocalProofs M translation baseContext
    rawDynamicTruthReadyAndGuardedMixedQFPAHelpers helperRoots ->
  RawDynamicTruthNativeLocalProofTraceAt M tail predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence ->
  RawDynamicTruthNativeLocalExactRowParametersAt M predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaEvidence piEvidence
    sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthNativeLocalReducedStagedRootsWithoutPredecessorAt M
    baseContext sigmaDomain piDomain sigmaEvidence piEvidence
    sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthLocalBooleanDiagonalPairRootsAt M baseContext ->
  RawDynamicTruthLocalRootAt M baseContext
    (rawDynamicTruthImpGuardedPredecessorStateExclusivityCode M) ->
  RawDynamicTruthNativeLocalGuardedReducedStagedRootsAt M baseContext
    sigmaDomain piDomain sigmaEvidence piEvidence
    sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication.
Proof.
  intros M hPA translation witnessList baseContext helperRoots
    tail predecessorLevel inputGlobalSigma inputGlobalPi
    sigmaDomain piDomain sigmaEvidence piEvidence
    sigmaRowDomain piRowDomain lowerPi lowerSigma
    hagreement hwitness hhelpers htrace hrows
    (hcases & hsigmaRow & hpiRow & kernelTail & _)
    hboolean hguardedPredecessor.
  pose proof
    (raw_dynamicTruthNativeLocalNonConditionalReducedKernelInputsAt_of_current_kernel_tail
      M baseContext lowerPi lowerSigma kernelTail) as kernel.
  pose proof
    (raw_dynamicTruthLocalCollisionPairFamilyWithoutImpAt_of_42_helpers_on_exact_rows_and_boolean
      M hPA translation witnessList baseContext helperRoots
      tail predecessorLevel inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain lowerPi lowerSigma
      hagreement hwitness hhelpers htrace hrows kernel hboolean)
    as hwithoutImp.
  repeat split; assumption.
Qed.

End
  PABoundedRawCodedDynamicTruthNativeLocalGuardedRemainderBridge.
