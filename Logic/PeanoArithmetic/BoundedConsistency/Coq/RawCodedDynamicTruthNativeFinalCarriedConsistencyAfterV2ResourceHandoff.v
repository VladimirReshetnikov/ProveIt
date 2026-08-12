(**
  Resource-level handoff from the exact V2 dispatcher to the native final
  carried-consistency bridge.

  The V2 dispatcher is already an exact proof-producing construction, but its
  public endpoint is parameterised by a long list of literal append rows and
  three Imp frontiers.  The carried-consistency theorem, in turn, consumes
  the resulting V2 compiler as one premise.  This module composes those two
  interfaces without weakening either side:

  - the literal rows, dynamic Or law, and Imp frontiers remain explicit;
  - the basic/extended direct-input code equalities remain explicit; and
  - the carried consistency bridge and strong-prefix closure remainder are
    passed unchanged to the final proof constructor.

  Thus a future proof of the row/frontier resource bundle can use the theorem
  below directly, while audits can still identify every genuinely missing
  arithmetic resource.  No semantic truth-to-proof conversion or arbitrary
  model induction is introduced here.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedTemplateNumeralParameters
  RawCodedTemplateDirectStructuralTranslation
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs
  RawCodedDynamicTruthNativeLocalStagedCallbackCompilation
  RawCodedDynamicTruthNativeAlignedStrongStepLogicalRootsCompilation
  RawCodedRestrictedPADerivationSoundnessOrIntroductionLeftNativeLawTransport
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpIntroductionRecursive
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpIntroductionTruth
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpElimination
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell
  RawCodedDynamicTruthNativeFinalStagedRootCompilation
  RawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessCarriedBridge
  RawCodedDynamicTruthNativeStagedPositiveSuccessor
  RawCodedRestrictedPADerivationSoundnessAssumptionNativeClosureProjection
  RawCodedRestrictedPADerivationSoundnessDirectBottomAdmissibilityAwareDispatcherIntegration
  RawCodedRestrictedPADerivationSoundnessOrIntroductionLeftNativeClosureContinuation
  RawCodedDynamicTruthNativeFinalCarriedConsistencyAfterV2Soundness.

Module
  PABoundedRawCodedDynamicTruthNativeFinalCarriedConsistencyAfterV2ResourceHandoff.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedTemplateNumeralParameters.
Import
  PABoundedRawCodedTemplateDirectStructuralTranslation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.
Import PABoundedRawCodedDynamicTruthNativeLocalStagedCallbackCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeAlignedStrongStepLogicalRootsCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessOrIntroductionLeftNativeLawTransport.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpIntroductionRecursive.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpIntroductionTruth.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpElimination.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.
Import PABoundedRawCodedDynamicTruthNativeFinalStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessCarriedBridge.
Import PABoundedRawCodedDynamicTruthNativeStagedPositiveSuccessor.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectBottomAdmissibilityAwareDispatcherIntegration.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessOrIntroductionLeftNativeClosureContinuation.
Import
  PABoundedRawCodedDynamicTruthNativeFinalCarriedConsistencyAfterV2Soundness.

(** The exact V2 resource bundle at one direct-input record.  The first two
    premises are the native closure package and the aligned strong-step
    structural package.  The remaining fields are precisely the thirteen
    literal rows, the empty-base dynamic Or law, and the three Imp frontiers
    consumed by the V2 assembler. *)
Definition RawDynamicTruthNativeFinalV2ResourceBundle
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (parameters : RawCodedTemplateNumeralParameters M)
    (contextTruth conclusionTruth :
      RawCoqRestrictedPATruthDirectSelector M parameters)
    (currentGlobalSigma currentGlobalPi predecessorLevel nextSigmaEvidence : M)
    (tail : nat -> M) (predecessorLevel' baseContext currentLocal : M)
    (nextInputGlobalSigma nextInputGlobalPi : M)
    (aligned : RawDynamicTruthNativeLocalAlignedPredecessorAt M tail
      predecessorLevel' baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi)
    (inputLevelNumeral : M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawCoqRestrictedPANativeDirectTruthInputsWithClosureAtFor
    M hPA parameters currentGlobalSigma currentGlobalPi predecessorLevel
    nextSigmaEvidence contextTruth conclusionTruth inputs /\
  RawDynamicTruthNativeAlignedStrongStepStructuralInputsAt
    M hPA tail predecessorLevel' baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned
    inputLevelNumeral inputs /\
  RawCoqRestrictedPADirectV2LiteralRows M hPA inputs /\
  RawCoqRestrictedPADirectDynamicTruthLawRootAtEmpty M hPA inputs /\
  RawCoqRestrictedPADirectSelectedImpIntroductionRecursiveTail
    M hPA inputs /\
  RawCoqRestrictedPADirectSelectedImpIntroductionFixedRowSplitTail
    M hPA inputs /\
  RawCoqRestrictedPADirectSelectedImpECoreTail M hPA inputs.

Arguments RawDynamicTruthNativeFinalV2ResourceBundle
  M hPA parameters contextTruth conclusionTruth
  currentGlobalSigma currentGlobalPi predecessorLevel nextSigmaEvidence
  tail predecessorLevel' baseContext currentLocal
  nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral inputs
  : clear implicits.

(** The resource bundle is exactly sufficient for the V2 compiler.  Keeping
    this as a separate theorem gives callers a short, named adapter and
    prevents accidental omission of one of the three Imp frontiers. *)
Theorem raw_remainingRuleCasesV2Compiler_of_resource_bundle :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (parameters : RawCodedTemplateNumeralParameters M)
    (contextTruth conclusionTruth :
      RawCoqRestrictedPATruthDirectSelector M parameters)
    currentGlobalSigma currentGlobalPi predecessorLevel nextSigmaEvidence
    (tail : nat -> M) predecessorLevel' baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi
    (aligned : RawDynamicTruthNativeLocalAlignedPredecessorAt M tail
      predecessorLevel' baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi)
    inputLevelNumeral
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawDynamicTruthNativeFinalV2ResourceBundle M hPA parameters
    contextTruth conclusionTruth currentGlobalSigma currentGlobalPi
    predecessorLevel nextSigmaEvidence tail predecessorLevel' baseContext
    currentLocal nextInputGlobalSigma nextInputGlobalPi aligned
    inputLevelNumeral inputs ->
  RawCoqRestrictedPADirectRemainingRuleCasesV2StandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA parameters contextTruth conclusionTruth
    currentGlobalSigma currentGlobalPi predecessorLevel nextSigmaEvidence
    tail predecessorLevel' baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral inputs
    hresources.
  unfold RawDynamicTruthNativeFinalV2ResourceBundle in hresources.
  destruct hresources as
    [hclosure [hstructural [hrows [hdynamic
      [himpRecursive [hsplit himpE]]]]]].
  exact
    (raw_remainingRuleCasesV2Compiler_of_literalRows_and_threeImpFrontiers_of_nativeClosureAtFor_of_dynamicLawAtEmpty
      M hPA parameters contextTruth conclusionTruth
      currentGlobalSigma currentGlobalPi predecessorLevel nextSigmaEvidence
      tail predecessorLevel' baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral inputs
      hclosure hstructural hrows hdynamic himpRecursive hsplit himpE).
Qed.

(** Full carried-consistency handoff.  The V2 compiler is generated from the
    resource bundle at [extendedInputs]; the final theorem then transports
    its universal-soundness certificate back to [basicInputs] using the two
    displayed code equalities. *)
Theorem
    raw_dynamicTruthNativeFinalStagedNextFinalProof_of_v2_resource_bundle_and_carried_consistency
    : forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (basicInputs extendedInputs : RawCodedTemplateDirectStructuralInputs M)
      (parameters : RawCodedTemplateNumeralParameters M)
      (contextTruth conclusionTruth :
        RawCoqRestrictedPATruthDirectSelector M parameters)
      currentGlobalSigma currentGlobalPi predecessorLevel nextSigmaEvidence
      (tail : nat -> M) predecessorLevel' baseContext alignedCurrentLocal
      nextInputGlobalSigma nextInputGlobalPi
      (aligned : RawDynamicTruthNativeLocalAlignedPredecessorAt M tail
        predecessorLevel' baseContext alignedCurrentLocal
        nextInputGlobalSigma nextInputGlobalPi)
      inputLevelNumeral
      (stageTail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness nextFinal successorNumeralCode sourceBaseContext
      replacement axiom closureCount,
  rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirectCode M
      extendedInputs =
    rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirectCode M
      basicInputs ->
  rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M extendedInputs =
    rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M basicInputs ->
  RawDynamicTruthNativeFinalV2ResourceBundle M hPA parameters
    contextTruth conclusionTruth currentGlobalSigma currentGlobalPi
    predecessorLevel nextSigmaEvidence tail predecessorLevel' baseContext
    alignedCurrentLocal nextInputGlobalSigma nextInputGlobalPi aligned
    inputLevelNumeral extendedInputs ->
  RawDynamicTruthNativeFinalStagedGraphTraceAt M stageTail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution
    nextAxiomSoundness nextFinal successorNumeralCode ->
  RawCoqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder
    M basicInputs replacement axiom closureCount ->
  RawDynamicTruthNativeFinalCarriedConsistencyCodeBridgeAt M
    (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M basicInputs)
    stageTail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution
    nextAxiomSoundness nextFinal successorNumeralCode sourceBaseContext ->
  exists finalCertificate : M,
    RawDynamicTruthNativeStagedNextFinalProofAt M
      stageTail level nextFinal finalCertificate.
Proof.
  intros M hPA basicInputs extendedInputs
    parameters contextTruth conclusionTruth
    currentGlobalSigma currentGlobalPi predecessorLevel nextSigmaEvidence
    tail predecessorLevel' baseContext alignedCurrentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    stageTail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution
    nextAxiomSoundness nextFinal successorNumeralCode sourceBaseContext
    replacement axiom closureCount
    hbodyCode huniversalCode hresources htrace hremainder hcarried.
  pose proof
    (raw_remainingRuleCasesV2Compiler_of_resource_bundle
      M hPA parameters contextTruth conclusionTruth
      currentGlobalSigma currentGlobalPi predecessorLevel nextSigmaEvidence
      tail predecessorLevel' baseContext alignedCurrentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
      extendedInputs hresources) as hremaining.
  exact
    (raw_dynamicTruthNativeFinalStagedNextFinalProof_of_remaining_v2_carried_code_equalities
      M hPA basicInputs extendedInputs stageTail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness nextFinal successorNumeralCode sourceBaseContext
      replacement axiom closureCount hbodyCode huniversalCode htrace
      hremaining hremainder hcarried).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeFinalCarriedConsistencyAfterV2ResourceHandoff.
