(**
  Feed extended-input V2 soundness into the basic carried bridge.

  The synchronized native construction carries consistency before the
  ordinary rule-case certificate is compiled.  Rule cases use an extended
  direct translation, while the carried implication is indexed by the basic
  translation.  This module performs the entire honest handoff:

    1. transport the basic carrier-closure remainder to the extended body;
    2. compile ordinary universal soundness from the V2 rule cases;
    3. retarget that certificate along equality of the universal codes; and
    4. apply the existing carried-then-ordinary final-proof theorem.

  The generic theorem assumes only the two code equalities, not equality of
  the input records.  A concrete corollary discharges both equalities for an
  arbitrary opaque selector tail using the syntactic support theorems.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedPAProvability
  RawCodedTemplateNumeralParameters
  RawCodedTemplateDirectStructuralTranslation
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs
  RawCodedRestrictedPADerivationSoundnessExtendedDirectInputs
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell
  RawCodedRestrictedPADerivationSoundnessDirectBottomAdmissibilityAwareDispatcherIntegration
  RawCodedRestrictedPADerivationSoundnessUniversalDirectCodeTailInvariance
  RawCodedDynamicTruthNativeStagedPositiveSuccessor
  RawCodedDynamicTruthNativeFinalStagedRootCompilation
  RawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessCarriedBridge
  RawCodedDynamicTruthNativeFinalCarriedConsistencyAfterOrdinarySoundness.

Module
  PABoundedRawCodedDynamicTruthNativeFinalCarriedConsistencyAfterV2Soundness.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessExtendedDirectInputs.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectBottomAdmissibilityAwareDispatcherIntegration.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessUniversalDirectCodeTailInvariance.
Import PABoundedRawCodedDynamicTruthNativeStagedPositiveSuccessor.
Import PABoundedRawCodedDynamicTruthNativeFinalStagedRootCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessCarriedBridge.
Import
  PABoundedRawCodedDynamicTruthNativeFinalCarriedConsistencyAfterOrdinarySoundness.

(** Fully generic record-independent handoff.  The equalities mention only
    the two translated formula codes observed by this construction. *)
Theorem
    raw_dynamicTruthNativeFinalStagedNextFinalProof_of_remaining_v2_carried_code_equalities
    : forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (basicInputs extendedInputs : RawCodedTemplateDirectStructuralInputs M)
      (tail : nat -> M) level
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
  RawDynamicTruthNativeFinalStagedGraphTraceAt M tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode ->
  RawCoqRestrictedPADirectRemainingRuleCasesV2StandardTailCompiler
    M hPA extendedInputs ->
  RawCoqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder
    M basicInputs replacement axiom closureCount ->
  RawDynamicTruthNativeFinalCarriedConsistencyCodeBridgeAt M
    (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M basicInputs)
    tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution
    nextAxiomSoundness nextFinal successorNumeralCode sourceBaseContext ->
  exists finalCertificate : M,
    RawDynamicTruthNativeStagedNextFinalProofAt M
      tail level nextFinal finalCertificate.
Proof.
  intros M hPA basicInputs extendedInputs tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution
    nextAxiomSoundness nextFinal successorNumeralCode sourceBaseContext
    replacement axiom closureCount hbodyCode huniversalCode htrace
    hremaining hremainder hcarried.
  pose proof
    (raw_coqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder_transport
      M basicInputs extendedInputs replacement axiom closureCount
      (eq_sym hbodyCode) hremainder) as hextendedRemainder.
  destruct
    (raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversalDirect_of_remaining_v2_after_orIntroductionLeft
      M hPA extendedInputs hremaining
      replacement axiom closureCount hextendedRemainder)
    as [soundnessCertificate hextendedCertificate].
  assert (hbasicCertificate : RawCodedPAProofOf M
      (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M basicInputs)
      soundnessCertificate).
  {
    rewrite <- huniversalCode.
    exact hextendedCertificate.
  }
  exact
    (raw_dynamicTruthNativeFinalStagedNextFinalProof_of_direct_carried_then_ordinary
      M hPA basicInputs tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness nextFinal successorNumeralCode sourceBaseContext
      soundnessCertificate htrace hbasicCertificate hcarried).
Qed.

(** Opaque-tail specialization.  No property of the extra selectors is
    required here beyond the direct-operation witnesses stored in [tail]. *)
Corollary
    raw_dynamicTruthNativeFinalStagedNextFinalProof_of_extended_remaining_v2_and_basic_carried
    : forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (parameters : RawCodedTemplateNumeralParameters M)
      (contextTruth conclusionTruth :
        RawCoqRestrictedPATruthDirectSelector M parameters)
      (opaqueTail : RawCoqRestrictedPAOpaqueTailDirectSelector M parameters)
      (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness nextFinal successorNumeralCode sourceBaseContext
      replacement axiom closureCount,
  RawDynamicTruthNativeFinalStagedGraphTraceAt M tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode ->
  RawCoqRestrictedPADirectRemainingRuleCasesV2StandardTailCompiler M hPA
    (rawCoqRestrictedPADerivationSoundnessExtendedDirectStructuralInputs
      M hPA parameters contextTruth conclusionTruth opaqueTail) ->
  RawCoqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder M
    (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
      M hPA parameters contextTruth conclusionTruth)
    replacement axiom closureCount ->
  RawDynamicTruthNativeFinalCarriedConsistencyCodeBridgeAt M
    (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M
      (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth))
    tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution
    nextAxiomSoundness nextFinal successorNumeralCode sourceBaseContext ->
  exists finalCertificate : M,
    RawDynamicTruthNativeStagedNextFinalProofAt M
      tail level nextFinal finalCertificate.
Proof.
  intros M hPA parameters contextTruth conclusionTruth opaqueTail tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution
    nextAxiomSoundness nextFinal successorNumeralCode sourceBaseContext
    replacement axiom closureCount htrace hremaining hremainder hcarried.
  apply
    (raw_dynamicTruthNativeFinalStagedNextFinalProof_of_remaining_v2_carried_code_equalities
      M hPA
      (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth)
      (rawCoqRestrictedPADerivationSoundnessExtendedDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth opaqueTail)
      tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness nextFinal successorNumeralCode sourceBaseContext
      replacement axiom closureCount).
  - exact
      (raw_coqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirectCode_extended_eq_basic
        M hPA parameters contextTruth conclusionTruth opaqueTail).
  - exact
      (raw_coqRestrictedPADerivationSoundnessUniversalDirectCode_extended_eq_basic
        M hPA parameters contextTruth conclusionTruth opaqueTail).
  - exact htrace.
  - exact hremaining.
  - exact hremainder.
  - exact hcarried.
Qed.

End
  PABoundedRawCodedDynamicTruthNativeFinalCarriedConsistencyAfterV2Soundness.
