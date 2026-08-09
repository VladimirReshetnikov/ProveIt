(**
  Carry final consistency assembly across one later bottom-proof extension.

  Arithmetic and native axiom-context compilation may already have selected
  an intermediate witnessed PA base.  The honest selected-Sigma refutation
  can require another finite standard-axiom prefix.  Its root therefore need
  not inhabit the intermediate bridge context.

  This module packages that last growth step.  It transports all eleven
  staged prerequisites, the native coherence root, and each of the three
  arithmetic roots to the bottom compiler's returned base.  The pointwise
  assembler can then consume the checked bottom root directly.  No equality
  between the intermediate and final contexts is assumed.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTemplateNumeralParameters
  RawCodedTemplateTernaryApplication
  RawCodedTemplateDirectStructuralTranslation
  RawCodedDynamicContextTruthSelector
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPAConsistencyFromUniversalSoundnessDirect
  RawCodedRestrictedPAConsistencyFromUniversalSoundnessDirectOpenShell
  RawCodedRestrictedPAConsistencyFromUniversalSoundnessDirectOpenIntegration
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell
  RawCodedDynamicTruthNativeFinalStagedRootCompilation
  RawCodedDynamicTruthNativeFinalStagedPrerequisitesWitnessedTransport
  RawCodedRestrictedPAAxiomContextTruthNativeDirectBodyShell
  RawCodedRestrictedPAConsistencyBridgeContextTransport
  RawCodedRestrictedPANativeFinalUnifiedTruthLink
  RawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessCarriedBridge
  RawCodedDynamicTruthNativeFinalCarriedConsistencyFromUnifiedSupport.

Module
  PABoundedRawCodedDynamicTruthNativeFinalCarriedConsistencyBottomGrowth.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedDynamicContextTruthSelector.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundnessDirect.
Import
  PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundnessDirectOpenShell.
Import
  PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundnessDirectOpenIntegration.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.
Import PABoundedRawCodedDynamicTruthNativeFinalStagedRootCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeFinalStagedPrerequisitesWitnessedTransport.
Import
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectBodyShell.
Import PABoundedRawCodedRestrictedPAConsistencyBridgeContextTransport.
Import PABoundedRawCodedRestrictedPANativeFinalUnifiedTruthLink.
Import
  PABoundedRawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessCarriedBridge.
Import
  PABoundedRawCodedDynamicTruthNativeFinalCarriedConsistencyFromUnifiedSupport.

(** The exact proof-producing output of a context-growing bottom compiler.
    Keeping all three carrier codes in one existential package prevents a
    caller from pairing a root with a different witness/context extension. *)
Definition RawDynamicTruthNativeFinalDirectBottomGrowthAt
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (successorNumeralCode sourceBaseContext : M) : Prop :=
  exists finalWitnessList finalBaseContext bottomRoot : M,
    RawCodedPAAxiomWitnessContext M finalWitnessList finalBaseContext /\
    RawContextListIncluded M sourceBaseContext finalBaseContext /\
    RawCodedPALocalProofOf M
      (rawCoqRestrictedPAConsistencyBridgeContextCode M
        successorNumeralCode finalBaseContext)
      (rawCoqRestrictedPABottomTruthRefutationDirectCode M inputs)
      bottomRoot.

Arguments RawDynamicTruthNativeFinalDirectBottomGrowthAt
  M inputs successorNumeralCode sourceBaseContext : clear implicits.

(** The witnessed base is a structural coordinate of every staged
    prerequisite package.  Expose it once for transport clients. *)
Lemma raw_dynamicTruthNativeFinalStagedPrerequisites_witnessed : forall
    (M : RawPAModel) witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution
    nextAxiomSoundness,
  RawDynamicTruthNativeFinalStagedPrerequisitesOn M
    witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution
    nextAxiomSoundness ->
  RawCodedPAAxiomWitnessContext M witnessList baseContext.
Proof.
  intros M witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution
    nextAxiomSoundness hprerequisites.
  destruct hprerequisites as
    (currentLocalRoot & currentCrossLevelRoot & currentShiftRoot &
      currentSubstitutionRoot & currentAxiomSoundnessRoot &
      currentFinalRoot & nextLocalRoot & nextCrossLevelRoot &
      nextShiftRoot & nextSubstitutionRoot & nextAxiomSoundnessRoot &
      [hprefix _]).
  destruct hprefix as
    [hwitnessed _ _ _ _ _ _ _ _ _ _].
  exact hwitnessed.
Qed.

(** Compose literal membership inclusions.  This relation is extensional in
    membership, so no represented list traversal or model arithmetic is
    needed for transitivity. *)
Lemma raw_contextListIncluded_trans : forall (M : RawPAModel) first second third,
  RawContextListIncluded M first second ->
  RawContextListIncluded M second third ->
  RawContextListIncluded M first third.
Proof.
  intros M first second third hfirst hsecond member hmember.
  exact (hsecond member (hfirst member hmember)).
Qed.

Theorem
    raw_dynamicTruthNativeFinalCarriedConsistencyCodeBridge_of_bottom_growth
    : forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (parameters : RawCodedTemplateNumeralParameters M)
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      nextSigmaEvidence nextGlobalSigma nextGlobalPi
      (sigmaApplicationSelector :
        RawCodedTernaryApplicationSelector M nextGlobalSigma)
      (contextApplicationSelector :
        RawCodedTernaryApplicationSelector M
          (rawDynamicContextAllSigmaCode sigmaApplicationSelector))
      closureCount axiom carriedSourceBaseContext
      intermediateWitnessList intermediateBaseContext
      coherenceRoot admissibleRoot contextBoundedRoot contextAdequateRoot,
  RawDynamicTruthNativeFinalStagedGraphTraceAt M tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode ->
  RawDynamicTruthNativeFinalStagedPrerequisitesOn M
    intermediateWitnessList intermediateBaseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution
    nextAxiomSoundness ->
  RawContextListIncluded M carriedSourceBaseContext intermediateBaseContext ->
  rawDirectTemplateTerm inputs
    coqRestrictedPASoundnessLowerLevelTerm = successorNumeralCode ->
  RawCoqRestrictedPANativeFinalUnifiedTruthLinkAt
    M parameters inputs tail level
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence nextAxiomSoundness nextGlobalSigma nextGlobalPi
    sigmaApplicationSelector contextApplicationSelector
    closureCount axiom ->
  RawCodedPALocalProofOf M
    (rawCoqRestrictedPAConsistencyBridgeContextCode
      M successorNumeralCode intermediateBaseContext)
    (rawFormulaImpCode M nextAxiomSoundness
      (rawCoqRestrictedPAAxiomContextsTruthDirectCode M inputs))
    coherenceRoot ->
  RawCoqRestrictedPAOpenShellArithmeticResidual M inputs
    (rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode
      M inputs successorNumeralCode intermediateBaseContext)
    admissibleRoot contextBoundedRoot contextAdequateRoot ->
  RawDynamicTruthNativeFinalDirectBottomGrowthAt M inputs
    successorNumeralCode intermediateBaseContext ->
  RawDynamicTruthNativeFinalCarriedConsistencyCodeBridgeAt M
    (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M inputs)
    tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode carriedSourceBaseContext.
Proof.
  intros M hPA parameters inputs tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence nextGlobalSigma nextGlobalPi
    sigmaApplicationSelector contextApplicationSelector
    closureCount axiom carriedSourceBaseContext
    intermediateWitnessList intermediateBaseContext
    coherenceRoot admissibleRoot contextBoundedRoot contextAdequateRoot
    htrace hintermediatePrerequisites hcarriedIncluded hlevel hunified
    hcoherence harithmetic hbottomGrowth.
  destruct hbottomGrowth as
    (finalWitnessList & finalBaseContext & bottomRoot &
      hfinalWitnessed & hintermediateIncluded & hbottom).
  pose proof
    (raw_dynamicTruthNativeFinalStagedPrerequisites_witnessed
      M intermediateWitnessList intermediateBaseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness hintermediatePrerequisites)
    as hintermediateWitnessed.
  pose proof
    (raw_dynamicTruthNativeFinalStagedPrerequisites_witnessed_context_transport
      M hPA intermediateWitnessList intermediateBaseContext
      finalWitnessList finalBaseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness hintermediatePrerequisites
      hfinalWitnessed hintermediateIncluded)
    as hfinalPrerequisites.
  pose proof
    (raw_dynamicTruthNativeFinal_bridge_context_all_atomically_adequate
      M hPA tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness nextFinal successorNumeralCode
      finalWitnessList finalBaseContext htrace hfinalPrerequisites)
    as hfinalBridgeAdequate.
  pose proof
    (raw_codedPAAxiomWitnessContext_context_realizable M
      intermediateWitnessList intermediateBaseContext
      hintermediateWitnessed) as hintermediateRealizable.
  pose proof
    (raw_codedPAAxiomWitnessContext_context_realizable M
      finalWitnessList finalBaseContext hfinalWitnessed)
    as hfinalRealizable.
  destruct
    (raw_codedPALocalProof_coqRestrictedPAConsistencyBridgeContext_transport
      M hPA successorNumeralCode
      intermediateBaseContext finalBaseContext
      (rawFormulaImpCode M nextAxiomSoundness
        (rawCoqRestrictedPAAxiomContextsTruthDirectCode M inputs))
      coherenceRoot hintermediateRealizable hfinalRealizable
      hintermediateIncluded hfinalBridgeAdequate hcoherence)
    as [finalCoherenceRoot hfinalCoherence].
  destruct harithmetic as
    [hadmissible [hcontextBounded hcontextAdequate]].
  destruct
    (raw_codedPALocalProof_coqRestrictedPAConsistencyBridgeBodyDirectContext_transport
      M hPA inputs successorNumeralCode
      intermediateBaseContext finalBaseContext
      (rawDirectTemplateFormula inputs
        coqRestrictedPAOpenShellAdmissibleTemplate)
      admissibleRoot hintermediateRealizable hfinalRealizable
      hintermediateIncluded hfinalBridgeAdequate hadmissible)
    as [finalAdmissibleRoot hfinalAdmissible].
  destruct
    (raw_codedPALocalProof_coqRestrictedPAConsistencyBridgeBodyDirectContext_transport
      M hPA inputs successorNumeralCode
      intermediateBaseContext finalBaseContext
      (rawDirectTemplateFormula inputs
        coqRestrictedPAOpenShellContextBoundedTemplate)
      contextBoundedRoot hintermediateRealizable hfinalRealizable
      hintermediateIncluded hfinalBridgeAdequate hcontextBounded)
    as [finalContextBoundedRoot hfinalContextBounded].
  destruct
    (raw_codedPALocalProof_coqRestrictedPAConsistencyBridgeBodyDirectContext_transport
      M hPA inputs successorNumeralCode
      intermediateBaseContext finalBaseContext
      (rawDirectTemplateFormula inputs
        coqRestrictedPAOpenShellContextAdequateTemplate)
      contextAdequateRoot hintermediateRealizable hfinalRealizable
      hintermediateIncluded hfinalBridgeAdequate hcontextAdequate)
    as [finalContextAdequateRoot hfinalContextAdequate].
  assert (hfinalArithmetic :
      RawCoqRestrictedPAOpenShellArithmeticResidual M inputs
        (rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode
          M inputs successorNumeralCode finalBaseContext)
        finalAdmissibleRoot finalContextBoundedRoot
        finalContextAdequateRoot).
  {
    split; [exact hfinalAdmissible |].
    split; assumption.
  }
  pose proof
    (raw_contextListIncluded_trans M carriedSourceBaseContext
      intermediateBaseContext finalBaseContext
      hcarriedIncluded hintermediateIncluded) as hcarriedFinalIncluded.
  exact
    (raw_dynamicTruthNativeFinalCarriedConsistencyCodeBridge_of_unified_support_arithmetic_and_bottom_root
      M hPA parameters inputs tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness nextFinal successorNumeralCode
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      nextSigmaEvidence nextGlobalSigma nextGlobalPi
      sigmaApplicationSelector contextApplicationSelector
      closureCount axiom carriedSourceBaseContext
      finalWitnessList finalBaseContext finalCoherenceRoot bottomRoot
      finalAdmissibleRoot finalContextBoundedRoot finalContextAdequateRoot
      htrace hfinalPrerequisites hcarriedFinalIncluded hlevel hunified
      hfinalCoherence hfinalArithmetic hbottom).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeFinalCarriedConsistencyBottomGrowth.
