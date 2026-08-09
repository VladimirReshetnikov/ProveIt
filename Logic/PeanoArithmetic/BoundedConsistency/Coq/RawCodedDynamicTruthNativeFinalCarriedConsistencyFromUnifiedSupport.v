(**
  Assemble a carried final consistency bridge from one unified native truth
  package.

  Arithmetic growth and staged-prerequisite transport have already selected
  the final witnessed PA base.  At that base, the unified native package
  supplies both the axiom-context link and the successor-Sigma conclusion
  link for the same direct structural inputs.  Given the represented
  axiom-context coherence root, this module compiles the selected bottom
  refutation, transports the staged axiom field below the restricted bridge
  heads, runs the open shell with its synchronized arithmetic residual, and
  introduces the universal-soundness implication.

  The result has exactly the carried-code-bridge interface consumed by the
  twice-growing final accumulator.  In particular, no fixed-context compiler
  is manufactured from a construction that genuinely extended the PA base.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFixedLevelTruthTotality
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTemplateNumeralParameters
  RawCodedTemplateTernaryApplication
  RawCodedTemplateDirectStructuralTranslation
  RawCodedDynamicContextTruthSelector
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPAConsistencyFromUniversalSoundnessDirect
  RawCodedRestrictedPAConsistencyFromUniversalSoundnessDirectOpenIntegration
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell
  RawCodedDynamicTruthNativeFinalStagedRootCompilation
  RawCodedDynamicTruthNativeFinalBridgeFieldsHeadAdequacy
  RawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessBridgeDirect
  RawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessCarriedBridge
  RawCodedRestrictedPABottomTruthNativeDirectRefutationLink
  RawCodedRestrictedPANativeFinalUnifiedTruthLink.

Module
  PABoundedRawCodedDynamicTruthNativeFinalCarriedConsistencyFromUnifiedSupport.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedDynamicContextTruthSelector.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundnessDirect.
Import
  PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundnessDirectOpenIntegration.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.
Import PABoundedRawCodedDynamicTruthNativeFinalStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeFinalBridgeFieldsHeadAdequacy.
Import
  PABoundedRawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessBridgeDirect.
Import
  PABoundedRawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessCarriedBridge.
Import PABoundedRawCodedRestrictedPABottomTruthNativeDirectRefutationLink.
Import PABoundedRawCodedRestrictedPANativeFinalUnifiedTruthLink.

Theorem
    raw_dynamicTruthNativeFinalCarriedConsistencyCodeBridge_of_unified_support_and_arithmetic
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
      closureCount axiom sourceBaseContext
      finalWitnessList finalBaseContext
      coherenceRoot admissibleRoot contextBoundedRoot contextAdequateRoot,
  RawDynamicTruthNativeFinalStagedGraphTraceAt M tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode ->
  RawDynamicTruthNativeFinalStagedPrerequisitesOn M
    finalWitnessList finalBaseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution
    nextAxiomSoundness ->
  RawContextListIncluded M sourceBaseContext finalBaseContext ->
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
      M successorNumeralCode finalBaseContext)
    (rawFormulaImpCode M nextAxiomSoundness
      (rawCoqRestrictedPAAxiomContextsTruthDirectCode M inputs))
    coherenceRoot ->
  RawCoqRestrictedPAOpenShellArithmeticResidual M inputs
    (rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode
      M inputs successorNumeralCode finalBaseContext)
    admissibleRoot contextBoundedRoot contextAdequateRoot ->
  RawCoqRestrictedPASelectedSigmaBottomRefutationRootCompiler M ->
  RawDynamicTruthNativeFinalCarriedConsistencyCodeBridgeAt M
    (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M inputs)
    tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode sourceBaseContext.
Proof.
  intros M hPA parameters inputs tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence nextGlobalSigma nextGlobalPi
    sigmaApplicationSelector contextApplicationSelector
    closureCount axiom sourceBaseContext
    finalWitnessList finalBaseContext
    coherenceRoot admissibleRoot contextBoundedRoot contextAdequateRoot
    htrace hfinalPrerequisites hincluded hlevel hunified hcoherence
    harithmetic hbottomCompiler.
  destruct hunified as [haxiomLink [hbottomLink hremainder]].
  set (bridgeContext :=
    rawCoqRestrictedPAConsistencyBridgeContextCode
      M successorNumeralCode finalBaseContext).
  destruct (hbottomCompiler parameters inputs
    currentGlobalSigma currentGlobalPi level
    nextGlobalSigma nextGlobalPi sigmaApplicationSelector
    bridgeContext hbottomLink) as [bottomRoot hbottomSelected].
  assert (hbottom : RawCodedPALocalProofOf M bridgeContext
      (rawCoqRestrictedPABottomTruthRefutationDirectCode M inputs)
      bottomRoot).
  {
    rewrite
      (raw_coqRestrictedPABottomTruthRefutationDirectCode_native_view
        M parameters inputs nextGlobalSigma sigmaApplicationSelector
        (proj2 (proj2 hbottomLink))).
    exact hbottomSelected.
  }
  pose proof
    (raw_dynamicTruthNativeFinalBridgeFieldsHeadAdequacyCompiler M hPA
      tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode finalWitnessList finalBaseContext
      htrace hfinalPrerequisites) as hfieldsAdequate.
  destruct
    (raw_coqRestrictedPASelectedAxiomContextTruthDirectSupport_of_residual
      M hPA inputs tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode finalWitnessList finalBaseContext
      coherenceRoot bottomRoot htrace hfinalPrerequisites hfieldsAdequate
      (conj hcoherence hbottom))
    as [nextAxiomSoundnessRoot hsupport].
  destruct
    (raw_coqRestrictedPAConsistencyFromUniversalSoundnessDirect_child_of_arithmetic
      M hPA inputs successorNumeralCode finalWitnessList finalBaseContext
      nextAxiomSoundness nextAxiomSoundnessRoot coherenceRoot bottomRoot
      admissibleRoot contextBoundedRoot contextAdequateRoot
      hlevel hsupport harithmetic) as [child hchild].
  set (bridgeRoot :=
    rawCoqRestrictedPAConsistencyFromSoundnessBridgeDirectRoot
      M inputs successorNumeralCode finalBaseContext child).
  assert (hbridge : RawCodedPALocalProofOf M bridgeContext
      (rawCoqRestrictedPAConsistencyFromSoundnessBridgeDirectCode M inputs)
      bridgeRoot).
  {
    unfold bridgeRoot,
      rawCoqRestrictedPAConsistencyFromSoundnessBridgeDirectRoot.
    rewrite raw_coqRestrictedPAConsistencyFromSoundnessBridgeDirectCode_view,
      hlevel.
    exact (raw_codedPALocalProofOf_impI M hPA bridgeContext
      (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M inputs)
      (rawRestrictedTargetFormulaContextCode M successorNumeralCode
        restrictedPAConsistencyFormulaContext)
      child hchild).
  }
  pose proof htrace as htraceCopy.
  destruct htraceCopy as [_ _ _ _ _ _ _ hsource].
  destruct hsource as [_ _ hnextTarget _].
  exists finalWitnessList, finalBaseContext, bridgeRoot.
  split; [exact hfinalPrerequisites |].
  split; [exact hincluded |].
  unfold bridgeContext in hbridge |- *.
  rewrite raw_coqRestrictedPAConsistencyFromSoundnessBridgeDirectCode_view,
    hlevel in hbridge.
  now rewrite hnextTarget in hbridge.
Qed.

End
  PABoundedRawCodedDynamicTruthNativeFinalCarriedConsistencyFromUnifiedSupport.
