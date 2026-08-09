(**
  Feed witnessed direct rule semantics through the twice-growing final bridge.

  The direct strong-prefix induction compiler produces an ordinary proof of
  universal derivation soundness in its own finite witnessed PA context.  The
  first growing stage merges that certificate with the eleven staged roots;
  a carried consistency producer may then add further finite PA prefixes for
  arithmetic and synchronized-list theorems.  This module composes those
  steps and exposes the resulting literal sixth-stage proof certificate.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedRestrictedPAProof
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateDirectStructuralTranslation
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell
  RawCodedRestrictedPADerivationSoundnessDirectRuleCases
  RawCodedRestrictedPADerivationSoundnessDirectGrowingIntegrationFromWitnessedRuleCases
  RawCodedDynamicTruthNativeStagedPositiveSuccessor
  RawCodedDynamicTruthNativeFinalStagedRootCompilation
  RawCodedDynamicTruthNativeFinalBridgeFieldsHeadAdequacy
  RawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessBridgeDirect
  RawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessCarriedBridge.

Module
  PABoundedRawCodedDynamicTruthNativeFinalGrowingFromDirectRuleCasesCarried.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCases.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectGrowingIntegrationFromWitnessedRuleCases.
Import PABoundedRawCodedDynamicTruthNativeStagedPositiveSuccessor.
Import PABoundedRawCodedDynamicTruthNativeFinalStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeFinalBridgeFieldsHeadAdequacy.
Import
  PABoundedRawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessBridgeDirect.
Import
  PABoundedRawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessCarriedBridge.

Theorem
    raw_dynamicTruthNativeFinalGrowingUniversalSoundnessDirectBridge_of_witnessed_rule_cases_carried
    : forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      (ruleTail : TemplateContext)
      replacement axiom closureCount ruleBaseWitnessList,
  RawCodedPAAxiomWitnessContext M ruleBaseWitnessList
    (rawTemplateContextCode
      (rawDirectStructuralTemplateTranslation M hPA inputs) ruleTail) ->
  RawCoqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder
    M inputs replacement axiom closureCount ->
  RawCoqRestrictedPADirectRuleCaseSemanticRoots M hPA inputs ruleTail ->
  forall (stagedTail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode stagedWitnessList stagedBaseContext,
  RawDynamicTruthNativeFinalStagedGraphTraceAt M stagedTail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode ->
  RawDynamicTruthNativeFinalStagedPrerequisitesOn M
    stagedWitnessList stagedBaseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution
    nextAxiomSoundness ->
  rawDirectTemplateTerm inputs
    coqRestrictedPASoundnessLowerLevelTerm = successorNumeralCode ->
  (forall mergedWitnessList mergedBaseContext,
    RawDynamicTruthNativeFinalStagedPrerequisitesOn M
      mergedWitnessList mergedBaseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness ->
    RawDynamicTruthNativeFinalCarriedConsistencyCodeBridgeAt M
      (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M inputs)
      stagedTail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness nextFinal successorNumeralCode mergedBaseContext) ->
  RawDynamicTruthNativeFinalGrowingUniversalSoundnessDirectBridgeAt
    M inputs stagedTail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode.
Proof.
  intros M hPA inputs ruleTail replacement axiom closureCount
    ruleBaseWitnessList hruleBase hremainder hsemantic
    stagedTail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode stagedWitnessList stagedBaseContext
    htrace hprerequisites hlevel hcarried.
  destruct
    (raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversalDirect_of_rule_case_semantic_roots_on_witnessed_tail
      M hPA inputs ruleTail replacement axiom closureCount
      ruleBaseWitnessList hruleBase hremainder hsemantic)
    as [soundnessCertificate hsoundness].
  pose proof
    (raw_dynamicTruthNativeFinalBridgeFieldsHeadAdequacyCompiler M hPA
      stagedTail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode stagedWitnessList stagedBaseContext
      htrace hprerequisites) as hfieldsAdequate.
  exact
    (raw_dynamicTruthNativeFinalGrowingUniversalSoundnessDirectBridge_of_ordinary_carried
      M hPA inputs stagedTail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode stagedWitnessList stagedBaseContext
      soundnessCertificate htrace hprerequisites hsoundness
      hfieldsAdequate hcarried).
Qed.

Corollary
    raw_dynamicTruthNativeFinalGrowingStagedNextFinalProof_of_witnessed_rule_cases_carried
    : forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      (ruleTail : TemplateContext)
      replacement axiom closureCount ruleBaseWitnessList,
  RawCodedPAAxiomWitnessContext M ruleBaseWitnessList
    (rawTemplateContextCode
      (rawDirectStructuralTemplateTranslation M hPA inputs) ruleTail) ->
  RawCoqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder
    M inputs replacement axiom closureCount ->
  RawCoqRestrictedPADirectRuleCaseSemanticRoots M hPA inputs ruleTail ->
  forall (stagedTail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode stagedWitnessList stagedBaseContext,
  RawDynamicTruthNativeFinalStagedGraphTraceAt M stagedTail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode ->
  RawDynamicTruthNativeFinalStagedPrerequisitesOn M
    stagedWitnessList stagedBaseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution
    nextAxiomSoundness ->
  rawDirectTemplateTerm inputs
    coqRestrictedPASoundnessLowerLevelTerm = successorNumeralCode ->
  (forall mergedWitnessList mergedBaseContext,
    RawDynamicTruthNativeFinalStagedPrerequisitesOn M
      mergedWitnessList mergedBaseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness ->
    RawDynamicTruthNativeFinalCarriedConsistencyCodeBridgeAt M
      (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M inputs)
      stagedTail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness nextFinal successorNumeralCode mergedBaseContext) ->
  exists finalCertificate : M,
    RawDynamicTruthNativeStagedNextFinalProofAt M
      stagedTail level nextFinal finalCertificate.
Proof.
  intros M hPA inputs ruleTail replacement axiom closureCount
    ruleBaseWitnessList hruleBase hremainder hsemantic
    stagedTail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode stagedWitnessList stagedBaseContext
    htrace hprerequisites hlevel hcarried.
  pose proof
    (raw_dynamicTruthNativeFinalGrowingUniversalSoundnessDirectBridge_of_witnessed_rule_cases_carried
      M hPA inputs ruleTail replacement axiom closureCount
      ruleBaseWitnessList hruleBase hremainder hsemantic
      stagedTail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode stagedWitnessList stagedBaseContext
      htrace hprerequisites hlevel hcarried) as hbridge.
  exact
    (raw_dynamicTruthNativeFinalGrowingStagedNextFinalProof_of_direct_bridge
      M hPA inputs stagedTail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode htrace hbridge).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeFinalGrowingFromDirectRuleCasesCarried.
