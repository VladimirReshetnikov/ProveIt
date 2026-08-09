(**
  Connect witnessed direct rule semantics to the grown final-stage bridge.

  The represented strong-prefix induction now accepts semantic rule roots in
  an arbitrary finite witnessed PA tail and returns an ordinary proof of the
  exact direct universal-soundness code.  Independently, the final-stage
  bridge can merge such an ordinary proof into the eleven-root staged
  prerequisite context and rebuild the direct consistency implication over
  the merged base.

  This module composes those two verified steps.  It leaves visible exactly
  the substantive proof-producing boundaries: the twenty-three semantic
  rule laws, the nonstandard closure remainder, and the direct
  consistency-from-soundness compiler.  No soundness certificate or final
  bridge root is supplied by the caller.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedRestrictedPAProof
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateDirectStructuralTranslation
  RawCodedDynamicTruthNativeStagedPositiveSuccessor
  RawCodedDynamicTruthNativeFinalStagedRootCompilation
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell
  RawCodedRestrictedPADerivationSoundnessDirectRuleCases
  RawCodedRestrictedPADerivationSoundnessDirectGrowingIntegrationFromWitnessedRuleCases
  RawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessBridgeDirect.

Module
  PABoundedRawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessFromDirectRuleCases.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedDynamicTruthNativeStagedPositiveSuccessor.
Import PABoundedRawCodedDynamicTruthNativeFinalStagedRootCompilation.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCases.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectGrowingIntegrationFromWitnessedRuleCases.
Import
  PABoundedRawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessBridgeDirect.

(** The rule compiler's witnessed base and the final staged base are kept
    separate.  The former is hidden inside the resulting ordinary soundness
    certificate; the grown bridge then merges it honestly with the latter. *)
Theorem
    raw_dynamicTruthNativeFinalGrowingUniversalSoundnessDirectBridge_of_witnessed_rule_case_semantic_roots
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
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness ->
  rawDirectTemplateTerm inputs
    coqRestrictedPASoundnessLowerLevelTerm = successorNumeralCode ->
  RawDynamicTruthNativeFinalConsistencyFromUniversalSoundnessDirectCompiler
    M inputs ->
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
    htrace hprerequisites hlevel hconsistencyCompiler.
  destruct
    (raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversalDirect_of_rule_case_semantic_roots_on_witnessed_tail
      M hPA inputs ruleTail replacement axiom closureCount
      ruleBaseWitnessList hruleBase hremainder hsemantic)
    as [soundnessCertificate hsoundness].
  exact
    (raw_dynamicTruthNativeFinalGrowingUniversalSoundnessDirectBridge_of_ordinary_complete_fields
      M hPA inputs stagedTail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode stagedWitnessList stagedBaseContext
      soundnessCertificate htrace hprerequisites hsoundness
      hlevel hconsistencyCompiler).
Qed.

(** The grown bridge is now consumable all the way to the public sixth-stage
    graph/proof pair.  This corollary makes that connection explicit for the
    witnessed direct rule-case producer: the caller supplies neither an
    ordinary soundness certificate nor any final proof root. *)
Corollary
    raw_dynamicTruthNativeFinalGrowingStagedNextFinalProof_of_witnessed_rule_case_semantic_roots
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
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness ->
  rawDirectTemplateTerm inputs
    coqRestrictedPASoundnessLowerLevelTerm = successorNumeralCode ->
  RawDynamicTruthNativeFinalConsistencyFromUniversalSoundnessDirectCompiler
    M inputs ->
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
    htrace hprerequisites hlevel hconsistencyCompiler.
  pose proof
    (raw_dynamicTruthNativeFinalGrowingUniversalSoundnessDirectBridge_of_witnessed_rule_case_semantic_roots
      M hPA inputs ruleTail replacement axiom closureCount
      ruleBaseWitnessList hruleBase hremainder hsemantic
      stagedTail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode stagedWitnessList stagedBaseContext
      htrace hprerequisites hlevel hconsistencyCompiler)
    as hbridge.
  exact
    (raw_dynamicTruthNativeFinalGrowingStagedNextFinalProof_of_direct_bridge
      M hPA inputs stagedTail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode htrace hbridge).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessFromDirectRuleCases.
