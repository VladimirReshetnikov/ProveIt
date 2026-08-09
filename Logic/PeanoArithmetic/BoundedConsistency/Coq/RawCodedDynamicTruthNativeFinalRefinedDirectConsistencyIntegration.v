(**
  Thread the refined direct-consistency resources into the final bridge.

  Three focused developments now expose substantially sharper interfaces
  than the historical direct consistency compiler:

  - the open-shell integration asks only for its three arithmetic roots;
  - native axiom/context coherence asks only for the synchronized
    witness/context traversal body; and
  - native bottom refutation asks for the exact selected successor-Sigma
    application, together with its graph/package selector link.

  This module composes those interfaces without introducing another opaque
  proof-producing premise.  The first theorem reconstructs the existing
  consistency-from-universal-soundness compiler.  The next two theorems feed
  that compiler through the witnessed rule-case soundness construction and
  all the way to the literal sixth-stage graph/proof pair.

  Consequently a downstream closure of the three remaining represented
  inductions immediately reaches the public final proof certificate; no
  additional consistency or final-stage adapter remains between them.
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
  RawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessBridgeDirect
  RawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessFromDirectRuleCases
  RawCodedRestrictedPAConsistencyFromUniversalSoundnessDirectOpenIntegration
  RawCodedRestrictedPAAxiomContextTruthNativeDirectCoherenceLink
  RawCodedRestrictedPAAxiomContextTruthNativeDirectBodyShell
  RawCodedRestrictedPABottomTruthNativeDirectRefutationLink.

Module
  PABoundedRawCodedDynamicTruthNativeFinalRefinedDirectConsistencyIntegration.

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
  PABoundedRawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessBridgeDirect.
Import
  PABoundedRawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessFromDirectRuleCases.
Import
  PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundnessDirectOpenIntegration.
Import
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectCoherenceLink.
Import
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectBodyShell.
Import PABoundedRawCodedRestrictedPABottomTruthNativeDirectRefutationLink.

(** Assemble the exact existing consistency compiler from the three refined
    proof-producing boundaries and the two representation-only native links.
    Keeping the arguments split makes the remaining work visible to audits
    and lets each compiler be implemented independently. *)
Theorem
    raw_dynamicTruthNativeFinalConsistencyFromUniversalSoundnessDirectCompiler_of_refined_resources
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPAConsistencyFromUniversalSoundnessDirectArithmeticCompiler
    M inputs ->
  RawDynamicTruthNativeFinalAxiomContextTruthNativeLinkCompiler M inputs ->
  RawCoqRestrictedPANativeAxiomContextTruthTraversalLeafCompiler M ->
  RawDynamicTruthNativeFinalBottomTruthNativeSelectorLinkCompiler M inputs ->
  RawDynamicTruthNativeFinalSelectedSigmaBottomRefutationRootCompiler
    M inputs ->
  RawDynamicTruthNativeFinalConsistencyFromUniversalSoundnessDirectCompiler
    M inputs.
Proof.
  intros M hPA inputs harithmetic haxiomLink haxiomTraversal
    hbottomLink hbottomRoot.
  apply
    (raw_dynamicTruthNativeFinalConsistencyFromUniversalSoundnessDirectCompiler_of_open_and_split_truth_support
      M hPA inputs).
  - exact
      (raw_coqRestrictedPAConsistencyFromUniversalSoundnessDirectOpenCompiler_of_arithmetic
        M hPA inputs harithmetic).
  - exact
      (raw_dynamicTruthNativeFinalSelectedAxiomContextTruthDirectCoherenceCompiler_of_native_link
        M inputs haxiomLink
        (raw_dynamicTruthNativeFinalSelectedAxiomContextTruthRootCompiler_of_traversal_leaf
          M hPA inputs haxiomTraversal)).
  - exact
      (raw_dynamicTruthNativeFinalBottomTruthDirectRefutationCompiler_of_native_selector
        M inputs hbottomLink hbottomRoot).
Qed.

(** Pointwise grown bridge from witnessed rule semantics and the refined
    consistency resources.  The ordinary soundness certificate is still
    generated internally by represented strong-prefix induction. *)
Theorem
    raw_dynamicTruthNativeFinalGrowingUniversalSoundnessDirectBridge_of_witnessed_rule_cases_and_refined_resources
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
  RawCoqRestrictedPAConsistencyFromUniversalSoundnessDirectArithmeticCompiler
    M inputs ->
  RawDynamicTruthNativeFinalAxiomContextTruthNativeLinkCompiler M inputs ->
  RawCoqRestrictedPANativeAxiomContextTruthTraversalLeafCompiler M ->
  RawDynamicTruthNativeFinalBottomTruthNativeSelectorLinkCompiler M inputs ->
  RawDynamicTruthNativeFinalSelectedSigmaBottomRefutationRootCompiler
    M inputs ->
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
  RawDynamicTruthNativeFinalGrowingUniversalSoundnessDirectBridgeAt
    M inputs stagedTail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode.
Proof.
  intros M hPA inputs ruleTail replacement axiom closureCount
    ruleBaseWitnessList hruleBase hremainder hsemantic
    harithmetic haxiomLink haxiomTraversal hbottomLink hbottomRoot
    stagedTail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode stagedWitnessList stagedBaseContext
    htrace hprerequisites hlevel.
  exact
    (raw_dynamicTruthNativeFinalGrowingUniversalSoundnessDirectBridge_of_witnessed_rule_case_semantic_roots
      M hPA inputs ruleTail replacement axiom closureCount
      ruleBaseWitnessList hruleBase hremainder hsemantic
      stagedTail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode stagedWitnessList stagedBaseContext
      htrace hprerequisites hlevel
      (raw_dynamicTruthNativeFinalConsistencyFromUniversalSoundnessDirectCompiler_of_refined_resources
        M hPA inputs harithmetic haxiomLink haxiomTraversal
        hbottomLink hbottomRoot)).
Qed.

(** Literal public final graph/proof pair.  This corollary confirms that the
    refined resources are not stranded below the callback boundary. *)
Corollary
    raw_dynamicTruthNativeFinalGrowingStagedNextFinalProof_of_witnessed_rule_cases_and_refined_resources
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
  RawCoqRestrictedPAConsistencyFromUniversalSoundnessDirectArithmeticCompiler
    M inputs ->
  RawDynamicTruthNativeFinalAxiomContextTruthNativeLinkCompiler M inputs ->
  RawCoqRestrictedPANativeAxiomContextTruthTraversalLeafCompiler M ->
  RawDynamicTruthNativeFinalBottomTruthNativeSelectorLinkCompiler M inputs ->
  RawDynamicTruthNativeFinalSelectedSigmaBottomRefutationRootCompiler
    M inputs ->
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
  exists finalCertificate : M,
    RawDynamicTruthNativeStagedNextFinalProofAt M
      stagedTail level nextFinal finalCertificate.
Proof.
  intros M hPA inputs ruleTail replacement axiom closureCount
    ruleBaseWitnessList hruleBase hremainder hsemantic
    harithmetic haxiomLink haxiomTraversal hbottomLink hbottomRoot
    stagedTail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode stagedWitnessList stagedBaseContext
    htrace hprerequisites hlevel.
  apply
    (raw_dynamicTruthNativeFinalGrowingStagedNextFinalProof_of_direct_bridge
      M hPA inputs stagedTail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode htrace).
  exact
    (raw_dynamicTruthNativeFinalGrowingUniversalSoundnessDirectBridge_of_witnessed_rule_cases_and_refined_resources
      M hPA inputs ruleTail replacement axiom closureCount
      ruleBaseWitnessList hruleBase hremainder hsemantic
      harithmetic haxiomLink haxiomTraversal hbottomLink hbottomRoot
      stagedTail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode stagedWitnessList stagedBaseContext
      htrace hprerequisites hlevel).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeFinalRefinedDirectConsistencyIntegration.
