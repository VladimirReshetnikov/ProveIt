(**
  Handoff from the direct strong-step endpoint to predecessor global rows.

  The restricted-proof and rule-validity roots initially live beneath the
  caller's constructor and endpoint assumptions.  This compiler inserts the
  two predecessor-state assumptions in front of that prefix, derives the
  current formula's atomic and rank-domain invariants, aligns them with the
  native trace outputs, transports both global-row sources through the same
  retained PA witness extension, and invokes the prefix-general predecessor
  logical-roots compiler.

  No temporary assumption is folded into the witnessed PA tail.  The final
  context therefore has exactly the same caller prefix, while every context
  extension is accounted for by a finite standard PA-axiom witness list.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedContextLists
  RawCodedRestrictedPAProof
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofExistential
  RawCodedPALocalProofExistentialEliminationChain
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplateFormulaAtomicAdequacy
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthLocalAdmissibilityCompilation
  RawCodedDynamicTruthPredecessorStateExclusivityCompilation
  RawCodedDynamicTruthPredecessorGlobalExistentialElimination
  RawCodedDynamicTruthPredecessorAdmissibilityAssignmentCompilation
  RawCodedDynamicTruthGlobalOpenedRowSelection
  RawCodedDynamicTruthPredecessorGlobalRowEvidence
  RawCodedStrongStepProofEndpointAtomicAdequacyProofCompilation
  RawCodedStrongStepProofEndpointEvidenceCompilation.

Import ListNotations.

Module PABoundedRawCodedStrongStepPredecessorGlobalRowEvidenceCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofExistentialEliminationChain.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplateFormulaAtomicAdequacy.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedDynamicTruthLocalAdmissibilityCompilation.
Import
  PABoundedRawCodedDynamicTruthPredecessorStateExclusivityCompilation.
Import
  PABoundedRawCodedDynamicTruthPredecessorGlobalExistentialElimination.
Import
  PABoundedRawCodedDynamicTruthPredecessorAdmissibilityAssignmentCompilation.
Import PABoundedRawCodedDynamicTruthGlobalOpenedRowSelection.
Import PABoundedRawCodedDynamicTruthPredecessorGlobalRowEvidence.
Import
  PABoundedRawCodedStrongStepProofEndpointAtomicAdequacyProofCompilation.
Import PABoundedRawCodedStrongStepProofEndpointEvidenceCompilation.

(** Every finite prefix translated by the direct structural translation is
    atomically adequate.  Membership is immaterial because the translation
    contract supplies a represented unit-shift trace for every template
    formula. *)
Lemma raw_directStructuralTemplatePrefix_atomically_adequate : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M) prefix,
  RawCodedTemplatePrefixAtomicallyAdequate M
    (rawDirectStructuralTemplateTranslation M hPA inputs) prefix.
Proof.
  intros M hPA inputs prefix formula _.
  exact (raw_codedTemplateFormula_atomically_adequate_core M hPA
    (rawDirectStructuralTemplateTranslation M hPA inputs) formula).
Qed.

(** Complete context-safe handoff.  The three alignment premises name only
    carrier-level facts already present in a native local proof trace: the
    common level numeral and the two functional substitution outputs. *)
Theorem
    raw_codedPALocalProof_strongStepPredecessorLogicalRoots_of_restricted_rule_and_global_sources_and_selected_compiler_families_under_prefix :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    baseWitnessList baseContext prefix
    levelNumeral (localSigma localPi : TemplateFormula)
    sigmaDomain piDomain
    sigmaConclusion piConclusion
    restrictedRoot ruleRoot sigmaSourceRoot piSourceRoot,
  RawCodedTemplatePrefixAtomicallyAdequate M
    (rawDirectStructuralTemplateTranslation M hPA inputs) prefix ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  rawDirectTemplateTerm inputs
    coqRestrictedPASoundnessLowerLevelTerm = levelNumeral ->
  RawCodedFormulaSingleSubstitution M levelNumeral
    (rawNumeralValue M
      (formulaCode dynamicTruthLocalSigmaInputDomainTemplate))
    sigmaDomain ->
  RawCodedFormulaSingleSubstitution M levelNumeral
    (rawNumeralValue M
      (formulaCode dynamicTruthLocalPiInputDomainTemplate))
    piDomain ->
  RawCodedDynamicTruthSelectedPayloadShiftCompilerOnWitnessedExtensions
    M (rawDirectStructuralTemplateTranslation M hPA inputs)
    baseContext prefix 0 localSigma localPi sigmaConclusion ->
  RawCodedDynamicTruthSelectedPayloadShiftCompilerOnWitnessedExtensions
    M (rawDirectStructuralTemplateTranslation M hPA inputs)
    baseContext prefix 1 localSigma localPi piConclusion ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      baseContext prefix)
    (rawDirectTemplateFormula inputs
      coqRestrictedPADerivationSoundnessRestrictedProofTemplate)
    restrictedRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      baseContext prefix)
    (rawDirectTemplateFormula inputs
      coqStrongStepProofEndpointAtomicAdequacyRulePremise)
    ruleRoot ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthPredecessorJointStateContext M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        baseContext prefix))
    (rawTemplateFormula
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqDynamicTruthGlobalExistentialSource 0 localSigma localPi))
    sigmaSourceRoot ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthPredecessorJointStateContext M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        baseContext prefix))
    (rawTemplateFormula
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqDynamicTruthGlobalExistentialSource 1 localSigma localPi))
    piSourceRoot ->
  exists targetWitnessList targetContext,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawDynamicTruthPredecessorStateLogicalRootsAt M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        targetContext prefix)
      sigmaDomain piDomain
      (rawTemplateFormula
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        sigmaConclusion)
      (rawTemplateFormula
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        piConclusion).
Proof.
  intros M hPA inputs baseWitnessList baseContext prefix
    levelNumeral localSigma localPi sigmaDomain piDomain
    sigmaConclusion piConclusion
    restrictedRoot ruleRoot sigmaSourceRoot piSourceRoot
    hprefix hbase hlevel hsigmaDomain hpiDomain
    hsigmaFamily hpiFamily hrestricted hrule
    hsigmaSource hpiSource.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  set (callerContext :=
    rawTemplateContextCodeOnTail translation baseContext prefix).
  assert (hbaseRealizable : RawContextListRealizable M baseContext).
  {
    exact (raw_codedPAAxiomWitnessContext_context_realizable
      M baseWitnessList baseContext hbase).
  }
  assert (hcallerRealizable : RawContextListRealizable M callerContext).
  {
    exact (raw_templateContextOnTail_realizable M hPA translation
      baseContext prefix hbaseRealizable).
  }
  assert (hstateAdequate : RawCodedTemplatePrefixAtomicallyAdequate M
      translation coqDynamicTruthPredecessorStateTemplateContext).
  {
    exact
      (raw_dynamicTruthPredecessorStateTemplateContext_atomically_adequate
        M hPA translation
        (rawDirectStructuralTemplatePAAgreement M hPA inputs)).
  }
  destruct
    (raw_codedPALocalProof_templatePrefix M hPA translation
      callerContext coqDynamicTruthPredecessorStateTemplateContext
      (rawDirectTemplateFormula inputs
        coqRestrictedPADerivationSoundnessRestrictedProofTemplate)
      restrictedRoot hcallerRealizable hstateAdequate hrestricted)
    as [stateRestrictedRoot hstateRestricted].
  destruct
    (raw_codedPALocalProof_templatePrefix M hPA translation
      callerContext coqDynamicTruthPredecessorStateTemplateContext
      (rawDirectTemplateFormula inputs
        coqStrongStepProofEndpointAtomicAdequacyRulePremise)
      ruleRoot hcallerRealizable hstateAdequate hrule)
    as [stateRuleRoot hstateRule].
  assert (hcombinedPrefix : RawCodedTemplatePrefixAtomicallyAdequate M
      translation
      (coqDynamicTruthPredecessorStateTemplateContext ++ prefix)).
  {
    exact
      (raw_dynamicTruthPredecessorStateTemplateContext_app_atomically_adequate
        M hPA translation
        (rawDirectStructuralTemplatePAAgreement M hPA inputs)
        prefix hprefix).
  }
  assert (hstateRestrictedCombined : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqDynamicTruthPredecessorStateTemplateContext ++ prefix))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADerivationSoundnessRestrictedProofTemplate)
      stateRestrictedRoot).
  {
    rewrite (raw_dynamicTruthPredecessorStateTemplateContext_app_code
      M translation
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      baseContext prefix).
    rewrite <- (raw_dynamicTruthPredecessorStateTemplateContextCode
      M translation
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      (rawTemplateContextCodeOnTail translation baseContext prefix)).
    exact hstateRestricted.
  }
  assert (hstateRuleCombined : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqDynamicTruthPredecessorStateTemplateContext ++ prefix))
      (rawDirectTemplateFormula inputs
        coqStrongStepProofEndpointAtomicAdequacyRulePremise)
      stateRuleRoot).
  {
    rewrite (raw_dynamicTruthPredecessorStateTemplateContext_app_code
      M translation
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      baseContext prefix).
    rewrite <- (raw_dynamicTruthPredecessorStateTemplateContextCode
      M translation
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      (rawTemplateContextCodeOnTail translation baseContext prefix)).
    exact hstateRule.
  }
  destruct
    (raw_codedPALocalProof_strongStepEndpointEvidence_of_restricted_and_rule_roots_on_witnessed_tail_under_prefix
      M hPA inputs baseWitnessList baseContext
      (coqDynamicTruthPredecessorStateTemplateContext ++ prefix)
      stateRestrictedRoot stateRuleRoot hcombinedPrefix hbase
      hstateRestrictedCombined hstateRuleCombined)
    as (endpointWitnesses & atomicResultRoot & rankResultRoot &
      hendpointWitnessed & hendpointIncluded &
      hendpointAtomic & hendpointRank).
  set (endpointWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      endpointWitnesses baseWitnessList).
  set (endpointContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      endpointWitnesses baseContext).
  assert (hendpointAtomicNative : RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M
        (rawTemplateContextCodeOnTail translation endpointContext prefix))
      (rawDynamicTruthLocalAtomicAdequacyCode M) atomicResultRoot).
  {
    rewrite <- (raw_dynamicTruthPredecessorStateTemplateContext_app_code
      M translation
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      endpointContext prefix).
    rewrite <- (raw_strongStepEndpointAtomicAdequacyConclusion_code
      M hPA inputs).
    exact hendpointAtomic.
  }
  assert (hendpointRankNative : RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M
        (rawTemplateContextCodeOnTail translation endpointContext prefix))
      (rawFormulaOrCode M sigmaDomain piDomain) rankResultRoot).
  {
    rewrite <- (raw_dynamicTruthPredecessorStateTemplateContext_app_code
      M translation
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      endpointContext prefix).
    rewrite <- (raw_strongStepEndpointQuantifierBoundedConclusion_code
      M hPA inputs levelNumeral sigmaDomain piDomain
      hlevel hsigmaDomain hpiDomain).
    exact hendpointRank.
  }
  assert (hsigmaSourceTemplate : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqDynamicTruthPredecessorStateTemplateContext ++ prefix))
      (rawTemplateFormula translation
        (coqDynamicTruthGlobalExistentialSource 0 localSigma localPi))
      sigmaSourceRoot).
  {
    rewrite (raw_dynamicTruthPredecessorStateTemplateContext_app_code
      M translation
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      baseContext prefix).
    exact hsigmaSource.
  }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation baseWitnessList baseContext
      endpointWitnessList endpointContext
      (coqDynamicTruthPredecessorStateTemplateContext ++ prefix)
      (rawTemplateFormula translation
        (coqDynamicTruthGlobalExistentialSource 0 localSigma localPi))
      sigmaSourceRoot hbase hendpointWitnessed hendpointIncluded
      hsigmaSourceTemplate)
    as [transportedSigmaSourceRoot htransportedSigmaSource].
  assert (htransportedSigmaSourceJoint : RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M
        (rawTemplateContextCodeOnTail translation endpointContext prefix))
      (rawTemplateFormula translation
        (coqDynamicTruthGlobalExistentialSource 0 localSigma localPi))
      transportedSigmaSourceRoot).
  {
    rewrite <- (raw_dynamicTruthPredecessorStateTemplateContext_app_code
      M translation
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      endpointContext prefix).
    exact htransportedSigmaSource.
  }
  assert (hpiSourceTemplate : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqDynamicTruthPredecessorStateTemplateContext ++ prefix))
      (rawTemplateFormula translation
        (coqDynamicTruthGlobalExistentialSource 1 localSigma localPi))
      piSourceRoot).
  {
    rewrite (raw_dynamicTruthPredecessorStateTemplateContext_app_code
      M translation
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      baseContext prefix).
    exact hpiSource.
  }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation baseWitnessList baseContext
      endpointWitnessList endpointContext
      (coqDynamicTruthPredecessorStateTemplateContext ++ prefix)
      (rawTemplateFormula translation
        (coqDynamicTruthGlobalExistentialSource 1 localSigma localPi))
      piSourceRoot hbase hendpointWitnessed hendpointIncluded
      hpiSourceTemplate)
    as [transportedPiSourceRoot htransportedPiSource].
  assert (htransportedPiSourceJoint : RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M
        (rawTemplateContextCodeOnTail translation endpointContext prefix))
      (rawTemplateFormula translation
        (coqDynamicTruthGlobalExistentialSource 1 localSigma localPi))
      transportedPiSourceRoot).
  {
    rewrite <- (raw_dynamicTruthPredecessorStateTemplateContext_app_code
      M translation
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      endpointContext prefix).
    exact htransportedPiSource.
  }
  destruct
    (raw_dynamicTruthPredecessorStateLogicalRootsAt_of_global_row_pair_under_prefix_atomic_and_domain_of_selected_compiler_families
      M hPA translation
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      endpointWitnessList endpointContext prefix
      localSigma localPi sigmaDomain piDomain
      sigmaConclusion piConclusion
      transportedSigmaSourceRoot transportedPiSourceRoot
      atomicResultRoot rankResultRoot hprefix hendpointWitnessed
      (fun sourceWitnessList sourceContext hsource hsourceIncluded =>
        hsigmaFamily sourceWitnessList sourceContext hsource
          (fun member hmember =>
            hsourceIncluded member
              (hendpointIncluded member hmember)))
      (fun sourceWitnessList sourceContext hsource hsourceIncluded =>
        hpiFamily sourceWitnessList sourceContext hsource
          (fun member hmember =>
            hsourceIncluded member
              (hendpointIncluded member hmember)))
      htransportedSigmaSourceJoint htransportedPiSourceJoint
      hendpointAtomicNative hendpointRankNative)
    as (targetWitnessList & targetContext & htargetWitnessed &
      htargetIncluded & hroots).
  exists targetWitnessList, targetContext.
  split; [exact htargetWitnessed |].
  split.
  - intros member hmember.
    exact (htargetIncluded member (hendpointIncluded member hmember)).
  - exact hroots.
Qed.

(** Empty-prefix client with dependency-ordered growing global sources.
    Append traversal may choose a larger witnessed PA tail before the two
    predecessor-state source roots exist.  Rather than collapse those roots
    back to the caller context, transport the restricted and rule premises
    once to that selected tail, specialize both payload families there, and
    invoke the complete handoff. *)
Theorem
    raw_codedPALocalProof_strongStepPredecessorLogicalRoots_of_restricted_rule_and_growing_global_sources_and_selected_compiler_families :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    baseWitnessList baseContext levelNumeral
    (localSigma localPi : TemplateFormula)
    sigmaDomain piDomain sigmaConclusion piConclusion
    restrictedRoot ruleRoot,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  rawDirectTemplateTerm inputs
    coqRestrictedPASoundnessLowerLevelTerm = levelNumeral ->
  RawCodedFormulaSingleSubstitution M levelNumeral
    (rawNumeralValue M
      (formulaCode dynamicTruthLocalSigmaInputDomainTemplate))
    sigmaDomain ->
  RawCodedFormulaSingleSubstitution M levelNumeral
    (rawNumeralValue M
      (formulaCode dynamicTruthLocalPiInputDomainTemplate))
    piDomain ->
  RawCodedDynamicTruthSelectedPayloadShiftCompilerOnWitnessedExtensions
    M (rawDirectStructuralTemplateTranslation M hPA inputs)
    baseContext [] 0 localSigma localPi sigmaConclusion ->
  RawCodedDynamicTruthSelectedPayloadShiftCompilerOnWitnessedExtensions
    M (rawDirectStructuralTemplateTranslation M hPA inputs)
    baseContext [] 1 localSigma localPi piConclusion ->
  RawCodedPALocalProofOf M baseContext
    (rawDirectTemplateFormula inputs
      coqRestrictedPADerivationSoundnessRestrictedProofTemplate)
    restrictedRoot ->
  RawCodedPALocalProofOf M baseContext
    (rawDirectTemplateFormula inputs
      coqStrongStepProofEndpointAtomicAdequacyRulePremise)
    ruleRoot ->
  RawDynamicTruthPredecessorGlobalRootsOnWitnessedExtensionFrom M
    baseContext
    (rawDirectTemplateFormula inputs
      (coqDynamicTruthGlobalExistentialSource 0 localSigma localPi))
    (rawDirectTemplateFormula inputs
      (coqDynamicTruthGlobalExistentialSource 1 localSigma localPi)) ->
  exists targetWitnessList targetContext,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawDynamicTruthPredecessorStateLogicalRootsAt M targetContext
      sigmaDomain piDomain
      (rawDirectTemplateFormula inputs sigmaConclusion)
      (rawDirectTemplateFormula inputs piConclusion).
Proof.
  intros M hPA inputs baseWitnessList baseContext levelNumeral
    localSigma localPi sigmaDomain piDomain sigmaConclusion piConclusion
    restrictedRoot ruleRoot hbase hlevel hsigmaDomain hpiDomain
    hsigmaFamily hpiFamily hrestricted hrule
    (sourceWitnessList & sourceContext & hsourceWitnessed &
      hbaseIncluded & hsourceRoots).
  destruct hsourceRoots as
    [(sigmaSourceRoot & hsigmaSource) (piSourceRoot & hpiSource)].
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation baseWitnessList baseContext
      sourceWitnessList sourceContext []
      (rawDirectTemplateFormula inputs
        coqRestrictedPADerivationSoundnessRestrictedProofTemplate)
      restrictedRoot hbase hsourceWitnessed hbaseIncluded hrestricted) as
    [transportedRestrictedRoot htransportedRestricted].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation baseWitnessList baseContext
      sourceWitnessList sourceContext []
      (rawDirectTemplateFormula inputs
        coqStrongStepProofEndpointAtomicAdequacyRulePremise)
      ruleRoot hbase hsourceWitnessed hbaseIncluded hrule) as
    [transportedRuleRoot htransportedRule].
  cbn [rawTemplateContextCodeOnTail] in
    htransportedRestricted, htransportedRule.
  destruct
    (raw_codedPALocalProof_strongStepPredecessorLogicalRoots_of_restricted_rule_and_global_sources_and_selected_compiler_families_under_prefix
      M hPA inputs sourceWitnessList sourceContext [] levelNumeral
      localSigma localPi sigmaDomain piDomain
      sigmaConclusion piConclusion
      transportedRestrictedRoot transportedRuleRoot
      sigmaSourceRoot piSourceRoot) as
    (targetWitnessList & targetContext & htargetWitnessed &
      hsourceIncluded & hroots).
  - intros formula hmember. contradiction.
  - exact hsourceWitnessed.
  - exact hlevel.
  - exact hsigmaDomain.
  - exact hpiDomain.
  - intros witnessList extendedContext hwitnessed hincluded.
    exact (hsigmaFamily witnessList extendedContext hwitnessed
      (fun member hmember =>
        hincluded member (hbaseIncluded member hmember))).
  - intros witnessList extendedContext hwitnessed hincluded.
    exact (hpiFamily witnessList extendedContext hwitnessed
      (fun member hmember =>
        hincluded member (hbaseIncluded member hmember))).
  - exact htransportedRestricted.
  - exact htransportedRule.
  - exact hsigmaSource.
  - exact hpiSource.
  - exists targetWitnessList, targetContext.
    split; [exact htargetWitnessed |].
    split.
    + intros member hmember.
      exact (hsourceIncluded member (hbaseIncluded member hmember)).
    + cbn [rawTemplateContextCodeOnTail] in hroots.
      exact hroots.
Qed.

(** Backward-compatible strong handoff for clients that can identify selected
    payload codes directly.  Native clients should use the proof-producing
    compiler-family theorem above. *)
Theorem
    raw_codedPALocalProof_strongStepPredecessorLogicalRoots_of_restricted_rule_and_global_sources_under_prefix :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    baseWitnessList baseContext prefix
    levelNumeral (localSigma localPi : TemplateFormula)
    sigmaDomain piDomain
    sigmaConclusion piConclusion
    restrictedRoot ruleRoot sigmaSourceRoot piSourceRoot,
  RawCodedTemplatePrefixAtomicallyAdequate M
    (rawDirectStructuralTemplateTranslation M hPA inputs) prefix ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  rawDirectTemplateTerm inputs
    coqRestrictedPASoundnessLowerLevelTerm = levelNumeral ->
  RawCodedFormulaSingleSubstitution M levelNumeral
    (rawNumeralValue M
      (formulaCode dynamicTruthLocalSigmaInputDomainTemplate))
    sigmaDomain ->
  RawCodedFormulaSingleSubstitution M levelNumeral
    (rawNumeralValue M
      (formulaCode dynamicTruthLocalPiInputDomainTemplate))
    piDomain ->
  rawTemplateFormula
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqDynamicTruthGlobalOpenedRootRowSelectedPayload
        0 localSigma localPi) =
    rawTemplateFormula
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (templateFormulaShiftMany 10 sigmaConclusion) ->
  rawTemplateFormula
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqDynamicTruthGlobalOpenedRootRowSelectedPayload
        1 localSigma localPi) =
    rawTemplateFormula
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (templateFormulaShiftMany 10 piConclusion) ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      baseContext prefix)
    (rawDirectTemplateFormula inputs
      coqRestrictedPADerivationSoundnessRestrictedProofTemplate)
    restrictedRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      baseContext prefix)
    (rawDirectTemplateFormula inputs
      coqStrongStepProofEndpointAtomicAdequacyRulePremise)
    ruleRoot ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthPredecessorJointStateContext M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        baseContext prefix))
    (rawTemplateFormula
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqDynamicTruthGlobalExistentialSource 0 localSigma localPi))
    sigmaSourceRoot ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthPredecessorJointStateContext M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        baseContext prefix))
    (rawTemplateFormula
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqDynamicTruthGlobalExistentialSource 1 localSigma localPi))
    piSourceRoot ->
  exists targetWitnessList targetContext,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawDynamicTruthPredecessorStateLogicalRootsAt M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        targetContext prefix)
      sigmaDomain piDomain
      (rawTemplateFormula
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        sigmaConclusion)
      (rawTemplateFormula
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        piConclusion).
Proof.
  intros M hPA inputs baseWitnessList baseContext prefix
    levelNumeral localSigma localPi sigmaDomain piDomain
    sigmaConclusion piConclusion
    restrictedRoot ruleRoot sigmaSourceRoot piSourceRoot
    hprefix hbase hlevel hsigmaDomain hpiDomain
    hsigmaAlignment hpiAlignment hrestricted hrule
    hsigmaSource hpiSource.
  apply
    (raw_codedPALocalProof_strongStepPredecessorLogicalRoots_of_restricted_rule_and_global_sources_and_selected_compiler_families_under_prefix
      M hPA inputs baseWitnessList baseContext prefix
      levelNumeral localSigma localPi sigmaDomain piDomain
      sigmaConclusion piConclusion restrictedRoot ruleRoot
      sigmaSourceRoot piSourceRoot hprefix hbase hlevel
      hsigmaDomain hpiDomain).
  - intros sourceWitnessList sourceContext hsource hsourceIncluded
      witnesses selectedRoot hextended hincluded hselected.
    exists selectedRoot.
    rewrite <- hsigmaAlignment.
    exact hselected.
  - intros sourceWitnessList sourceContext hsource hsourceIncluded
      witnesses selectedRoot hextended hincluded hselected.
    exists selectedRoot.
    rewrite <- hpiAlignment.
    exact hselected.
  - exact hrestricted.
  - exact hrule.
  - exact hsigmaSource.
  - exact hpiSource.
Qed.

(** Prefix-general arithmetic endpoint.  Restricted-proof and rule-validity
    roots may depend on any finite adequate template prefix, which is retained
    verbatim while the witnessed PA tail grows.  The conclusion codes are
    aligned with the native atomic and rank-domain constructors here once. *)
Theorem
    raw_codedPALocalProof_strongStepPredecessor_atomic_and_domain_of_restricted_and_rule_roots_under_prefix :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    baseWitnessList baseContext prefix
    levelNumeral sigmaDomain piDomain restrictedRoot ruleRoot,
  RawCodedTemplatePrefixAtomicallyAdequate M
    (rawDirectStructuralTemplateTranslation M hPA inputs) prefix ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  rawDirectTemplateTerm inputs
    coqRestrictedPASoundnessLowerLevelTerm = levelNumeral ->
  RawCodedFormulaSingleSubstitution M levelNumeral
    (rawNumeralValue M
      (formulaCode dynamicTruthLocalSigmaInputDomainTemplate))
    sigmaDomain ->
  RawCodedFormulaSingleSubstitution M levelNumeral
    (rawNumeralValue M
      (formulaCode dynamicTruthLocalPiInputDomainTemplate))
    piDomain ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      baseContext prefix)
    (rawDirectTemplateFormula inputs
      coqRestrictedPADerivationSoundnessRestrictedProofTemplate)
    restrictedRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      baseContext prefix)
    (rawDirectTemplateFormula inputs
      coqStrongStepProofEndpointAtomicAdequacyRulePremise)
    ruleRoot ->
  exists targetWitnessList targetContext atomicRoot domainRoot,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        targetContext prefix)
      (rawDynamicTruthLocalAtomicAdequacyCode M) atomicRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        targetContext prefix)
      (rawFormulaOrCode M sigmaDomain piDomain) domainRoot.
Proof.
  intros M hPA inputs baseWitnessList baseContext prefix
    levelNumeral sigmaDomain piDomain restrictedRoot ruleRoot
    hprefix hbase hlevel hsigmaDomain hpiDomain hrestricted hrule.
  destruct
    (raw_codedPALocalProof_strongStepEndpointEvidence_of_restricted_and_rule_roots_on_witnessed_tail_under_prefix
      M hPA inputs baseWitnessList baseContext prefix
      restrictedRoot ruleRoot hprefix hbase hrestricted hrule)
    as (endpointWitnesses & atomicResultRoot & rankResultRoot &
      hendpointWitnessed & hendpointIncluded &
      hendpointAtomic & hendpointRank).
  set (endpointWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      endpointWitnesses baseWitnessList).
  set (endpointContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      endpointWitnesses baseContext).
  assert (hendpointAtomicNative : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        endpointContext prefix)
      (rawDynamicTruthLocalAtomicAdequacyCode M) atomicResultRoot).
  {
    rewrite <- (raw_strongStepEndpointAtomicAdequacyConclusion_code
      M hPA inputs).
    exact hendpointAtomic.
  }
  assert (hendpointRankNative : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        endpointContext prefix)
      (rawFormulaOrCode M sigmaDomain piDomain) rankResultRoot).
  {
    rewrite <- (raw_strongStepEndpointQuantifierBoundedConclusion_code
      M hPA inputs levelNumeral sigmaDomain piDomain
      hlevel hsigmaDomain hpiDomain).
    exact hendpointRank.
  }
  exists endpointWitnessList, endpointContext,
    atomicResultRoot, rankResultRoot.
  split; [exact hendpointWitnessed |].
  split; [exact hendpointIncluded |].
  split; assumption.
Qed.

(** If the two proof-dependent endpoint premises occur in the retained
    template prefix, their local roots are assumption leaves rather than
    external compiler obligations.  The prefix may contain arbitrary other
    assumptions and is retained verbatim in both conclusions.  Atomic
    adequacy is automatic for every formula translated by a template
    translation, so callers need supply only the two membership facts. *)
Theorem
    raw_codedPALocalProof_strongStepPredecessor_atomic_and_domain_from_template_assumptions_under_prefix :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    baseWitnessList baseContext prefix
    levelNumeral sigmaDomain piDomain,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  In coqRestrictedPADerivationSoundnessRestrictedProofTemplate prefix ->
  In coqStrongStepProofEndpointAtomicAdequacyRulePremise prefix ->
  rawDirectTemplateTerm inputs
    coqRestrictedPASoundnessLowerLevelTerm = levelNumeral ->
  RawCodedFormulaSingleSubstitution M levelNumeral
    (rawNumeralValue M
      (formulaCode dynamicTruthLocalSigmaInputDomainTemplate))
    sigmaDomain ->
  RawCodedFormulaSingleSubstitution M levelNumeral
    (rawNumeralValue M
      (formulaCode dynamicTruthLocalPiInputDomainTemplate))
    piDomain ->
  exists targetWitnessList targetContext atomicRoot domainRoot,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        targetContext prefix)
      (rawDynamicTruthLocalAtomicAdequacyCode M) atomicRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        targetContext prefix)
      (rawFormulaOrCode M sigmaDomain piDomain) domainRoot.
Proof.
  intros M hPA inputs baseWitnessList baseContext prefix
    levelNumeral sigmaDomain piDomain
    hbase hrestrictedIn hruleIn hlevel hsigmaDomain hpiDomain.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  set (restrictedDerivation := trpAss prefix
    coqRestrictedPADerivationSoundnessRestrictedProofTemplate).
  set (ruleDerivation := trpAss prefix
    coqStrongStepProofEndpointAtomicAdequacyRulePremise).
  pose proof
    (raw_templateAssumptionOnPAAxiomContext_localProof
      M hPA translation baseWitnessList baseContext
      prefix coqRestrictedPADerivationSoundnessRestrictedProofTemplate
      hbase hrestrictedIn)
    as hrestricted.
  pose proof
    (raw_templateAssumptionOnPAAxiomContext_localProof
      M hPA translation baseWitnessList baseContext
      prefix coqStrongStepProofEndpointAtomicAdequacyRulePremise
      hbase hruleIn)
    as hrule.
  cbn [restrictedDerivation] in hrestricted.
  cbn [ruleDerivation] in hrule.
  exact
    (raw_codedPALocalProof_strongStepPredecessor_atomic_and_domain_of_restricted_and_rule_roots_under_prefix
      M hPA inputs baseWitnessList baseContext prefix
      levelNumeral sigmaDomain piDomain
      (rawTemplateProofCodeOnTail translation baseContext
        restrictedDerivation)
      (rawTemplateProofCodeOnTail translation baseContext ruleDerivation)
      (raw_directStructuralTemplatePrefix_atomically_adequate
        M hPA inputs prefix)
      hbase hlevel hsigmaDomain hpiDomain hrestricted hrule).
Qed.

(** The endpoint engine consumes its two proof-dependent premises only after
    the predecessor-state assumptions have been prefixed.  Exposing that
    exact boundary is strictly weaker than asking for the premises over the
    bare PA-axiom tail: a caller which learns them from the two state rows can
    now use them without an invalid contraction step. *)
Theorem
    raw_codedPALocalProof_strongStepPredecessor_atomic_and_domain_of_restricted_and_rule_roots_under_predecessor_state :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    baseWitnessList baseContext levelNumeral sigmaDomain piDomain
    restrictedRoot ruleRoot,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  rawDirectTemplateTerm inputs
    coqRestrictedPASoundnessLowerLevelTerm = levelNumeral ->
  RawCodedFormulaSingleSubstitution M levelNumeral
    (rawNumeralValue M
      (formulaCode dynamicTruthLocalSigmaInputDomainTemplate))
    sigmaDomain ->
  RawCodedFormulaSingleSubstitution M levelNumeral
    (rawNumeralValue M
      (formulaCode dynamicTruthLocalPiInputDomainTemplate))
    piDomain ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthPredecessorJointStateContext M baseContext)
    (rawDirectTemplateFormula inputs
      coqRestrictedPADerivationSoundnessRestrictedProofTemplate)
    restrictedRoot ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthPredecessorJointStateContext M baseContext)
    (rawDirectTemplateFormula inputs
      coqStrongStepProofEndpointAtomicAdequacyRulePremise)
    ruleRoot ->
  exists targetWitnessList targetContext atomicRoot domainRoot,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M targetContext)
      (rawDynamicTruthLocalAtomicAdequacyCode M) atomicRoot /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M targetContext)
      (rawFormulaOrCode M sigmaDomain piDomain) domainRoot.
Proof.
  intros M hPA inputs baseWitnessList baseContext
    levelNumeral sigmaDomain piDomain restrictedRoot ruleRoot
    hbase hlevel hsigmaDomain hpiDomain hrestricted hrule.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  assert (hstateAdequate : RawCodedTemplatePrefixAtomicallyAdequate M
      translation coqDynamicTruthPredecessorStateTemplateContext).
  {
    exact
      (raw_dynamicTruthPredecessorStateTemplateContext_atomically_adequate
        M hPA translation
        (rawDirectStructuralTemplatePAAgreement M hPA inputs)).
  }
  rewrite <- (raw_dynamicTruthPredecessorStateTemplateContextCode
    M translation (rawDirectStructuralTemplatePAAgreement M hPA inputs)
    baseContext) in hrestricted, hrule.
  destruct
    (raw_codedPALocalProof_strongStepPredecessor_atomic_and_domain_of_restricted_and_rule_roots_under_prefix
      M hPA inputs baseWitnessList baseContext
      coqDynamicTruthPredecessorStateTemplateContext
      levelNumeral sigmaDomain piDomain restrictedRoot ruleRoot
      hstateAdequate hbase hlevel hsigmaDomain hpiDomain
      hrestricted hrule)
    as (endpointWitnessList & endpointContext &
      atomicResultRoot & rankResultRoot &
      hendpointWitnessed & hendpointIncluded &
      hendpointAtomic & hendpointRank).
  assert (hendpointAtomicNative : RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M endpointContext)
      (rawDynamicTruthLocalAtomicAdequacyCode M) atomicResultRoot).
  {
    rewrite <- (raw_dynamicTruthPredecessorStateTemplateContextCode
      M translation
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      endpointContext).
    exact hendpointAtomic.
  }
  assert (hendpointRankNative : RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M endpointContext)
      (rawFormulaOrCode M sigmaDomain piDomain) rankResultRoot).
  {
    rewrite <- (raw_dynamicTruthPredecessorStateTemplateContextCode
      M translation
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      endpointContext).
    exact hendpointRank.
  }
  exists endpointWitnessList, endpointContext,
    atomicResultRoot, rankResultRoot.
  split; [exact hendpointWitnessed |].
  split; [exact hendpointIncluded |].
  split; assumption.
Qed.

(** Root production may itself append standard PA axioms before entering the
    state prefix.  Apply the exact state-prefix endpoint on that witnessed
    source and compose the caller-to-source and source-to-target inclusions;
    no proof needs to be contracted back to the original tail. *)
Theorem
    raw_codedPALocalProof_strongStepPredecessor_atomic_and_domain_of_restricted_and_rule_roots_under_predecessor_state_on_witnessed_extension_from :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    baseContext sourceWitnessList sourceContext
    levelNumeral sigmaDomain piDomain restrictedRoot ruleRoot,
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawContextListIncluded M baseContext sourceContext ->
  rawDirectTemplateTerm inputs
    coqRestrictedPASoundnessLowerLevelTerm = levelNumeral ->
  RawCodedFormulaSingleSubstitution M levelNumeral
    (rawNumeralValue M
      (formulaCode dynamicTruthLocalSigmaInputDomainTemplate))
    sigmaDomain ->
  RawCodedFormulaSingleSubstitution M levelNumeral
    (rawNumeralValue M
      (formulaCode dynamicTruthLocalPiInputDomainTemplate))
    piDomain ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthPredecessorJointStateContext M sourceContext)
    (rawDirectTemplateFormula inputs
      coqRestrictedPADerivationSoundnessRestrictedProofTemplate)
    restrictedRoot ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthPredecessorJointStateContext M sourceContext)
    (rawDirectTemplateFormula inputs
      coqStrongStepProofEndpointAtomicAdequacyRulePremise)
    ruleRoot ->
  exists targetWitnessList targetContext atomicRoot domainRoot,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M targetContext)
      (rawDynamicTruthLocalAtomicAdequacyCode M) atomicRoot /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M targetContext)
      (rawFormulaOrCode M sigmaDomain piDomain) domainRoot.
Proof.
  intros M hPA inputs baseContext sourceWitnessList sourceContext
    levelNumeral sigmaDomain piDomain restrictedRoot ruleRoot
    hsourceWitnessed hbaseSourceIncluded hlevel
    hsigmaDomain hpiDomain hrestricted hrule.
  destruct
    (raw_codedPALocalProof_strongStepPredecessor_atomic_and_domain_of_restricted_and_rule_roots_under_predecessor_state
      M hPA inputs sourceWitnessList sourceContext levelNumeral
      sigmaDomain piDomain restrictedRoot ruleRoot hsourceWitnessed
      hlevel hsigmaDomain hpiDomain hrestricted hrule)
    as (targetWitnessList & targetContext & atomicRoot & domainRoot &
      htargetWitnessed & hsourceTargetIncluded & hatomic & hdomain).
  exists targetWitnessList, targetContext, atomicRoot, domainRoot.
  split; [exact htargetWitnessed |].
  split.
  - intros member hmember.
    exact (hsourceTargetIncluded member
      (hbaseSourceIncluded member hmember)).
  - split; assumption.
Qed.

(** Extract the dependency prefix of the complete handoff.  Restricted-proof
    and rule validity alone determine atomic adequacy and the disjunction of
    the two rank domains.  Keeping this endpoint independent of global-row
    evidence lets a later append traversal choose a further witnessed
    context without carrying selected-payload callbacks.  This compatibility
    wrapper transports bare-context roots to the weaker state-prefix lemma
    above. *)
Theorem
    raw_codedPALocalProof_strongStepPredecessor_atomic_and_domain_of_restricted_and_rule_roots :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    baseWitnessList baseContext levelNumeral sigmaDomain piDomain
    restrictedRoot ruleRoot,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  rawDirectTemplateTerm inputs
    coqRestrictedPASoundnessLowerLevelTerm = levelNumeral ->
  RawCodedFormulaSingleSubstitution M levelNumeral
    (rawNumeralValue M
      (formulaCode dynamicTruthLocalSigmaInputDomainTemplate))
    sigmaDomain ->
  RawCodedFormulaSingleSubstitution M levelNumeral
    (rawNumeralValue M
      (formulaCode dynamicTruthLocalPiInputDomainTemplate))
    piDomain ->
  RawCodedPALocalProofOf M baseContext
    (rawDirectTemplateFormula inputs
      coqRestrictedPADerivationSoundnessRestrictedProofTemplate)
    restrictedRoot ->
  RawCodedPALocalProofOf M baseContext
    (rawDirectTemplateFormula inputs
      coqStrongStepProofEndpointAtomicAdequacyRulePremise)
    ruleRoot ->
  exists targetWitnessList targetContext atomicRoot domainRoot,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M targetContext)
      (rawDynamicTruthLocalAtomicAdequacyCode M) atomicRoot /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M targetContext)
      (rawFormulaOrCode M sigmaDomain piDomain) domainRoot.
Proof.
  intros M hPA inputs baseWitnessList baseContext
    levelNumeral sigmaDomain piDomain restrictedRoot ruleRoot
    hbase hlevel hsigmaDomain hpiDomain hrestricted hrule.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  assert (hbaseRealizable : RawContextListRealizable M baseContext).
  {
    exact (raw_codedPAAxiomWitnessContext_context_realizable
      M baseWitnessList baseContext hbase).
  }
  assert (hstateAdequate : RawCodedTemplatePrefixAtomicallyAdequate M
      translation coqDynamicTruthPredecessorStateTemplateContext).
  {
    exact
      (raw_dynamicTruthPredecessorStateTemplateContext_atomically_adequate
        M hPA translation
        (rawDirectStructuralTemplatePAAgreement M hPA inputs)).
  }
  destruct
    (raw_codedPALocalProof_templatePrefix M hPA translation
      baseContext coqDynamicTruthPredecessorStateTemplateContext
      (rawDirectTemplateFormula inputs
        coqRestrictedPADerivationSoundnessRestrictedProofTemplate)
      restrictedRoot hbaseRealizable hstateAdequate hrestricted)
    as [stateRestrictedRoot hstateRestricted].
  destruct
    (raw_codedPALocalProof_templatePrefix M hPA translation
      baseContext coqDynamicTruthPredecessorStateTemplateContext
      (rawDirectTemplateFormula inputs
        coqStrongStepProofEndpointAtomicAdequacyRulePremise)
      ruleRoot hbaseRealizable hstateAdequate hrule)
    as [stateRuleRoot hstateRule].
  rewrite (raw_dynamicTruthPredecessorStateTemplateContextCode
    M translation (rawDirectStructuralTemplatePAAgreement M hPA inputs)
    baseContext) in hstateRestricted, hstateRule.
  exact
    (raw_codedPALocalProof_strongStepPredecessor_atomic_and_domain_of_restricted_and_rule_roots_under_predecessor_state
      M hPA inputs baseWitnessList baseContext levelNumeral
      sigmaDomain piDomain stateRestrictedRoot stateRuleRoot
      hbase hlevel hsigmaDomain hpiDomain hstateRestricted hstateRule).
Qed.

End PABoundedRawCodedStrongStepPredecessorGlobalRowEvidenceCompilation.
