(**
  Assemble predecessor logical roots from already compiled evidence.

  The historical strong-step route obtains Sigma and Pi evidence by opening
  two global traversal sources and selecting their root rows.  That is useful
  when only uninstantiated global sources are available, but it is needlessly
  strong when a traversal compiler has already produced the two formulas
  obtained by applying those global predicates to the current arguments.

  This module extracts the shared remainder.  Atomic adequacy and the rank
  disjunction still generate the honest admissibility proof on a finite PA
  witness extension.  Arbitrary caller-supplied evidence proofs are then
  transported to precisely that same extension and packaged with the new
  admissibility root.  No selected-row callback, source decoding, or formula
  equality is required.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedContextLists
  RawCodedRestrictedPAProof
  RawCodedSyntaxConstructors
  RawCodedPAAxiomWitnessPrefix
  RawCodedPAAxiomContextSelfShift
  RawCodedPALocalProofExistential
  RawCodedPALocalProofUniversalEliminationChain
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedDynamicTruthPredecessorGlobalExistentialElimination
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthImpBranchExclusivity
  RawCodedDynamicTruthLocalExclusiveTemplateDirectInputs
  RawCodedDynamicTruthLocalFieldProjectionCompilation
  RawCodedDynamicTruthLocalAdmissibilityCompilation
  RawCodedDynamicTruthPredecessorStateExclusivityCompilation
  RawCodedDynamicTruthPredecessorAdmissibilityAssignmentCompilation
  RawCodedDynamicTruthPredecessorAtomicDomainGlobalRootsSynchronization.

Module
  PABoundedRawCodedDynamicTruthPredecessorDirectEvidenceLogicalRoots.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPAAxiomContextSelfShift.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofUniversalEliminationChain.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import
  PABoundedRawCodedDynamicTruthPredecessorGlobalExistentialElimination.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedDynamicTruthImpBranchExclusivity.
Import PABoundedRawCodedDynamicTruthLocalExclusiveTemplateDirectInputs.
Import PABoundedRawCodedDynamicTruthLocalFieldProjectionCompilation.
Import PABoundedRawCodedDynamicTruthLocalAdmissibilityCompilation.
Import
  PABoundedRawCodedDynamicTruthPredecessorStateExclusivityCompilation.
Import
  PABoundedRawCodedDynamicTruthPredecessorAdmissibilityAssignmentCompilation.
Import
  PABoundedRawCodedDynamicTruthPredecessorAtomicDomainGlobalRootsSynchronization.

(** The evidence endpoints are arbitrary carrier formula codes.  The only
    syntactic data retained here is the caller prefix, needed to transport
    proofs through the standard-axiom witness extension without erasing any
    temporary assumptions. *)
Theorem
    raw_dynamicTruthPredecessorStateLogicalRootsAt_of_direct_evidence_under_prefix_atomic_and_domain :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext prefix
      sigmaDomain piDomain sigmaEvidence piEvidence
      atomicRoot domainRoot sigmaRoot piRoot,
  RawCodedTemplatePrefixAtomicallyAdequate M translation prefix ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthPredecessorJointStateContext M
      (rawTemplateContextCodeOnTail translation baseContext prefix))
    (rawDynamicTruthLocalAtomicAdequacyCode M) atomicRoot ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthPredecessorJointStateContext M
      (rawTemplateContextCodeOnTail translation baseContext prefix))
    (rawFormulaOrCode M sigmaDomain piDomain) domainRoot ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthPredecessorJointStateContext M
      (rawTemplateContextCodeOnTail translation baseContext prefix))
    sigmaEvidence sigmaRoot ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthPredecessorJointStateContext M
      (rawTemplateContextCodeOnTail translation baseContext prefix))
    piEvidence piRoot ->
  exists targetWitnessList targetContext,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawDynamicTruthPredecessorStateLogicalRootsAt M
      (rawTemplateContextCodeOnTail translation targetContext prefix)
      sigmaDomain piDomain sigmaEvidence piEvidence.
Proof.
  intros M hPA translation hagreement
    baseWitnessList baseContext prefix
    sigmaDomain piDomain sigmaEvidence piEvidence
    atomicRoot domainRoot sigmaRoot piRoot
    hprefix hbase hatomic hdomain hsigma hpi.
  destruct
    (raw_dynamicTruthPredecessorLocalAdmissibility_on_witnessed_extension_under_prefix_of_atomic_and_domain
      M hPA translation hagreement baseWitnessList baseContext prefix
      sigmaDomain piDomain atomicRoot domainRoot
      hprefix hbase hatomic hdomain)
    as (witnesses & admissibleRoot & htargetWitnessed & hadmissible).
  set (targetWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses baseWitnessList).
  set (targetContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses baseContext).
  assert (hincluded : RawContextListIncluded M baseContext targetContext).
  {
    unfold targetContext.
    exact (raw_standardPAAxiomWitnessPrefixContextCode_target_included
      M hPA witnesses baseContext).
  }
  assert (hsigmaTemplate : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqDynamicTruthPredecessorStateTemplateContext ++ prefix))
      sigmaEvidence sigmaRoot).
  {
    rewrite (raw_dynamicTruthPredecessorStateTemplateContext_app_code
      M translation hagreement baseContext prefix).
    exact hsigma.
  }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation baseWitnessList baseContext
      targetWitnessList targetContext
      (coqDynamicTruthPredecessorStateTemplateContext ++ prefix)
      sigmaEvidence sigmaRoot hbase htargetWitnessed hincluded
      hsigmaTemplate)
    as [transportedSigmaRoot htransportedSigma].
  assert (htransportedSigmaJoint : RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M
        (rawTemplateContextCodeOnTail translation targetContext prefix))
      sigmaEvidence transportedSigmaRoot).
  {
    rewrite <- (raw_dynamicTruthPredecessorStateTemplateContext_app_code
      M translation hagreement targetContext prefix).
    exact htransportedSigma.
  }
  assert (hpiTemplate : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqDynamicTruthPredecessorStateTemplateContext ++ prefix))
      piEvidence piRoot).
  {
    rewrite (raw_dynamicTruthPredecessorStateTemplateContext_app_code
      M translation hagreement baseContext prefix).
    exact hpi.
  }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation baseWitnessList baseContext
      targetWitnessList targetContext
      (coqDynamicTruthPredecessorStateTemplateContext ++ prefix)
      piEvidence piRoot hbase htargetWitnessed hincluded hpiTemplate)
    as [transportedPiRoot htransportedPi].
  assert (htransportedPiJoint : RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M
        (rawTemplateContextCodeOnTail translation targetContext prefix))
      piEvidence transportedPiRoot).
  {
    rewrite <- (raw_dynamicTruthPredecessorStateTemplateContext_app_code
      M translation hagreement targetContext prefix).
    exact htransportedPi.
  }
  exists targetWitnessList, targetContext.
  split; [exact htargetWitnessed |].
  split; [exact hincluded |].
  refine
    {| rawDynamicTruthPredecessorLogicalRoots_admissible := _;
       rawDynamicTruthPredecessorLogicalRoots_sigmaEvidence := _;
       rawDynamicTruthPredecessorLogicalRoots_piEvidence := _ |}.
  - exists admissibleRoot. exact hadmissible.
  - exists transportedSigmaRoot. exact htransportedSigmaJoint.
  - exists transportedPiRoot. exact htransportedPiJoint.
Qed.

(** End-to-end corrected predecessor closure from instantiated template
    leaves.  Admissibility may append standard PA axioms; the source local
    law and both evidence roots are transported to that retained extension
    under the identical three-times-shifted caller prefix before the
    prefix-preserving exclusivity bridge closes its binders. *)
Theorem
    raw_dynamicTruthImpPredecessorStateExclusivityRoot_of_instantiated_evidence_under_template_prefix :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext prefix
      sourceRoot atomicRoot domainRoot sigmaRoot piRoot,
  RawCodedTemplatePrefixAtomicallyAdequate M translation
    (templateContextShift (templateContextShift
      (templateContextShift prefix))) ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext
      (templateContextShift (templateContextShift
        (templateContextShift prefix))))
    (rawTemplateFormula translation
      (tfAll (tfAll (tfAll
        coqDynamicTruthLocalExclusiveBodyTemplate))))
    sourceRoot ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthPredecessorJointStateContext M
      (rawTemplateContextCodeOnTail translation baseContext
        (templateContextShift (templateContextShift
          (templateContextShift prefix)))))
    (rawTemplateFormula translation
      coqDynamicTruthPredecessorLocalAtomicAdequacyTemplate)
    atomicRoot ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthPredecessorJointStateContext M
      (rawTemplateContextCodeOnTail translation baseContext
        (templateContextShift (templateContextShift
          (templateContextShift prefix)))))
    (rawFormulaOrCode M
      (rawTemplateFormula translation
        coqDynamicTruthPredecessorLocalSigmaDomainTemplate)
      (rawTemplateFormula translation
        coqDynamicTruthPredecessorLocalPiDomainTemplate))
    domainRoot ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthPredecessorJointStateContext M
      (rawTemplateContextCodeOnTail translation baseContext
        (templateContextShift (templateContextShift
          (templateContextShift prefix)))))
    (rawTemplateFormula translation
      coqDynamicTruthPredecessorLocalSigmaEvidenceTemplate)
    sigmaRoot ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthPredecessorJointStateContext M
      (rawTemplateContextCodeOnTail translation baseContext
        (templateContextShift (templateContextShift
          (templateContextShift prefix)))))
    (rawTemplateFormula translation
      coqDynamicTruthPredecessorLocalPiEvidenceTemplate)
    piRoot ->
  exists targetWitnessList targetContext predecessorRoot,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation targetContext prefix)
      (rawDynamicTruthImpPredecessorStateExclusivityCode M)
      predecessorRoot.
Proof.
  intros M hPA translation hagreement baseWitnessList baseContext prefix
    sourceRoot atomicRoot domainRoot sigmaRoot piRoot
    hshiftedPrefix hbase hsource hatomic hdomain hsigma hpi.
  set (prefix3 := templateContextShift (templateContextShift
    (templateContextShift prefix))).
  destruct
    (raw_dynamicTruthPredecessorChildAdmissibilityTemplate_on_witnessed_extension_under_prefix
      M hPA translation hagreement baseWitnessList baseContext prefix3
      atomicRoot domainRoot hshiftedPrefix hbase hatomic hdomain)
    as (witnesses & admissibleRoot & htargetWitnessed & hadmissible).
  set (targetWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses baseWitnessList).
  set (targetContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses baseContext).
  assert (hincluded : RawContextListIncluded M baseContext targetContext).
  {
    unfold targetContext.
    exact (raw_standardPAAxiomWitnessPrefixContextCode_target_included
      M hPA witnesses baseContext).
  }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation baseWitnessList baseContext
      targetWitnessList targetContext prefix3
      (rawTemplateFormula translation
        (tfAll (tfAll (tfAll
          coqDynamicTruthLocalExclusiveBodyTemplate))))
      sourceRoot hbase htargetWitnessed hincluded hsource)
    as [transportedSourceRoot htransportedSource].
  assert (hsigmaTemplate : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqDynamicTruthPredecessorStateTemplateContext ++ prefix3))
      (rawTemplateFormula translation
        coqDynamicTruthPredecessorLocalSigmaEvidenceTemplate)
      sigmaRoot).
  {
    rewrite (raw_dynamicTruthPredecessorStateTemplateContext_app_code
      M translation hagreement baseContext prefix3).
    exact hsigma.
  }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation baseWitnessList baseContext
      targetWitnessList targetContext
      (coqDynamicTruthPredecessorStateTemplateContext ++ prefix3)
      (rawTemplateFormula translation
        coqDynamicTruthPredecessorLocalSigmaEvidenceTemplate)
      sigmaRoot hbase htargetWitnessed hincluded hsigmaTemplate)
    as [transportedSigmaRoot htransportedSigmaTemplate].
  assert (htransportedSigma : RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M
        (rawTemplateContextCodeOnTail translation targetContext prefix3))
      (rawTemplateFormula translation
        coqDynamicTruthPredecessorLocalSigmaEvidenceTemplate)
      transportedSigmaRoot).
  {
    rewrite <- (raw_dynamicTruthPredecessorStateTemplateContext_app_code
      M translation hagreement targetContext prefix3).
    exact htransportedSigmaTemplate.
  }
  assert (hpiTemplate : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqDynamicTruthPredecessorStateTemplateContext ++ prefix3))
      (rawTemplateFormula translation
        coqDynamicTruthPredecessorLocalPiEvidenceTemplate)
      piRoot).
  {
    rewrite (raw_dynamicTruthPredecessorStateTemplateContext_app_code
      M translation hagreement baseContext prefix3).
    exact hpi.
  }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation baseWitnessList baseContext
      targetWitnessList targetContext
      (coqDynamicTruthPredecessorStateTemplateContext ++ prefix3)
      (rawTemplateFormula translation
        coqDynamicTruthPredecessorLocalPiEvidenceTemplate)
      piRoot hbase htargetWitnessed hincluded hpiTemplate)
    as [transportedPiRoot htransportedPiTemplate].
  assert (htransportedPi : RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M
        (rawTemplateContextCodeOnTail translation targetContext prefix3))
      (rawTemplateFormula translation
        coqDynamicTruthPredecessorLocalPiEvidenceTemplate)
      transportedPiRoot).
  {
    rewrite <- (raw_dynamicTruthPredecessorStateTemplateContext_app_code
      M translation hagreement targetContext prefix3).
    exact htransportedPiTemplate.
  }
  destruct
    (raw_dynamicTruthImpPredecessorStateExclusivityRoot_of_instantiated_template_under_template_prefix
      M hPA translation targetContext prefix transportedSourceRoot
      (raw_codedPAAxiomWitnessContext_context_realizable M
        targetWitnessList targetContext htargetWitnessed)
      (raw_codedPAAxiomWitnessContext_selfShift M hPA
        targetWitnessList targetContext htargetWitnessed)
      htransportedSource
      (ex_intro _ admissibleRoot hadmissible)
      (ex_intro _ transportedSigmaRoot htransportedSigma)
      (ex_intro _ transportedPiRoot htransportedPi))
    as [predecessorRoot hpredecessor].
  exists targetWitnessList, targetContext, predecessorRoot.
  split; [exact htargetWitnessed |].
  split; assumption.
Qed.

(** A projected local decision law is useful on every witnessed extension,
    not only in the callback context where its conjunction was first
    eliminated.  Transport the closed triple-universal proof to the
    admissibility extension, insert the exact temporary prefix retained by
    the caller, and apply the opened decision implication there.

    The single adequacy premise is deliberately stated for the combined
    predecessor-state/caller prefix.  It is both necessary for inserting
    that prefix and sufficient for the smaller caller prefix required by
    admissibility, so clients do not have to provide two overlapping
    certificates. *)
Theorem
    raw_dynamicTruthPredecessorEvidenceDecision_of_projected_decision_under_prefix_atomic_and_domain :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext prefix
      sigmaDomain piDomain sigmaEvidence piEvidence
      decisionSourceRoot atomicRoot domainRoot,
  RawCodedTemplatePrefixAtomicallyAdequate M translation
    (coqDynamicTruthPredecessorStateTemplateContext ++ prefix) ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedUniversalEliminationChain M
    (rawDynamicTruthLocalFormulaAll3Code M
      (rawDynamicTruthLocalDecisionCode M
        sigmaDomain piDomain sigmaEvidence piEvidence))
    (rawDynamicTruthLocalDecisionCode M
      sigmaDomain piDomain sigmaEvidence piEvidence) ->
  RawCodedPALocalProofOf M baseContext
    (rawDynamicTruthLocalFormulaAll3Code M
      (rawDynamicTruthLocalDecisionCode M
        sigmaDomain piDomain sigmaEvidence piEvidence))
    decisionSourceRoot ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthPredecessorJointStateContext M
      (rawTemplateContextCodeOnTail translation baseContext prefix))
    (rawDynamicTruthLocalAtomicAdequacyCode M) atomicRoot ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthPredecessorJointStateContext M
      (rawTemplateContextCodeOnTail translation baseContext prefix))
    (rawFormulaOrCode M sigmaDomain piDomain) domainRoot ->
  exists targetWitnessList targetContext decisionRoot,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M
        (rawTemplateContextCodeOnTail translation targetContext prefix))
      (rawFormulaOrCode M sigmaEvidence piEvidence) decisionRoot.
Proof.
  intros M hPA translation hagreement baseWitnessList baseContext prefix
    sigmaDomain piDomain sigmaEvidence piEvidence
    decisionSourceRoot atomicRoot domainRoot
    hcombinedPrefix hbase hchain hdecision hatomic hdomain.
  assert (hprefix : RawCodedTemplatePrefixAtomicallyAdequate
      M translation prefix).
  {
    intros formula hformula.
    exact (hcombinedPrefix formula (in_or_app _ _ _ (or_intror hformula))).
  }
  destruct
    (raw_dynamicTruthPredecessorLocalAdmissibility_on_witnessed_extension_under_prefix_of_atomic_and_domain
      M hPA translation hagreement baseWitnessList baseContext prefix
      sigmaDomain piDomain atomicRoot domainRoot
      hprefix hbase hatomic hdomain)
    as (witnesses & admissibleRoot & htargetWitnessed & hadmissible).
  set (targetWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses baseWitnessList).
  set (targetContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses baseContext).
  assert (hincluded : RawContextListIncluded M baseContext targetContext).
  {
    unfold targetContext.
    exact (raw_standardPAAxiomWitnessPrefixContextCode_target_included
      M hPA witnesses baseContext).
  }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation baseWitnessList baseContext
      targetWitnessList targetContext []
      (rawDynamicTruthLocalFormulaAll3Code M
        (rawDynamicTruthLocalDecisionCode M
          sigmaDomain piDomain sigmaEvidence piEvidence))
      decisionSourceRoot hbase htargetWitnessed hincluded hdecision)
    as [transportedDecisionRoot htransportedDecision].
  cbn [rawTemplateContextCodeOnTail] in htransportedDecision.
  destruct
    (raw_codedPALocalProof_templatePrefix
      M hPA translation targetContext
      (coqDynamicTruthPredecessorStateTemplateContext ++ prefix)
      (rawDynamicTruthLocalFormulaAll3Code M
        (rawDynamicTruthLocalDecisionCode M
          sigmaDomain piDomain sigmaEvidence piEvidence))
      transportedDecisionRoot
      (raw_codedPAAxiomWitnessContext_context_realizable
        M targetWitnessList targetContext htargetWitnessed)
      hcombinedPrefix htransportedDecision)
    as [prefixedDecisionRoot hprefixedDecision].
  assert (hjointDecision : RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M
        (rawTemplateContextCodeOnTail translation targetContext prefix))
      (rawDynamicTruthLocalFormulaAll3Code M
        (rawDynamicTruthLocalDecisionCode M
          sigmaDomain piDomain sigmaEvidence piEvidence))
      prefixedDecisionRoot).
  {
    rewrite <- (raw_dynamicTruthPredecessorStateTemplateContext_app_code
      M translation hagreement targetContext prefix).
    exact hprefixedDecision.
  }
  destruct
    (raw_codedPALocalProofOf_dynamicTruthLocalEvidenceDecision_of_elimination_chain
      M hPA
      (rawDynamicTruthPredecessorJointStateContext M
        (rawTemplateContextCodeOnTail translation targetContext prefix))
      sigmaDomain piDomain sigmaEvidence piEvidence
      prefixedDecisionRoot admissibleRoot
      hchain hjointDecision hadmissible)
    as [decisionRoot hdecisionRoot].
  exists targetWitnessList, targetContext, decisionRoot.
  split; [exact htargetWitnessed |].
  split; [exact hincluded | exact hdecisionRoot].
Qed.

(** Empty-prefix specialization for clients whose evidence roots already
    live directly under the two predecessor-state assumptions. *)
Corollary
    raw_dynamicTruthPredecessorStateLogicalRootsAt_of_direct_evidence_atomic_and_domain :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext
      sigmaDomain piDomain sigmaEvidence piEvidence
      atomicRoot domainRoot sigmaRoot piRoot,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthPredecessorJointStateContext M baseContext)
    (rawDynamicTruthLocalAtomicAdequacyCode M) atomicRoot ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthPredecessorJointStateContext M baseContext)
    (rawFormulaOrCode M sigmaDomain piDomain) domainRoot ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthPredecessorJointStateContext M baseContext)
    sigmaEvidence sigmaRoot ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthPredecessorJointStateContext M baseContext)
    piEvidence piRoot ->
  exists targetWitnessList targetContext,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawDynamicTruthPredecessorStateLogicalRootsAt M targetContext
      sigmaDomain piDomain sigmaEvidence piEvidence.
Proof.
  intros M hPA translation hagreement
    baseWitnessList baseContext sigmaDomain piDomain
    sigmaEvidence piEvidence atomicRoot domainRoot sigmaRoot piRoot
    hbase hatomic hdomain hsigma hpi.
  pose proof
    (raw_dynamicTruthPredecessorStateLogicalRootsAt_of_direct_evidence_under_prefix_atomic_and_domain
      M hPA translation hagreement baseWitnessList baseContext []
      sigmaDomain piDomain sigmaEvidence piEvidence
      atomicRoot domainRoot sigmaRoot piRoot
      (fun formula hformula => match hformula with end)
      hbase hatomic hdomain hsigma hpi) as hresult.
  cbn [rawTemplateContextCodeOnTail] in hresult.
  exact hresult.
Qed.

(** Growing evidence clients may choose their witnessed extension before
    admissibility is compiled.  Transport the two smaller arithmetic roots
    across that already chosen extension, then invoke the direct-evidence
    endpoint there.  This orders dependencies without requiring either
    evidence proof to contract back to the caller's context. *)
Theorem
    raw_dynamicTruthPredecessorStateLogicalRootsAt_of_direct_global_roots_on_witnessed_extension_atomic_and_domain :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext
      sigmaDomain piDomain sigmaEvidence piEvidence
      atomicRoot domainRoot,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthPredecessorJointStateContext M baseContext)
    (rawDynamicTruthLocalAtomicAdequacyCode M) atomicRoot ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthPredecessorJointStateContext M baseContext)
    (rawFormulaOrCode M sigmaDomain piDomain) domainRoot ->
  RawDynamicTruthPredecessorGlobalRootsOnWitnessedExtensionFrom M
    baseContext sigmaEvidence piEvidence ->
  exists targetWitnessList targetContext,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawDynamicTruthPredecessorStateLogicalRootsAt M targetContext
      sigmaDomain piDomain sigmaEvidence piEvidence.
Proof.
  intros M hPA translation hagreement
    baseWitnessList baseContext sigmaDomain piDomain
    sigmaEvidence piEvidence atomicRoot domainRoot
    hbase hatomic hdomain hglobalRoots.
  destruct
    (raw_dynamicTruthPredecessorAtomicDomainGlobalRootsAt_of_growing_global_roots
      M hPA translation hagreement baseWitnessList baseContext
      sigmaDomain piDomain sigmaEvidence piEvidence atomicRoot domainRoot
      hbase hatomic hdomain hglobalRoots)
    as (evidenceWitnessList & evidenceContext & hevidenceWitnessed &
      hbaseEvidenceIncluded & hsynchronized).
  destruct hsynchronized as
    [(transportedAtomicRoot & htransportedAtomic)
      (transportedDomainRoot & htransportedDomain)
      (sigmaRoot & hsigma) (piRoot & hpi)].
  destruct
    (raw_dynamicTruthPredecessorStateLogicalRootsAt_of_direct_evidence_atomic_and_domain
      M hPA translation hagreement evidenceWitnessList evidenceContext
      sigmaDomain piDomain sigmaEvidence piEvidence transportedAtomicRoot
      transportedDomainRoot sigmaRoot piRoot hevidenceWitnessed
      htransportedAtomic htransportedDomain hsigma hpi)
    as (targetWitnessList & targetContext & htargetWitnessed &
      hevidenceTargetIncluded & hlogicalRoots).
  exists targetWitnessList, targetContext.
  split; [exact htargetWitnessed |].
  split.
  - intros member hmember.
    exact (hevidenceTargetIncluded member
      (hbaseEvidenceIncluded member hmember)).
  - exact hlogicalRoots.
Qed.

End
  PABoundedRawCodedDynamicTruthPredecessorDirectEvidenceLogicalRoots.
