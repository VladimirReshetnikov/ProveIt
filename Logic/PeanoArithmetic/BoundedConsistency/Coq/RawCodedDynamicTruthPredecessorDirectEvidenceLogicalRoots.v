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
  RawCodedPALocalProofExistential
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedDynamicTruthPredecessorGlobalExistentialElimination
  RawCodedDynamicTruthLocalAdmissibilityCompilation
  RawCodedDynamicTruthPredecessorStateExclusivityCompilation
  RawCodedDynamicTruthPredecessorAdmissibilityAssignmentCompilation.

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
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import
  PABoundedRawCodedDynamicTruthPredecessorGlobalExistentialElimination.
Import PABoundedRawCodedDynamicTruthLocalAdmissibilityCompilation.
Import
  PABoundedRawCodedDynamicTruthPredecessorStateExclusivityCompilation.
Import
  PABoundedRawCodedDynamicTruthPredecessorAdmissibilityAssignmentCompilation.

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
    hbase hatomic hdomain
    (evidenceWitnessList & evidenceContext & hevidenceWitnessed &
      hbaseEvidenceIncluded & hevidenceRoots).
  destruct hevidenceRoots as
    [[sigmaRoot hsigma] [piRoot hpi]].
  assert (hatomicTemplate : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        coqDynamicTruthPredecessorStateTemplateContext)
      (rawDynamicTruthLocalAtomicAdequacyCode M) atomicRoot).
  {
    rewrite (raw_dynamicTruthPredecessorStateTemplateContextCode
      M translation hagreement baseContext).
    exact hatomic.
  }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation baseWitnessList baseContext
      evidenceWitnessList evidenceContext
      coqDynamicTruthPredecessorStateTemplateContext
      (rawDynamicTruthLocalAtomicAdequacyCode M) atomicRoot
      hbase hevidenceWitnessed hbaseEvidenceIncluded hatomicTemplate)
    as [transportedAtomicRoot htransportedAtomic].
  assert (htransportedAtomicJoint : RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M evidenceContext)
      (rawDynamicTruthLocalAtomicAdequacyCode M)
      transportedAtomicRoot).
  {
    rewrite <- (raw_dynamicTruthPredecessorStateTemplateContextCode
      M translation hagreement evidenceContext).
    exact htransportedAtomic.
  }
  assert (hdomainTemplate : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        coqDynamicTruthPredecessorStateTemplateContext)
      (rawFormulaOrCode M sigmaDomain piDomain) domainRoot).
  {
    rewrite (raw_dynamicTruthPredecessorStateTemplateContextCode
      M translation hagreement baseContext).
    exact hdomain.
  }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation baseWitnessList baseContext
      evidenceWitnessList evidenceContext
      coqDynamicTruthPredecessorStateTemplateContext
      (rawFormulaOrCode M sigmaDomain piDomain) domainRoot
      hbase hevidenceWitnessed hbaseEvidenceIncluded hdomainTemplate)
    as [transportedDomainRoot htransportedDomain].
  assert (htransportedDomainJoint : RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M evidenceContext)
      (rawFormulaOrCode M sigmaDomain piDomain)
      transportedDomainRoot).
  {
    rewrite <- (raw_dynamicTruthPredecessorStateTemplateContextCode
      M translation hagreement evidenceContext).
    exact htransportedDomain.
  }
  destruct
    (raw_dynamicTruthPredecessorStateLogicalRootsAt_of_direct_evidence_atomic_and_domain
      M hPA translation hagreement evidenceWitnessList evidenceContext
      sigmaDomain piDomain sigmaEvidence piEvidence
      transportedAtomicRoot transportedDomainRoot sigmaRoot piRoot
      hevidenceWitnessed htransportedAtomicJoint htransportedDomainJoint
      hsigma hpi)
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
