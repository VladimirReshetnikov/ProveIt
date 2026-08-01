(**
  Synchronize predecessor atomic/domain leaves with growing global roots.

  Global traversal may select a finite PA-witness extension after arithmetic
  endpoint compilation has already produced atomic adequacy and the domain
  disjunction.  This module performs the common witnessed-tail transport
  once and returns all four roots in one exact predecessor-state context.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedContextLists
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedDynamicTruthLocalAdmissibilityCompilation
  RawCodedDynamicTruthPredecessorStateExclusivityCompilation
  RawCodedDynamicTruthPredecessorGlobalExistentialElimination.

Module
  PABoundedRawCodedDynamicTruthPredecessorAtomicDomainGlobalRootsSynchronization.

Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedDynamicTruthLocalAdmissibilityCompilation.
Import
  PABoundedRawCodedDynamicTruthPredecessorStateExclusivityCompilation.
Import
  PABoundedRawCodedDynamicTruthPredecessorGlobalExistentialElimination.

(** Four synchronized proof families, kept generic in both domain and global
    conclusion codes so positive and rank-zero clients share the package. *)
Record RawDynamicTruthPredecessorAtomicDomainGlobalRootsAt
    (M : RawPAModel) (baseContext sigmaDomain piDomain
      sigmaGlobal piGlobal : M) : Prop := {
  rawDynamicTruthPredecessorAtomicDomainGlobal_atomic : exists root,
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M baseContext)
      (rawDynamicTruthLocalAtomicAdequacyCode M) root;
  rawDynamicTruthPredecessorAtomicDomainGlobal_domain : exists root,
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M baseContext)
      (rawFormulaOrCode M sigmaDomain piDomain) root;
  rawDynamicTruthPredecessorAtomicDomainGlobal_sigma : exists root,
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M baseContext)
      sigmaGlobal root;
  rawDynamicTruthPredecessorAtomicDomainGlobal_pi : exists root,
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M baseContext)
      piGlobal root
}.

Arguments RawDynamicTruthPredecessorAtomicDomainGlobalRootsAt
  M baseContext sigmaDomain piDomain sigmaGlobal piGlobal : clear implicits.

(** Move the two already-compiled arithmetic leaves to the witnessed context
    selected by global traversal.  The translation is arbitrary up to PA
    agreement because it is used only to identify the fixed state prefix. *)
Theorem
    raw_dynamicTruthPredecessorAtomicDomainGlobalRootsAt_of_growing_global_roots :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext sigmaDomain piDomain
      sigmaGlobal piGlobal atomicRoot domainRoot,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthPredecessorJointStateContext M baseContext)
    (rawDynamicTruthLocalAtomicAdequacyCode M) atomicRoot ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthPredecessorJointStateContext M baseContext)
    (rawFormulaOrCode M sigmaDomain piDomain) domainRoot ->
  RawDynamicTruthPredecessorGlobalRootsOnWitnessedExtensionFrom M
    baseContext sigmaGlobal piGlobal ->
  exists targetWitnessList targetContext,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawDynamicTruthPredecessorAtomicDomainGlobalRootsAt M targetContext
      sigmaDomain piDomain sigmaGlobal piGlobal.
Proof.
  intros M hPA translation hagreement baseWitnessList baseContext
    sigmaDomain piDomain sigmaGlobal piGlobal atomicRoot domainRoot
    hbase hatomic hdomain
    (targetWitnessList & targetContext & htarget & hincluded & hglobals).
  destruct hglobals as
    [(sigmaGlobalRoot & hsigmaGlobal) (piGlobalRoot & hpiGlobal)].

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
      targetWitnessList targetContext
      coqDynamicTruthPredecessorStateTemplateContext
      (rawDynamicTruthLocalAtomicAdequacyCode M) atomicRoot
      hbase htarget hincluded hatomicTemplate)
    as [transportedAtomicRoot htransportedAtomicTemplate].

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
      targetWitnessList targetContext
      coqDynamicTruthPredecessorStateTemplateContext
      (rawFormulaOrCode M sigmaDomain piDomain) domainRoot
      hbase htarget hincluded hdomainTemplate)
    as [transportedDomainRoot htransportedDomainTemplate].

  assert (htransportedAtomic : RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M targetContext)
      (rawDynamicTruthLocalAtomicAdequacyCode M) transportedAtomicRoot).
  {
    rewrite <- (raw_dynamicTruthPredecessorStateTemplateContextCode
      M translation hagreement targetContext).
    exact htransportedAtomicTemplate.
  }
  assert (htransportedDomain : RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M targetContext)
      (rawFormulaOrCode M sigmaDomain piDomain) transportedDomainRoot).
  {
    rewrite <- (raw_dynamicTruthPredecessorStateTemplateContextCode
      M translation hagreement targetContext).
    exact htransportedDomainTemplate.
  }

  exists targetWitnessList, targetContext.
  split; [exact htarget |].
  split; [exact hincluded |].
  constructor.
  - exists transportedAtomicRoot. exact htransportedAtomic.
  - exists transportedDomainRoot. exact htransportedDomain.
  - exists sigmaGlobalRoot. exact hsigmaGlobal.
  - exists piGlobalRoot. exact hpiGlobal.
Qed.

End
  PABoundedRawCodedDynamicTruthPredecessorAtomicDomainGlobalRootsSynchronization.
