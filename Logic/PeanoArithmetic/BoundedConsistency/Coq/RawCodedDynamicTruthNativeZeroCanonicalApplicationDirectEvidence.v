(**
  Turn canonical rank-zero application roots into direct predecessor evidence.

  The generic application transport works below an arbitrary adequate
  template prefix.  Here that prefix is instantiated with the two literal
  predecessor-state assumptions.  Atomic adequacy and the rank-domain root
  are transported along the same witnessed-tail inclusion, so all four
  direct-evidence leaves end in one exact joint-state context.

  The main theorem remains polymorphic in the structural translation: PA
  agreement alone identifies the prefix and supplies its atomic adequacy.
  The bottom direct translation is exposed only as a convenient corollary.
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
  RawCodedTemplateBottomDirectStructuralInputs
  RawCodedDynamicTruthLocalAdmissibilityCompilation
  RawCodedDynamicTruthPredecessorStateExclusivityCompilation
  RawCodedDynamicTruthPredecessorGlobalExistentialElimination
  RawCodedDynamicTruthPredecessorAdmissibilityAssignmentCompilation
  RawCodedDynamicTruthPredecessorAtomicDomainGlobalRootsSynchronization
  RawCodedDynamicTruthZeroLocalExclusiveTemplateIdentification
  RawCodedDynamicTruthNativeZeroPredecessorLogicalRootsCompilation
  RawCodedDynamicTruthNativeZeroCanonicalTraceExactification
  RawCodedDynamicTruthNativeZeroCanonicalApplicationProofTransport.

Module
  PABoundedRawCodedDynamicTruthNativeZeroCanonicalApplicationDirectEvidence.

Import PA.
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
Import PABoundedRawCodedTemplateBottomDirectStructuralInputs.
Import PABoundedRawCodedDynamicTruthLocalAdmissibilityCompilation.
Import
  PABoundedRawCodedDynamicTruthPredecessorStateExclusivityCompilation.
Import
  PABoundedRawCodedDynamicTruthPredecessorGlobalExistentialElimination.
Import
  PABoundedRawCodedDynamicTruthPredecessorAdmissibilityAssignmentCompilation.
Import
  PABoundedRawCodedDynamicTruthPredecessorAtomicDomainGlobalRootsSynchronization.
Import
  PABoundedRawCodedDynamicTruthZeroLocalExclusiveTemplateIdentification.
Import
  PABoundedRawCodedDynamicTruthNativeZeroPredecessorLogicalRootsCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeZeroCanonicalTraceExactification.
Import
  PABoundedRawCodedDynamicTruthNativeZeroCanonicalApplicationProofTransport.

(** The exact four roots available immediately after a canonical first-step
    traversal.  In contrast with the native direct-evidence package, the two
    polarity fields still conclude the canonical application formulas. *)
Record RawDynamicTruthZeroCanonicalApplicationRootsAt
    (M : RawPAModel) (baseContext : M) : Prop := {
  rawDynamicTruthZeroCanonicalApplicationRoots_atomic : exists root,
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M baseContext)
      (rawDynamicTruthLocalAtomicAdequacyCode M) root;
  rawDynamicTruthZeroCanonicalApplicationRoots_domain : exists root,
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M baseContext)
      (rawFormulaOrCode M
        (rawDynamicTruthZeroSigmaDomainCode M)
        (rawDynamicTruthZeroPiDomainCode M)) root;
  rawDynamicTruthZeroCanonicalApplicationRoots_sigma : exists root,
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M baseContext)
      (rawQuotedFormulaCode M
        dynamicTruthZeroInputGlobalSigmaApplicationFormula) root;
  rawDynamicTruthZeroCanonicalApplicationRoots_pi : exists root,
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M baseContext)
      (rawQuotedFormulaCode M
        dynamicTruthZeroInputGlobalPiApplicationFormula) root
}.

Arguments RawDynamicTruthZeroCanonicalApplicationRootsAt M baseContext
  : clear implicits.

(** Existing growing-global traversal clients can stop at their native pair
    package.  The generic synchronization lemma moves the arithmetic leaves
    to the traversal-selected context; literal canonical conclusion codes
    then give the application record without further proof construction. *)
Theorem
    raw_dynamicTruthZeroCanonicalApplicationRootsAt_of_growing_global_roots :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext atomicRoot domainRoot,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthPredecessorJointStateContext M baseContext)
    (rawDynamicTruthLocalAtomicAdequacyCode M) atomicRoot ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthPredecessorJointStateContext M baseContext)
    (rawFormulaOrCode M
      (rawDynamicTruthZeroSigmaDomainCode M)
      (rawDynamicTruthZeroPiDomainCode M)) domainRoot ->
  RawDynamicTruthPredecessorGlobalRootsOnWitnessedExtensionFrom M
    baseContext
    (rawQuotedFormulaCode M
      dynamicTruthZeroInputGlobalSigmaApplicationFormula)
    (rawQuotedFormulaCode M
      dynamicTruthZeroInputGlobalPiApplicationFormula) ->
  exists targetWitnessList targetContext,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawDynamicTruthZeroCanonicalApplicationRootsAt M targetContext.
Proof.
  intros M hPA translation hagreement baseWitnessList baseContext
    atomicRoot domainRoot hbase hatomic hdomain hglobals.
  destruct
    (raw_dynamicTruthPredecessorAtomicDomainGlobalRootsAt_of_growing_global_roots
      M hPA translation hagreement baseWitnessList baseContext
      (rawDynamicTruthZeroSigmaDomainCode M)
      (rawDynamicTruthZeroPiDomainCode M)
      (rawQuotedFormulaCode M
        dynamicTruthZeroInputGlobalSigmaApplicationFormula)
      (rawQuotedFormulaCode M
        dynamicTruthZeroInputGlobalPiApplicationFormula)
      atomicRoot domainRoot hbase hatomic hdomain hglobals)
    as (targetWitnessList & targetContext & htarget & hincluded & hroots).
  destruct hroots as [hatomic' hdomain' hsigma hpi].
  exists targetWitnessList, targetContext.
  split; [exact htarget |].
  split; [exact hincluded |].
  constructor; assumption.
Qed.

(** Convert the canonical applications while preserving the two structural
    leaves.  Every source root is transported to the one witnessed context
    selected by the application-to-evidence theorem; no context equality or
    proof-root coincidence is assumed. *)
Theorem
    raw_dynamicTruthZeroDirectEvidenceRoots_of_canonicalApplicationRoots :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall sourceWitnessList sourceContext,
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawDynamicTruthZeroCanonicalApplicationRootsAt M sourceContext ->
  exists targetWitnessList targetContext,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M sourceContext targetContext /\
    RawDynamicTruthZeroDirectEvidenceRootsAt M targetContext.
Proof.
  intros M hPA translation hagreement sourceWitnessList sourceContext
    hsource hroots.
  destruct hroots as
    [(atomicRoot & hatomic) (domainRoot & hdomain)
      (sigmaApplicationRoot & hsigmaApplication)
      (piApplicationRoot & hpiApplication)].

  assert (hsigmaApplicationTemplate : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation sourceContext
        coqDynamicTruthPredecessorStateTemplateContext)
      (rawQuotedFormulaCode M
        dynamicTruthZeroInputGlobalSigmaApplicationFormula)
      sigmaApplicationRoot).
  {
    rewrite (raw_dynamicTruthPredecessorStateTemplateContextCode
      M translation hagreement sourceContext).
    exact hsigmaApplication.
  }
  assert (hpiApplicationTemplate : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation sourceContext
        coqDynamicTruthPredecessorStateTemplateContext)
      (rawQuotedFormulaCode M
        dynamicTruthZeroInputGlobalPiApplicationFormula)
      piApplicationRoot).
  {
    rewrite (raw_dynamicTruthPredecessorStateTemplateContextCode
      M translation hagreement sourceContext).
    exact hpiApplication.
  }
  destruct
    (raw_dynamicTruthZeroNativeEvidenceRoots_of_canonicalApplicationRoots_under_prefix
      M hPA translation hagreement sourceWitnessList sourceContext
      coqDynamicTruthPredecessorStateTemplateContext
      sigmaApplicationRoot piApplicationRoot
      (raw_dynamicTruthPredecessorStateTemplateContext_atomically_adequate
        M hPA translation hagreement)
      hsource hsigmaApplicationTemplate hpiApplicationTemplate)
    as (targetWitnessList & targetContext & sigmaEvidenceRoot &
      piEvidenceRoot & htarget & hincluded & hsigmaEvidenceTemplate &
      hpiEvidenceTemplate).

  (** The two non-polarity roots follow the same tail inclusion under the
      same state prefix. *)
  assert (hatomicTemplate : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation sourceContext
        coqDynamicTruthPredecessorStateTemplateContext)
      (rawDynamicTruthLocalAtomicAdequacyCode M) atomicRoot).
  {
    rewrite (raw_dynamicTruthPredecessorStateTemplateContextCode
      M translation hagreement sourceContext).
    exact hatomic.
  }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation sourceWitnessList sourceContext
      targetWitnessList targetContext
      coqDynamicTruthPredecessorStateTemplateContext
      (rawDynamicTruthLocalAtomicAdequacyCode M) atomicRoot
      hsource htarget hincluded hatomicTemplate)
    as [transportedAtomicRoot htransportedAtomicTemplate].

  assert (hdomainTemplate : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation sourceContext
        coqDynamicTruthPredecessorStateTemplateContext)
      (rawFormulaOrCode M
        (rawDynamicTruthZeroSigmaDomainCode M)
        (rawDynamicTruthZeroPiDomainCode M)) domainRoot).
  {
    rewrite (raw_dynamicTruthPredecessorStateTemplateContextCode
      M translation hagreement sourceContext).
    exact hdomain.
  }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation sourceWitnessList sourceContext
      targetWitnessList targetContext
      coqDynamicTruthPredecessorStateTemplateContext
      (rawFormulaOrCode M
        (rawDynamicTruthZeroSigmaDomainCode M)
        (rawDynamicTruthZeroPiDomainCode M)) domainRoot
      hsource htarget hincluded hdomainTemplate)
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
      (rawFormulaOrCode M
        (rawDynamicTruthZeroSigmaDomainCode M)
        (rawDynamicTruthZeroPiDomainCode M)) transportedDomainRoot).
  {
    rewrite <- (raw_dynamicTruthPredecessorStateTemplateContextCode
      M translation hagreement targetContext).
    exact htransportedDomainTemplate.
  }
  assert (hsigmaEvidence : RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M targetContext)
      (rawDynamicTruthZeroSigmaEvidenceCode M) sigmaEvidenceRoot).
  {
    unfold rawDynamicTruthZeroSigmaEvidenceCode.
    rewrite <- (raw_dynamicTruthPredecessorStateTemplateContextCode
      M translation hagreement targetContext).
    exact hsigmaEvidenceTemplate.
  }
  assert (hpiEvidence : RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M targetContext)
      (rawDynamicTruthZeroPiEvidenceCode M) piEvidenceRoot).
  {
    unfold rawDynamicTruthZeroPiEvidenceCode.
    rewrite <- (raw_dynamicTruthPredecessorStateTemplateContextCode
      M translation hagreement targetContext).
    exact hpiEvidenceTemplate.
  }

  exists targetWitnessList, targetContext.
  split; [exact htarget |].
  split; [exact hincluded |].
  constructor.
  - exists transportedAtomicRoot. exact htransportedAtomic.
  - exists transportedDomainRoot. exact htransportedDomain.
  - exists sigmaEvidenceRoot. exact hsigmaEvidence.
  - exists piEvidenceRoot. exact hpiEvidence.
Qed.

(** Converse four-root conversion.  Rather than repeating the transport of
    the atomic and domain leaves, package the two backward implication
    results through the existing growing-global synchronization theorem. *)
Theorem
    raw_dynamicTruthZeroCanonicalApplicationRoots_of_directEvidenceRoots :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall sourceWitnessList sourceContext,
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawDynamicTruthZeroDirectEvidenceRootsAt M sourceContext ->
  exists targetWitnessList targetContext,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M sourceContext targetContext /\
    RawDynamicTruthZeroCanonicalApplicationRootsAt M targetContext.
Proof.
  intros M hPA translation hagreement sourceWitnessList sourceContext
    hsource hroots.
  destruct hroots as
    [(atomicRoot & hatomic) (domainRoot & hdomain)
      (sigmaEvidenceRoot & hsigmaEvidence)
      (piEvidenceRoot & hpiEvidence)].
  assert (hsigmaEvidenceTemplate : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation sourceContext
        coqDynamicTruthPredecessorStateTemplateContext)
      (rawQuotedFormulaCode M dynamicTruthZeroSigmaEvidenceFormula)
      sigmaEvidenceRoot).
  {
    unfold rawDynamicTruthZeroSigmaEvidenceCode in hsigmaEvidence.
    rewrite (raw_dynamicTruthPredecessorStateTemplateContextCode
      M translation hagreement sourceContext).
    exact hsigmaEvidence.
  }
  assert (hpiEvidenceTemplate : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation sourceContext
        coqDynamicTruthPredecessorStateTemplateContext)
      (rawQuotedFormulaCode M dynamicTruthZeroPiEvidenceFormula)
      piEvidenceRoot).
  {
    unfold rawDynamicTruthZeroPiEvidenceCode in hpiEvidence.
    rewrite (raw_dynamicTruthPredecessorStateTemplateContextCode
      M translation hagreement sourceContext).
    exact hpiEvidence.
  }
  destruct
    (raw_dynamicTruthZeroCanonicalApplicationRoots_of_nativeEvidenceRoots_under_prefix
      M hPA translation hagreement sourceWitnessList sourceContext
      coqDynamicTruthPredecessorStateTemplateContext
      sigmaEvidenceRoot piEvidenceRoot
      (raw_dynamicTruthPredecessorStateTemplateContext_atomically_adequate
        M hPA translation hagreement)
      hsource hsigmaEvidenceTemplate hpiEvidenceTemplate)
    as (applicationWitnessList & applicationContext &
      sigmaApplicationRoot & piApplicationRoot & happlicationWitnessed &
      hsourceApplicationIncluded & hsigmaApplicationTemplate &
      hpiApplicationTemplate).
  assert (hsigmaApplication : RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M applicationContext)
      (rawQuotedFormulaCode M
        dynamicTruthZeroInputGlobalSigmaApplicationFormula)
      sigmaApplicationRoot).
  {
    rewrite <- (raw_dynamicTruthPredecessorStateTemplateContextCode
      M translation hagreement applicationContext).
    exact hsigmaApplicationTemplate.
  }
  assert (hpiApplication : RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M applicationContext)
      (rawQuotedFormulaCode M
        dynamicTruthZeroInputGlobalPiApplicationFormula)
      piApplicationRoot).
  {
    rewrite <- (raw_dynamicTruthPredecessorStateTemplateContextCode
      M translation hagreement applicationContext).
    exact hpiApplicationTemplate.
  }
  assert (hglobals :
      RawDynamicTruthPredecessorGlobalRootsOnWitnessedExtensionFrom M
        sourceContext
        (rawQuotedFormulaCode M
          dynamicTruthZeroInputGlobalSigmaApplicationFormula)
        (rawQuotedFormulaCode M
          dynamicTruthZeroInputGlobalPiApplicationFormula)).
  {
    exists applicationWitnessList, applicationContext.
    split; [exact happlicationWitnessed |].
    split; [exact hsourceApplicationIncluded |].
    constructor.
    - exists sigmaApplicationRoot. exact hsigmaApplication.
    - exists piApplicationRoot. exact hpiApplication.
  }
  exact
    (raw_dynamicTruthZeroCanonicalApplicationRootsAt_of_growing_global_roots
      M hPA translation hagreement sourceWitnessList sourceContext
      atomicRoot domainRoot hsource hatomic hdomain hglobals).
Qed.

(** Closed specialization requiring no translation witness from callers. *)
Corollary
    raw_dynamicTruthZeroDirectEvidenceRoots_of_canonicalApplicationRoots_bottom :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      sourceWitnessList sourceContext,
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawDynamicTruthZeroCanonicalApplicationRootsAt M sourceContext ->
  exists targetWitnessList targetContext,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M sourceContext targetContext /\
    RawDynamicTruthZeroDirectEvidenceRootsAt M targetContext.
Proof.
  intros M hPA sourceWitnessList sourceContext hsource hroots.
  exact
    (raw_dynamicTruthZeroDirectEvidenceRoots_of_canonicalApplicationRoots
      M hPA (rawBottomDirectStructuralTemplateTranslation M hPA)
      (rawBottomDirectStructuralTemplatePAAgreement M hPA)
      sourceWitnessList sourceContext hsource hroots).
Qed.

Corollary
    raw_dynamicTruthZeroCanonicalApplicationRoots_of_directEvidenceRoots_bottom :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      sourceWitnessList sourceContext,
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawDynamicTruthZeroDirectEvidenceRootsAt M sourceContext ->
  exists targetWitnessList targetContext,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M sourceContext targetContext /\
    RawDynamicTruthZeroCanonicalApplicationRootsAt M targetContext.
Proof.
  intros M hPA sourceWitnessList sourceContext hsource hroots.
  exact
    (raw_dynamicTruthZeroCanonicalApplicationRoots_of_directEvidenceRoots
      M hPA (rawBottomDirectStructuralTemplateTranslation M hPA)
      (rawBottomDirectStructuralTemplatePAAgreement M hPA)
      sourceWitnessList sourceContext hsource hroots).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeZeroCanonicalApplicationDirectEvidence.
