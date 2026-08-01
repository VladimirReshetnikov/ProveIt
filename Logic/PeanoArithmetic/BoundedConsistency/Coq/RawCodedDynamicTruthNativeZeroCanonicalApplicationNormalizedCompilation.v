(**
  Canonical application-root boundary for the normalized rank-zero callback.

  Normalization retains the represented local resources and the complete
  canonical trace.  A proof-producing traversal may extend the witnessed PA
  tail while compiling the two first-successor applications.  This module
  states that exact residual and shows that it is sufficient for the older
  native direct-evidence callback by composing the reusable predecessor-state
  transport.
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
  RawCodedTemplatePAEmbedding
  RawCodedDynamicTruthLocalAdmissibilityCompilation
  RawCodedDynamicTruthPredecessorStateExclusivityCompilation
  RawCodedDynamicTruthNativeZeroPredecessorLogicalRootsCompilation
  RawCodedDynamicTruthNativeZeroCanonicalTraceExactification
  RawCodedDynamicTruthNativeZeroCanonicalApplicationDirectEvidence.

Module
  PABoundedRawCodedDynamicTruthNativeZeroCanonicalApplicationNormalizedCompilation.

Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedDynamicTruthLocalAdmissibilityCompilation.
Import
  PABoundedRawCodedDynamicTruthPredecessorStateExclusivityCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeZeroPredecessorLogicalRootsCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeZeroCanonicalTraceExactification.
Import
  PABoundedRawCodedDynamicTruthNativeZeroCanonicalApplicationDirectEvidence.

(** Producer-facing split of the canonical application package.  Arithmetic
    endpoint compilation may first choose a witnessed context carrying
    atomic adequacy and the domain disjunction.  Global traversal is then
    allowed to grow once more while returning the two canonical applications
    through the standard growing-pair interface. *)
Definition
    RawDynamicTruthNativeLocalZeroGrowingCanonicalGlobalApplicationResourcesCompilerOnCanonicalNormalizedResources
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M) : Prop :=
  forall (tail : nat -> M) witnessList baseContext (helperRoots : list M)
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalZeroNormalizedResourcesAt M translation
      witnessList baseContext helperRoots ->
    RawDynamicTruthNativeLocalZeroCanonicalFullTraceAt M tail
      sigmaDomain piDomain sigmaEvidence piEvidence ->
    exists endpointWitnessList endpointContext atomicRoot domainRoot,
      RawCodedPAAxiomWitnessContext M endpointWitnessList endpointContext /\
      RawContextListIncluded M baseContext endpointContext /\
      RawCodedPALocalProofOf M
        (rawDynamicTruthPredecessorJointStateContext M endpointContext)
        (rawDynamicTruthLocalAtomicAdequacyCode M) atomicRoot /\
      RawCodedPALocalProofOf M
        (rawDynamicTruthPredecessorJointStateContext M endpointContext)
        (rawFormulaOrCode M
          (rawDynamicTruthZeroSigmaDomainCode M)
          (rawDynamicTruthZeroPiDomainCode M)) domainRoot /\
      RawDynamicTruthPredecessorGlobalRootsOnWitnessedExtensionFrom M
        endpointContext
        (rawQuotedFormulaCode M
          dynamicTruthZeroInputGlobalSigmaApplicationFormula)
        (rawQuotedFormulaCode M
          dynamicTruthZeroInputGlobalPiApplicationFormula).

Arguments
  RawDynamicTruthNativeLocalZeroGrowingCanonicalGlobalApplicationResourcesCompilerOnCanonicalNormalizedResources
  M translation : clear implicits.

(** Exact proof-producing residue after rank-zero normalization.  The output
    may grow the witnessed tail and concludes canonical applications, not
    native truth evidence.  Atomic adequacy and the domain disjunction travel
    with those applications so the subsequent evidence handoff is closed. *)
Definition
    RawDynamicTruthNativeLocalZeroGrowingCanonicalApplicationRootsCompilerOnCanonicalNormalizedResources
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M) : Prop :=
  forall (tail : nat -> M) witnessList baseContext (helperRoots : list M)
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalZeroNormalizedResourcesAt M translation
      witnessList baseContext helperRoots ->
    RawDynamicTruthNativeLocalZeroCanonicalFullTraceAt M tail
      sigmaDomain piDomain sigmaEvidence piEvidence ->
    exists applicationWitnessList applicationContext,
      RawCodedPAAxiomWitnessContext M
        applicationWitnessList applicationContext /\
      RawContextListIncluded M baseContext applicationContext /\
      RawDynamicTruthZeroCanonicalApplicationRootsAt M applicationContext.

Arguments
  RawDynamicTruthNativeLocalZeroGrowingCanonicalApplicationRootsCompilerOnCanonicalNormalizedResources
  M translation : clear implicits.

(** Synchronize the split producer resources into the compact four-root
    application package.  Both possible context-growth steps are retained
    and their inclusions are composed, rather than requiring contraction to
    the normalized callback base. *)
Theorem
    raw_dynamicTruthNativeLocalZeroGrowingCanonicalApplicationRootsCompilerOnCanonicalNormalizedResources_of_global_application_resources
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  RawDynamicTruthNativeLocalZeroGrowingCanonicalGlobalApplicationResourcesCompilerOnCanonicalNormalizedResources
    M translation ->
  RawDynamicTruthNativeLocalZeroGrowingCanonicalApplicationRootsCompilerOnCanonicalNormalizedResources
    M translation.
Proof.
  intros M hPA translation hagreement hcompiler tail witnessList
    baseContext helperRoots sigmaDomain piDomain sigmaEvidence piEvidence
    hresources htrace.
  destruct
    (hcompiler tail witnessList baseContext helperRoots
      sigmaDomain piDomain sigmaEvidence piEvidence hresources htrace)
    as (endpointWitnessList & endpointContext & atomicRoot & domainRoot &
      hendpointWitnessed & hbaseEndpointIncluded & hatomic & hdomain &
      hglobals).
  destruct
    (raw_dynamicTruthZeroCanonicalApplicationRootsAt_of_growing_global_roots
      M hPA translation hagreement endpointWitnessList endpointContext
      atomicRoot domainRoot hendpointWitnessed hatomic hdomain hglobals)
    as (applicationWitnessList & applicationContext &
      happlicationWitnessed & hendpointApplicationIncluded &
      happlications).
  exists applicationWitnessList, applicationContext.
  split; [exact happlicationWitnessed |].
  split.
  - intros member hmember.
    exact (hendpointApplicationIncluded member
      (hbaseEndpointIncluded member hmember)).
  - exact happlications.
Qed.

(** Canonical application production suffices for native direct evidence.
    The two possible context extensions are composed explicitly, keeping the
    residual compiler free to select whatever finite PA witness prefix its
    traversal needs. *)
Theorem
    raw_dynamicTruthNativeLocalZeroGrowingDirectEvidenceCompilerOnCanonicalNormalizedResources_of_canonicalApplicationRoots
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  RawDynamicTruthNativeLocalZeroGrowingCanonicalApplicationRootsCompilerOnCanonicalNormalizedResources
    M translation ->
  RawDynamicTruthNativeLocalZeroGrowingDirectEvidenceCompilerOnCanonicalNormalizedResources
    M translation.
Proof.
  intros M hPA translation hagreement hcompiler tail witnessList
    baseContext helperRoots sigmaDomain piDomain sigmaEvidence piEvidence
    hresources htrace.
  destruct
    (hcompiler tail witnessList baseContext helperRoots
      sigmaDomain piDomain sigmaEvidence piEvidence hresources htrace)
    as (applicationWitnessList & applicationContext &
      happlicationWitnessed & hbaseApplicationIncluded & happlications).
  destruct
    (raw_dynamicTruthZeroDirectEvidenceRoots_of_canonicalApplicationRoots
      M hPA translation hagreement applicationWitnessList applicationContext
      happlicationWitnessed happlications)
    as (evidenceWitnessList & evidenceContext & hevidenceWitnessed &
      happlicationEvidenceIncluded & hevidence).
  exists evidenceWitnessList, evidenceContext.
  split; [exact hevidenceWitnessed |].
  split.
  - intros member hmember.
    exact (happlicationEvidenceIncluded member
      (hbaseApplicationIncluded member hmember)).
  - exact hevidence.
Qed.

End
  PABoundedRawCodedDynamicTruthNativeZeroCanonicalApplicationNormalizedCompilation.
