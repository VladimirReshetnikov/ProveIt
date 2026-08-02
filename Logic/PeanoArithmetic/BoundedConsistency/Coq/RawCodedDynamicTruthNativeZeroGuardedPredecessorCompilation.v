(**
  Guarded predecessor compilation at the normalized rank-zero boundary.

  The guarded implication theorem needs five roots in its real branch after
  the predecessor and constructor binders have been introduced.  This file
  packages those exact roots, closes the guarded predecessor formula, and
  exposes the remaining traversal producer as one sharply typed interface.
  Fixed helper compilation and zero-field normalization are no longer part
  of that residual.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedContextLists
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedTemplatePAEmbedding
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateFormulaAtomicAdequacy
  RawCodedTemplateBottomDirectStructuralInputs
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthLocalExclusiveTemplateDirectInputs
  RawCodedDynamicTruthImpDirectChildAdmissibilityProofCompilation
  RawCodedDynamicTruthImpGuardedBranchExclusivity
  RawCodedDynamicTruthLocalCollisionMatrixAssembly
  RawCodedDynamicTruthImpGuardedPredecessorExclusivityCompilation
  RawCodedDynamicTruthNativeZeroPredecessorLogicalRootsCompilation
  RawCodedDynamicTruthNativeZeroGuardedNormalization.

Import ListNotations.

Module
  PABoundedRawCodedDynamicTruthNativeZeroGuardedPredecessorCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateFormulaAtomicAdequacy.
Import PABoundedRawCodedTemplateBottomDirectStructuralInputs.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedDynamicTruthLocalExclusiveTemplateDirectInputs.
Import
  PABoundedRawCodedDynamicTruthImpDirectChildAdmissibilityProofCompilation.
Import PABoundedRawCodedDynamicTruthImpGuardedBranchExclusivity.
Import PABoundedRawCodedDynamicTruthLocalCollisionMatrixAssembly.
Import
  PABoundedRawCodedDynamicTruthImpGuardedPredecessorExclusivityCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeZeroPredecessorLogicalRootsCompilation.
Import PABoundedRawCodedDynamicTruthNativeZeroGuardedNormalization.

(** Local direct-translation adequacy avoids importing the substantially
    stronger global-row compiler merely for this elementary consequence of
    the translation contract. *)
Lemma raw_guardedDirectStructuralTemplatePrefix_atomically_adequate : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M) prefix,
  RawCodedTemplatePrefixAtomicallyAdequate M
    (rawDirectStructuralTemplateTranslation M hPA inputs) prefix.
Proof.
  intros M hPA inputs prefix formula _.
  exact (raw_codedTemplateFormula_atomically_adequate_core M hPA
    (rawDirectStructuralTemplateTranslation M hPA inputs) formula).
Qed.

(** All five roots inhabit the same deepest branch context.  Existential
    root codes stay in [Prop], so the interface commits to no computational
    choice and can be transported or merged by ordinary witnessed-context
    machinery. *)
Record RawDynamicTruthImpGuardedBranchRootsAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (baseContext : M) (callerPrefix : TemplateContext) : Prop := {
  rawDynamicTruthImpGuardedBranch_source : exists sourceRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqDynamicTruthImpGuardedDeepPrefix callerPrefix))
      (rawTemplateFormula translation
        (tfAll (tfAll (tfAll
          coqDynamicTruthLocalExclusiveBodyTemplate)))) sourceRoot;
  rawDynamicTruthImpGuardedBranch_parentAtomic : exists atomicRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqDynamicTruthImpGuardedDeepPrefix callerPrefix))
      (rawTemplateFormula translation
        (coqDynamicTruthImpDirectChildAtomicPremiseTemplate
          coqDynamicTruthImpGuardedLevelTerm
          coqDynamicTruthImpGuardedParentTerm
          coqDynamicTruthImpGuardedLeftTerm
          coqDynamicTruthImpGuardedRightTerm
          coqDynamicTruthImpGuardedChildTerm)) atomicRoot;
  rawDynamicTruthImpGuardedBranch_parentDomain : exists domainRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqDynamicTruthImpGuardedDeepPrefix callerPrefix))
      (rawTemplateFormula translation
        (coqDynamicTruthImpDirectChildDomainPremiseTemplate
          coqDynamicTruthImpGuardedLevelTerm
          coqDynamicTruthImpGuardedParentTerm
          coqDynamicTruthImpGuardedLeftTerm
          coqDynamicTruthImpGuardedRightTerm
          coqDynamicTruthImpGuardedChildTerm)) domainRoot;
  rawDynamicTruthImpGuardedBranch_sigmaEvidence : exists sigmaRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqDynamicTruthImpGuardedDeepPrefix callerPrefix))
      (rawTemplateFormula translation
        coqDynamicTruthImpGuardedLocalSigmaEvidenceTemplate) sigmaRoot;
  rawDynamicTruthImpGuardedBranch_piEvidence : exists piRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqDynamicTruthImpGuardedDeepPrefix callerPrefix))
      (rawTemplateFormula translation
        coqDynamicTruthImpGuardedLocalPiEvidenceTemplate) piRoot
}.

Arguments RawDynamicTruthImpGuardedBranchRootsAt
  M translation baseContext callerPrefix : clear implicits.

(** General closure adapter.  It is independent of rank zero and accepts any
    agreeing translation whose concrete deep prefix is atomically adequate. *)
Theorem
    raw_dynamicTruthImpGuardedPredecessorRoot_on_witnessed_extension_of_branch_roots :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      translation baseWitnessList baseContext callerPrefix,
  RawCodedTemplatePAAgreement M translation ->
  RawCodedTemplatePrefixAtomicallyAdequate M translation
    (coqDynamicTruthImpGuardedDeepPrefix callerPrefix) ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawDynamicTruthImpGuardedBranchRootsAt M translation
    baseContext callerPrefix ->
  exists targetWitnessList targetContext predecessorRoot,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation targetContext callerPrefix)
      (rawDynamicTruthImpGuardedPredecessorStateExclusivityCode M)
      predecessorRoot.
Proof.
  intros M hPA translation baseWitnessList baseContext callerPrefix
    hagreement hadequate hbase hroots.
  destruct hroots as
    [(sourceRoot & hsource) (atomicRoot & hatomic)
      (domainRoot & hdomain) (sigmaRoot & hsigma) (piRoot & hpi)].
  exact
    (raw_dynamicTruthImpGuardedPredecessorStateExclusivityRoot_of_branch_roots_under_template_prefix
      M hPA translation hagreement baseWitnessList baseContext callerPrefix
      sourceRoot atomicRoot domainRoot sigmaRoot piRoot
      hadequate hbase hsource hatomic hdomain hsigma hpi).
Qed.

(** The only remaining normalized rank-zero producer: select the five branch
    roots on one witnessed extension.  The helper cells and all normalized
    local data are already carried by [resources]. *)
Definition
    RawDynamicTruthNativeLocalZeroGrowingGuardedBranchRootsCompilerOnNormalizedResources
    (M : RawPAModel) (hPA : RawPASatisfies M) : Prop :=
  forall (tail : nat -> M) witnessList baseContext (helperRoots : list M)
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalZeroGuardedNormalizedResourcesAt M
      (rawBottomDirectStructuralTemplateTranslation M hPA)
      witnessList baseContext helperRoots ->
    RawDynamicTruthNativeLocalZeroCanonicalFullTraceAt M tail
      sigmaDomain piDomain sigmaEvidence piEvidence ->
    exists branchWitnessList branchContext,
      RawCodedPAAxiomWitnessContext M branchWitnessList branchContext /\
      RawContextListIncluded M baseContext branchContext /\
      RawDynamicTruthImpGuardedBranchRootsAt M
        (rawBottomDirectStructuralTemplateTranslation M hPA)
        branchContext [].

Arguments
  RawDynamicTruthNativeLocalZeroGrowingGuardedBranchRootsCompilerOnNormalizedResources
  M hPA : clear implicits.

Definition
    RawDynamicTruthNativeLocalZeroGrowingGuardedPredecessorRootCompilerOnNormalizedResources
    (M : RawPAModel) (hPA : RawPASatisfies M) : Prop :=
  forall (tail : nat -> M) witnessList baseContext (helperRoots : list M)
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalZeroGuardedNormalizedResourcesAt M
      (rawBottomDirectStructuralTemplateTranslation M hPA)
      witnessList baseContext helperRoots ->
    RawDynamicTruthNativeLocalZeroCanonicalFullTraceAt M tail
      sigmaDomain piDomain sigmaEvidence piEvidence ->
    exists targetWitnessList targetContext,
      RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
      RawContextListIncluded M baseContext targetContext /\
      RawDynamicTruthLocalRootAt M targetContext
        (rawDynamicTruthImpGuardedPredecessorStateExclusivityCode M).

Arguments
  RawDynamicTruthNativeLocalZeroGrowingGuardedPredecessorRootCompilerOnNormalizedResources
  M hPA : clear implicits.

(** Close the guarded predecessor and compose the producer's context growth
    with the finite PA extension selected by child-admissibility compilation. *)
Theorem
    raw_dynamicTruthNativeLocalZeroGrowingGuardedPredecessorRootCompilerOnNormalizedResources_of_branch_roots :
    forall (M : RawPAModel) (hPA : RawPASatisfies M),
  RawDynamicTruthNativeLocalZeroGrowingGuardedBranchRootsCompilerOnNormalizedResources
    M hPA ->
  RawDynamicTruthNativeLocalZeroGrowingGuardedPredecessorRootCompilerOnNormalizedResources
    M hPA.
Proof.
  intros M hPA hcompiler tail witnessList baseContext helperRoots
    sigmaDomain piDomain sigmaEvidence piEvidence hresources htrace.
  destruct (hcompiler tail witnessList baseContext helperRoots
    sigmaDomain piDomain sigmaEvidence piEvidence hresources htrace) as
    (branchWitnessList & branchContext & hbranchWitnessed &
      hbaseBranchIncluded & hbranchRoots).
  destruct
    (raw_dynamicTruthImpGuardedPredecessorRoot_on_witnessed_extension_of_branch_roots
      M hPA (rawBottomDirectStructuralTemplateTranslation M hPA)
      branchWitnessList branchContext []
      (rawBottomDirectStructuralTemplatePAAgreement M hPA)
      (raw_guardedDirectStructuralTemplatePrefix_atomically_adequate M hPA
        (rawBottomTemplateDirectStructuralInputs M hPA)
        (coqDynamicTruthImpGuardedDeepPrefix []))
      hbranchWitnessed hbranchRoots) as
    (targetWitnessList & targetContext & predecessorRoot &
      htargetWitnessed & hbranchTargetIncluded & hpredecessor).
  exists targetWitnessList, targetContext.
  split; [exact htargetWitnessed |].
  split.
  - intros member hmember.
    exact (hbranchTargetIncluded member
      (hbaseBranchIncluded member hmember)).
  - exists predecessorRoot.
    cbn [rawTemplateContextCodeOnTail].
    exact hpredecessor.
Qed.

End
  PABoundedRawCodedDynamicTruthNativeZeroGuardedPredecessorCompilation.
