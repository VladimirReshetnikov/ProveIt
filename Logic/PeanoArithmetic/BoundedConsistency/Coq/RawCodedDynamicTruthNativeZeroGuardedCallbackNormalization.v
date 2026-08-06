(**
  Recover the callback-shaped guarded rank-zero predecessor compiler.

  The guarded predecessor traversal is deliberately stated over normalized
  rank-zero resources.  The native local callback, however, starts with the
  complete current six-field package and the forty-two fixed helpers.  This
  module performs the structural conversion between those two boundaries:

  - construct the four predecessor-state projection roots on the witnessed
    callback context;
  - normalize the guarded helper package at level zero;
  - invert the ordinary local trace at zero and canonicalize its two global
    inputs; and
  - invoke the normalized guarded predecessor compiler.

  The result still proves the guarded predecessor formula.  In particular,
  it does not identify that formula with the stronger historical
  unconditional predecessor-exclusivity formula; the two formulas are
  syntactically distinct and require different local-matrix endpoints.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedContextLists
  RawCodedRestrictedPAProof
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTemplateBottomDirectStructuralInputs
  RawCodedDynamicTruthImpBranchExclusivity
  RawCodedDynamicTruthImpGuardedBranchExclusivity
  RawCodedDynamicTruthLocalCollisionMatrixAssembly
  RawCodedDynamicTruthPredecessorStateProjectionCompilation
  RawCodedDynamicTruthNativeLocalProofCompilation
  RawCodedDynamicTruthNativeLocalHelperBatchGeneralization
  RawCodedDynamicTruthNativeZeroPredecessorLogicalRootsCompilation
  RawCodedDynamicTruthNativeZeroGuardedNormalization
  RawCodedDynamicTruthNativeZeroGuardedPredecessorCompilation.

Module
  PABoundedRawCodedDynamicTruthNativeZeroGuardedCallbackNormalization.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateBottomDirectStructuralInputs.
Import PABoundedRawCodedDynamicTruthImpBranchExclusivity.
Import PABoundedRawCodedDynamicTruthImpGuardedBranchExclusivity.
Import PABoundedRawCodedDynamicTruthLocalCollisionMatrixAssembly.
Import PABoundedRawCodedDynamicTruthPredecessorStateProjectionCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalProofCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeLocalHelperBatchGeneralization.
Import
  PABoundedRawCodedDynamicTruthNativeZeroPredecessorLogicalRootsCompilation.
Import PABoundedRawCodedDynamicTruthNativeZeroGuardedNormalization.
Import
  PABoundedRawCodedDynamicTruthNativeZeroGuardedPredecessorCompilation.

(** The guarded formula retains two constructor witnesses and a direct-child
    premise underneath the three state binders.  Recording this elementary
    syntactic fact prevents a downstream adapter from silently rewriting a
    guarded root to the historical, strictly stronger formula. *)
Lemma dynamicTruthImpGuardedPredecessorStateExclusivityFormula_neq_legacy :
  dynamicTruthImpGuardedPredecessorStateExclusivityFormula <>
    dynamicTruthImpPredecessorStateExclusivityFormula.
Proof.
  unfold dynamicTruthImpGuardedPredecessorStateExclusivityFormula,
    dynamicTruthImpGuardedPredecessorStateExclusivityBodyFormula,
    dynamicTruthImpPredecessorStateExclusivityFormula.
  discriminate.
Qed.

(** Exact rank-zero interface available at a native callback invocation.
    It retains the corrected forty-two-helper context and returns the guarded
    predecessor root on a witnessed extension of that literal context. *)
Definition
    RawDynamicTruthNativeLocalZeroGrowingGuardedPredecessorRootCompilerOnCurrentGuardedHelperContext
    (M : RawPAModel) (hPA : RawPASatisfies M) : Prop :=
  forall (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      witnessList baseContext (helperRoots : list M)
      inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalCurrentGuardedHelperContextAt M
      (rawBottomDirectStructuralTemplateTranslation M hPA)
      tail level currentLocal currentCrossLevel currentShift
      currentSubstitution currentAxiomSoundness currentFinal
      witnessList baseContext helperRoots ->
    RawDynamicTruthNativeLocalProofTraceAt M tail level
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence ->
    level = raw_zero M ->
    exists targetWitnessList targetContext,
      RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
      RawContextListIncluded M baseContext targetContext /\
      RawDynamicTruthLocalRootAt M targetContext
        (rawDynamicTruthImpGuardedPredecessorStateExclusivityCode M).

Arguments
  RawDynamicTruthNativeLocalZeroGrowingGuardedPredecessorRootCompilerOnCurrentGuardedHelperContext
  M hPA : clear implicits.

(** Structural normalization adapter from the traversal-facing producer to
    the exact guarded callback boundary.  No current-field proof is erased:
    the guarded helper package supplies its witnessed context, while the
    existing zero-normalization theorem supplies all projected resources. *)
Theorem
    raw_dynamicTruthNativeLocalZeroGrowingGuardedPredecessorRootCompilerOnCurrentGuardedHelperContext_of_normalized_resources
    : forall (M : RawPAModel) (hPA : RawPASatisfies M),
  RawDynamicTruthNativeLocalZeroGrowingGuardedPredecessorRootCompilerOnNormalizedResources
    M hPA ->
  RawDynamicTruthNativeLocalZeroGrowingGuardedPredecessorRootCompilerOnCurrentGuardedHelperContext
    M hPA.
Proof.
  intros M hPA hcompiler tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal witnessList baseContext helperRoots
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence hcurrent htrace hlevel.
  pose proof hcurrent as hcurrentForWitness.
  unfold RawDynamicTruthNativeLocalCurrentGuardedHelperContextAt,
    RawDynamicTruthNativeLocalCurrentHelperBatchContextAt
    in hcurrentForWitness.
  destruct hcurrentForWitness as
    [_ (_ & _ & _ & _ & _ & _ & hbaseWitnessed & _)].
  pose proof
    (raw_dynamicTruthPredecessorStateProjectionRootsAt_of_realizable
      M hPA baseContext
      (raw_codedPAAxiomWitnessContext_context_realizable
        M witnessList baseContext hbaseWitnessed)) as hstateRoots.
  pose proof
    (raw_dynamicTruthNativeLocalCurrentGuardedHelperContextAt_zero_normalized
      M hPA (rawBottomDirectStructuralTemplateTranslation M hPA)
      tail level currentLocal currentCrossLevel currentShift
      currentSubstitution currentAxiomSoundness currentFinal
      witnessList baseContext helperRoots hcurrent hlevel hstateRoots)
    as hnormalized.
  subst level.
  exact (hcompiler tail witnessList baseContext helperRoots
    sigmaDomain piDomain sigmaEvidence piEvidence hnormalized
    (raw_dynamicTruthNativeLocalZeroFullTraceAt_canonical
      M hPA tail inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence
      (proj1 (raw_dynamicTruthNativeLocalProofTraceAt_zero_iff M tail
        inputGlobalSigma inputGlobalPi sigmaDomain piDomain
        sigmaEvidence piEvidence) htrace))).
Qed.

(** Convenience composition from the five guarded branch roots. *)
Corollary
    raw_dynamicTruthNativeLocalZeroGrowingGuardedPredecessorRootCompilerOnCurrentGuardedHelperContext_of_branch_roots
    : forall (M : RawPAModel) (hPA : RawPASatisfies M),
  RawDynamicTruthNativeLocalZeroGrowingGuardedBranchRootsCompilerOnNormalizedResources
    M hPA ->
  RawDynamicTruthNativeLocalZeroGrowingGuardedPredecessorRootCompilerOnCurrentGuardedHelperContext
    M hPA.
Proof.
  intros M hPA hbranch.
  apply
    raw_dynamicTruthNativeLocalZeroGrowingGuardedPredecessorRootCompilerOnCurrentGuardedHelperContext_of_normalized_resources.
  exact
    (raw_dynamicTruthNativeLocalZeroGrowingGuardedPredecessorRootCompilerOnNormalizedResources_of_branch_roots
      M hPA hbranch).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeZeroGuardedCallbackNormalization.
