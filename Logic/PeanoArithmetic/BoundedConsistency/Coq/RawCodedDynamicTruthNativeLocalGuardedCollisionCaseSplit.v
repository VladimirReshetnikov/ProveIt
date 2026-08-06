(**
  Assemble guarded collision roots by the native zero/successor split.

  Rank zero and positive rank use genuinely different proof resources.  The
  former is normalized to the canonical bottom trace; the latter carries an
  aligned predecessor record.  This module keeps those producers separate and
  performs only the structural case analysis already proved for a native local
  callback.  Both branches may grow their witnessed PA tails.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedRestrictedPAProof
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedLtSuccCasesProofCompilation
  RawCodedTemplateProofCompiler
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateBottomDirectStructuralInputs
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedStrongStepProofEndpointAtomicAdequacyProofCompilation
  RawCodedDynamicTruthLocalCollisionMatrixAssembly
  RawCodedDynamicTruthPredecessorStateProjectionCompilation
  RawCodedDynamicTruthMixedQFOpaqueQuantifierCellCompilation
  RawCodedDynamicTruthImpGuardedBranchExclusivity
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthNativeLocalProofCompilation
  RawCodedDynamicTruthNativeLocalStagedCallbackCompilation
  RawCodedDynamicTruthNativeLocalHelperBatchGeneralization
  RawCodedDynamicTruthNativeLocalGuardedNonImpPairCompilation
  RawCodedDynamicTruthNativeLocalGrowingPredecessorStagedCallbackCompilation
  RawCodedDynamicTruthNativeLocalGuardedBuilderDecomposition
  RawCodedDynamicTruthNativeZeroPredecessorLogicalRootsCompilation
  RawCodedDynamicTruthNativeZeroGuardedNormalization
  RawCodedDynamicTruthNativeZeroGuardedEvidenceIdentification
  RawCodedDynamicTruthNativeZeroGuardedFixedProductionBoundary
  RawCodedDynamicTruthNativeZeroGuardedCollisionCompilation.

Module
  PABoundedRawCodedDynamicTruthNativeLocalGuardedCollisionCaseSplit.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedLtSuccCasesProofCompilation.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateBottomDirectStructuralInputs.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import PABoundedRawCodedStrongStepProofEndpointAtomicAdequacyProofCompilation.
Import PABoundedRawCodedDynamicTruthLocalCollisionMatrixAssembly.
Import PABoundedRawCodedDynamicTruthPredecessorStateProjectionCompilation.
Import PABoundedRawCodedDynamicTruthMixedQFOpaqueQuantifierCellCompilation.
Import PABoundedRawCodedDynamicTruthImpGuardedBranchExclusivity.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeLocalProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalStagedCallbackCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeLocalHelperBatchGeneralization.
Import
  PABoundedRawCodedDynamicTruthNativeLocalGuardedNonImpPairCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeLocalGrowingPredecessorStagedCallbackCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeLocalGuardedBuilderDecomposition.
Import
  PABoundedRawCodedDynamicTruthNativeZeroPredecessorLogicalRootsCompilation.
Import PABoundedRawCodedDynamicTruthNativeZeroGuardedNormalization.
Import
  PABoundedRawCodedDynamicTruthNativeZeroGuardedEvidenceIdentification.
Import
  PABoundedRawCodedDynamicTruthNativeZeroGuardedFixedProductionBoundary.
Import
  PABoundedRawCodedDynamicTruthNativeZeroGuardedCollisionCompilation.

(** Rank-zero producer at the literal guarded callback interface. *)
Definition
    RawDynamicTruthNativeLocalZeroGrowingGuardedCollisionRootsCompilerOnCurrentGuardedHelperContext
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (translation : RawCodedTemplateTranslation M) : Prop :=
  forall (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      witnessList baseContext (helperRoots : list M)
      inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalCurrentGuardedHelperContextAt M translation
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
      RawDynamicTruthLocalBooleanDiagonalPairRootsAt M targetContext /\
      RawDynamicTruthLocalRootAt M targetContext
        (rawDynamicTruthImpGuardedPredecessorStateExclusivityCode M).

Arguments
  RawDynamicTruthNativeLocalZeroGrowingGuardedCollisionRootsCompilerOnCurrentGuardedHelperContext
  M hPA translation : clear implicits.

(** Positive-rank producer after the native trace has selected and aligned its
    predecessor.  Passing the existing witness list is weaker than asking the
    producer to rediscover a witness for [baseContext]. *)
Definition
    RawDynamicTruthNativeLocalAlignedGrowingGuardedCollisionRootsCompilerOnWitnessedBase
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi
      (aligned : RawDynamicTruthNativeLocalAlignedPredecessorAt M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi)
      sourceWitnessList,
    RawCodedPAAxiomWitnessContext M sourceWitnessList baseContext ->
    exists targetWitnessList targetContext,
      RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
      RawContextListIncluded M baseContext targetContext /\
      RawDynamicTruthLocalBooleanDiagonalPairRootsAt M targetContext /\
      RawDynamicTruthLocalRootAt M targetContext
        (rawDynamicTruthImpGuardedPredecessorStateExclusivityCode M).

Arguments
  RawDynamicTruthNativeLocalAlignedGrowingGuardedCollisionRootsCompilerOnWitnessedBase
  M : clear implicits.

(** Invocation-local proof resources for the rank-zero collision.  Both
    direct-shell premises may grow independently from the normalized
    callback's witnessed PA tail.  The constructor-specific fixed producers
    may also depend on the normalized invocation and canonical trace; this is
    weaker than demanding a single model-global producer for every callback.

    The selected direct inputs are returned together with their evidence
    identification, so all three constructor branches use one translation
    without imposing that translation on the normalization phase. *)
Definition
    RawDynamicTruthNativeLocalZeroGuardedCollisionProofResourcesCompilerOnNormalizedResources
    (M : RawPAModel) (hPA : RawPASatisfies M) : Prop :=
  forall (tail : nat -> M) witnessList baseContext (helperRoots : list M)
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalZeroGuardedNormalizedResourcesAt M
      (rawBottomDirectStructuralTemplateTranslation M hPA)
      witnessList baseContext helperRoots ->
    RawDynamicTruthNativeLocalZeroCanonicalFullTraceAt M tail
      sigmaDomain piDomain sigmaEvidence piEvidence ->
    exists inputs : RawCodedTemplateDirectStructuralInputs M,
      RawDynamicTruthZeroGuardedEvidenceIdentification M inputs /\
      RawCodedPAGrowingTemplateLocalProofAt M
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        witnessList baseContext []
        (rawDirectTemplateFormula inputs
          coqRestrictedPADerivationSoundnessRestrictedProofTemplate) /\
      RawCodedPAGrowingTemplateLocalProofAt M
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        witnessList baseContext []
        (rawDirectTemplateFormula inputs
          coqStrongStepProofEndpointAtomicAdequacyRulePremise) /\
      RawDynamicTruthZeroCanonicalIdentifiedGuardedCollisionFixedDeepIndependentGrowingFixedProductionOrRefutationCompilers
        M hPA inputs.

Arguments
  RawDynamicTruthNativeLocalZeroGuardedCollisionProofResourcesCompilerOnNormalizedResources
  M hPA : clear implicits.

(** Normalize the literal guarded callback, canonicalize its zero trace, and
    invoke the relaxed collision endpoint.  State-projection roots are
    reconstructed from realizability of the witnessed PA context, so the
    producer interface does not repeat that derived resource. *)
Theorem
    raw_dynamicTruthNativeLocalZeroGrowingGuardedCollisionRootsCompilerOnCurrentGuardedHelperContext_of_normalized_proof_resources :
    forall (M : RawPAModel) (hPA : RawPASatisfies M),
  RawDynamicTruthNativeLocalZeroGuardedCollisionProofResourcesCompilerOnNormalizedResources
    M hPA ->
  RawDynamicTruthNativeLocalZeroGrowingGuardedCollisionRootsCompilerOnCurrentGuardedHelperContext
    M hPA (rawBottomDirectStructuralTemplateTranslation M hPA).
Proof.
  intros M hPA hresources tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal witnessList baseContext helperRoots
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain sigmaEvidence
    piEvidence hcurrent htrace hlevel.
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
  pose proof
    (raw_dynamicTruthNativeLocalZeroFullTraceAt_canonical
      M hPA tail inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence
      (proj1 (raw_dynamicTruthNativeLocalProofTraceAt_zero_iff M tail
        inputGlobalSigma inputGlobalPi sigmaDomain piDomain
        sigmaEvidence piEvidence) htrace)) as hcanonicalTrace.
  destruct
    (hresources tail witnessList baseContext helperRoots
      sigmaDomain piDomain sigmaEvidence piEvidence
      hnormalized hcanonicalTrace) as
    (inputs & hidentification & hrestricted & hrule & hfixed).
  exact
    (raw_dynamicTruthLocalGuardedCollisionRootsAt_on_witnessed_extension_of_zero_normalized_independently_growing_restricted_rule_roots_and_guarded_collision_fixed_productions_or_refutations
      M hPA inputs
      (rawBottomDirectStructuralTemplateTranslation M hPA)
      witnessList baseContext helperRoots hidentification hnormalized
      hrestricted hrule hfixed).
Qed.

(** Structural assembly into the public collision builder.  No collision
    formula is proved here; the theorem only routes the exact zero or aligned
    successor resources to the corresponding producer. *)
Theorem
    raw_dynamicTruthNativeLocalCurrentGrowingGuardedCollisionRootsBuilder_of_zero_and_witnessed_aligned :
    forall (M : RawPAModel) (hPA : RawPASatisfies M),
  forall (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeLocalZeroGrowingGuardedCollisionRootsCompilerOnCurrentGuardedHelperContext
    M hPA translation ->
  RawDynamicTruthNativeLocalAlignedGrowingGuardedCollisionRootsCompilerOnWitnessedBase
    M ->
  RawDynamicTruthNativeLocalCurrentGrowingGuardedCollisionRootsBuilder
    M translation.
Proof.
  intros M hPA translation hzero haligned tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal witnessList baseContext helperRoots
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain sigmaEvidence
    piEvidence hcurrent htrace sigmaRowDomain piRowDomain
    lowerPiApplication lowerSigmaApplication hrows.
  pose proof
    (raw_dynamicTruthNativeLocalCurrentHelperContextAt_of_guarded
      M translation tail level currentLocal currentCrossLevel currentShift
      currentSubstitution currentAxiomSoundness currentFinal
      witnessList baseContext helperRoots hcurrent) as hlegacyCurrent.
  destruct
    (raw_dynamicTruthNativeLocalCurrentHelperContextAt_exact_cases_aligned_with_next
      M hPA translation tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal witnessList baseContext
      (firstn (length rawDynamicTruthReadyAndAllMixedQFPAHelpers)
        helperRoots)
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain sigmaEvidence
      piEvidence hlegacyCurrent htrace) as
    [(_currentLocalRoot & hlevel & _hfield & _hcurrentRoot) |
      (predecessorLevel & _hlevel & aligned & _halignedRows)].
  - exact
      (hzero tail level
        currentLocal currentCrossLevel currentShift currentSubstitution
        currentAxiomSoundness currentFinal witnessList baseContext helperRoots
        inputGlobalSigma inputGlobalPi sigmaDomain piDomain sigmaEvidence
        piEvidence hcurrent htrace hlevel).
  - pose proof hcurrent as hfields.
    unfold RawDynamicTruthNativeLocalCurrentGuardedHelperContextAt,
      RawDynamicTruthNativeLocalCurrentHelperBatchContextAt in hfields.
    destruct hfields as
      [_ (_ & _ & _ & _ & _ & _ & hbaseWitnessed & _)].
    exact
      (haligned tail predecessorLevel baseContext currentLocal
        inputGlobalSigma inputGlobalPi aligned witnessList hbaseWitnessed).
Qed.

(** Public collision builder with the entire rank-zero normalization adapter
    inlined.  Only the honest normalized proof resources and the independent
    aligned positive producer remain as premises. *)
Corollary
    raw_dynamicTruthNativeLocalCurrentGrowingGuardedCollisionRootsBuilder_of_zero_normalized_proof_resources_and_witnessed_aligned :
    forall (M : RawPAModel) (hPA : RawPASatisfies M),
  RawDynamicTruthNativeLocalZeroGuardedCollisionProofResourcesCompilerOnNormalizedResources
    M hPA ->
  RawDynamicTruthNativeLocalAlignedGrowingGuardedCollisionRootsCompilerOnWitnessedBase
    M ->
  RawDynamicTruthNativeLocalCurrentGrowingGuardedCollisionRootsBuilder
    M (rawBottomDirectStructuralTemplateTranslation M hPA).
Proof.
  intros M hPA hzeroResources haligned.
  exact
    (raw_dynamicTruthNativeLocalCurrentGrowingGuardedCollisionRootsBuilder_of_zero_and_witnessed_aligned
      M hPA (rawBottomDirectStructuralTemplateTranslation M hPA)
      (raw_dynamicTruthNativeLocalZeroGrowingGuardedCollisionRootsCompilerOnCurrentGuardedHelperContext_of_normalized_proof_resources
        M hPA hzeroResources)
      haligned).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeLocalGuardedCollisionCaseSplit.
