(**
  Rank-zero normalization retaining guarded implication helpers.

  Legacy normalization intentionally stored only the original forty-helper
  family.  The corrected implication matrix needs the two appended guarded
  cells on that same witnessed context.  This module repeats no graph
  reasoning: it projects the legacy prefix, invokes the established zero
  normalization once, and then restores the complete forty-two-helper proof
  family in a guarded normalized record.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedPALocalProofExistential
  RawCodedRestrictedPAProof
  RawCodedTemplateProofCompiler
  RawCodedTemplatePAEmbedding
  RawCodedTruthCertificateMasterFixedHelperBatchExtension
  RawCodedDynamicTruthMixedQFOpaqueQuantifierCellCompilation
  RawCodedDynamicTruthLocalCollisionMatrixAssembly
  RawCodedDynamicTruthLocalFieldProjectionCompilation
  RawCodedDynamicTruthPredecessorStateProjectionCompilation
  RawCodedDynamicTruthImpGuardedBranchExclusivity
  RawCodedDynamicTruthNativeLocalGuardedMatrixCompilation
  RawCodedDynamicTruthNativeLocalHelperBatchGeneralization
  RawCodedDynamicTruthNativeZeroPredecessorLogicalRootsCompilation.

Module PABoundedRawCodedDynamicTruthNativeZeroGuardedNormalization.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTruthCertificateMasterFixedHelperBatchExtension.
Import PABoundedRawCodedDynamicTruthMixedQFOpaqueQuantifierCellCompilation.
Import PABoundedRawCodedDynamicTruthLocalCollisionMatrixAssembly.
Import PABoundedRawCodedDynamicTruthLocalFieldProjectionCompilation.
Import PABoundedRawCodedDynamicTruthPredecessorStateProjectionCompilation.
Import PABoundedRawCodedDynamicTruthImpGuardedBranchExclusivity.
Import
  PABoundedRawCodedDynamicTruthNativeLocalGuardedMatrixCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeLocalHelperBatchGeneralization.
Import
  PABoundedRawCodedDynamicTruthNativeZeroPredecessorLogicalRootsCompilation.

(** The normalized six fields, local projection, and predecessor-state
    projections are unchanged.  Only the helper index is strengthened from
    the legacy prefix to the complete corrected batch. *)
Record RawDynamicTruthNativeLocalZeroGuardedNormalizedResourcesAt
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M)
    (witnessList baseContext : M) (helperRoots : list M) : Prop := {
  rawDynamicTruthNativeLocalZeroGuardedNormalized_fields :
    RawDynamicTruthNativeLocalZeroCurrentFieldRootsAt M
      witnessList baseContext;
  rawDynamicTruthNativeLocalZeroGuardedNormalized_localProjections :
    exists sourceRoot,
      RawDynamicTruthLocalDecisionExclusiveProjectedRootsAt M baseContext
        (rawDynamicTruthZeroSigmaDomainCode M)
        (rawDynamicTruthZeroPiDomainCode M)
        (rawDynamicTruthZeroSigmaEvidenceCode M)
        (rawDynamicTruthZeroPiEvidenceCode M) sourceRoot;
  rawDynamicTruthNativeLocalZeroGuardedNormalized_helpers :
    RawFixedPAHelperBatchLocalProofs M translation baseContext
      rawDynamicTruthReadyAndGuardedMixedQFPAHelpers helperRoots;
  rawDynamicTruthNativeLocalZeroGuardedNormalized_state :
    RawDynamicTruthPredecessorStateProjectionRootsAt M baseContext
}.

Arguments RawDynamicTruthNativeLocalZeroGuardedNormalizedResourcesAt
  M translation witnessList baseContext helperRoots : clear implicits.

(** Normalize a guarded current context without re-proving any rank-zero
    field identification.  The legacy theorem sees the computational helper
    prefix, while the result retains the original full root list. *)
Theorem
    raw_dynamicTruthNativeLocalCurrentGuardedHelperContextAt_zero_normalized :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M)
      (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      witnessList baseContext helperRoots,
  RawDynamicTruthNativeLocalCurrentGuardedHelperContextAt M translation
    tail level currentLocal currentCrossLevel currentShift
    currentSubstitution currentAxiomSoundness currentFinal
    witnessList baseContext helperRoots ->
  level = raw_zero M ->
  RawDynamicTruthPredecessorStateProjectionRootsAt M baseContext ->
  RawDynamicTruthNativeLocalZeroGuardedNormalizedResourcesAt M translation
    witnessList baseContext helperRoots.
Proof.
  intros M hPA translation tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal witnessList baseContext helperRoots
    hguarded hlevel hstate.
  pose proof hguarded as hguardedForHelpers.
  pose proof
    (raw_dynamicTruthNativeLocalCurrentHelperContextAt_of_guarded
      M translation tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      witnessList baseContext helperRoots hguarded) as hlegacyCurrent.
  pose proof
    (raw_dynamicTruthNativeLocalCurrentHelperContextAt_zero_normalized
      M hPA translation tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal witnessList baseContext
      (firstn (length rawDynamicTruthReadyAndAllMixedQFPAHelpers)
        helperRoots)
      hlegacyCurrent hlevel hstate) as hlegacyNormalized.
  destruct hlegacyNormalized as
    [hfields hlocalProjections _ hnormalizedState].
  unfold RawDynamicTruthNativeLocalCurrentGuardedHelperContextAt,
    RawDynamicTruthNativeLocalCurrentHelperBatchContextAt
    in hguardedForHelpers.
  destruct hguardedForHelpers as
    [_ (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      hhelpers)].
  constructor.
  - exact hfields.
  - exact hlocalProjections.
  - exact hhelpers.
  - exact hnormalizedState.
Qed.

(** Every guarded normalized package still satisfies the exact historical
    interface on the computed forty-root prefix. *)
Corollary
    raw_dynamicTruthNativeLocalZeroNormalizedResourcesAt_of_guarded :
    forall (M : RawPAModel) translation
      witnessList baseContext helperRoots,
  RawDynamicTruthNativeLocalZeroGuardedNormalizedResourcesAt M translation
    witnessList baseContext helperRoots ->
  RawDynamicTruthNativeLocalZeroNormalizedResourcesAt M translation
    witnessList baseContext
      (firstn (length rawDynamicTruthReadyAndAllMixedQFPAHelpers)
        helperRoots).
Proof.
  intros M translation witnessList baseContext helperRoots hguarded.
  destruct hguarded as [hfields hlocal hhelpers hstate].
  constructor.
  - exact hfields.
  - exact hlocal.
  - unfold rawDynamicTruthReadyAndGuardedMixedQFPAHelpers in hhelpers.
    exact (raw_fixedPAHelperBatchLocalProofs_app_prefix_firstn M
      translation baseContext rawDynamicTruthReadyAndAllMixedQFPAHelpers
      rawDynamicTruthGuardedImpCollisionFixedPAHelpers helperRoots
      hhelpers).
  - exact hstate.
Qed.

Definition RawDynamicTruthNativeLocalZeroGuardedCollisionCellRootsAt
    (M : RawPAModel) (context : M) : Prop :=
  RawDynamicTruthLocalRootAt M context
    (rawDynamicTruthImpFalseLeftGuardedConditionalCellCode M) /\
  RawDynamicTruthLocalRootAt M context
    (rawDynamicTruthImpTrueRightGuardedConditionalCellCode M).

Arguments RawDynamicTruthNativeLocalZeroGuardedCollisionCellRootsAt
  M context : clear implicits.

(** The corrected fixed cells can be projected immediately at the normalized
    boundary; no trace or current-field information is consumed. *)
Theorem
    raw_dynamicTruthNativeLocalZeroGuardedCollisionCellRootsAt_of_normalized :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      translation witnessList baseContext helperRoots,
  RawCodedTemplatePAAgreement M translation ->
  RawDynamicTruthNativeLocalZeroGuardedNormalizedResourcesAt M translation
    witnessList baseContext helperRoots ->
  RawDynamicTruthNativeLocalZeroGuardedCollisionCellRootsAt M baseContext.
Proof.
  intros M hPA translation witnessList baseContext helperRoots
    hagreement hnormalized.
  pose proof (rawDynamicTruthNativeLocalZeroGuardedNormalized_helpers
    M translation witnessList baseContext helperRoots hnormalized)
    as hhelpers.
  destruct (raw_dynamicTruthNativeLocal_helper_roots_of_42_helpers
    M hPA translation baseContext helperRoots hagreement hhelpers) as
    [legacyRoots [_ [hfalse htrue]]].
  split; assumption.
Qed.

End PABoundedRawCodedDynamicTruthNativeZeroGuardedNormalization.
