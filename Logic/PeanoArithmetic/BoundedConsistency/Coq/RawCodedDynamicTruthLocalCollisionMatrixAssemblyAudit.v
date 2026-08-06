(** Kernel-facing audit for the native local collision matrix assembly. *)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedPALocalProofExistential
  RawCodedPALocalProofFiniteDisjunctionMatrix
  RawCodedDynamicTruthQFBranchExclusivity
  RawCodedDynamicTruthImpBranchExclusivity
  RawCodedDynamicTruthBooleanBranchExclusivity
  RawCodedDynamicTruthQuantifierBranchExclusivity
  RawCodedDynamicTruthLocalCollisionMatrixAssembly.

Import ListNotations.

Module PABoundedRawCodedDynamicTruthLocalCollisionMatrixAssemblyAudit.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofFiniteDisjunctionMatrix.
Import PABoundedRawCodedDynamicTruthQFBranchExclusivity.
Import PABoundedRawCodedDynamicTruthImpBranchExclusivity.
Import PABoundedRawCodedDynamicTruthBooleanBranchExclusivity.
Import PABoundedRawCodedDynamicTruthQuantifierBranchExclusivity.
Import PABoundedRawCodedDynamicTruthLocalCollisionMatrixAssembly.

(** The carrier rows have the advertised literal order. *)
Goal forall (M : RawPAModel) lowerPi,
  rawDynamicTruthLocalSigmaBranches M lowerPi =
  [ rawDynamicTruthSigmaQFEx8BranchCode M;
    rawDynamicTruthSigmaImpFalseLeftEx8BranchCode M;
    rawDynamicTruthSigmaImpTrueRightEx8BranchCode M;
    rawDynamicTruthSigmaAndEx8BranchCode M;
    rawDynamicTruthSigmaOrEx8BranchCode M;
    rawDynamicTruthSigmaEx8BranchCode M;
    rawDynamicTruthSigmaUniversalEx8BranchCode M lowerPi ].
Proof. reflexivity. Qed.

Goal forall (M : RawPAModel) lowerSigma,
  rawDynamicTruthLocalPiBranches M lowerSigma =
  [ rawDynamicTruthPiQFEx8BranchCode M;
    rawDynamicTruthPiImpEx8BranchCode M;
    rawDynamicTruthPiAndEx8BranchCode M;
    rawDynamicTruthPiOrEx8BranchCode M;
    rawDynamicTruthPiAllEx8BranchCode M;
    rawDynamicTruthPiExistentialEx8BranchCode M lowerSigma ].
Proof. reflexivity. Qed.

Goal forall M lowerPi,
  length (rawDynamicTruthLocalSigmaBranches M lowerPi) = 7.
Proof. exact rawDynamicTruthLocalSigmaBranches_length. Qed.

Goal forall M lowerSigma,
  length (rawDynamicTruthLocalPiBranches M lowerSigma) = 6.
Proof. exact rawDynamicTruthLocalPiBranches_length. Qed.

Goal length dynamicTruthLocalCollisionKinds = 42.
Proof. exact dynamicTruthLocalCollisionKinds_length. Qed.

(** Each of the seven rows reduces to the surveyed six cell classes. *)
Goal map (dynamicTruthLocalCollisionKind DTLocalSigmaQF)
    dynamicTruthLocalPiBranchOrder =
  [ DTLocalCollisionQF;
    DTLocalCollisionMixedReplay;
    DTLocalCollisionMixedReplay;
    DTLocalCollisionMixedReplay;
    DTLocalCollisionMixedQuantifier;
    DTLocalCollisionMixedQuantifier ].
Proof. reflexivity. Qed.

Goal map (dynamicTruthLocalCollisionKind DTLocalSigmaImpFalseLeft)
    dynamicTruthLocalPiBranchOrder =
  [ DTLocalCollisionMixedReplay;
    DTLocalCollisionImpConditional;
    DTLocalCollisionFixedConstructor;
    DTLocalCollisionFixedConstructor;
    DTLocalCollisionFixedConstructor;
    DTLocalCollisionBinderOffDiagonal ].
Proof. reflexivity. Qed.

Goal map (dynamicTruthLocalCollisionKind DTLocalSigmaImpTrueRight)
    dynamicTruthLocalPiBranchOrder =
  [ DTLocalCollisionMixedReplay;
    DTLocalCollisionImpConditional;
    DTLocalCollisionFixedConstructor;
    DTLocalCollisionFixedConstructor;
    DTLocalCollisionFixedConstructor;
    DTLocalCollisionBinderOffDiagonal ].
Proof. reflexivity. Qed.

Goal map (dynamicTruthLocalCollisionKind DTLocalSigmaAnd)
    dynamicTruthLocalPiBranchOrder =
  [ DTLocalCollisionMixedReplay;
    DTLocalCollisionFixedConstructor;
    DTLocalCollisionBooleanConditional;
    DTLocalCollisionFixedConstructor;
    DTLocalCollisionFixedConstructor;
    DTLocalCollisionBinderOffDiagonal ].
Proof. reflexivity. Qed.

Goal map (dynamicTruthLocalCollisionKind DTLocalSigmaOr)
    dynamicTruthLocalPiBranchOrder =
  [ DTLocalCollisionMixedReplay;
    DTLocalCollisionFixedConstructor;
    DTLocalCollisionFixedConstructor;
    DTLocalCollisionBooleanConditional;
    DTLocalCollisionFixedConstructor;
    DTLocalCollisionBinderOffDiagonal ].
Proof. reflexivity. Qed.

Goal map (dynamicTruthLocalCollisionKind DTLocalSigmaEx)
    dynamicTruthLocalPiBranchOrder =
  [ DTLocalCollisionMixedQuantifier;
    DTLocalCollisionFixedConstructor;
    DTLocalCollisionFixedConstructor;
    DTLocalCollisionFixedConstructor;
    DTLocalCollisionFixedConstructor;
    DTLocalCollisionQuantifierConditional ].
Proof. reflexivity. Qed.

Goal map (dynamicTruthLocalCollisionKind DTLocalSigmaAll)
    dynamicTruthLocalPiBranchOrder =
  [ DTLocalCollisionMixedQuantifier;
    DTLocalCollisionBinderOffDiagonal;
    DTLocalCollisionBinderOffDiagonal;
    DTLocalCollisionBinderOffDiagonal;
    DTLocalCollisionQuantifierConditional;
    DTLocalCollisionBinderOffDiagonal ].
Proof. reflexivity. Qed.

(** The record visibly retains every unresolved common-context seam. *)
Check RawDynamicTruthLocalRootAt.
Check RawDynamicTruthLocalCollisionMatrixInputs.
Check rawDynamicTruthLocalCollision_context_realizable.
Check rawDynamicTruthLocalCollision_lowerPi_adequate.
Check rawDynamicTruthLocalCollision_lowerSigma_adequate.
Check rawDynamicTruthLocalCollision_context_self_shift.
Check rawDynamicTruthLocalCollision_qf_root.
Check rawDynamicTruthLocalCollision_predecessor_root.
Check rawDynamicTruthLocalCollision_impFalse_root.
Check rawDynamicTruthLocalCollision_impTrue_root.
Check rawDynamicTruthLocalCollision_and_root.
Check rawDynamicTruthLocalCollision_or_root.
Check rawDynamicTruthLocalCollision_fixed_pairs.
Check rawDynamicTruthLocalCollision_binder_inputs.
Check rawDynamicTruthLocalCollision_sigmaEx_direct_trace.
Check rawDynamicTruthLocalCollision_sigmaAll_direct_trace.
Check rawDynamicTruthLocalCollision_sigmaEx_cross_root.
Check rawDynamicTruthLocalCollision_sigmaAll_cross_root.
Check rawDynamicTruthLocalCollision_mixed_replay_root.
Check rawDynamicTruthLocalCollision_mixed_cell_roots.

(** Exact endpoints: all 42 pair implications, then bottom from Or7/Or6. *)
Check raw_dynamicTruthLocalCollisionMatrix_pair_of_imp_pairs.
Check raw_dynamicTruthLocalCollisionMatrix_pair.
Check raw_dynamicTruthLocalCollisionMatrix_pair_guarded_imp.
Check raw_dynamicTruthLocalCollisionMatrix_pair_family.
Check raw_dynamicTruthLocalCollisionMatrix_pair_family_guarded_imp.
Check rawDynamicTruthLocalSigmaOr7Code.
Check rawDynamicTruthLocalPiOr6Code.
Check
  raw_codedPALocalProofOf_dynamicTruthLocalCollisionMatrix_bottom_of_pair_family.
Check raw_codedPALocalProofOf_dynamicTruthLocalCollisionMatrix_bottom.
Check
  raw_codedPALocalProofOf_dynamicTruthLocalCollisionMatrix_bottom_guarded_imp.

Goal forall (M : RawPAModel), RawPASatisfies M -> forall
    context lowerPi lowerSigma,
  RawDynamicTruthLocalCollisionMatrixInputs M context
    lowerPi lowerSigma ->
  RawCodedPALocalFiniteDisjunctionPairFamily M context
    (rawDynamicTruthLocalSigmaBranches M lowerPi)
    (rawDynamicTruthLocalPiBranches M lowerSigma)
    (rawFormulaBotCode M).
Proof. exact raw_dynamicTruthLocalCollisionMatrix_pair_family. Qed.

Print Assumptions raw_dynamicTruthLocalCollisionMatrix_pair_of_imp_pairs.
Print Assumptions raw_dynamicTruthLocalCollisionMatrix_pair.
Print Assumptions raw_dynamicTruthLocalCollisionMatrix_pair_guarded_imp.
Print Assumptions raw_dynamicTruthLocalCollisionMatrix_pair_family.
Print Assumptions raw_dynamicTruthLocalCollisionMatrix_pair_family_guarded_imp.
Print Assumptions
  raw_codedPALocalProofOf_dynamicTruthLocalCollisionMatrix_bottom_of_pair_family.
Print Assumptions
  raw_codedPALocalProofOf_dynamicTruthLocalCollisionMatrix_bottom.
Print Assumptions
  raw_codedPALocalProofOf_dynamicTruthLocalCollisionMatrix_bottom_guarded_imp.

End PABoundedRawCodedDynamicTruthLocalCollisionMatrixAssemblyAudit.
