(**
  Kernel-facing audit for the witnessed-tail native local leaf compiler.

  Besides listing the public endpoints, this file checks that the generalized
  contexts reduce definitionally to the older literal contexts at the empty
  tail.  The assumption reports at the end cover helper extraction, matrix
  transport, concrete row/matrix closure, and the final interface adapter.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import HierarchyReduction.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedDynamicTruthNativeLocalProofCompilation
  RawCodedDynamicTruthNativeLocalLeafRootCompiler.

Module PABoundedRawCodedDynamicTruthNativeLocalLeafRootCompilerAudit.

Import PA.
Import PAHierarchyReduction.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedDynamicTruthNativeLocalProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalLeafRootCompiler.

(** Literal contexts and the two deliberately separate global interfaces. *)
Check rawDynamicTruthNativeLocalAdmissibleContextOn.
Check rawDynamicTruthNativeLocalExclusiveSigmaContextOn.
Check rawDynamicTruthNativeLocalExclusivePiContextOn.
Check RawDynamicTruthNativeLocalDecisionRootOn.
Check RawDynamicTruthNativeLocalExclusiveRootOn.
Check RawDynamicTruthNativeLocalDecisionEvidenceRootInterface.
Check RawDynamicTruthNativeGlobalEvidenceRowRootInterface.

Goal forall (M : RawPAModel) sigmaDomain piDomain,
  rawDynamicTruthNativeLocalAdmissibleContextOn M (raw_zero M)
    sigmaDomain piDomain =
  rawDynamicTruthNativeLocalAdmissibleContext M sigmaDomain piDomain.
Proof. reflexivity. Qed.

Goal forall (M : RawPAModel)
    sigmaDomain piDomain sigmaEvidence,
  rawDynamicTruthNativeLocalExclusiveSigmaContextOn M (raw_zero M)
    sigmaDomain piDomain sigmaEvidence =
  rawDynamicTruthNativeLocalExclusiveSigmaContext M
    sigmaDomain piDomain sigmaEvidence.
Proof. reflexivity. Qed.

Goal forall (M : RawPAModel)
    sigmaDomain piDomain sigmaEvidence piEvidence,
  rawDynamicTruthNativeLocalExclusivePiContextOn M (raw_zero M)
    sigmaDomain piDomain sigmaEvidence piEvidence =
  rawDynamicTruthNativeLocalExclusivePiContext M
    sigmaDomain piDomain sigmaEvidence piEvidence.
Proof. reflexivity. Qed.

Goal forall (M : RawPAModel)
    sigmaDomain piDomain sigmaEvidence piEvidence,
  RawDynamicTruthNativeLocalDecisionRootOn M (raw_zero M)
    sigmaDomain piDomain sigmaEvidence piEvidence =
  RawDynamicTruthNativeLocalDecisionLeafRootAt M
    sigmaDomain piDomain sigmaEvidence piEvidence.
Proof. reflexivity. Qed.

Goal forall (M : RawPAModel)
    sigmaDomain piDomain sigmaEvidence piEvidence,
  RawDynamicTruthNativeLocalExclusiveRootOn M (raw_zero M)
    sigmaDomain piDomain sigmaEvidence piEvidence =
  RawDynamicTruthNativeLocalExclusiveLeafRootAt M
    sigmaDomain piDomain sigmaEvidence piEvidence.
Proof. reflexivity. Qed.

(** The synchronized forty-helper layer and its exact residual boundary. *)
Check raw_dynamicTruthNativeLocal_helper_root.
Check raw_dynamicTruthNativeLocal_basicCollisionRoots_of_40_helpers.
Check raw_fixedPAHelperBatchLocalProofs_app_inv.
Check raw_dynamicTruthNativeLocal_fixedPairBatch_of_40_helpers.
Check raw_dynamicTruthNativeLocal_binderPrincipalRoots_of_40_helpers.
Check raw_dynamicTruthNativeLocal_mixedQFRoots_of_40_helpers.
Check RawDynamicTruthNativeLocalCollisionResidualInputsAt.
Check rawDynamicTruthNativeLocalCollision_contextRealizable.
Check rawDynamicTruthNativeLocalCollision_lowerPiAdequate.
Check rawDynamicTruthNativeLocalCollision_lowerSigmaAdequate.
Check rawDynamicTruthNativeLocalCollision_contextSelfShift.
Check rawDynamicTruthNativeLocalCollision_predecessorRoot.
Check rawDynamicTruthNativeLocalCollision_fixedPairs.
Check rawDynamicTruthNativeLocalCollision_binderProjections.
Check rawDynamicTruthNativeLocalCollision_sigmaExTrace.
Check rawDynamicTruthNativeLocalCollision_sigmaAllTrace.
Check rawDynamicTruthNativeLocalCollision_sigmaExCrossRoot.
Check rawDynamicTruthNativeLocalCollision_sigmaAllCrossRoot.
Check rawDynamicTruthNativeLocalCollision_mixedReplayRoot.
Check raw_dynamicTruthNativeLocalCollisionMatrixInputs_of_40_helpers.

(** Honest context extension and the first-class exclusive matrix package. *)
Check raw_dynamicTruthLocalRootAt_adequateCons.
Check raw_dynamicTruthBinderOffDiagonalInputs_adequateCons.
Check raw_dynamicTruthLocalCollisionMatrixInputs_adequateCons.
Check raw_dynamicTruthLocalCollisionMatrixInputs_on_exclusive_context.
Check RawDynamicTruthNativeLocalExclusiveMatrixResourcesAt.
Check raw_dynamicTruthNativeLocalExclusiveMatrixResourcesAt_of_40_helpers.
Check raw_dynamicTruthNativeLocalExclusiveRootOn_of_rows_and_matrix.
Check raw_dynamicTruthNativeLocalExclusiveRootOn_of_interface.

(** Witnessed-tail leaf bundle and the explicit literal-empty-tail adapter. *)
Check RawDynamicTruthNativeLocalLeafRootsOn.
Check raw_dynamicTruthNativeLocalLeafRootsOn_of_interfaces.
Check raw_dynamicTruthNativeLocalLeafRootsAt_of_empty_tail.
Check RawDynamicTruthNativeLocalEmptyTailMatrixResourceCompiler.
Check raw_dynamicTruthNativeLocalLeafRootCompiler_of_interfaces.

Print Assumptions
  raw_dynamicTruthNativeLocal_fixedPairBatch_of_40_helpers.
Print Assumptions
  raw_dynamicTruthNativeLocal_mixedQFRoots_of_40_helpers.
Print Assumptions
  raw_dynamicTruthNativeLocalCollisionMatrixInputs_of_40_helpers.
Print Assumptions
  raw_dynamicTruthLocalCollisionMatrixInputs_on_exclusive_context.
Print Assumptions
  raw_dynamicTruthNativeLocalExclusiveMatrixResourcesAt_of_40_helpers.
Print Assumptions
  raw_dynamicTruthNativeLocalExclusiveRootOn_of_rows_and_matrix.
Print Assumptions
  raw_dynamicTruthNativeLocalLeafRootsOn_of_interfaces.
Print Assumptions
  raw_dynamicTruthNativeLocalLeafRootCompiler_of_interfaces.

End PABoundedRawCodedDynamicTruthNativeLocalLeafRootCompilerAudit.
