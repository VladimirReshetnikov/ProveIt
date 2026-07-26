(** Assumption and public-surface audit for the finite fixed-helper batch. *)

From BoundedPAConsistency Require Import
  RawCodedTruthCertificateMasterFixedHelperBatchExtension.

Import PABoundedRawCodedTruthCertificateMasterFixedHelperBatchExtension.

(** Each entry carries the derivation of its own ordinary PA formula. *)
Check RawFixedPAHelper.
Check rawFixedPAHelperFormula.
Check rawFixedPAHelperBProv.

(** Targets are exposed uniformly through one template translation. *)
Check rawFixedPAHelperTranslatedTargetCode.
Check rawFixedPAHelperBatchTranslatedTargetCodes.

(** The ordered local-proof family preserves one root per helper. *)
Check RawFixedPAHelperBatchLocalProofs.
Check raw_fixedPAHelperBatchLocalProofs_length.
Check raw_fixedPAHelperBatchLocalProofs_standardPrefix.

(** One witnessed context contains all six master roots and the full batch. *)
Check RawSixFieldMasterCommonContextProofsWithFixedPAHelperBatchOf.
Check raw_sixFieldMasterCommonContextProofsWithFixedPAHelperBatch.
Check raw_sixFieldMasterCommonContextProofsWithFixedPAHelperSingleton.

(** Concrete QF/implication collision batch and its shared translation. *)
Check rawDynamicTruthQFCollisionFixedPAHelper.
Check rawDynamicTruthImpFalseLeftCollisionFixedPAHelper.
Check rawDynamicTruthImpTrueRightCollisionFixedPAHelper.
Check rawDynamicTruthFirstThreeCollisionFixedPAHelpers.
Check rawDynamicTruthFirstThreeCollisionFixedPAHelperTargets_eq_quoted.
Check raw_sixFieldMasterCommonContextProofsWithFirstThreeCollisionHelpers.

Print Assumptions raw_fixedPAHelperBatchLocalProofs_standardPrefix.
Print Assumptions
  raw_sixFieldMasterCommonContextProofsWithFixedPAHelperBatch.
Print Assumptions
  raw_sixFieldMasterCommonContextProofsWithFixedPAHelperSingleton.
Print Assumptions
  rawDynamicTruthFirstThreeCollisionFixedPAHelperTargets_eq_quoted.
Print Assumptions
  raw_sixFieldMasterCommonContextProofsWithFirstThreeCollisionHelpers.
