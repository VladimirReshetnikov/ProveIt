(** Public-surface and assumption audit for the ready collision batch. *)

From Stdlib Require Import List.
From BoundedPAConsistency Require Import
  RawCodedTruthCertificateMasterFixedHelperBatchExtension
  RawCodedDynamicTruthConstructorBranchDisjointness
  RawCodedTruthCertificateMasterCollisionHelperBatch.

Import ListNotations.
Import PABoundedRawCodedTruthCertificateMasterFixedHelperBatchExtension.
Import PABoundedRawCodedDynamicTruthConstructorBranchDisjointness.
Import PABoundedRawCodedTruthCertificateMasterCollisionHelperBatch.

Check rawDynamicTruthAndCollisionFixedPAHelper.
Check rawDynamicTruthOrCollisionFixedPAHelper.
Check rawDynamicTruthFixedConstructorCollisionPAHelper.
Check rawDynamicTruthFixedConstructorCollisionPAHelpers.
Check rawDynamicTruthFixedConstructorCollisionPAHelpers_length.
Check rawDynamicTruthReadyCollisionFixedPAHelpers.
Check rawDynamicTruthReadyCollisionFixedPAHelpers_length.
Check rawFixedPAHelperBatchTranslatedTargetCodes_eq_quoted.
Check rawDynamicTruthReadyCollisionFixedPAHelperTargets_eq_quoted.
Check raw_sixFieldMasterCommonContextProofsWithReadyCollisionHelpers.

(** The batch has the advertised strict size. *)
Goal length rawDynamicTruthReadyCollisionFixedPAHelpers = 21.
Proof. exact rawDynamicTruthReadyCollisionFixedPAHelpers_length. Qed.

(** Its constructor suffix agrees position-for-position with the explicit
    sixteen-cell classification. *)
Goal map rawFixedPAHelperFormula
    rawDynamicTruthFixedConstructorCollisionPAHelpers =
  map (fun cell =>
    dynamicTruthFixedConstructorBranchDisjointnessFormula
      (fst cell) (snd cell))
    dynamicTruthFixedConstructorCells.
Proof. reflexivity. Qed.

Print Assumptions rawDynamicTruthFixedConstructorCollisionPAHelpers_length.
Print Assumptions rawDynamicTruthReadyCollisionFixedPAHelpers_length.
Print Assumptions rawFixedPAHelperBatchTranslatedTargetCodes_eq_quoted.
Print Assumptions
  rawDynamicTruthReadyCollisionFixedPAHelperTargets_eq_quoted.
Print Assumptions
  raw_sixFieldMasterCommonContextProofsWithReadyCollisionHelpers.
