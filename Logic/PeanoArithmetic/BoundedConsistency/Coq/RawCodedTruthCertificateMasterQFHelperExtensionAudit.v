(** Public-surface and assumption audit for the native QF helper extension. *)

From BoundedPAConsistency Require Import
  RawCodedTruthCertificateMasterQFHelperExtension.

Import PABoundedRawCodedTruthCertificateMasterQFHelperExtension.

(** Exact native target and its arbitrary-agreement construction. *)
Check RawSixFieldMasterCommonContextProofsWithQFHelperOf.
Check raw_sixFieldMasterCommonContextProofsWithQFHelper_of_agreement.

(** Translation-free specialization for every raw PA model. *)
Check raw_sixFieldMasterCommonContextProofsWithQFHelper.

Print Assumptions
  raw_sixFieldMasterCommonContextProofsWithQFHelper_of_agreement.
Print Assumptions raw_sixFieldMasterCommonContextProofsWithQFHelper.
