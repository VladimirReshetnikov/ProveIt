(** Assumption and public-surface audit for the fixed-helper extension. *)

From BoundedPAConsistency Require Import
  RawCodedTruthCertificateMasterFixedHelperExtension.

Import PABoundedRawCodedTruthCertificateMasterFixedHelperExtension.

(** One witnessed context and seven local roots are exposed by the package. *)
Check RawSixFieldMasterCommonContextProofsWithFixedPAHelperOf.

(** A fixed ordinary PA theorem extends any existing six-field package. *)
Check raw_sixFieldMasterCommonContextProofsWithFixedPAHelper_of_BProv.

Print Assumptions
  raw_sixFieldMasterCommonContextProofsWithFixedPAHelper_of_BProv.
