(** Audit surface for strong-prefix child truth under renaming. *)

From BoundedPAConsistency Require Import
  RawCodedRestrictedPADerivationSoundnessDirectRenamedChildTruth.

Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRenamedChildTruth.

Check
  raw_codedPALocalProofOf_coqRestrictedPADirectAndIntroductionChildTruth_renamed.

Print Assumptions
  raw_codedPALocalProofOf_coqRestrictedPADirectAndIntroductionChildTruth_renamed.
