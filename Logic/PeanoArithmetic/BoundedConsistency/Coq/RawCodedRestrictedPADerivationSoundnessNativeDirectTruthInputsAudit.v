(** Assumption audit for the coherent native direct-truth input package. *)

From BoundedPAConsistency Require Import
  RawCodedRestrictedPADerivationSoundnessNativeDirectTruthInputs.

Import
  PABoundedRawCodedRestrictedPADerivationSoundnessNativeDirectTruthInputs.

Check
  raw_coqRestrictedPADerivationSoundnessNativeDirectTruthInputs_exists.

Print Assumptions
  raw_coqRestrictedPADerivationSoundnessNativeDirectTruthInputs_exists.
