(**
  Audit surface for scope discharge at the fixed-standard-level
  derivation-soundness induction boundary.

  The compiler theorems remain conditional on explicit zero- and
  successor-case local proofs; checking them here must not be read as a
  construction of those proofs.
*)

From BoundedPAConsistency Require Import
  RawCodedRestrictedPADerivationSoundnessScopeDischarge.

Import
  PABoundedRawCodedRestrictedPADerivationSoundnessScopeDischarge.

Check
  raw_codedRestrictedPADerivationSoundnessClosureInductionData_scoped.
Check
  raw_codedPALocalProofOf_restrictedPADerivationSoundness_induction.
Check
  raw_codedPAProofOf_restrictedPADerivationSoundness_induction.

Print Assumptions
  raw_codedRestrictedPADerivationSoundnessClosureInductionData_scoped.
Print Assumptions
  raw_codedPALocalProofOf_restrictedPADerivationSoundness_induction.
Print Assumptions
  raw_codedPAProofOf_restrictedPADerivationSoundness_induction.
