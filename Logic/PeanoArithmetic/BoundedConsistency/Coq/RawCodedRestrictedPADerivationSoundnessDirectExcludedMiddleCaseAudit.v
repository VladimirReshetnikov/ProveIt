(** Kernel-facing audit for the direct excluded-middle rule case. *)

From BoundedPAConsistency Require Import
  RawCodedRestrictedPADerivationSoundnessDirectExcludedMiddleCase.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExcludedMiddleCaseAudit.

Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExcludedMiddleCase.

Check coqRestrictedPADirectExcludedMiddleDeepContext.
Check coqRestrictedPADirectExcludedMiddleCaseTemplate.
Check coqRestrictedPADirectExcludedMiddleCaseContext.
Check coqRestrictedPADirectExcludedMiddle_case_shape.

Check coqRestrictedPADirectExcludedMiddleAdmissibleTemplate.
Check coqRestrictedPADirectExcludedMiddleContextTruthTemplate.
Check coqRestrictedPADirectExcludedMiddleConclusionTruthTemplate.
Check coqRestrictedPADirectExcludedMiddleRemainingTemplate.
Check coqRestrictedPADirectExcludedMiddle_remaining_shape.

(** This formula, rather than the desired constructor branch, is the only
    public semantic input. *)
Check coqRestrictedPADirectExcludedMiddleTruthLawTemplate.
Check RawCoqRestrictedPADirectExcludedMiddleTruthLawRoot.

Check coqRestrictedPADirectExcludedMiddleBottomRoot_valid.
Check coqRestrictedPADirectExcludedMiddleImpRoot_valid.
Check coqRestrictedPADirectExcludedMiddleOrRoot_valid.
Check coqRestrictedPADirectExcludedMiddleLiftRoot_valid.

Check raw_codedPALocalProofOf_coqRestrictedPADirectExcludedMiddleCase.
Check raw_coqRestrictedPADirectStrongStepExcludedMiddleCaseRoot.

(** The generated proof plumbing adds no axiom beyond the relational choice
    principles inherited throughout raw model-coded PA proof construction.
    In particular, the final theorem does not assume the whole strong step,
    the whole rule-case family, or an already proved conclusion. *)
Print Assumptions coqRestrictedPADirectExcludedMiddle_case_shape.
Print Assumptions coqRestrictedPADirectExcludedMiddle_remaining_shape.
Print Assumptions
  raw_codedPALocalProofOf_coqRestrictedPADirectExcludedMiddleCase.
Print Assumptions
  raw_coqRestrictedPADirectStrongStepExcludedMiddleCaseRoot.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExcludedMiddleCaseAudit.
