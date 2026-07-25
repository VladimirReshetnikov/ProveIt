(** Assumption audit for the exact compact-selector proof successor. *)

From BoundedPAConsistency Require Import
  RawCodedCompactSelectorProofSuccessor.

Import PABoundedRawCodedCompactSelectorProofSuccessor.

Print Assumptions
  raw_restrictedPAConsistencyProofSuccessorInAllModels_iff_step_BProv.
Print Assumptions
  PA_BProv_compactSelectorInductionSourceAll_of_step.
Print Assumptions
  PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_step.
