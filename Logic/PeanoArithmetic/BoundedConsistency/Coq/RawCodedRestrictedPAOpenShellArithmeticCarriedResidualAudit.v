(** Assumption audit for the synchronized carried arithmetic residual. *)

From BoundedPAConsistency Require Import
  RawCodedRestrictedPAOpenShellArithmeticCarriedResidual.

Import
  PABoundedRawCodedRestrictedPAOpenShellArithmeticCarriedResidual.

Check raw_coqRestrictedPAOpenShell_arithmetic_residual_growing.

Print Assumptions raw_coqRestrictedPAOpenShell_arithmetic_residual_growing.
