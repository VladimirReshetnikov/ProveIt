(**
  Audit surface for the honest Bottom-E recursive-truth boundary.

  The first printed theorem is the unconditional result: on every standard
  witnessed tail, Bottom-E yields truth of the closed bottom formula at the
  current assignment, provided the represented admissibility row remains in
  the local context.  The final checks keep the two residual operations
  separate so an assignment-code transport cannot be mistaken for removal of
  the common-coverage premise used by recursive descent.
*)

From BoundedPAConsistency Require Import
  RawCodedRestrictedPADerivationSoundnessDirectBottomRecursiveTruthAdmissibleBoundary.

Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectBottomRecursiveTruthAdmissibleBoundary.

Check raw_bottom_child_interface.
Check raw_bottomCurrentTruth_of_openedCoverageCompiler.
Check
  RawCoqRestrictedPADirectBottomCurrentTruthUnderAdmissibilityStandardTailCompiler.
Check raw_bottomCurrentTruthUnderAdmissibility_standardTail.

Check coqRestrictedPADirectBottomCurrentAssignmentNormalizationTemplate.
Check
  RawCoqRestrictedPADirectBottomCurrentAssignmentNormalizationStandardTailCompiler.

Check coqRestrictedPADirectBottomAdmissibilityErasureTemplate.
Check
  RawCoqRestrictedPADirectBottomAdmissibilityErasureStandardTailCompiler.

Check raw_bottomRecursiveClosedTruthLawRoot_of_factored_residuals.

Print Assumptions raw_bottom_child_interface.
Print Assumptions raw_bottomCurrentTruth_of_openedCoverageCompiler.
Print Assumptions raw_bottomCurrentTruthUnderAdmissibility_standardTail.
Print Assumptions raw_bottomRecursiveClosedTruthLawRoot_of_factored_residuals.
