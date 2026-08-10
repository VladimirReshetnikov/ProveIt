(** Fixed right-branch instance of the Or-E endpoint shape. *)

From BoundedPAConsistency Require Import
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageShapeSupport.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageRightEndpointShape.

Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageShapeSupport.

Lemma coqRestrictedPADirectOrElimination_right_endpoint_shape :
  coqRestrictedPADirectOrEliminationChildEndpointInterfaceTemplate
    CoqOrEliminationRightBranchChild =
  embedPAFormula (proofRuleValidTermAt
    (coqRestrictedPADirectOrEliminationChildPATerm
      CoqOrEliminationRightBranchChild)
    (coqRestrictedPADirectOrEliminationChildContextPATerm
      CoqOrEliminationRightBranchChild)
    (coqRestrictedPADirectOrEliminationChildConclusionPATerm
      CoqOrEliminationRightBranchChild)).
Proof. reflexivity. Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageRightEndpointShape.
