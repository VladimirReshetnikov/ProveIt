(** Fixed left-branch instance of the Or-E endpoint shape. *)

From BoundedPAConsistency Require Import
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageShapeSupport.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageLeftEndpointShape.

Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageShapeSupport.

Lemma coqRestrictedPADirectOrElimination_left_endpoint_shape :
  coqRestrictedPADirectOrEliminationChildEndpointInterfaceTemplate
    CoqOrEliminationLeftBranchChild =
  embedPAFormula (proofRuleValidTermAt
    (coqRestrictedPADirectOrEliminationChildPATerm
      CoqOrEliminationLeftBranchChild)
    (coqRestrictedPADirectOrEliminationChildContextPATerm
      CoqOrEliminationLeftBranchChild)
    (coqRestrictedPADirectOrEliminationChildConclusionPATerm
      CoqOrEliminationLeftBranchChild)).
Proof. reflexivity. Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageLeftEndpointShape.
