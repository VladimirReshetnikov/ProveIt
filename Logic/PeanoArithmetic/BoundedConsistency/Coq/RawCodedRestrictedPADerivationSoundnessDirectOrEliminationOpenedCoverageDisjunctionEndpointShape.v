(** Fixed disjunction-child instance of the Or-E endpoint shape. *)

From BoundedPAConsistency Require Import
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageShapeSupport.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageDisjunctionEndpointShape.

Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageShapeSupport.

Lemma coqRestrictedPADirectOrElimination_disjunction_endpoint_shape :
  coqRestrictedPADirectOrEliminationChildEndpointInterfaceTemplate
    CoqOrEliminationDisjunctionChild =
  embedPAFormula (proofRuleValidTermAt
    (coqRestrictedPADirectOrEliminationChildPATerm
      CoqOrEliminationDisjunctionChild)
    (coqRestrictedPADirectOrEliminationChildContextPATerm
      CoqOrEliminationDisjunctionChild)
    (coqRestrictedPADirectOrEliminationChildConclusionPATerm
      CoqOrEliminationDisjunctionChild)).
Proof. reflexivity. Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageDisjunctionEndpointShape.
