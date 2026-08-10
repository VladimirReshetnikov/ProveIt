(** The displayed endpoint of the Eq-E motive child. *)

From BoundedPAConsistency Require Import
  RawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageMotiveShapeDefinitions.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageMotiveEndpointShape.

Import PA.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedTemplateSyntax.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageMotiveShapeDefinitions.

Lemma coqRestrictedPADirectEqE_motive_child_endpoint_shape :
  coqRestrictedPADirectEqEMotiveChildEndpointTemplate =
  embedPAFormula
    (proofRuleValidTermAt (tVar 1) (tVar 7) (tVar 0)).
Proof. reflexivity. Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageMotiveEndpointShape.
