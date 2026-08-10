(** The body-child endpoint shape, isolated for strict checking. *)

From BoundedPAConsistency Require Import
  RawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationOpenedCoverageSourceTemplateValidityChildShapesCoreDefinitions.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationOpenedCoverageSourceTemplateValidityChildShapesCoreBodyEndpointShape.

Import PA.
Import PAListFormulas.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedTemplateSyntax.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationOpenedCoverageSourceTemplateValidityChildShapesCoreDefinitions.

Lemma coqRestrictedPADirectExE_body_child_endpoint_shape :
  coqRestrictedPADirectExEBodyChildEndpointTemplate =
  embedPAFormula
    (proofRuleValidTermAt (tVar 1)
      (nodeTerm (tVar 6) (tVar 4)) (tVar 3)).
Proof. reflexivity. Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationOpenedCoverageSourceTemplateValidityChildShapesCoreBodyEndpointShape.
