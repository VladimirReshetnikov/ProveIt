(** The body-child restricted-interface shape, isolated for checking. *)

From BoundedPAConsistency Require Import
  RawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationOpenedCoverageSourceTemplateValidityChildShapesCoreDefinitions.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationOpenedCoverageSourceTemplateValidityChildShapesCoreBodyRestrictedShape.

Import PA.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedProofFormulaCoverage.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedRestrictedTargetTemplateContext.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationOpenedCoverageSourceTemplateValidityChildShapesCoreDefinitions.

Lemma coqRestrictedPADirectExE_body_child_restricted_shape :
  coqRestrictedPADirectExEBodyChildRestrictedTemplate =
  tfAnd
    (restrictedTargetTemplateFormulaContext
      coqRestrictedPASoundnessLowerLevelTerm
      (restrictedTargetProofContext (tVar 1)))
    (tfAnd (embedPAFormula (proofAtomicallyAdequateTermAt (tVar 1)))
      (tfAnd (embedPAFormula (proofHasFormulaCoverageTermAt (tVar 1)))
        (embedPAFormula (proofRuleCoverageTermAt (tVar 1))))).
Proof. reflexivity. Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationOpenedCoverageSourceTemplateValidityChildShapesCoreBodyRestrictedShape.
