(** The existential-child restricted-interface shape, isolated for checking. *)

From BoundedPAConsistency Require Import
  RawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationOpenedCoverageSourceTemplateValidityChildShapesCoreDefinitions.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationOpenedCoverageSourceTemplateValidityChildShapesCoreExistentialRestrictedShape.

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

Lemma coqRestrictedPADirectExE_existential_child_restricted_shape :
  coqRestrictedPADirectExEExistentialChildRestrictedTemplate =
  tfAnd
    (restrictedTargetTemplateFormulaContext
      coqRestrictedPASoundnessLowerLevelTerm
      (restrictedTargetProofContext (tVar 2)))
    (tfAnd (embedPAFormula (proofAtomicallyAdequateTermAt (tVar 2)))
      (tfAnd (embedPAFormula (proofHasFormulaCoverageTermAt (tVar 2)))
        (embedPAFormula (proofRuleCoverageTermAt (tVar 2))))).
Proof. reflexivity. Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationOpenedCoverageSourceTemplateValidityChildShapesCoreExistentialRestrictedShape.
