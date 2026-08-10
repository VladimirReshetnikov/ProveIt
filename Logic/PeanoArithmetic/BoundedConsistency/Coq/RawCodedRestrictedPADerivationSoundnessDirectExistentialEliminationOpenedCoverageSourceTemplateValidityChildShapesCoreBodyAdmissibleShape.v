(** The body-child admissibility shape, isolated for strict checking. *)

From BoundedPAConsistency Require Import
  RawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationOpenedCoverageSourceTemplateValidityChildShapesCoreDefinitions.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationOpenedCoverageSourceTemplateValidityChildShapesCoreBodyAdmissibleShape.

Import PA.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedProofFormulaCoverage.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedRestrictedTargetTemplateContext.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationOpenedCoverageSourceTemplateValidityChildShapesCoreDefinitions.

Lemma coqRestrictedPADirectExE_body_child_admissible_shape :
  coqRestrictedPADirectExEBodyChildAdmissibleTemplate =
  tfAnd
    (tfAnd (embedPAFormula (codedFormulaAtomicallyAdequateTermAt (tVar 3)))
      (tfAnd (embedPAFormula
        (codedAssignmentDefinedThroughTermAt (tVar 9) (tVar 8) (tVar 3)))
        (restrictedTargetTemplateFormulaContext
          coqRestrictedPASoundnessLowerLevelTerm
          (restrictedTargetFormulaQuantifierBoundedContext (tVar 3)))))
    (embedPAFormula (pEx (pAnd
      (proofFormulaCoverageTermAt (tVar 2) (tVar 0))
      (codedAssignmentDefinedThroughTermAt (tVar 10) (tVar 9) (tVar 0))))).
Proof. reflexivity. Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationOpenedCoverageSourceTemplateValidityChildShapesCoreBodyAdmissibleShape.
