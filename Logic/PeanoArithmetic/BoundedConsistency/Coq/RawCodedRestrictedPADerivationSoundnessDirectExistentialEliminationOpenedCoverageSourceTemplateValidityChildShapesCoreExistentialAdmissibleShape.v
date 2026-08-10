(** The existential-child admissibility shape, isolated for checking. *)

From BoundedPAConsistency Require Import
  RawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationOpenedCoverageSourceTemplateValidityChildShapesCoreDefinitions.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationOpenedCoverageSourceTemplateValidityChildShapesCoreExistentialAdmissibleShape.

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

Lemma coqRestrictedPADirectExE_existential_child_admissible_shape :
  coqRestrictedPADirectExEExistentialChildAdmissibleTemplate =
  tfAnd
    (tfAnd (embedPAFormula (codedFormulaAtomicallyAdequateTermAt (tVar 0)))
      (tfAnd (embedPAFormula
        (codedAssignmentDefinedThroughTermAt (tVar 9) (tVar 8) (tVar 0)))
        (restrictedTargetTemplateFormulaContext
          coqRestrictedPASoundnessLowerLevelTerm
          (restrictedTargetFormulaQuantifierBoundedContext (tVar 0)))))
    (embedPAFormula (pEx (pAnd
      (proofFormulaCoverageTermAt (tVar 3) (tVar 0))
      (codedAssignmentDefinedThroughTermAt (tVar 10) (tVar 9) (tVar 0))))).
Proof. reflexivity. Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationOpenedCoverageSourceTemplateValidityChildShapesCoreExistentialAdmissibleShape.
