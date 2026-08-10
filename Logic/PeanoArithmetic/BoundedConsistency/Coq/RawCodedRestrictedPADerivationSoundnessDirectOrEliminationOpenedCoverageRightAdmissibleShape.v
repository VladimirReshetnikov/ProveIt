(** Fixed right-branch instance of the Or-E admissible shape. *)

From BoundedPAConsistency Require Import
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageShapeSupport.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageRightAdmissibleShape.

Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageShapeSupport.

Lemma coqRestrictedPADirectOrElimination_right_admissible_shape :
  coqRestrictedPADirectOrEliminationChildAdmissibleTemplate
    CoqOrEliminationRightBranchChild =
  tfAnd
    (tfAnd (embedPAFormula (codedFormulaAtomicallyAdequateTermAt
        (coqRestrictedPADirectOrEliminationChildConclusionPATerm
          CoqOrEliminationRightBranchChild)))
      (tfAnd (embedPAFormula (codedAssignmentDefinedThroughTermAt
          (tVar 9) (tVar 8)
          (coqRestrictedPADirectOrEliminationChildConclusionPATerm
            CoqOrEliminationRightBranchChild)))
        (restrictedTargetTemplateFormulaContext
          coqRestrictedPASoundnessLowerLevelTerm
          (restrictedTargetFormulaQuantifierBoundedContext
            (coqRestrictedPADirectOrEliminationChildConclusionPATerm
              CoqOrEliminationRightBranchChild)))))
    (embedPAFormula (pEx (pAnd
      (proofFormulaCoverageTermAt
        (liftTerm 1
          (coqRestrictedPADirectOrEliminationChildPATerm
            CoqOrEliminationRightBranchChild)) (tVar 0))
      (codedAssignmentDefinedThroughTermAt
        (tVar 10) (tVar 9) (tVar 0))))).
Proof. reflexivity. Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageRightAdmissibleShape.
