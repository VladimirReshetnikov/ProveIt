(** Fixed left-branch instance of the Or-E admissible shape. *)

From BoundedPAConsistency Require Import
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageShapeSupport.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageLeftAdmissibleShape.

Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageShapeSupport.

Lemma coqRestrictedPADirectOrElimination_left_admissible_shape :
  coqRestrictedPADirectOrEliminationChildAdmissibleTemplate
    CoqOrEliminationLeftBranchChild =
  tfAnd
    (tfAnd (embedPAFormula (codedFormulaAtomicallyAdequateTermAt
        (coqRestrictedPADirectOrEliminationChildConclusionPATerm
          CoqOrEliminationLeftBranchChild)))
      (tfAnd (embedPAFormula (codedAssignmentDefinedThroughTermAt
          (tVar 9) (tVar 8)
          (coqRestrictedPADirectOrEliminationChildConclusionPATerm
            CoqOrEliminationLeftBranchChild)))
        (restrictedTargetTemplateFormulaContext
          coqRestrictedPASoundnessLowerLevelTerm
          (restrictedTargetFormulaQuantifierBoundedContext
            (coqRestrictedPADirectOrEliminationChildConclusionPATerm
              CoqOrEliminationLeftBranchChild)))))
    (embedPAFormula (pEx (pAnd
      (proofFormulaCoverageTermAt
        (liftTerm 1
          (coqRestrictedPADirectOrEliminationChildPATerm
            CoqOrEliminationLeftBranchChild)) (tVar 0))
      (codedAssignmentDefinedThroughTermAt
        (tVar 10) (tVar 9) (tVar 0))))).
Proof. reflexivity. Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageLeftAdmissibleShape.
