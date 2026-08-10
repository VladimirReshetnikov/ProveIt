(** Fixed disjunction-child instance of the Or-E admissible shape. *)

From BoundedPAConsistency Require Import
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageShapeSupport.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageDisjunctionAdmissibleShape.

Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageShapeSupport.

Lemma coqRestrictedPADirectOrElimination_disjunction_admissible_shape :
  coqRestrictedPADirectOrEliminationChildAdmissibleTemplate
    CoqOrEliminationDisjunctionChild =
  tfAnd
    (tfAnd (embedPAFormula (codedFormulaAtomicallyAdequateTermAt
        (coqRestrictedPADirectOrEliminationChildConclusionPATerm
          CoqOrEliminationDisjunctionChild)))
      (tfAnd (embedPAFormula (codedAssignmentDefinedThroughTermAt
          (tVar 9) (tVar 8)
          (coqRestrictedPADirectOrEliminationChildConclusionPATerm
            CoqOrEliminationDisjunctionChild)))
        (restrictedTargetTemplateFormulaContext
          coqRestrictedPASoundnessLowerLevelTerm
          (restrictedTargetFormulaQuantifierBoundedContext
            (coqRestrictedPADirectOrEliminationChildConclusionPATerm
              CoqOrEliminationDisjunctionChild)))))
    (embedPAFormula (pEx (pAnd
      (proofFormulaCoverageTermAt
        (liftTerm 1
          (coqRestrictedPADirectOrEliminationChildPATerm
            CoqOrEliminationDisjunctionChild)) (tVar 0))
      (codedAssignmentDefinedThroughTermAt
        (tVar 10) (tVar 9) (tVar 0))))).
Proof. reflexivity. Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageDisjunctionAdmissibleShape.
