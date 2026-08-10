(** Fixed right-branch instance of the Or-E restricted shape. *)

From BoundedPAConsistency Require Import
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageShapeSupport.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageRightRestrictedShape.

Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageShapeSupport.

Lemma coqRestrictedPADirectOrElimination_right_restricted_shape :
  coqRestrictedPADirectOrEliminationChildRestrictedTemplate
    CoqOrEliminationRightBranchChild =
  tfAnd
    (restrictedTargetTemplateFormulaContext
      coqRestrictedPASoundnessLowerLevelTerm
      (restrictedTargetProofContext
        (coqRestrictedPADirectOrEliminationChildPATerm
          CoqOrEliminationRightBranchChild)))
    (tfAnd (embedPAFormula (proofAtomicallyAdequateTermAt
        (coqRestrictedPADirectOrEliminationChildPATerm
          CoqOrEliminationRightBranchChild)))
      (tfAnd (embedPAFormula (proofHasFormulaCoverageTermAt
          (coqRestrictedPADirectOrEliminationChildPATerm
            CoqOrEliminationRightBranchChild)))
        (embedPAFormula (proofRuleCoverageTermAt
          (coqRestrictedPADirectOrEliminationChildPATerm
            CoqOrEliminationRightBranchChild))))).
Proof. reflexivity. Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageRightRestrictedShape.
