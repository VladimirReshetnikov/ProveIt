(** Fixed left-branch instance of the Or-E restricted shape. *)

From BoundedPAConsistency Require Import
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageShapeSupport.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageLeftRestrictedShape.

Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageShapeSupport.

Lemma coqRestrictedPADirectOrElimination_left_restricted_shape :
  coqRestrictedPADirectOrEliminationChildRestrictedTemplate
    CoqOrEliminationLeftBranchChild =
  tfAnd
    (restrictedTargetTemplateFormulaContext
      coqRestrictedPASoundnessLowerLevelTerm
      (restrictedTargetProofContext
        (coqRestrictedPADirectOrEliminationChildPATerm
          CoqOrEliminationLeftBranchChild)))
    (tfAnd (embedPAFormula (proofAtomicallyAdequateTermAt
        (coqRestrictedPADirectOrEliminationChildPATerm
          CoqOrEliminationLeftBranchChild)))
      (tfAnd (embedPAFormula (proofHasFormulaCoverageTermAt
          (coqRestrictedPADirectOrEliminationChildPATerm
            CoqOrEliminationLeftBranchChild)))
        (embedPAFormula (proofRuleCoverageTermAt
          (coqRestrictedPADirectOrEliminationChildPATerm
            CoqOrEliminationLeftBranchChild))))).
Proof. reflexivity. Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageLeftRestrictedShape.
