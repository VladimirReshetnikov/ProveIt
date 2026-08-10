(** Fixed disjunction-child instance of the Or-E restricted shape. *)

From BoundedPAConsistency Require Import
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageShapeSupport.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageDisjunctionRestrictedShape.

Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageShapeSupport.

Lemma coqRestrictedPADirectOrElimination_disjunction_restricted_shape :
  coqRestrictedPADirectOrEliminationChildRestrictedTemplate
    CoqOrEliminationDisjunctionChild =
  tfAnd
    (restrictedTargetTemplateFormulaContext
      coqRestrictedPASoundnessLowerLevelTerm
      (restrictedTargetProofContext
        (coqRestrictedPADirectOrEliminationChildPATerm
          CoqOrEliminationDisjunctionChild)))
    (tfAnd (embedPAFormula (proofAtomicallyAdequateTermAt
        (coqRestrictedPADirectOrEliminationChildPATerm
          CoqOrEliminationDisjunctionChild)))
      (tfAnd (embedPAFormula (proofHasFormulaCoverageTermAt
          (coqRestrictedPADirectOrEliminationChildPATerm
            CoqOrEliminationDisjunctionChild)))
        (embedPAFormula (proofRuleCoverageTermAt
          (coqRestrictedPADirectOrEliminationChildPATerm
            CoqOrEliminationDisjunctionChild))))).
Proof. reflexivity. Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageDisjunctionRestrictedShape.
