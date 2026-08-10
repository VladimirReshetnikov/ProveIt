(** The source-instance admissibility component of the Eq-E motive child. *)

From BoundedPAConsistency Require Import
  RawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageMotiveShapeDefinitions.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageMotiveAdmissibleShape.

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
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageMotiveShapeDefinitions.

(** The proof code is shifted to [#2] underneath the coverage existential;
    the source-instance conclusion remains the existential's [#0]. *)
Lemma coqRestrictedPADirectEqE_motive_child_admissible_shape :
  coqRestrictedPADirectEqEMotiveChildAdmissibleTemplate =
  tfAnd
    (tfAnd (embedPAFormula (codedFormulaAtomicallyAdequateTermAt (tVar 0)))
      (tfAnd (embedPAFormula
        (codedAssignmentDefinedThroughTermAt (tVar 9) (tVar 8) (tVar 0)))
        (restrictedTargetTemplateFormulaContext
          coqRestrictedPASoundnessLowerLevelTerm
          (restrictedTargetFormulaQuantifierBoundedContext (tVar 0)))))
    (embedPAFormula (pEx (pAnd
      (proofFormulaCoverageTermAt (tVar 2) (tVar 0))
      (codedAssignmentDefinedThroughTermAt (tVar 10) (tVar 9) (tVar 0))))).
Proof. reflexivity. Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageMotiveAdmissibleShape.
