(** The restricted-proof component of the Eq-E motive child. *)

From BoundedPAConsistency Require Import
  RawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageMotiveShapeDefinitions.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageMotiveRestrictedShape.

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
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageMotiveShapeDefinitions.

Lemma coqRestrictedPADirectEqE_motive_child_restricted_shape :
  coqRestrictedPADirectEqEMotiveChildRestrictedTemplate =
  tfAnd
    (restrictedTargetTemplateFormulaContext
      coqRestrictedPASoundnessLowerLevelTerm
      (restrictedTargetProofContext (tVar 1)))
    (tfAnd (embedPAFormula (proofAtomicallyAdequateTermAt (tVar 1)))
      (tfAnd (embedPAFormula (proofHasFormulaCoverageTermAt (tVar 1)))
        (embedPAFormula (proofRuleCoverageTermAt (tVar 1))))).
Proof. reflexivity. Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageMotiveRestrictedShape.
