(** Isolated Boolean PA-reification certificate for the renamed Eq-E case. *)

From BoundedPAConsistency Require Import
  RawCodedTemplateSyntax
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationSupport
  RawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageDefinitions.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageReificationCaseCertificate.

Import PABoundedRawCodedTemplateSyntax.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationSupport.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageDefinitions.

Theorem coqRestrictedPADirectEqualityEliminationOpenedCase_succeeds :
  coqRestrictedPADirectAndIntroductionOpenedCoverageReificationChecker
    (templateFormulaRename S
      coqRestrictedPADirectEqualityEliminationCaseTemplate) = true.
Proof.
  unfold
    coqRestrictedPADirectAndIntroductionOpenedCoverageReificationChecker.
  rewrite templateFormulaHasPAReificationAfterAbstracting_rename.
  vm_compute. reflexivity.
Qed.

Theorem coqRestrictedPADirectEqualityEliminationOpenedCase_reifies :
  exists output,
    templateFormulaAsPAFormula
      (templateFormulaAbstractParameter
        coqRestrictedPASoundnessLowerLevelParameterName
        (templateFormulaRename S
          coqRestrictedPADirectEqualityEliminationCaseTemplate)) =
    Some output.
Proof.
  destruct
    (coqRestrictedPADirectAndIntroductionOpenedCoverageReificationChecker_sound
      0
      (templateFormulaRename S
        coqRestrictedPADirectEqualityEliminationCaseTemplate)
      coqRestrictedPADirectEqualityEliminationOpenedCase_succeeds)
    as [output houtput].
  exists output.
  change (templateFormulaAsPAFormula
    (templateFormulaAbstractParameterAt
      coqRestrictedPASoundnessLowerLevelParameterName 0
      (templateFormulaRename S
        coqRestrictedPADirectEqualityEliminationCaseTemplate)) =
    Some output).
  exact houtput.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageReificationCaseCertificate.
