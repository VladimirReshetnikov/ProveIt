(** Isolated Boolean PA-reification certificate for the Or-E case premise. *)

From BoundedPAConsistency Require Import
  RawCodedTemplateSyntax
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationSupport
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageDefinitions
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationCase.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageCaseCertificate.

Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationSupport.
Import PABoundedRawCodedTemplateSyntax.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageDefinitions.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationCase.

Theorem coqRestrictedPADirectOrEliminationOpenedCase_succeeds :
  coqRestrictedPADirectAndIntroductionOpenedCoverageReificationChecker
    (templateFormulaRename S
      coqRestrictedPADirectOrEliminationCaseTemplate) = true.
Proof.
  unfold
    coqRestrictedPADirectAndIntroductionOpenedCoverageReificationChecker.
  rewrite templateFormulaHasPAReificationAfterAbstracting_rename.
  vm_compute. reflexivity.
Qed.

Theorem coqRestrictedPADirectOrEliminationOpenedCase_reifies :
  exists output,
    templateFormulaAsPAFormula
      (templateFormulaAbstractParameter
        coqRestrictedPASoundnessLowerLevelParameterName
        (templateFormulaRename S
          coqRestrictedPADirectOrEliminationCaseTemplate)) = Some output.
Proof.
  destruct
    (coqRestrictedPADirectAndIntroductionOpenedCoverageReificationChecker_sound
      0
      (templateFormulaRename S
        coqRestrictedPADirectOrEliminationCaseTemplate)
      coqRestrictedPADirectOrEliminationOpenedCase_succeeds)
    as [output houtput].
  exists output.
  change (templateFormulaAsPAFormula
    (templateFormulaAbstractParameterAt
      coqRestrictedPASoundnessLowerLevelParameterName 0
      (templateFormulaRename S
        coqRestrictedPADirectOrEliminationCaseTemplate)) = Some output).
  exact houtput.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageCaseCertificate.
