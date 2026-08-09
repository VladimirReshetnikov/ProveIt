(** Isolated Boolean PA-fragment certificate for admissibility. *)

From BoundedPAConsistency Require Import
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationSupport.

Module PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationAdmissibleCoreCertificate.

Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationSupport.

Theorem coqRestrictedPADirectAndIntroductionOpenedAdmissibleCore_succeeds :
  coqRestrictedPADirectAndIntroductionOpenedCoverageReificationChecker
    coqRestrictedPADirectAndIntroductionOpenedAdmissibleCoreTemplate = true.
Proof.
  unfold
    coqRestrictedPADirectAndIntroductionOpenedCoverageReificationChecker,
    coqRestrictedPADirectAndIntroductionOpenedAdmissibleCoreTemplate.
  rewrite templateFormulaHasPAReificationAfterAbstracting_rename.
  vm_compute. reflexivity.
Qed.

Theorem coqRestrictedPADirectAndIntroductionOpenedAdmissibleCore_reifies :
  exists output,
    templateFormulaAsPAFormula
      (templateFormulaAbstractParameter
        coqRestrictedPASoundnessLowerLevelParameterName
        coqRestrictedPADirectAndIntroductionOpenedAdmissibleCoreTemplate) =
    Some output.
Proof.
  destruct
    (coqRestrictedPADirectAndIntroductionOpenedCoverageReificationChecker_sound
      0 coqRestrictedPADirectAndIntroductionOpenedAdmissibleCoreTemplate
      coqRestrictedPADirectAndIntroductionOpenedAdmissibleCore_succeeds)
    as [output houtput].
  exists output.
  change (templateFormulaAsPAFormula
    (templateFormulaAbstractParameterAt
      coqRestrictedPASoundnessLowerLevelParameterName 0
      coqRestrictedPADirectAndIntroductionOpenedAdmissibleCoreTemplate) =
    Some output).
  exact houtput.
Qed.

End PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationAdmissibleCoreCertificate.
