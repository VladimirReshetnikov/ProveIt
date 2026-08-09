(** Isolated Boolean PA-fragment certificate for the restricted premise. *)

From BoundedPAConsistency Require Import
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationSupport.

Module PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationRestrictedCertificate.

Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationSupport.

Theorem coqRestrictedPADirectAndIntroductionOpenedRestricted_succeeds :
  coqRestrictedPADirectAndIntroductionOpenedCoverageReificationChecker
    coqRestrictedPADirectAndIntroductionOpenedRestrictedTemplate = true.
Proof.
  unfold
    coqRestrictedPADirectAndIntroductionOpenedCoverageReificationChecker,
    coqRestrictedPADirectAndIntroductionOpenedRestrictedTemplate.
  rewrite templateFormulaHasPAReificationAfterAbstracting_rename.
  vm_compute. reflexivity.
Qed.

Theorem coqRestrictedPADirectAndIntroductionOpenedRestricted_reifies :
  exists output,
    templateFormulaAsPAFormula
      (templateFormulaAbstractParameter
        coqRestrictedPASoundnessLowerLevelParameterName
        coqRestrictedPADirectAndIntroductionOpenedRestrictedTemplate) =
    Some output.
Proof.
  destruct
    (coqRestrictedPADirectAndIntroductionOpenedCoverageReificationChecker_sound
      0 coqRestrictedPADirectAndIntroductionOpenedRestrictedTemplate
      coqRestrictedPADirectAndIntroductionOpenedRestricted_succeeds)
    as [output houtput].
  exists output.
  change (templateFormulaAsPAFormula
    (templateFormulaAbstractParameterAt
      coqRestrictedPASoundnessLowerLevelParameterName 0
      coqRestrictedPADirectAndIntroductionOpenedRestrictedTemplate) =
    Some output).
  exact houtput.
Qed.

End PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationRestrictedCertificate.
