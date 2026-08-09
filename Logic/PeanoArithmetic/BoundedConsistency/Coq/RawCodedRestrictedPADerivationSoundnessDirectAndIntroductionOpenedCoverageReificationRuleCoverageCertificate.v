(** Isolated Boolean PA-fragment certificate for rule coverage. *)

From BoundedPAConsistency Require Import
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationSupport.

Module PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationRuleCoverageCertificate.

Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationSupport.

Theorem coqRestrictedPADirectAndIntroductionOpenedRuleCoverage_succeeds :
  coqRestrictedPADirectAndIntroductionOpenedCoverageReificationChecker
    coqRestrictedPADirectAndIntroductionOpenedRuleCoverageTemplate = true.
Proof.
  unfold
    coqRestrictedPADirectAndIntroductionOpenedCoverageReificationChecker,
    coqRestrictedPADirectAndIntroductionOpenedRuleCoverageTemplate.
  rewrite templateFormulaHasPAReificationAfterAbstracting_rename.
  vm_compute. reflexivity.
Qed.

Theorem coqRestrictedPADirectAndIntroductionOpenedRuleCoverage_reifies :
  exists output,
    templateFormulaAsPAFormula
      (templateFormulaAbstractParameter
        coqRestrictedPASoundnessLowerLevelParameterName
        coqRestrictedPADirectAndIntroductionOpenedRuleCoverageTemplate) =
    Some output.
Proof.
  destruct
    (coqRestrictedPADirectAndIntroductionOpenedCoverageReificationChecker_sound
      0 coqRestrictedPADirectAndIntroductionOpenedRuleCoverageTemplate
      coqRestrictedPADirectAndIntroductionOpenedRuleCoverage_succeeds)
    as [output houtput].
  exists output.
  change (templateFormulaAsPAFormula
    (templateFormulaAbstractParameterAt
      coqRestrictedPASoundnessLowerLevelParameterName 0
      coqRestrictedPADirectAndIntroductionOpenedRuleCoverageTemplate) =
    Some output).
  exact houtput.
Qed.

End PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationRuleCoverageCertificate.
