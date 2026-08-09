(** Isolated Boolean PA-fragment certificate for common coverage. *)

From BoundedPAConsistency Require Import
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationSupport.

Module PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationCommonCoverageCertificate.

Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationSupport.

Theorem coqRestrictedPADirectAndIntroductionOpenedCommonCoverage_succeeds :
  coqRestrictedPADirectAndIntroductionOpenedCoverageReificationChecker
    coqRestrictedPADirectAndIntroductionOpenedCommonCoverageTemplate = true.
Proof.
  unfold
    coqRestrictedPADirectAndIntroductionOpenedCoverageReificationChecker,
    coqRestrictedPADirectAndIntroductionOpenedCommonCoverageTemplate.
  vm_compute. reflexivity.
Qed.

Theorem coqRestrictedPADirectAndIntroductionOpenedCommonCoverage_reifies :
  exists output,
    templateFormulaAsPAFormula
      (templateFormulaAbstractParameter
        coqRestrictedPASoundnessLowerLevelParameterName
        coqRestrictedPADirectAndIntroductionOpenedCommonCoverageTemplate) =
    Some output.
Proof.
  destruct
    (coqRestrictedPADirectAndIntroductionOpenedCoverageReificationChecker_sound
      0 coqRestrictedPADirectAndIntroductionOpenedCommonCoverageTemplate
      coqRestrictedPADirectAndIntroductionOpenedCommonCoverage_succeeds)
    as [output houtput].
  exists output.
  change (templateFormulaAsPAFormula
    (templateFormulaAbstractParameterAt
      coqRestrictedPASoundnessLowerLevelParameterName 0
      coqRestrictedPADirectAndIntroductionOpenedCommonCoverageTemplate) =
    Some output).
  exact houtput.
Qed.

End PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationCommonCoverageCertificate.
