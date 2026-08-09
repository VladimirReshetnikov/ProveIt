(** Isolated Boolean PA-fragment certificate for the atomic premise. *)

From BoundedPAConsistency Require Import
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationSupport.

Module PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationAtomicCertificate.

Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationSupport.

Theorem coqRestrictedPADirectAndIntroductionOpenedAtomic_succeeds :
  coqRestrictedPADirectAndIntroductionOpenedCoverageReificationChecker
    coqRestrictedPADirectAndIntroductionOpenedAtomicTemplate = true.
Proof.
  unfold
    coqRestrictedPADirectAndIntroductionOpenedCoverageReificationChecker,
    coqRestrictedPADirectAndIntroductionOpenedAtomicTemplate.
  rewrite templateFormulaHasPAReificationAfterAbstracting_rename.
  vm_compute. reflexivity.
Qed.

Theorem coqRestrictedPADirectAndIntroductionOpenedAtomic_reifies :
  exists output,
    templateFormulaAsPAFormula
      (templateFormulaAbstractParameter
        coqRestrictedPASoundnessLowerLevelParameterName
        coqRestrictedPADirectAndIntroductionOpenedAtomicTemplate) =
    Some output.
Proof.
  destruct
    (coqRestrictedPADirectAndIntroductionOpenedCoverageReificationChecker_sound
      0 coqRestrictedPADirectAndIntroductionOpenedAtomicTemplate
      coqRestrictedPADirectAndIntroductionOpenedAtomic_succeeds)
    as [output houtput].
  exists output.
  change (templateFormulaAsPAFormula
    (templateFormulaAbstractParameterAt
      coqRestrictedPASoundnessLowerLevelParameterName 0
      coqRestrictedPADirectAndIntroductionOpenedAtomicTemplate) =
    Some output).
  exact houtput.
Qed.

End PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationAtomicCertificate.
