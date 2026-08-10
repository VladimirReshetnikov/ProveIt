(** Isolated Boolean PA-reification certificate for the Eq-E motive child. *)

From BoundedPAConsistency Require Import
  RawCodedTemplateSyntax
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationSupport
  RawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageDefinitions.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageReificationMotiveChildCertificate.

Import PABoundedRawCodedTemplateSyntax.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationSupport.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageDefinitions.

Theorem coqRestrictedPADirectEqualityEliminationOpenedMotiveChild_succeeds :
  coqRestrictedPADirectAndIntroductionOpenedCoverageReificationChecker
    (templateFormulaRename S
      coqRestrictedPADirectEqualityEliminationMotiveChildInterfaceTemplate) =
  true.
Proof.
  unfold
    coqRestrictedPADirectAndIntroductionOpenedCoverageReificationChecker.
  rewrite templateFormulaHasPAReificationAfterAbstracting_rename.
  vm_compute. reflexivity.
Qed.

Theorem coqRestrictedPADirectEqualityEliminationOpenedMotiveChild_reifies :
  exists output,
    templateFormulaAsPAFormula
      (templateFormulaAbstractParameter
        coqRestrictedPASoundnessLowerLevelParameterName
        (templateFormulaRename S
          coqRestrictedPADirectEqualityEliminationMotiveChildInterfaceTemplate)) =
    Some output.
Proof.
  destruct
    (coqRestrictedPADirectAndIntroductionOpenedCoverageReificationChecker_sound
      0
      (templateFormulaRename S
        coqRestrictedPADirectEqualityEliminationMotiveChildInterfaceTemplate)
      coqRestrictedPADirectEqualityEliminationOpenedMotiveChild_succeeds)
    as [output houtput].
  exists output.
  change (templateFormulaAsPAFormula
    (templateFormulaAbstractParameterAt
      coqRestrictedPASoundnessLowerLevelParameterName 0
      (templateFormulaRename S
        coqRestrictedPADirectEqualityEliminationMotiveChildInterfaceTemplate)) =
    Some output).
  exact houtput.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageReificationMotiveChildCertificate.
