(** Isolated Boolean PA-reification certificate for the Eq-E equality child. *)

From BoundedPAConsistency Require Import
  RawCodedTemplateSyntax
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationSupport
  RawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageDefinitions.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageReificationEqualityChildCertificate.

Import PABoundedRawCodedTemplateSyntax.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationSupport.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageDefinitions.

Theorem coqRestrictedPADirectEqualityEliminationOpenedEqualityChild_succeeds :
  coqRestrictedPADirectAndIntroductionOpenedCoverageReificationChecker
    (templateFormulaRename S
      coqRestrictedPADirectEqualityEliminationEqualityChildInterfaceTemplate) =
  true.
Proof.
  unfold
    coqRestrictedPADirectAndIntroductionOpenedCoverageReificationChecker.
  rewrite templateFormulaHasPAReificationAfterAbstracting_rename.
  vm_compute. reflexivity.
Qed.

Theorem coqRestrictedPADirectEqualityEliminationOpenedEqualityChild_reifies :
  exists output,
    templateFormulaAsPAFormula
      (templateFormulaAbstractParameter
        coqRestrictedPASoundnessLowerLevelParameterName
        (templateFormulaRename S
          coqRestrictedPADirectEqualityEliminationEqualityChildInterfaceTemplate)) =
    Some output.
Proof.
  destruct
    (coqRestrictedPADirectAndIntroductionOpenedCoverageReificationChecker_sound
      0
      (templateFormulaRename S
        coqRestrictedPADirectEqualityEliminationEqualityChildInterfaceTemplate)
      coqRestrictedPADirectEqualityEliminationOpenedEqualityChild_succeeds)
    as [output houtput].
  exists output.
  change (templateFormulaAsPAFormula
    (templateFormulaAbstractParameterAt
      coqRestrictedPASoundnessLowerLevelParameterName 0
      (templateFormulaRename S
        coqRestrictedPADirectEqualityEliminationEqualityChildInterfaceTemplate)) =
    Some output).
  exact houtput.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageReificationEqualityChildCertificate.
