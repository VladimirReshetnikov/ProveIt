(** Isolated PA-reification certificate for the Or-E disjunction child. *)

From BoundedPAConsistency Require Import
  RawCodedTemplateSyntax
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationSupport
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageDefinitions.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageDisjunctionChildCertificate.

Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationSupport.
Import PABoundedRawCodedTemplateSyntax.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageDefinitions.

Theorem coqRestrictedPADirectOrEliminationOpenedDisjunctionChild_succeeds :
  coqRestrictedPADirectAndIntroductionOpenedCoverageReificationChecker
    (templateFormulaRename S
      (coqRestrictedPADirectOrEliminationChildInterfaceTemplate
        CoqOrEliminationDisjunctionChild)) = true.
Proof.
  unfold
    coqRestrictedPADirectAndIntroductionOpenedCoverageReificationChecker.
  rewrite templateFormulaHasPAReificationAfterAbstracting_rename.
  vm_compute. reflexivity.
Qed.

Theorem coqRestrictedPADirectOrEliminationOpenedDisjunctionChild_reifies :
  exists output,
    templateFormulaAsPAFormula
      (templateFormulaAbstractParameter
        coqRestrictedPASoundnessLowerLevelParameterName
        (templateFormulaRename S
          (coqRestrictedPADirectOrEliminationChildInterfaceTemplate
            CoqOrEliminationDisjunctionChild))) = Some output.
Proof.
  destruct
    (coqRestrictedPADirectAndIntroductionOpenedCoverageReificationChecker_sound
      0
      (templateFormulaRename S
        (coqRestrictedPADirectOrEliminationChildInterfaceTemplate
          CoqOrEliminationDisjunctionChild))
      coqRestrictedPADirectOrEliminationOpenedDisjunctionChild_succeeds)
    as [output houtput].
  exists output.
  change (templateFormulaAsPAFormula
    (templateFormulaAbstractParameterAt
      coqRestrictedPASoundnessLowerLevelParameterName 0
      (templateFormulaRename S
        (coqRestrictedPADirectOrEliminationChildInterfaceTemplate
          CoqOrEliminationDisjunctionChild))) = Some output).
  exact houtput.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageDisjunctionChildCertificate.
