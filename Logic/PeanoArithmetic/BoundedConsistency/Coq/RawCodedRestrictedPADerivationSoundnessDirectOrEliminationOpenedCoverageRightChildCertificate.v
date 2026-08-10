(** Isolated PA-reification certificate for the Or-E right branch child. *)

From BoundedPAConsistency Require Import
  RawCodedTemplateSyntax
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationSupport
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageDefinitions.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageRightChildCertificate.

Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationSupport.
Import PABoundedRawCodedTemplateSyntax.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageDefinitions.

Theorem coqRestrictedPADirectOrEliminationOpenedRightChild_succeeds :
  coqRestrictedPADirectAndIntroductionOpenedCoverageReificationChecker
    (templateFormulaRename S
      (coqRestrictedPADirectOrEliminationChildInterfaceTemplate
        CoqOrEliminationRightBranchChild)) = true.
Proof.
  unfold
    coqRestrictedPADirectAndIntroductionOpenedCoverageReificationChecker.
  rewrite templateFormulaHasPAReificationAfterAbstracting_rename.
  vm_compute. reflexivity.
Qed.

Theorem coqRestrictedPADirectOrEliminationOpenedRightChild_reifies :
  exists output,
    templateFormulaAsPAFormula
      (templateFormulaAbstractParameter
        coqRestrictedPASoundnessLowerLevelParameterName
        (templateFormulaRename S
          (coqRestrictedPADirectOrEliminationChildInterfaceTemplate
            CoqOrEliminationRightBranchChild))) = Some output.
Proof.
  destruct
    (coqRestrictedPADirectAndIntroductionOpenedCoverageReificationChecker_sound
      0
      (templateFormulaRename S
        (coqRestrictedPADirectOrEliminationChildInterfaceTemplate
          CoqOrEliminationRightBranchChild))
      coqRestrictedPADirectOrEliminationOpenedRightChild_succeeds)
    as [output houtput].
  exists output.
  change (templateFormulaAsPAFormula
    (templateFormulaAbstractParameterAt
      coqRestrictedPASoundnessLowerLevelParameterName 0
      (templateFormulaRename S
        (coqRestrictedPADirectOrEliminationChildInterfaceTemplate
          CoqOrEliminationRightBranchChild))) = Some output).
  exact houtput.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageRightChildCertificate.
