(** Isolated PA-reification certificate for the Or-E left branch child. *)

From BoundedPAConsistency Require Import
  RawCodedTemplateSyntax
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationSupport
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageDefinitions.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageLeftChildCertificate.

Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationSupport.
Import PABoundedRawCodedTemplateSyntax.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageDefinitions.

Theorem coqRestrictedPADirectOrEliminationOpenedLeftChild_succeeds :
  coqRestrictedPADirectAndIntroductionOpenedCoverageReificationChecker
    (templateFormulaRename S
      (coqRestrictedPADirectOrEliminationChildInterfaceTemplate
        CoqOrEliminationLeftBranchChild)) = true.
Proof.
  unfold
    coqRestrictedPADirectAndIntroductionOpenedCoverageReificationChecker.
  rewrite templateFormulaHasPAReificationAfterAbstracting_rename.
  vm_compute. reflexivity.
Qed.

Theorem coqRestrictedPADirectOrEliminationOpenedLeftChild_reifies :
  exists output,
    templateFormulaAsPAFormula
      (templateFormulaAbstractParameter
        coqRestrictedPASoundnessLowerLevelParameterName
        (templateFormulaRename S
          (coqRestrictedPADirectOrEliminationChildInterfaceTemplate
            CoqOrEliminationLeftBranchChild))) = Some output.
Proof.
  destruct
    (coqRestrictedPADirectAndIntroductionOpenedCoverageReificationChecker_sound
      0
      (templateFormulaRename S
        (coqRestrictedPADirectOrEliminationChildInterfaceTemplate
          CoqOrEliminationLeftBranchChild))
      coqRestrictedPADirectOrEliminationOpenedLeftChild_succeeds)
    as [output houtput].
  exists output.
  change (templateFormulaAsPAFormula
    (templateFormulaAbstractParameterAt
      coqRestrictedPASoundnessLowerLevelParameterName 0
      (templateFormulaRename S
        (coqRestrictedPADirectOrEliminationChildInterfaceTemplate
          CoqOrEliminationLeftBranchChild))) = Some output).
  exact houtput.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageLeftChildCertificate.
