(** Reification of the fixed opened Or-E coverage source. *)

From PAHF Require Import PAHF.
From BoundedPAConsistency Require Import
  RawCodedTemplateSyntax
  RawCodedTemplateParameterAbstraction
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationSupport
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationRestrictedCertificate
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationAtomicCertificate
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationFormulaCoverageCertificate
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationRuleCoverageCertificate
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationAdmissibleCoreCertificate
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationCommonCoverageCertificate
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageDefinitions
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageCaseCertificate
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageDisjunctionChildCertificate
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageLeftChildCertificate
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageRightChildCertificate.

Module PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageSourceReification.

Import PA.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateParameterAbstraction.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationSupport.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationRestrictedCertificate.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationAtomicCertificate.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationFormulaCoverageCertificate.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationRuleCoverageCertificate.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationAdmissibleCoreCertificate.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationCommonCoverageCertificate.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageDefinitions.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageCaseCertificate.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageDisjunctionChildCertificate.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageLeftChildCertificate.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageRightChildCertificate.

(** ------------------------------------------------------------------
    PA reification and direct-code agreement.  The source definitions and
    all four computational leaf certificates are imported above, so this
    module performs only the small opaque-equation assembly. *)

Lemma raw_orElimination_openedLeafFormula_reifies : forall input output,
  templateFormulaAsPAFormula
    (templateFormulaAbstractParameter
      coqRestrictedPASoundnessLowerLevelParameterName input) = Some output ->
  templateFormulaAsPAFormula
    (templateFormulaAbstractParameter
      coqRestrictedPASoundnessLowerLevelParameterName input) =
  Some (coqRestrictedPADirectOrEliminationOpenedLeafFormula input).
Proof.
  intros input output houtput.
  unfold coqRestrictedPADirectOrEliminationOpenedLeafFormula.
  now rewrite houtput.
Qed.

Lemma coqRestrictedPADirectOrEliminationOpenedCoverageSource_reifies :
  templateFormulaAsPAFormula
    coqRestrictedPADirectOrEliminationOpenedCoverageSourceBodyTemplate =
  Some coqRestrictedPADirectOrEliminationOpenedCoverageSourceBodyFormula.
Proof.
  destruct coqRestrictedPADirectAndIntroductionOpenedRestricted_reifies
    as [restricted hrestricted].
  destruct coqRestrictedPADirectAndIntroductionOpenedAtomic_reifies
    as [atomic hatomic].
  destruct coqRestrictedPADirectAndIntroductionOpenedFormulaCoverage_reifies
    as [formulaCoverage hformulaCoverage].
  destruct coqRestrictedPADirectAndIntroductionOpenedRuleCoverage_reifies
    as [ruleCoverage hruleCoverage].
  destruct coqRestrictedPADirectAndIntroductionOpenedAdmissibleCore_reifies
    as [admissibleCore hadmissibleCore].
  destruct coqRestrictedPADirectAndIntroductionOpenedCommonCoverage_reifies
    as [commonCoverage hcommonCoverage].
  destruct coqRestrictedPADirectOrEliminationOpenedCase_reifies
    as [case hcase].
  destruct coqRestrictedPADirectOrEliminationOpenedDisjunctionChild_reifies
    as [disjunctionChild hdisjunctionChild].
  destruct coqRestrictedPADirectOrEliminationOpenedLeftChild_reifies
    as [leftChild hleftChild].
  destruct coqRestrictedPADirectOrEliminationOpenedRightChild_reifies
    as [rightChild hrightChild].
  pose proof (raw_orElimination_openedLeafFormula_reifies
    _ _ hrestricted) as hrestrictedExact.
  pose proof (raw_orElimination_openedLeafFormula_reifies
    _ _ hatomic) as hatomicExact.
  pose proof (raw_orElimination_openedLeafFormula_reifies
    _ _ hformulaCoverage) as hformulaCoverageExact.
  pose proof (raw_orElimination_openedLeafFormula_reifies
    _ _ hruleCoverage) as hruleCoverageExact.
  pose proof (raw_orElimination_openedLeafFormula_reifies
    _ _ hadmissibleCore) as hadmissibleCoreExact.
  pose proof (raw_orElimination_openedLeafFormula_reifies
    _ _ hcommonCoverage) as hcommonCoverageExact.
  pose proof (raw_orElimination_openedLeafFormula_reifies
    _ _ hcase) as hcaseExact.
  pose proof (raw_orElimination_openedLeafFormula_reifies
    _ _ hdisjunctionChild) as hdisjunctionChildExact.
  pose proof (raw_orElimination_openedLeafFormula_reifies
    _ _ hleftChild) as hleftChildExact.
  pose proof (raw_orElimination_openedLeafFormula_reifies
    _ _ hrightChild) as hrightChildExact.
  unfold coqRestrictedPADirectOrEliminationOpenedCoverageSourceBodyTemplate,
    coqRestrictedPADirectOrEliminationOpenedCoverageLawTemplate,
    coqRestrictedPADirectOrEliminationChildInterfacesTemplate,
    coqRestrictedPADirectOrEliminationOpenedCoverageSourceBodyFormula.
  eapply templateFormulaAsPAFormula_abstract_imp_success.
  - exact hrestrictedExact.
  - eapply templateFormulaAsPAFormula_abstract_imp_success.
    + exact hatomicExact.
    + eapply templateFormulaAsPAFormula_abstract_imp_success.
      * exact hformulaCoverageExact.
      * eapply templateFormulaAsPAFormula_abstract_imp_success.
        -- exact hruleCoverageExact.
        -- eapply templateFormulaAsPAFormula_abstract_imp_success.
           ++ exact hadmissibleCoreExact.
           ++ eapply templateFormulaAsPAFormula_abstract_imp_success.
              ** exact hcommonCoverageExact.
              ** eapply templateFormulaAsPAFormula_abstract_imp_success.
                 --- exact hcaseExact.
                 --- change (templateFormulaAsPAFormula
                       (templateFormulaAbstractParameter
                         coqRestrictedPASoundnessLowerLevelParameterName
                         (tfAnd
                           (templateFormulaRename S
                             (coqRestrictedPADirectOrEliminationChildInterfaceTemplate
                               CoqOrEliminationDisjunctionChild))
                           (tfAnd
                             (templateFormulaRename S
                               (coqRestrictedPADirectOrEliminationChildInterfaceTemplate
                                 CoqOrEliminationLeftBranchChild))
                             (templateFormulaRename S
                               (coqRestrictedPADirectOrEliminationChildInterfaceTemplate
                                 CoqOrEliminationRightBranchChild))))) =
                     Some
                       (pAnd
                         coqRestrictedPADirectOrEliminationOpenedDisjunctionChildFormula
                         (pAnd
                           coqRestrictedPADirectOrEliminationOpenedLeftChildFormula
                           coqRestrictedPADirectOrEliminationOpenedRightChildFormula))).
                     eapply templateFormulaAsPAFormula_abstract_and_success.
                     +++ exact hdisjunctionChildExact.
                     +++ eapply
                           templateFormulaAsPAFormula_abstract_and_success.
                         *** exact hleftChildExact.
                         *** exact hrightChildExact.
Qed.

End PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageSourceReification.
