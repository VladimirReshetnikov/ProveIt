(**
  Reification of the fixed opened Eq-E coverage source.

  The aggregate source is deliberately reconstructed from isolated leaf
  certificates.  This keeps the expensive Boolean computations out of this
  proof and makes the final formula skeleton transparent to strict checking.
*)

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
  RawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageDefinitions
  RawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageReificationCaseCertificate
  RawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageReificationEqualityChildCertificate
  RawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageReificationMotiveChildCertificate.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageSourceReification.

Import PA.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateParameterAbstraction.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationSupport.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationRestrictedCertificate.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationAtomicCertificate.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationFormulaCoverageCertificate.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationRuleCoverageCertificate.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationAdmissibleCoreCertificate.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationCommonCoverageCertificate.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageDefinitions.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageReificationCaseCertificate.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageReificationEqualityChildCertificate.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageReificationMotiveChildCertificate.

(** Turn an existential leaf witness into the exact match-selected formula
    used by the explicit arithmetic source. *)
Lemma raw_equalityElimination_openedLeafFormula_reifies : forall input output,
  templateFormulaAsPAFormula
    (templateFormulaAbstractParameter
      coqRestrictedPASoundnessLowerLevelParameterName input) = Some output ->
  templateFormulaAsPAFormula
    (templateFormulaAbstractParameter
      coqRestrictedPASoundnessLowerLevelParameterName input) =
  Some (coqRestrictedPADirectEqualityEliminationOpenedLeafFormula input).
Proof.
  intros input output houtput.
  unfold coqRestrictedPADirectEqualityEliminationOpenedLeafFormula.
  now rewrite houtput.
Qed.

(** Assemble the seven common implications and the paired recursive-child
    result without reevaluating any of their reification checkers. *)
Lemma coqRestrictedPADirectEqualityEliminationOpenedCoverageSource_reifies :
  templateFormulaAsPAFormula
    coqRestrictedPADirectEqualityEliminationOpenedCoverageSourceBodyTemplate =
  Some coqRestrictedPADirectEqualityEliminationOpenedCoverageSourceBodyFormula.
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
  destruct coqRestrictedPADirectEqualityEliminationOpenedCase_reifies
    as [case hcase].
  destruct coqRestrictedPADirectEqualityEliminationOpenedEqualityChild_reifies
    as [equalityChild hequalityChild].
  destruct coqRestrictedPADirectEqualityEliminationOpenedMotiveChild_reifies
    as [motiveChild hmotiveChild].
  pose proof (raw_equalityElimination_openedLeafFormula_reifies
    _ _ hrestricted) as hrestrictedExact.
  pose proof (raw_equalityElimination_openedLeafFormula_reifies
    _ _ hatomic) as hatomicExact.
  pose proof (raw_equalityElimination_openedLeafFormula_reifies
    _ _ hformulaCoverage) as hformulaCoverageExact.
  pose proof (raw_equalityElimination_openedLeafFormula_reifies
    _ _ hruleCoverage) as hruleCoverageExact.
  pose proof (raw_equalityElimination_openedLeafFormula_reifies
    _ _ hadmissibleCore) as hadmissibleCoreExact.
  pose proof (raw_equalityElimination_openedLeafFormula_reifies
    _ _ hcommonCoverage) as hcommonCoverageExact.
  pose proof (raw_equalityElimination_openedLeafFormula_reifies
    _ _ hcase) as hcaseExact.
  pose proof (raw_equalityElimination_openedLeafFormula_reifies
    _ _ hequalityChild) as hequalityChildExact.
  pose proof (raw_equalityElimination_openedLeafFormula_reifies
    _ _ hmotiveChild) as hmotiveChildExact.
  unfold
    coqRestrictedPADirectEqualityEliminationOpenedCoverageSourceBodyTemplate,
    coqRestrictedPADirectEqualityEliminationOpenedCoverageLawTemplate,
    coqRestrictedPADirectEqualityEliminationChildInterfacesTemplate,
    coqRestrictedPADirectEqualityEliminationOpenedCoverageSourceBodyFormula.
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
                             coqRestrictedPADirectEqualityEliminationEqualityChildInterfaceTemplate)
                           (templateFormulaRename S
                             coqRestrictedPADirectEqualityEliminationMotiveChildInterfaceTemplate))) =
                     Some
                       (pAnd
                         coqRestrictedPADirectEqualityEliminationOpenedEqualityChildBodyFormula
                         coqRestrictedPADirectEqualityEliminationOpenedMotiveChildBodyFormula)).
                     eapply templateFormulaAsPAFormula_abstract_and_success.
                     +++ exact hequalityChildExact.
                     +++ exact hmotiveChildExact.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageSourceReification.
