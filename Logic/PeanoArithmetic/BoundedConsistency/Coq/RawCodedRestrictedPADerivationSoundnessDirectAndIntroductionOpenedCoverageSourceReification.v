(** Reification of the fixed opened And-I coverage source. *)

From BoundedPAConsistency Require Import
  RawCodedTemplateParameterAbstraction
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationSupport
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationRestrictedCertificate
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationAtomicCertificate
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationFormulaCoverageCertificate
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationRuleCoverageCertificate
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationAdmissibleCoreCertificate
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationCommonCoverageCertificate
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationCaseCertificate
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationLeftResultCertificate
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationRightResultCertificate
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageSourceDefinitions.

Module PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageSourceReification.

Import PABoundedRawCodedTemplateParameterAbstraction.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationSupport.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationRestrictedCertificate.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationAtomicCertificate.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationFormulaCoverageCertificate.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationRuleCoverageCertificate.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationAdmissibleCoreCertificate.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationCommonCoverageCertificate.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationCaseCertificate.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationLeftResultCertificate.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationRightResultCertificate.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageSourceDefinitions.

Lemma coqRestrictedPADirectAndIntroductionOpenedCoverageSource_reifies :
  templateFormulaAsPAFormula
    coqRestrictedPADirectAndIntroductionOpenedCoverageSourceBodyTemplate =
  Some
    coqRestrictedPADirectAndIntroductionOpenedCoverageSourceBodyFormula.
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
  destruct coqRestrictedPADirectAndIntroductionOpenedCase_reifies
    as [case hcase].
  destruct coqRestrictedPADirectAndIntroductionOpenedLeftResult_reifies
    as [leftResult hleftResult].
  destruct coqRestrictedPADirectAndIntroductionOpenedRightResult_reifies
    as [rightResult hrightResult].

  (** Each large component is opaque at this point.  The only remaining
      computation is the eight-node implication/conjunction skeleton, so
      composing the component equations cannot reopen any certificate. *)
  assert (hlaw : exists output,
    templateFormulaAsPAFormula
      (templateFormulaAbstractParameter
        coqRestrictedPASoundnessLowerLevelParameterName
        coqRestrictedPADirectAndIntroductionOpenedCoverageCompilerLawTemplate) =
    Some output).
  {
    unfold
      coqRestrictedPADirectAndIntroductionOpenedCoverageCompilerLawTemplate.
    eexists.
    eapply templateFormulaAsPAFormula_abstract_imp_success.
    - exact hrestricted.
    - eapply templateFormulaAsPAFormula_abstract_imp_success.
      + exact hatomic.
      + eapply templateFormulaAsPAFormula_abstract_imp_success.
        * exact hformulaCoverage.
        * eapply templateFormulaAsPAFormula_abstract_imp_success.
          -- exact hruleCoverage.
          -- eapply templateFormulaAsPAFormula_abstract_imp_success.
             ++ exact hadmissibleCore.
             ++ eapply templateFormulaAsPAFormula_abstract_imp_success.
                ** exact hcommonCoverage.
                ** eapply templateFormulaAsPAFormula_abstract_imp_success.
                   --- exact hcase.
                   --- eapply templateFormulaAsPAFormula_abstract_and_success.
                       +++ exact hleftResult.
                       +++ exact hrightResult.
  }
  destruct hlaw as [output houtput].
  change (templateFormulaAsPAFormula
    coqRestrictedPADirectAndIntroductionOpenedCoverageSourceBodyTemplate =
    Some output) in houtput.
  unfold
    coqRestrictedPADirectAndIntroductionOpenedCoverageSourceBodyFormula.
  now rewrite houtput.
Qed.

End PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageSourceReification.
