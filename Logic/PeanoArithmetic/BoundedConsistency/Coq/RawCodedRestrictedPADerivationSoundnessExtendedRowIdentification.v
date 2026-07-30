(**
  Native successor-row identification inside the extended soundness inputs.

  Slots zero and one of the shared direct translator remain the restricted
  soundness context/conclusion predicates.  The concrete tail installed here
  places the Sigma row's lower-Pi application in slot two and the Pi row's
  lower-Sigma application in slot three.  Both rows use the same two named
  hierarchy numeral parameters as the soundness template.

  The proof deliberately reuses the established lower-application
  compatibility theorem.  A temporary single-selector numeral package is
  needed only to expose that theorem's selector-independent term syntax; its
  parameters are literally the shared parameter record.  The actual row
  formula is always translated by the four-family extended input record.
*)

From Stdlib Require Import List Arith.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedNumeralTermCode
  RawCodedFormulaOperations
  RawCodedFormulaOperationCrossTraceFunctionality
  RawCodedTemplateSyntax
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateNumeralParameters
  RawCodedTemplateTernaryApplication
  RawCodedTemplateProjectionSchemas
  RawCodedDynamicTruthFixedSyntaxFragments
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedDynamicTruthTemplateNumeralParameters
  RawCodedDynamicTruthTemplateDirectInputs
  RawCodedDynamicTruthUniversalLeafSourceTemplate
  RawCodedDynamicTruthPiUniversalLeafSourceTemplate
  RawCodedDynamicTruthPiTemplateDirectInputs
  RawCodedDynamicTruthSigmaDomainProjectionProofCompilation
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs
  RawCodedRestrictedPADerivationSoundnessExtendedDirectInputs.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessExtendedRowIdentification.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaOperationCrossTraceFunctionality.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTemplateProjectionSchemas.
Import PABoundedRawCodedDynamicTruthFixedSyntaxFragments.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthTemplateNumeralParameters.
Import PABoundedRawCodedDynamicTruthTemplateDirectInputs.
Import PABoundedRawCodedDynamicTruthUniversalLeafSourceTemplate.
Import PABoundedRawCodedDynamicTruthPiUniversalLeafSourceTemplate.
Import PABoundedRawCodedDynamicTruthPiTemplateDirectInputs.
Import
  PABoundedRawCodedDynamicTruthSigmaDomainProjectionProofCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessExtendedDirectInputs.

Section SharedRows.

Context (M : RawPAModel) (hPA : RawPASatisfies M).
Context (parameters : RawCodedTemplateNumeralParameters M).
Context (contextTruth conclusionTruth :
  RawCoqRestrictedPATruthDirectSelector M parameters).
Context (lowerLevel upperLevel lowerPiCode lowerSigmaCode : M).
Context
  (lowerPiSelector :
    RawCodedTernaryApplicationSelector M lowerPiCode)
  (lowerSigmaSelector :
    RawCodedTernaryApplicationSelector M lowerSigmaCode).
Context
  (lowerPiCommuting :
    RawCoqDynamicTruthTemplateTernaryCommutingOnSyntax
      M lowerPiCode lowerPiSelector)
  (lowerSigmaCommuting :
    RawCoqDynamicTruthTemplateTernaryCommutingOnSyntax
      M lowerSigmaCode lowerSigmaSelector).
Context
  (lowerBound : rawNumeralTemplateParameterBound parameters
    coqDynamicTruthLowerLevelParameterName = lowerLevel)
  (upperBound : rawNumeralTemplateParameterBound parameters
    coqDynamicTruthUpperLevelParameterName = upperLevel).

Definition rawCoqRestrictedPAExtendedRowsTail :=
  rawCoqRestrictedPATernaryPairTailDirectSelector
    M hPA parameters lowerPiCode lowerSigmaCode
    lowerPiSelector lowerSigmaSelector
    lowerPiCommuting lowerSigmaCommuting.

Definition rawCoqRestrictedPAExtendedRowsInputs :=
  rawCoqRestrictedPADerivationSoundnessExtendedDirectStructuralInputs
    M hPA parameters contextTruth conclusionTruth
    rawCoqRestrictedPAExtendedRowsTail.

(** Single-selector packages used only by the already proved relational
    compatibility lemmas.  Their term translations coincide with the shared
    input translation because both carry [parameters]. *)
Definition rawCoqRestrictedPAExtendedRowsLowerPiPackage :=
  rawCoqDynamicTruthTemplateNumeralTermPackage M hPA
    lowerLevel upperLevel
    (rawCoqDynamicTruthTemplateOpaqueCode lowerPiSelector)
    parameters lowerBound upperBound.

Definition rawCoqRestrictedPAExtendedRowsLowerSigmaPackage :=
  rawCoqDynamicTruthTemplateNumeralTermPackage M hPA
    lowerLevel upperLevel
    (rawCoqDynamicTruthTemplateOpaqueCode lowerSigmaSelector)
    parameters lowerBound upperBound.

Lemma rawCoqRestrictedPAExtendedRows_upper_term : forall upperNumeral,
  rawNumeralTemplateParameterCode parameters
    coqDynamicTruthUpperLevelParameterName = upperNumeral ->
  rawDirectTemplateTerm rawCoqRestrictedPAExtendedRowsInputs
    coqDynamicTruthUpperLevelTerm = upperNumeral.
Proof.
  intros upperNumeral hupperCode.
  unfold rawCoqRestrictedPAExtendedRowsInputs.
  rewrite
    rawCoqRestrictedPADerivationSoundnessExtendedDirectTerm_view.
  unfold coqDynamicTruthUpperLevelTerm,
    rawCoqRestrictedPADerivationSoundnessTemplateTermView,
    rawCoqRestrictedPADerivationSoundnessTermViewSymbols.
  cbn [rawStructuralTemplateTermWith rawNumeralTemplateSymbols].
  exact hupperCode.
Qed.

Lemma rawCoqRestrictedPAExtendedRows_embed_formula : forall formula,
  rawDirectTemplateFormula rawCoqRestrictedPAExtendedRowsInputs
    (embedPAFormula formula) = rawQuotedFormulaCode M formula.
Proof.
  intro formula.
  unfold rawDirectTemplateFormula.
  apply rawStructuralTemplateFormulaWith_embedPA.
Qed.

Lemma rawCoqRestrictedPAExtendedRows_sigma_domain_trace : forall
    upperNumeral,
  rawNumeralTemplateParameterCode parameters
    coqDynamicTruthUpperLevelParameterName = upperNumeral ->
  RawCodedFormulaSingleSubstitution M upperNumeral
    (rawNumeralValue M
      (formulaCode dynamicTruthSigmaRowDomainTemplate))
    (rawDirectTemplateFormula rawCoqRestrictedPAExtendedRowsInputs
      coqDynamicTruthSigmaDomainLeafTemplate).
Proof.
  intros upperNumeral hupperCode.
  pose proof (rawDirectTemplateFormula_open M hPA
    rawCoqRestrictedPAExtendedRowsInputs
    (embedPAFormula dynamicTruthSigmaRowDomainTemplate)
    coqDynamicTruthUpperLevelTerm) as hopen.
  change (RawCodedFormulaSingleSubstitution M
    (rawDirectTemplateTerm rawCoqRestrictedPAExtendedRowsInputs
      coqDynamicTruthUpperLevelTerm)
    (rawDirectTemplateFormula rawCoqRestrictedPAExtendedRowsInputs
      (embedPAFormula dynamicTruthSigmaRowDomainTemplate))
    (rawDirectTemplateFormula rawCoqRestrictedPAExtendedRowsInputs
      coqDynamicTruthSigmaDomainLeafTemplate)) in hopen.
  rewrite (rawCoqRestrictedPAExtendedRows_upper_term
    upperNumeral hupperCode) in hopen.
  rewrite rawCoqRestrictedPAExtendedRows_embed_formula in hopen.
  rewrite rawQuotedFormulaCode_standard in hopen by exact hPA.
  exact hopen.
Qed.

Lemma rawCoqRestrictedPAExtendedRows_pi_domain_trace : forall
    upperNumeral,
  rawNumeralTemplateParameterCode parameters
    coqDynamicTruthUpperLevelParameterName = upperNumeral ->
  RawCodedFormulaSingleSubstitution M upperNumeral
    (rawNumeralValue M
      (formulaCode dynamicTruthPiRowDomainTemplate))
    (rawDirectTemplateFormula rawCoqRestrictedPAExtendedRowsInputs
      coqDynamicTruthPiDomainLeafTemplate).
Proof.
  intros upperNumeral hupperCode.
  pose proof (rawDirectTemplateFormula_open M hPA
    rawCoqRestrictedPAExtendedRowsInputs
    (embedPAFormula dynamicTruthPiRowDomainTemplate)
    coqDynamicTruthPiUpperLevelTerm) as hopen.
  change (RawCodedFormulaSingleSubstitution M
    (rawDirectTemplateTerm rawCoqRestrictedPAExtendedRowsInputs
      coqDynamicTruthUpperLevelTerm)
    (rawDirectTemplateFormula rawCoqRestrictedPAExtendedRowsInputs
      (embedPAFormula dynamicTruthPiRowDomainTemplate))
    (rawDirectTemplateFormula rawCoqRestrictedPAExtendedRowsInputs
      coqDynamicTruthPiDomainLeafTemplate)) in hopen.
  rewrite (rawCoqRestrictedPAExtendedRows_upper_term
    upperNumeral hupperCode) in hopen.
  rewrite rawCoqRestrictedPAExtendedRows_embed_formula in hopen.
  rewrite rawQuotedFormulaCode_standard in hopen by exact hPA.
  exact hopen.
Qed.

(** Exact code selected at each relocated opaque leaf. *)
Lemma rawCoqRestrictedPAExtendedRows_lowerPi_atom_code :
  rawDirectTemplateFormula rawCoqRestrictedPAExtendedRowsInputs
    (coqDynamicTruthLowerPiAtomTemplateAt
      coqRestrictedPALowerPiTruthPredicateName) =
  rawTernaryApplicationOutput lowerPiSelector
    (rawTermVarCode M (rawNumeralValue M 9))
    (rawTermVarCode M (rawNumeralValue M 1))
    (rawTermVarCode M (rawNumeralValue M 0)).
Proof.
  etransitivity.
  - apply
      rawCoqRestrictedPADerivationSoundnessExtendedTailLeaf_view.
  - reflexivity.
Qed.

Lemma rawCoqRestrictedPAExtendedRows_lowerSigma_atom_code :
  rawDirectTemplateFormula rawCoqRestrictedPAExtendedRowsInputs
    (coqDynamicTruthLowerSigmaAtomTemplateAt
      coqRestrictedPALowerSigmaTruthPredicateName) =
  rawTernaryApplicationOutput lowerSigmaSelector
    (rawTermVarCode M (rawNumeralValue M 9))
    (rawTermVarCode M (rawNumeralValue M 1))
    (rawTermVarCode M (rawNumeralValue M 0)).
Proof.
  etransitivity.
  - apply
      rawCoqRestrictedPADerivationSoundnessExtendedTailLeaf_view.
  - reflexivity.
Qed.

Lemma rawCoqRestrictedPAExtendedRows_lowerPi_identified : forall
    lowerApplication,
  RawDynamicTruthCoqLowerApplication M lowerPiCode lowerApplication ->
  rawDirectTemplateFormula rawCoqRestrictedPAExtendedRowsInputs
    (coqDynamicTruthLowerPiAtomTemplateAt
      coqRestrictedPALowerPiTruthPredicateName) = lowerApplication.
Proof.
  intros lowerApplication hlowerApplication.
  rewrite rawCoqRestrictedPAExtendedRows_lowerPi_atom_code.
  exact (raw_dynamicTruthCoqLowerApplication_functional M hPA
    lowerPiCode
    (rawTernaryApplicationOutput lowerPiSelector
      (rawTermVarCode M (rawNumeralValue M 9))
      (rawTermVarCode M (rawNumeralValue M 1))
      (rawTermVarCode M (rawNumeralValue M 0)))
    lowerApplication
    (rawCoqDynamicTruthLowerApplicationCompatibility_holds
      M hPA lowerLevel upperLevel lowerPiCode lowerPiSelector
      rawCoqRestrictedPAExtendedRowsLowerPiPackage)
    hlowerApplication).
Qed.

Lemma rawCoqRestrictedPAExtendedRows_lowerSigma_identified : forall
    lowerApplication,
  RawDynamicTruthPiCoqLowerApplication M
    lowerSigmaCode lowerApplication ->
  rawDirectTemplateFormula rawCoqRestrictedPAExtendedRowsInputs
    (coqDynamicTruthLowerSigmaAtomTemplateAt
      coqRestrictedPALowerSigmaTruthPredicateName) = lowerApplication.
Proof.
  intros lowerApplication hlowerApplication.
  rewrite rawCoqRestrictedPAExtendedRows_lowerSigma_atom_code.
  exact (raw_dynamicTruthPiCoqLowerApplication_functional M hPA
    lowerSigmaCode
    (rawTernaryApplicationOutput lowerSigmaSelector
      (rawTermVarCode M (rawNumeralValue M 9))
      (rawTermVarCode M (rawNumeralValue M 1))
      (rawTermVarCode M (rawNumeralValue M 0)))
    lowerApplication
    (rawCoqDynamicTruthPiLowerApplicationCompatibility_holds
      M hPA lowerLevel upperLevel lowerSigmaCode lowerSigmaSelector
      rawCoqRestrictedPAExtendedRowsLowerSigmaPackage)
    hlowerApplication).
Qed.

(** Direct row polynomials for the relocated leaves. *)
Lemma rawCoqRestrictedPAExtendedRows_sigma_branches :
  rawDirectTemplateFormula rawCoqRestrictedPAExtendedRowsInputs
    (coqDynamicTruthSigmaBranchesTemplateAt
      coqRestrictedPALowerPiTruthPredicateName) =
  rawCoqDynamicTruthSigmaBranchesTemplateCode M
    (rawDirectTemplateFormula rawCoqRestrictedPAExtendedRowsInputs
      (coqDynamicTruthLowerPiAtomTemplateAt
        coqRestrictedPALowerPiTruthPredicateName)).
Proof.
  unfold coqDynamicTruthSigmaBranchesTemplateAt,
    coqDynamicTruthSigmaQfLeafTemplate,
    coqDynamicTruthSigmaImpFalseLeftLeafTemplate,
    coqDynamicTruthSigmaImpTrueRightLeafTemplate,
    coqDynamicTruthSigmaAndLeafTemplate,
    coqDynamicTruthSigmaOrLeafTemplate,
    coqDynamicTruthSigmaExLeafTemplate,
    coqDynamicTruthSigmaUniversalLeafTemplateAt,
    coqDynamicTruthSigmaUniversalPrefixTemplate,
    coqDynamicTruthSigmaNoBinderCounterexampleTemplateAt,
    coqDynamicTruthSigmaBinderPrependTemplate,
    rawCoqDynamicTruthSigmaBranchesTemplateCode,
    rawCoqDynamicTruthSigmaUniversalLeafTemplateCode.
  cbn [templateRepeatedExists rawDirectTemplateFormula
    rawStructuralTemplateFormulaWith].
  reflexivity.
Qed.

Lemma rawCoqRestrictedPAExtendedRows_pi_branches :
  rawDirectTemplateFormula rawCoqRestrictedPAExtendedRowsInputs
    (coqDynamicTruthPiBranchesTemplateAt
      coqRestrictedPALowerSigmaTruthPredicateName) =
  rawCoqDynamicTruthPiBranchesTemplateCode M
    (rawDirectTemplateFormula rawCoqRestrictedPAExtendedRowsInputs
      (coqDynamicTruthLowerSigmaAtomTemplateAt
        coqRestrictedPALowerSigmaTruthPredicateName)).
Proof.
  unfold coqDynamicTruthPiBranchesTemplateAt,
    coqDynamicTruthPiQfLeafTemplate,
    coqDynamicTruthPiImpLeafTemplate,
    coqDynamicTruthPiAndLeafTemplate,
    coqDynamicTruthPiOrLeafTemplate,
    coqDynamicTruthPiAllLeafTemplate,
    coqDynamicTruthPiExistentialLeafTemplateAt,
    coqDynamicTruthPiExistentialPrefixTemplate,
    coqDynamicTruthPiNoBinderCounterexampleTemplateAt,
    coqDynamicTruthPiBinderPrependTemplate,
    rawCoqDynamicTruthPiBranchesTemplateCode,
    rawCoqDynamicTruthPiExistentialLeafTemplateCode.
  cbn [templateRepeatedExists rawDirectTemplateFormula
    rawStructuralTemplateFormulaWith].
  reflexivity.
Qed.

Lemma rawCoqRestrictedPAExtendedRows_sigma_row :
  rawDirectTemplateFormula rawCoqRestrictedPAExtendedRowsInputs
    (coqDynamicTruthSigmaSuccessorRowTemplateAt
      coqRestrictedPALowerPiTruthPredicateName) =
  rawCoqDynamicTruthSigmaSuccessorRowTemplateCode M
    (rawDirectTemplateFormula rawCoqRestrictedPAExtendedRowsInputs
      coqDynamicTruthSigmaDomainLeafTemplate)
    (rawDirectTemplateFormula rawCoqRestrictedPAExtendedRowsInputs
      (coqDynamicTruthLowerPiAtomTemplateAt
        coqRestrictedPALowerPiTruthPredicateName)).
Proof.
  unfold coqDynamicTruthSigmaSuccessorRowTemplateAt,
    rawCoqDynamicTruthSigmaSuccessorRowTemplateCode.
  change (rawFormulaEx8Code M
    (rawFormulaAndCode M
      (rawDirectTemplateFormula rawCoqRestrictedPAExtendedRowsInputs
        coqDynamicTruthSigmaDomainLeafTemplate)
      (rawDirectTemplateFormula rawCoqRestrictedPAExtendedRowsInputs
        (coqDynamicTruthSigmaBranchesTemplateAt
          coqRestrictedPALowerPiTruthPredicateName))) =
    rawFormulaEx8Code M
      (rawFormulaAndCode M
        (rawDirectTemplateFormula rawCoqRestrictedPAExtendedRowsInputs
          coqDynamicTruthSigmaDomainLeafTemplate)
        (rawCoqDynamicTruthSigmaBranchesTemplateCode M
          (rawDirectTemplateFormula rawCoqRestrictedPAExtendedRowsInputs
            (coqDynamicTruthLowerPiAtomTemplateAt
              coqRestrictedPALowerPiTruthPredicateName))))).
  rewrite rawCoqRestrictedPAExtendedRows_sigma_branches.
  reflexivity.
Qed.

Lemma rawCoqRestrictedPAExtendedRows_pi_row :
  rawDirectTemplateFormula rawCoqRestrictedPAExtendedRowsInputs
    (coqDynamicTruthPiSuccessorRowTemplateAt
      coqRestrictedPALowerSigmaTruthPredicateName) =
  rawCoqDynamicTruthPiSuccessorRowTemplateCode M
    (rawDirectTemplateFormula rawCoqRestrictedPAExtendedRowsInputs
      coqDynamicTruthPiDomainLeafTemplate)
    (rawDirectTemplateFormula rawCoqRestrictedPAExtendedRowsInputs
      (coqDynamicTruthLowerSigmaAtomTemplateAt
        coqRestrictedPALowerSigmaTruthPredicateName)).
Proof.
  unfold coqDynamicTruthPiSuccessorRowTemplateAt,
    rawCoqDynamicTruthPiSuccessorRowTemplateCode.
  change (rawDynamicTruthPiFormulaEx8Code M
    (rawFormulaAndCode M
      (rawDirectTemplateFormula rawCoqRestrictedPAExtendedRowsInputs
        coqDynamicTruthPiDomainLeafTemplate)
      (rawDirectTemplateFormula rawCoqRestrictedPAExtendedRowsInputs
        (coqDynamicTruthPiBranchesTemplateAt
          coqRestrictedPALowerSigmaTruthPredicateName))) =
    rawDynamicTruthPiFormulaEx8Code M
      (rawFormulaAndCode M
        (rawDirectTemplateFormula rawCoqRestrictedPAExtendedRowsInputs
          coqDynamicTruthPiDomainLeafTemplate)
        (rawCoqDynamicTruthPiBranchesTemplateCode M
          (rawDirectTemplateFormula rawCoqRestrictedPAExtendedRowsInputs
            (coqDynamicTruthLowerSigmaAtomTemplateAt
              coqRestrictedPALowerSigmaTruthPredicateName))))).
  rewrite rawCoqRestrictedPAExtendedRows_pi_branches.
  reflexivity.
Qed.

Theorem raw_coqRestrictedPAExtendedRows_identify_native : forall
    upperNumeral sigmaDomain piDomain
    sigmaLowerApplication piLowerApplication,
  rawNumeralTemplateParameterCode parameters
    coqDynamicTruthUpperLevelParameterName = upperNumeral ->
  RawCodedFormulaSingleSubstitution M upperNumeral
    (rawNumeralValue M
      (formulaCode dynamicTruthSigmaRowDomainTemplate)) sigmaDomain ->
  RawCodedFormulaSingleSubstitution M upperNumeral
    (rawNumeralValue M
      (formulaCode dynamicTruthPiRowDomainTemplate)) piDomain ->
  RawDynamicTruthCoqLowerApplication M
    lowerPiCode sigmaLowerApplication ->
  RawDynamicTruthPiCoqLowerApplication M
    lowerSigmaCode piLowerApplication ->
  rawDirectTemplateFormula rawCoqRestrictedPAExtendedRowsInputs
    (coqDynamicTruthSigmaSuccessorRowTemplateAt
      coqRestrictedPALowerPiTruthPredicateName) =
    rawDynamicTruthSigmaSuccessorRowCode M
      sigmaDomain sigmaLowerApplication /\
  rawDirectTemplateFormula rawCoqRestrictedPAExtendedRowsInputs
    (coqDynamicTruthPiSuccessorRowTemplateAt
      coqRestrictedPALowerSigmaTruthPredicateName) =
    rawDynamicTruthPiSuccessorRowCode M
      piDomain piLowerApplication.
Proof.
  intros upperNumeral sigmaDomain piDomain
    sigmaLowerApplication piLowerApplication
    hupperCode hsigmaDomain hpiDomain
    hsigmaLower hpiLower.
  pose proof (raw_codedFormulaSingleSubstitution_functional M hPA
    upperNumeral
    (rawNumeralValue M
      (formulaCode dynamicTruthSigmaRowDomainTemplate))
    (rawDirectTemplateFormula rawCoqRestrictedPAExtendedRowsInputs
      coqDynamicTruthSigmaDomainLeafTemplate)
    sigmaDomain
    (rawCoqRestrictedPAExtendedRows_sigma_domain_trace
      upperNumeral hupperCode)
    hsigmaDomain) as hsigmaDomainCode.
  pose proof (raw_codedFormulaSingleSubstitution_functional M hPA
    upperNumeral
    (rawNumeralValue M
      (formulaCode dynamicTruthPiRowDomainTemplate))
    (rawDirectTemplateFormula rawCoqRestrictedPAExtendedRowsInputs
      coqDynamicTruthPiDomainLeafTemplate)
    piDomain
    (rawCoqRestrictedPAExtendedRows_pi_domain_trace
      upperNumeral hupperCode)
    hpiDomain) as hpiDomainCode.
  split.
  - rewrite rawCoqRestrictedPAExtendedRows_sigma_row.
    rewrite hsigmaDomainCode.
    rewrite (rawCoqRestrictedPAExtendedRows_lowerPi_identified
      sigmaLowerApplication hsigmaLower).
    apply rawCoqDynamicTruthSigmaSuccessorRowTemplateCode_eq_native.
    exact hPA.
  - rewrite rawCoqRestrictedPAExtendedRows_pi_row.
    rewrite hpiDomainCode.
    rewrite (rawCoqRestrictedPAExtendedRows_lowerSigma_identified
      piLowerApplication hpiLower).
    apply rawCoqDynamicTruthPiSuccessorRowTemplateCode_eq_native.
    exact hPA.
Qed.

End SharedRows.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessExtendedRowIdentification.
