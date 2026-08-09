(**
  Correct the numeral-parameter namespace for canonical Sigma/Or rows.

  [coqDynamicTruthParameterSelect] was intentionally designed for templates
  mentioning only hierarchy names zero and one: every successor name maps to
  the upper-level numeral.  Once append names two through five are placed in
  the same translation, that fallback aliases row mode (name two) with the
  upper hierarchy level (name one).  At the first successor those values must
  be zero and one respectively, so that selector cannot identify the shared
  production with the canonical rank-zero production.

  This module provides the minimal corrected selector: name one denotes the
  upper numeral one and every other name denotes zero.  It then constructs a
  direct structural translation whose two shared opaque row predicates are
  the canonical global base predicates.  The existing native-row
  identification theorem proves all three atomic equalities isolated by
  [RawCodedDynamicTruthSigmaOrCanonicalProductionIdentification], hence the
  complete carrier-code equality follows without an assumed bridge.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedNumeralTermCode
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedFormulaOperationsStandardRealization
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplatePAEmbedding
  RawCodedTemplateNumeralParameters
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedTemplateTernaryApplication
  RawCodedTernaryPredicateDeepClosure
  RawCodedDynamicTruthTemplateNumeralParameters
  RawCodedDynamicTruthUniversalLeafSourceTemplate
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedDynamicTruthPairedGlobalSuccessorGraph
  RawCodedDynamicTruthGlobalBaseRootClosure
  RawCodedDynamicTruthSuccessorRowsAppendNormalization
  RawCodedFourStateTableAppendRowLtSuccCases
  RawCodedFourStateTableAppendGlobalTraversalAssembly
  RawCodedRestrictedPADerivationSoundnessExtendedRowIdentification
  RawCodedTemplateBottomDirectStructuralInputs
  RawCodedDynamicTruthSigmaOrFixedProductionAppendIntegration
  RawCodedDynamicTruthSigmaOrCanonicalProductionIdentification.

Module
  PABoundedRawCodedDynamicTruthSigmaOrCanonicalTranslationCorrection.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedFormulaOperationsStandardRealization.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTernaryPredicateDeepClosure.
Import PABoundedRawCodedDynamicTruthTemplateNumeralParameters.
Import PABoundedRawCodedDynamicTruthUniversalLeafSourceTemplate.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.
Import PABoundedRawCodedDynamicTruthGlobalBaseRootClosure.
Import PABoundedRawCodedDynamicTruthSuccessorRowsAppendNormalization.
Import PABoundedRawCodedFourStateTableAppendRowLtSuccCases.
Import PABoundedRawCodedFourStateTableAppendGlobalTraversalAssembly.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessExtendedRowIdentification.
Import PABoundedRawCodedTemplateBottomDirectStructuralInputs.
Import
  PABoundedRawCodedDynamicTruthSigmaOrFixedProductionAppendIntegration.
Import
  PABoundedRawCodedDynamicTruthSigmaOrCanonicalProductionIdentification.

(** The old two-level selector aliases the append mode with the upper level.
    This is harmless only under its documented two-name scope. *)
Lemma coqDynamicTruthParameterSelect_upper_mode_collision : forall
    (A : Type) (lower upper : A),
  coqDynamicTruthParameterSelect lower upper
      coqDynamicTruthUpperLevelParameterName =
    coqDynamicTruthParameterSelect lower upper
      coqFourStateTableAppendRowModeParameterName.
Proof. reflexivity. Qed.

(** Consequently the old selector cannot realize distinct values at those
    two coordinates.  This abstract no-go result avoids relying on any
    accidental property of a particular model's term-code representation. *)
Lemma coqDynamicTruthParameterSelect_cannot_separate_upper_and_mode : forall
    (A : Type) (lower upper mode : A),
  upper <> mode ->
  ~ (coqDynamicTruthParameterSelect lower upper
        coqDynamicTruthUpperLevelParameterName = upper /\
      coqDynamicTruthParameterSelect lower upper
        coqFourStateTableAppendRowModeParameterName = mode).
Proof.
  intros A lower upper mode hne [hupper hmode].
  apply hne.
  rewrite <- hmode, <- hupper.
  apply coqDynamicTruthParameterSelect_upper_mode_collision.
Qed.

(** Name one is the sole exceptional coordinate.  Thus lower hierarchy and
    append mode both denote zero, while the row's upper hierarchy denotes
    one.  Names three through six also remain harmless closed numerals until
    the append compiler replaces their row-field occurrences. *)
Definition coqDynamicTruthSigmaOrCanonicalParameterSelect {A : Type}
    (zero one : A) (name : TemplateParameterName) : A :=
  match name with
  | 1 => one
  | _ => zero
  end.

Arguments coqDynamicTruthSigmaOrCanonicalParameterSelect {A} _ _ _.

Definition rawDynamicTruthSigmaOrCanonicalNumeralParameters
    (M : RawPAModel) (hPA : RawPASatisfies M)
    : RawCodedTemplateNumeralParameters M.
Proof.
  refine
    {| rawNumeralTemplateParameterBound :=
         coqDynamicTruthSigmaOrCanonicalParameterSelect
           (raw_zero M) (raw_succ M (raw_zero M));
       rawNumeralTemplateParameterCode :=
         coqDynamicTruthSigmaOrCanonicalParameterSelect
           (rawQuotedTermCode M (Term.numeral 0))
           (rawQuotedTermCode M (Term.numeral 1));
       rawNumeralTemplateParameter_valid := _ |}.
  intros [|[|name]].
  - exact (raw_numeralTermCodeAt_standard M hPA 0).
  - exact (raw_numeralTermCodeAt_standard M hPA 1).
  - exact (raw_numeralTermCodeAt_standard M hPA 0).
Defined.

Arguments rawDynamicTruthSigmaOrCanonicalNumeralParameters M hPA
  : clear implicits.

Lemma rawDynamicTruthSigmaOrCanonicalParameters_lower_zero : forall
    M hPA,
  rawNumeralTemplateParameterCode
      (rawDynamicTruthSigmaOrCanonicalNumeralParameters M hPA)
      coqDynamicTruthLowerLevelParameterName =
    rawQuotedTermCode M (Term.numeral 0).
Proof. reflexivity. Qed.

Lemma rawDynamicTruthSigmaOrCanonicalParameters_upper_one : forall
    M hPA,
  rawNumeralTemplateParameterCode
      (rawDynamicTruthSigmaOrCanonicalNumeralParameters M hPA)
      coqDynamicTruthUpperLevelParameterName =
    rawQuotedTermCode M (Term.numeral 1).
Proof. reflexivity. Qed.

Lemma rawDynamicTruthSigmaOrCanonicalParameters_mode_zero : forall
    M hPA,
  rawNumeralTemplateParameterCode
      (rawDynamicTruthSigmaOrCanonicalNumeralParameters M hPA)
      coqFourStateTableAppendRowModeParameterName =
    rawQuotedTermCode M (Term.numeral 0).
Proof. reflexivity. Qed.

(** A direct translation realizing the corrected namespace and the two
    canonical predecessor predicates.  The existential hides selector
    choices only after all output equalities have been proved. *)
Theorem raw_dynamicTruthSigmaOrCanonicalTranslation_exists : forall
    (M : RawPAModel) (hPA : RawPASatisfies M),
  exists inputs : RawCodedTemplateDirectStructuralInputs M,
    let translation := rawDirectStructuralTemplateTranslation M
      hPA inputs in
    RawCodedTemplatePAAgreement M translation /\
    rawTemplateTerm translation
        (ttParameter coqFourStateTableAppendRowModeParameterName) =
      rawTemplateTerm translation (embedPATerm (Term.numeral 0)) /\
    rawTemplateFormula translation
        coqDynamicTruthSharedSigmaSuccessorRowTemplate =
      rawTemplateFormula translation
        (embedPAFormula
          coqDynamicTruthSigmaOrZeroCanonicalSigmaRowFormula) /\
    rawTemplateFormula translation
        coqDynamicTruthSharedPiSuccessorRowTemplate =
      rawTemplateFormula translation
        (embedPAFormula
          coqDynamicTruthSigmaOrZeroCanonicalPiRowFormula) /\
    rawTemplateFormula translation
        (coqFourStateTableAppendNamedClosedRowProductionTemplate
          coqDynamicTruthSharedSigmaSuccessorRowTemplate
          coqDynamicTruthSharedPiSuccessorRowTemplate) =
      rawTemplateFormula translation
        (templateFormulaOpen (embedPATerm (Term.numeral 0))
          (coqFourStateTableAppendEmbeddedModeProductionMotive
            coqDynamicTruthSigmaOrZeroCanonicalSigmaRowFormula
            coqDynamicTruthSigmaOrZeroCanonicalPiRowFormula)).
Proof.
  intros M hPA.
  pose proof
    (raw_quotedFormula_ternaryPredicateDeepClosed M hPA
      dynamicTruthGlobalPiBaseFormula
      dynamicTruthGlobalPiBaseFormula_scoped) as hlowerPiDeep.
  pose proof
    (raw_quotedFormula_ternaryPredicateDeepClosed M hPA
      dynamicTruthGlobalSigmaBaseFormula
      dynamicTruthGlobalSigmaBaseFormula_scoped) as hlowerSigmaDeep.
  destruct
    (raw_coqDynamicTruthTemplateTernarySelector_exists_of_deepClosed
      M hPA (rawQuotedFormulaCode M dynamicTruthGlobalPiBaseFormula)
      hlowerPiDeep) as [lowerPiSelector lowerPiCommuting].
  destruct
    (raw_coqDynamicTruthTemplateTernarySelector_exists_of_deepClosed
      M hPA (rawQuotedFormulaCode M dynamicTruthGlobalSigmaBaseFormula)
      hlowerSigmaDeep) as [lowerSigmaSelector lowerSigmaCommuting].
  set (parameters :=
    rawDynamicTruthSigmaOrCanonicalNumeralParameters M hPA).
  set (contextTruth :=
    rawBottomRestrictedPATruthDirectSelector M hPA parameters).
  set (conclusionTruth :=
    rawBottomRestrictedPATruthDirectSelector M hPA parameters).
  set (inputs := rawCoqRestrictedPAExtendedRowsInputs
    M hPA parameters contextTruth conclusionTruth
    (rawQuotedFormulaCode M dynamicTruthGlobalPiBaseFormula)
    (rawQuotedFormulaCode M dynamicTruthGlobalSigmaBaseFormula)
    lowerPiSelector lowerSigmaSelector
    lowerPiCommuting lowerSigmaCommuting).
  set (translation := rawDirectStructuralTemplateTranslation M hPA inputs).
  pose proof (rawDirectStructuralTemplatePAAgreement M hPA inputs)
    as hagreement.

  assert (hmode : rawTemplateTerm translation
      (ttParameter coqFourStateTableAppendRowModeParameterName) =
    rawTemplateTerm translation (embedPATerm (Term.numeral 0))).
  {
    unfold translation, inputs.
    rewrite
      rawCoqRestrictedPADerivationSoundnessExtendedDirectTerm_view.
    unfold rawCoqRestrictedPADerivationSoundnessTemplateTermView,
      rawCoqRestrictedPADerivationSoundnessTermViewSymbols.
    cbn [rawStructuralTemplateTermWith rawNumeralTemplateSymbols].
    reflexivity.
  }

  set (upperNumeral := rawQuotedTermCode M (Term.numeral 1)).
  set (sigmaDomain := rawQuotedFormulaCode M
    (dynamicTruthSigmaRowInstantiatedDomain (Term.numeral 1))).
  set (piDomain := rawQuotedFormulaCode M
    (dynamicTruthPiRowInstantiatedDomain (Term.numeral 1))).
  set (sigmaLowerApplication := rawQuotedFormulaCode M
    (Formula.rename dynamicTruthCoqLowerApplicationRenaming
      dynamicTruthGlobalPiBaseFormula)).
  set (piLowerApplication := rawQuotedFormulaCode M
    (Formula.rename dynamicTruthPiCoqLowerApplicationRenaming
      dynamicTruthGlobalSigmaBaseFormula)).

  assert (hsigmaDomain : RawCodedFormulaSingleSubstitution M
      upperNumeral
      (rawNumeralValue M
        (formulaCode dynamicTruthSigmaRowDomainTemplate))
      sigmaDomain).
  {
    unfold upperNumeral, sigmaDomain.
    exact (raw_dynamicTruthSigmaRowInstantiatedDomain_standard
      M hPA (Term.numeral 1)).
  }
  assert (hpiDomain : RawCodedFormulaSingleSubstitution M
      upperNumeral
      (rawNumeralValue M
        (formulaCode dynamicTruthPiRowDomainTemplate))
      piDomain).
  {
    unfold upperNumeral, piDomain,
      dynamicTruthPiRowInstantiatedDomain.
    rewrite <- (rawQuotedTermCode_standard M hPA (Term.numeral 1)).
    rewrite <- (rawQuotedFormulaCode_standard M hPA
      dynamicTruthPiRowDomainTemplate).
    exact (raw_codedFormulaSingleSubstitution_standard M hPA
      (Term.numeral 1) dynamicTruthPiRowDomainTemplate).
  }
  assert (hsigmaLower : RawDynamicTruthCoqLowerApplication M
      (rawQuotedFormulaCode M dynamicTruthGlobalPiBaseFormula)
      sigmaLowerApplication).
  {
    unfold sigmaLowerApplication.
    exact (raw_dynamicTruthCoqLowerApplication_standard_rename
      M hPA dynamicTruthGlobalPiBaseFormula
      dynamicTruthGlobalPiBaseFormula_scoped).
  }
  assert (hpiLower : RawDynamicTruthPiCoqLowerApplication M
      (rawQuotedFormulaCode M dynamicTruthGlobalSigmaBaseFormula)
      piLowerApplication).
  {
    unfold piLowerApplication.
    exact (raw_dynamicTruthPiCoqLowerApplication_standard_rename
      M hPA dynamicTruthGlobalSigmaBaseFormula
      dynamicTruthGlobalSigmaBaseFormula_scoped).
  }
  pose proof
    (raw_coqRestrictedPAExtendedRows_identify_native
      M hPA parameters contextTruth conclusionTruth
      (raw_zero M) (raw_succ M (raw_zero M))
      (rawQuotedFormulaCode M dynamicTruthGlobalPiBaseFormula)
      (rawQuotedFormulaCode M dynamicTruthGlobalSigmaBaseFormula)
      lowerPiSelector lowerSigmaSelector
      lowerPiCommuting lowerSigmaCommuting
      eq_refl eq_refl
      upperNumeral sigmaDomain piDomain
      sigmaLowerApplication piLowerApplication
      (rawDynamicTruthSigmaOrCanonicalParameters_upper_one M hPA)
      hsigmaDomain hpiDomain hsigmaLower hpiLower) as hrows.
  destruct hrows as [hsigmaRow hpiRow].

  assert (hsigma : rawTemplateFormula translation
      coqDynamicTruthSharedSigmaSuccessorRowTemplate =
    rawTemplateFormula translation
      (embedPAFormula
        coqDynamicTruthSigmaOrZeroCanonicalSigmaRowFormula)).
  {
    unfold translation,
      coqDynamicTruthSharedSigmaSuccessorRowTemplate in *.
    rewrite (rawTemplateFormula_embedPA hagreement
      coqDynamicTruthSigmaOrZeroCanonicalSigmaRowFormula).
    etransitivity; [exact hsigmaRow |].
    unfold sigmaDomain, sigmaLowerApplication,
      coqDynamicTruthSigmaOrZeroCanonicalSigmaRowFormula.
    apply rawDynamicTruthSigmaSuccessorRowCode_quoted.
    exact hPA.
  }
  assert (hpi : rawTemplateFormula translation
      coqDynamicTruthSharedPiSuccessorRowTemplate =
    rawTemplateFormula translation
      (embedPAFormula
        coqDynamicTruthSigmaOrZeroCanonicalPiRowFormula)).
  {
    unfold translation,
      coqDynamicTruthSharedPiSuccessorRowTemplate in *.
    rewrite (rawTemplateFormula_embedPA hagreement
      coqDynamicTruthSigmaOrZeroCanonicalPiRowFormula).
    etransitivity; [exact hpiRow |].
    unfold piDomain, piLowerApplication,
      coqDynamicTruthSigmaOrZeroCanonicalPiRowFormula.
    apply rawDynamicTruthPiSuccessorRowCode_quoted.
    exact hPA.
  }
  exists inputs.
  cbn zeta.
  split; [exact hagreement |].
  split; [exact hmode |].
  split; [exact hsigma |].
  split; [exact hpi |].
  exact
    (rawTemplateFormula_dynamicTruthSigmaOr_named_zeroCanonical_eq
      M translation hmode hsigma hpi).
Qed.

End
  PABoundedRawCodedDynamicTruthSigmaOrCanonicalTranslationCorrection.
