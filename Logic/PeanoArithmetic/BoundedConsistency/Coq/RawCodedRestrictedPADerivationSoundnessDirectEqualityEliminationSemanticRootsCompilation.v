(**
  Compile the exact Eq-E semantic roots on one standard PA witness tail.

  The represented opened-coverage source returns both recursive-child
  interfaces in a single conjunction, so their witness suffix is selected
  only once.  Projection followed by represented K-introduction adds the
  five antecedents of each public child law without changing that suffix.
  The already-compiled aligned mode-zero parent row supplies the dynamic
  truth law; append-stable synchronization then packages all three roots.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedProof
  RawCodedContextLists
  RawCodedSyntaxConstructors
  RawCodedPALocalProofConjunction
  RawCodedPALocalProofExistential
  RawCodedPAAxiomWitness
  RawCodedPAAxiomWitnessPrefix
  RawCodedRestrictedPAProof
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedTemplatePAEmbeddingSelfShiftTail
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateStructuralPAAgreement
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedTemplateLocalProofAffineStandardWitnessTailTransport
  RawCodedPALocalProofUniversalSourceInstance
  RawCodedFourStateTableAppendExistentialElimination
  RawCodedDynamicTruthSuccessorRowsAppendNormalization
  RawCodedDynamicTruthNativeLocalStagedCallbackCompilation
  RawCodedDynamicTruthNativeAlignedStrongStepLogicalRootsCompilation
  RawCodedPALocalProofIteratedUnusedAntecedents
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftRecursiveChildCompilation
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageValidity
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootCompilation
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageValidity
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionChildCoreExtraction
  RawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionAlignedTruthProduction
  RawCodedRestrictedPADerivationSoundnessDirectExistentialIntroductionEqualityEliminationAlignedTruthProduction
  RawCodedRestrictedPADerivationSoundnessDirectUniversalRulesAlignedTruthProduction
  RawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageDefinitions
  RawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageSource.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationSemanticRootsCompilation.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedProof.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedPALocalProofConjunction.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateStructuralPAAgreement.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedTemplateLocalProofAffineStandardWitnessTailTransport.
Import PABoundedRawCodedPALocalProofUniversalSourceInstance.
Import PABoundedRawCodedFourStateTableAppendExistentialElimination.
Import PABoundedRawCodedDynamicTruthSuccessorRowsAppendNormalization.
Import PABoundedRawCodedDynamicTruthNativeLocalStagedCallbackCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeAlignedStrongStepLogicalRootsCompilation.
Import PABoundedRawCodedPALocalProofIteratedUnusedAntecedents.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftRecursiveChildCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageValidity.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageValidity.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionChildCoreExtraction.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionAlignedTruthProduction.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialIntroductionEqualityEliminationAlignedTruthProduction.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectUniversalRulesAlignedTruthProduction.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageDefinitions.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageSource.

(** ------------------------------------------------------------------
    The opened source is eliminated in the one-variable eigencontext used
    by the earlier Or-E and Ex-E compilers. *)

Definition coqRestrictedPADirectEqualityEliminationCoverageEigenContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectOrIntroductionLeftDeepCommonCoverageBodyTemplate ::
    templateContextShift
      (coqRestrictedPADirectStrongStepEqualityEliminationReadyContext tail).

Arguments coqRestrictedPADirectEqualityEliminationCoverageEigenContext tail
  : clear implicits.

Lemma coqRestrictedPADirectEqualityElimination_eigen_inherited : forall
    tail formula,
  In formula
      (coqRestrictedPADirectStrongStepEqualityEliminationReadyContext tail) ->
  In (templateFormulaRename S formula)
    (coqRestrictedPADirectEqualityEliminationCoverageEigenContext tail).
Proof.
  intros tail formula hin. right.
  unfold templateContextShift, templateContextRename.
  apply in_map. exact hin.
Qed.

Lemma
    coqRestrictedPADirectEqualityElimination_eigen_coverage_body_in :
  forall tail,
  In coqRestrictedPADirectOrIntroductionLeftDeepCommonCoverageBodyTemplate
    (coqRestrictedPADirectEqualityEliminationCoverageEigenContext tail).
Proof. intros tail. left. reflexivity. Qed.

Lemma coqRestrictedPADirectEqualityElimination_eigen_restricted_in :
  forall tail,
  In (templateFormulaRename S
      coqRestrictedPADirectAndIntroductionDeepRestrictedTemplate)
    (coqRestrictedPADirectEqualityEliminationCoverageEigenContext tail).
Proof.
  intro tail.
  apply coqRestrictedPADirectEqualityElimination_eigen_inherited.
  apply coqRestrictedPADirectEqualityElimination_ready_restricted_in.
Qed.

Lemma coqRestrictedPADirectEqualityElimination_eigen_admissible_in :
  forall tail,
  In (templateFormulaRename S
      coqRestrictedPADirectAndIntroductionDeepAdmissibleTemplate)
    (coqRestrictedPADirectEqualityEliminationCoverageEigenContext tail).
Proof.
  intro tail.
  apply coqRestrictedPADirectEqualityElimination_eigen_inherited.
  apply coqRestrictedPADirectEqualityElimination_ready_admissible_in.
Qed.

Lemma coqRestrictedPADirectEqualityElimination_eigen_case_in : forall tail,
  In (templateFormulaRename S
      coqRestrictedPADirectEqualityEliminationCaseTemplate)
    (coqRestrictedPADirectEqualityEliminationCoverageEigenContext tail).
Proof.
  intro tail.
  apply coqRestrictedPADirectEqualityElimination_eigen_inherited.
  apply coqRestrictedPADirectEqualityElimination_ready_case_in.
Qed.

Lemma
    coqRestrictedPADirectEqualityEliminationCoverageEigenContext_app_witnesses :
  forall witnesses,
  coqRestrictedPADirectEqualityEliminationCoverageEigenContext
      (embedPAContext (map witnessedAxiom witnesses)) =
  coqRestrictedPADirectEqualityEliminationCoverageEigenContext [] ++
    embedPAContext (map witnessedAxiom witnesses).
Proof.
  intro witnesses.
  unfold coqRestrictedPADirectEqualityEliminationCoverageEigenContext.
  rewrite coqRestrictedPADirectEqualityEliminationReadyContext_app_witnesses.
  rewrite templateContextShift_app,
    templateContextShift_embedPAAxiomWitnesses_fixed.
  reflexivity.
Qed.

Lemma raw_equalityEliminationCoverageEigenContext_witnessed_code : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation -> forall witnesses,
  rawTemplateContextCode translation
    (coqRestrictedPADirectEqualityEliminationCoverageEigenContext
      (embedPAContext (map witnessedAxiom witnesses))) =
  rawTemplateContextCodeOnTail translation
    (rawStandardPAAxiomWitnessPrefixContextCode M witnesses (raw_zero M))
    (coqRestrictedPADirectEqualityEliminationCoverageEigenContext []).
Proof.
  intros M translation hagreement witnesses.
  rewrite
    coqRestrictedPADirectEqualityEliminationCoverageEigenContext_app_witnesses.
  rewrite rawTemplateContextCode_app_on_tail.
  assert (htail : rawTemplateContextCode translation
      (embedPAContext (map witnessedAxiom witnesses)) =
    rawStandardPAAxiomWitnessPrefixContextCode M witnesses (raw_zero M)).
  {
    rewrite rawTemplateContextCode_as_on_tail.
    apply (raw_templateContextCodeOnTail_embedPAAxiomWitnesses
      M translation hagreement witnesses (raw_zero M)).
  }
  now rewrite htail.
Qed.

(** ------------------------------------------------------------------
    Apply the represented arithmetic source and eliminate its common
    coverage witness, preserving the paired child result. *)

Definition
    RawCoqRestrictedPADirectEqualityEliminationOpenedCoverageCompilerLawRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectEqualityEliminationCoverageEigenContext tail))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectEqualityEliminationOpenedCoverageLawTemplate)
      root.

Definition
    RawCoqRestrictedPADirectEqualityEliminationPairedChildInterfaceRootAt
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectStrongStepEqualityEliminationReadyContext tail))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectEqualityEliminationChildInterfacesTemplate)
      root.

Arguments
  RawCoqRestrictedPADirectEqualityEliminationOpenedCoverageCompilerLawRoot
  M hPA inputs tail : clear implicits.
Arguments
  RawCoqRestrictedPADirectEqualityEliminationPairedChildInterfaceRootAt
  M hPA inputs tail : clear implicits.

Theorem
    raw_equalityEliminationPairedChildInterfaceRoot_of_openedCoverageCompiler :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectEqualityEliminationOpenedCoverageCompilerLawRoot
    M hPA inputs tail ->
  RawCoqRestrictedPADirectEqualityEliminationPairedChildInterfaceRootAt
    M hPA inputs tail.
Proof.
  intros M hPA inputs tail (openedRoot & hopened).
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  set (readyContext :=
    coqRestrictedPADirectStrongStepEqualityEliminationReadyContext tail).
  set (eigenContext :=
    coqRestrictedPADirectEqualityEliminationCoverageEigenContext tail).
  set (readyCode := rawTemplateContextCode translation readyContext).

  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAssumption
      M hPA translation readyContext
      coqRestrictedPADirectAndIntroductionDeepAdmissibleTemplate
      (coqRestrictedPADirectEqualityElimination_ready_admissible_in tail))
    as hadmissibleReady.
  rewrite coqRestrictedPADirectAndIntroduction_deep_admissible_agreement
    in hadmissibleReady.
  rewrite coqRestrictedPADirectOrIntroductionLeft_deep_admissible_shape
    in hadmissibleReady.
  rewrite rawTemplateFormula_and in hadmissibleReady.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA _ _ _ _
    hadmissibleReady) as hcommonCoverage.
  rewrite coqRestrictedPADirectOrIntroductionLeft_common_coverage_ex_shape
    in hcommonCoverage.
  rewrite rawTemplateFormula_ex in hcommonCoverage.

  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAssumption
      M hPA translation eigenContext
      (templateFormulaRename S
        coqRestrictedPADirectAndIntroductionDeepRestrictedTemplate)
      (coqRestrictedPADirectEqualityElimination_eigen_restricted_in tail))
    as hrestrictedEigen.
  rewrite coqRestrictedPADirectAndIntroduction_deep_restricted_agreement
    in hrestrictedEigen.
  rewrite coqRestrictedPADirectOrIntroductionLeft_deep_restricted_shape
    in hrestrictedEigen.
  cbn [templateFormulaRename] in hrestrictedEigen.
  rewrite rawTemplateFormula_and in hrestrictedEigen.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA _ _ _ _
    hrestrictedEigen) as hrestrictedCore.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA _ _ _ _
    hrestrictedEigen) as hrestrictedTail.
  rewrite rawTemplateFormula_and in hrestrictedTail.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA _ _ _ _
    hrestrictedTail) as hatomic.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA _ _ _ _
    hrestrictedTail) as hcoverageTail.
  rewrite rawTemplateFormula_and in hcoverageTail.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA _ _ _ _
    hcoverageTail) as hformulaCoverage.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA _ _ _ _
    hcoverageTail) as hruleCoverage.

  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAssumption
      M hPA translation eigenContext
      (templateFormulaRename S
        coqRestrictedPADirectAndIntroductionDeepAdmissibleTemplate)
      (coqRestrictedPADirectEqualityElimination_eigen_admissible_in tail))
    as hadmissibleEigen.
  rewrite coqRestrictedPADirectAndIntroduction_deep_admissible_agreement
    in hadmissibleEigen.
  rewrite coqRestrictedPADirectOrIntroductionLeft_deep_admissible_shape
    in hadmissibleEigen.
  cbn [templateFormulaRename] in hadmissibleEigen.
  rewrite rawTemplateFormula_and in hadmissibleEigen.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA _ _ _ _
    hadmissibleEigen) as hadmissibleCore.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAssumption
      M hPA translation eigenContext
      coqRestrictedPADirectOrIntroductionLeftDeepCommonCoverageBodyTemplate
      (coqRestrictedPADirectEqualityElimination_eigen_coverage_body_in tail))
    as hcoverageBody.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAssumption
      M hPA translation eigenContext
      (templateFormulaRename S
        coqRestrictedPADirectEqualityEliminationCaseTemplate)
      (coqRestrictedPADirectEqualityElimination_eigen_case_in tail))
    as hcase.

  unfold coqRestrictedPADirectEqualityEliminationOpenedCoverageLawTemplate
    in hopened.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation eigenContext _ _ openedRoot _
      hopened hrestrictedCore) as hopened1.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation eigenContext _ _ _ _ hopened1 hatomic)
    as hopened2.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation eigenContext _ _ _ _ hopened2 hformulaCoverage)
    as hopened3.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation eigenContext _ _ _ _ hopened3 hruleCoverage)
    as hopened4.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation eigenContext _ _ _ _ hopened4 hadmissibleCore)
    as hopened5.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation eigenContext _ _ _ _ hopened5 hcoverageBody)
    as hopened6.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation eigenContext _ _ _ _ hopened6 hcase)
    as hresultShifted.

  pose proof
    (raw_codedPALocalProofOf_exE M hPA readyCode
      (rawTemplateContextCode translation
        (templateContextShift readyContext))
      (rawTemplateFormula translation
        coqRestrictedPADirectOrIntroductionLeftDeepCommonCoverageBodyTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectEqualityEliminationChildInterfacesTemplate)
      (rawTemplateFormula translation
        (templateFormulaRename S
          coqRestrictedPADirectEqualityEliminationChildInterfacesTemplate))
      _ _ hcommonCoverage
      (raw_templateContext_shift M hPA translation readyContext)
      (rawTemplateFormula_shift translation
        coqRestrictedPADirectEqualityEliminationChildInterfacesTemplate)
      hresultShifted) as hresult.
  lazymatch type of hresult with
  | RawCodedPALocalProofOf _ _ _ ?resultRoot =>
      exists resultRoot; exact hresult
  end.
Qed.

(** ------------------------------------------------------------------
    Instantiate the universal arithmetic source and surround its selected
    tail with an arbitrary incoming witness prefix. *)

Theorem
    raw_codedPALocalProof_equalityEliminationOpenedCoverageLaw_on_witnessed_base :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    baseWitnessList baseContext,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) (root : M),
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses baseContext)
        (coqRestrictedPADirectEqualityEliminationCoverageEigenContext []))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectEqualityEliminationOpenedCoverageLawTemplate)
      root.
Proof.
  intros M hPA inputs baseWitnessList baseContext hbase.
  exact
    (raw_codedPALocalProof_universalSourceInstance_under_directPrefix
      M hPA inputs baseWitnessList baseContext
      coqRestrictedPADirectEqualityEliminationOpenedCoverageSourceBodyFormula
      (rawDirectTemplateTerm inputs
        coqRestrictedPASoundnessLowerLevelTerm)
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectEqualityEliminationOpenedCoverageLawTemplate)
      (coqRestrictedPADirectEqualityEliminationCoverageEigenContext [])
      hbase
      PA_proves_coqRestrictedPADirectEqualityEliminationOpenedCoverageSource
      (rawDirect_equalityEliminationOpenedCoverageSource_substitution
        M hPA inputs)).
Qed.

Definition
    RawCoqRestrictedPADirectEqualityEliminationPairedChildInterfaceStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawCoqStandardWitnessTailCompiler
    (fun witnesses =>
      RawCoqRestrictedPADirectEqualityEliminationPairedChildInterfaceRootAt
        M hPA inputs (embedPAContext (map witnessedAxiom witnesses))).

Arguments
  RawCoqRestrictedPADirectEqualityEliminationPairedChildInterfaceStandardTailCompiler
  M hPA inputs : clear implicits.

Theorem
    raw_equalityEliminationPairedChildInterface_standardTailCompiler :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectEqualityEliminationPairedChildInterfaceStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA inputs baseWitnesses.
  assert (hempty : RawCodedPAAxiomWitnessContext M
      (raw_zero M) (raw_zero M)).
  {
    pose proof (raw_codedPAAxiomWitnessContext_standard M hPA []) as h.
    cbn [rawQuotedPAAxiomWitnessList rawListCode map] in h.
    exact h.
  }
  destruct
    (raw_codedPALocalProof_equalityEliminationOpenedCoverageLaw_on_witnessed_base
      M hPA inputs (raw_zero M) (raw_zero M) hempty)
    as (sourceWitnesses & sourceRoot & _hwitnessed & hsource).
  assert (hcompiler :
    RawCoqRestrictedPADirectEqualityEliminationOpenedCoverageCompilerLawRoot
      M hPA inputs
      (embedPAContext (map witnessedAxiom sourceWitnesses))).
  {
    exists sourceRoot.
    rewrite
      (raw_equalityEliminationCoverageEigenContext_witnessed_code M
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawDirectStructuralTemplatePAAgreement M hPA inputs)
        sourceWitnesses).
    exact hsource.
  }
  destruct
    (raw_equalityEliminationPairedChildInterfaceRoot_of_openedCoverageCompiler
      M hPA inputs
      (embedPAContext (map witnessedAxiom sourceWitnesses)) hcompiler)
    as [interfaceRoot hinterface].
  rewrite coqRestrictedPADirectEqualityEliminationReadyContext_app_witnesses
    in hinterface.
  destruct
    (raw_codedPALocalProof_standardWitnessTail_surround_under_prefix
      M hPA
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      (coqRestrictedPADirectStrongStepEqualityEliminationReadyContext [])
      baseWitnesses sourceWitnesses []
      (rawTemplateFormula
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        coqRestrictedPADirectEqualityEliminationChildInterfacesTemplate)
      interfaceRoot hinterface) as [transportedRoot htransported].
  exists sourceWitnesses, transportedRoot.
  cbn [List.app] in htransported.
  rewrite app_nil_r in htransported.
  rewrite coqRestrictedPADirectEqualityEliminationReadyContext_app_witnesses.
  exact htransported.
Qed.

(** ------------------------------------------------------------------
    Project the synchronized pair and add exactly the antecedents used by
    the two public Eq-E child-interface laws. *)

Lemma coqRestrictedPADirectEqualityElimination_equality_law_imp_chain :
  coqTemplateImpChain
    [coqRestrictedPADirectEqualityEliminationDeepRestrictedTemplate;
     coqRestrictedPADirectEqualityEliminationCodeEqualityTemplate;
     coqRestrictedPADirectEqualityEliminationEqualityFormulaCodeTemplate;
     coqRestrictedPADirectEqualityEliminationEqualityChildEndpointTemplate;
     coqRestrictedPADirectEqualityEliminationDeepAdmissibleTemplate]
    coqRestrictedPADirectEqualityEliminationEqualityChildInterfaceTemplate =
  coqRestrictedPADirectEqualityEliminationEqualityChildInterfaceLawTemplate.
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectEqualityElimination_motive_law_imp_chain :
  coqTemplateImpChain
    [coqRestrictedPADirectEqualityEliminationDeepRestrictedTemplate;
     coqRestrictedPADirectEqualityEliminationCodeEqualityTemplate;
     coqRestrictedPADirectEqualityEliminationSourceSubstitutionTemplate;
     coqRestrictedPADirectEqualityEliminationMotiveChildEndpointTemplate;
     coqRestrictedPADirectEqualityEliminationDeepAdmissibleTemplate]
    coqRestrictedPADirectEqualityEliminationMotiveChildInterfaceTemplate =
  coqRestrictedPADirectEqualityEliminationMotiveChildInterfaceLawTemplate.
Proof. reflexivity. Qed.

Definition
    RawCoqRestrictedPADirectEqualityEliminationChildInterfaceRootsAtWitnesses
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (witnesses : StandardPAAxiomWitnessPrefix) : Prop :=
  RawCoqRestrictedPADirectEqualityEliminationChildInterfaceRootsAt
    M (rawDirectStructuralTemplateTranslation M hPA inputs)
    (coqRestrictedPADirectStrongStepEqualityEliminationReadyContext
      (embedPAContext (map witnessedAxiom witnesses))).

Definition
    RawCoqRestrictedPADirectEqualityEliminationChildInterfaceRootsStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawCoqStandardWitnessTailCompiler
    (RawCoqRestrictedPADirectEqualityEliminationChildInterfaceRootsAtWitnesses
      M hPA inputs).

Arguments
  RawCoqRestrictedPADirectEqualityEliminationChildInterfaceRootsAtWitnesses
  M hPA inputs witnesses : clear implicits.
Arguments
  RawCoqRestrictedPADirectEqualityEliminationChildInterfaceRootsStandardTailCompiler
  M hPA inputs : clear implicits.

Theorem raw_equalityEliminationChildInterfaceRoots_standardTailCompiler :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectEqualityEliminationChildInterfaceRootsStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA inputs baseWitnesses.
  destruct
    (raw_equalityEliminationPairedChildInterface_standardTailCompiler
      M hPA inputs baseWitnesses)
    as [suffix [pairRoot hpair]].
  set (translation := rawDirectStructuralTemplateTranslation M hPA inputs).
  set (allWitnesses := baseWitnesses ++ suffix).
  set (ready :=
    coqRestrictedPADirectStrongStepEqualityEliminationReadyContext
      (embedPAContext (map witnessedAxiom allWitnesses))).
  change (RawCodedPALocalProofOf M
    (rawTemplateContextCode translation ready)
    (rawTemplateFormula translation
      (tfAnd
        coqRestrictedPADirectEqualityEliminationEqualityChildInterfaceTemplate
        coqRestrictedPADirectEqualityEliminationMotiveChildInterfaceTemplate))
    pairRoot) in hpair.
  rewrite rawTemplateFormula_and in hpair.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA _ _ _ _ hpair)
    as hequalityInterface.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA _ _ _ _ hpair)
    as hmotiveInterface.
  lazymatch type of hequalityInterface with
  | RawCodedPALocalProofOf _ _ _ ?equalityInterfaceRoot =>
      destruct
        (raw_codedPALocalProofOf_iterated_unused_antecedents
          M hPA translation ready
          [coqRestrictedPADirectEqualityEliminationDeepRestrictedTemplate;
           coqRestrictedPADirectEqualityEliminationCodeEqualityTemplate;
           coqRestrictedPADirectEqualityEliminationEqualityFormulaCodeTemplate;
           coqRestrictedPADirectEqualityEliminationEqualityChildEndpointTemplate;
           coqRestrictedPADirectEqualityEliminationDeepAdmissibleTemplate]
          coqRestrictedPADirectEqualityEliminationEqualityChildInterfaceTemplate
          equalityInterfaceRoot hequalityInterface)
        as [equalityLawRoot hequalityLaw]
  end.
  rewrite coqRestrictedPADirectEqualityElimination_equality_law_imp_chain
    in hequalityLaw.
  lazymatch type of hmotiveInterface with
  | RawCodedPALocalProofOf _ _ _ ?motiveInterfaceRoot =>
      destruct
        (raw_codedPALocalProofOf_iterated_unused_antecedents
          M hPA translation ready
          [coqRestrictedPADirectEqualityEliminationDeepRestrictedTemplate;
           coqRestrictedPADirectEqualityEliminationCodeEqualityTemplate;
           coqRestrictedPADirectEqualityEliminationSourceSubstitutionTemplate;
           coqRestrictedPADirectEqualityEliminationMotiveChildEndpointTemplate;
           coqRestrictedPADirectEqualityEliminationDeepAdmissibleTemplate]
          coqRestrictedPADirectEqualityEliminationMotiveChildInterfaceTemplate
          motiveInterfaceRoot hmotiveInterface)
        as [motiveLawRoot hmotiveLaw]
  end.
  rewrite coqRestrictedPADirectEqualityElimination_motive_law_imp_chain
    in hmotiveLaw.
  exists suffix.
  unfold
    RawCoqRestrictedPADirectEqualityEliminationChildInterfaceRootsAtWitnesses,
    RawCoqRestrictedPADirectEqualityEliminationChildInterfaceRootsAt.
  cbn zeta.
  split.
  - exists equalityLawRoot. exact hequalityLaw.
  - exists motiveLawRoot. exact hmotiveLaw.
Qed.

Theorem
    raw_equalityEliminationChildInterfaceRootsAtWitnesses_append_stable :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqStandardWitnessTailAppendStable
    (RawCoqRestrictedPADirectEqualityEliminationChildInterfaceRootsAtWitnesses
      M hPA inputs).
Proof.
  intros M hPA inputs.
  unfold
    RawCoqRestrictedPADirectEqualityEliminationChildInterfaceRootsAtWitnesses,
    RawCoqRestrictedPADirectEqualityEliminationChildInterfaceRootsAt.
  apply raw_coqStandardWitnessTailAppendStable_and.
  - exact
      (raw_codedPALocalProof_affine_context_root_append_stable
        M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawDirectStructuralTemplatePAAgreement M hPA inputs)
        coqRestrictedPADirectStrongStepEqualityEliminationReadyContext
        coqRestrictedPADirectEqualityEliminationReadyContext_app_witnesses
        (rawDirectTemplateFormula inputs
          coqRestrictedPADirectEqualityEliminationEqualityChildInterfaceLawTemplate)).
  - exact
      (raw_codedPALocalProof_affine_context_root_append_stable
        M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawDirectStructuralTemplatePAAgreement M hPA inputs)
        coqRestrictedPADirectStrongStepEqualityEliminationReadyContext
        coqRestrictedPADirectEqualityEliminationReadyContext_app_witnesses
        (rawDirectTemplateFormula inputs
          coqRestrictedPADirectEqualityEliminationMotiveChildInterfaceLawTemplate)).
Qed.

(** ------------------------------------------------------------------
    Synchronize the exact recursive roots with the already compiled dynamic
    truth law, retaining a public append-stable package. *)

Definition
    RawCoqRestrictedPADirectEqualityEliminationSemanticRootsAtWitnesses
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (witnesses : StandardPAAxiomWitnessPrefix) : Prop :=
  RawCoqRestrictedPADirectStrongStepEqualityEliminationSemanticRoots
    M hPA inputs (embedPAContext (map witnessedAxiom witnesses)).

Definition
    RawCoqRestrictedPADirectEqualityEliminationSemanticRootsStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawCoqStandardWitnessTailCompiler
    (RawCoqRestrictedPADirectEqualityEliminationSemanticRootsAtWitnesses
      M hPA inputs).

Arguments
  RawCoqRestrictedPADirectEqualityEliminationSemanticRootsAtWitnesses
  M hPA inputs witnesses : clear implicits.
Arguments
  RawCoqRestrictedPADirectEqualityEliminationSemanticRootsStandardTailCompiler
  M hPA inputs : clear implicits.

Theorem raw_equalityEliminationSemanticRootsAtWitnesses_append_stable :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqStandardWitnessTailAppendStable
    (RawCoqRestrictedPADirectEqualityEliminationSemanticRootsAtWitnesses
      M hPA inputs).
Proof.
  intros M hPA inputs witnesses suffix hroots.
  unfold
    RawCoqRestrictedPADirectEqualityEliminationSemanticRootsAtWitnesses,
    RawCoqRestrictedPADirectStrongStepEqualityEliminationSemanticRoots
    in hroots |- *.
  cbn zeta in hroots |- *.
  destruct hroots as [[hequality hmotive] hdynamic].
  repeat split.
  - exact
      ((raw_codedPALocalProof_affine_context_root_append_stable
        M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawDirectStructuralTemplatePAAgreement M hPA inputs)
        coqRestrictedPADirectStrongStepEqualityEliminationReadyContext
        coqRestrictedPADirectEqualityEliminationReadyContext_app_witnesses
        (rawDirectTemplateFormula inputs
          coqRestrictedPADirectEqualityEliminationEqualityChildInterfaceLawTemplate))
        witnesses suffix hequality).
  - exact
      ((raw_codedPALocalProof_affine_context_root_append_stable
        M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawDirectStructuralTemplatePAAgreement M hPA inputs)
        coqRestrictedPADirectStrongStepEqualityEliminationReadyContext
        coqRestrictedPADirectEqualityEliminationReadyContext_app_witnesses
        (rawDirectTemplateFormula inputs
          coqRestrictedPADirectEqualityEliminationMotiveChildInterfaceLawTemplate))
        witnesses suffix hmotive).
  - exact
      ((raw_codedPALocalProof_affine_context_root_append_stable
        M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawDirectStructuralTemplatePAAgreement M hPA inputs)
        coqRestrictedPADirectStrongStepEqualityEliminationReadyContext
        coqRestrictedPADirectEqualityEliminationReadyContext_app_witnesses
        (rawDirectTemplateFormula inputs
          coqRestrictedPADirectEqualityEliminationDynamicTruthLawTemplate))
        witnesses suffix hdynamic).
Qed.

(** Exact public endpoint.  The two recursive laws are unconditional; the
    sole non-structural premise is the literal mode-zero Eq-E result row. *)
Theorem
    raw_equalityEliminationSemanticRoots_standardTailCompiler_of_aligned_append_concrete_row :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (tail : nat -> M) predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi
    (aligned : RawDynamicTruthNativeLocalAlignedPredecessorAt M tail
      predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi)
    inputLevelNumeral
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawDynamicTruthNativeAlignedStrongStepStructuralInputsAt
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned
      inputLevelNumeral inputs ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepEqualityEliminationReadyContext []) ->
  RawCoqRestrictedPADirectEqualityEliminationSemanticRootsStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hstructural hresources.
  pose proof
    (raw_equalityEliminationChildInterfaceRoots_standardTailCompiler
      M hPA inputs) as hchildrenCompiler.
  pose proof
    (raw_equalityEliminationDynamicTruthStandardTailCompiler_of_aligned_append_concrete_row
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
      inputs hstructural hresources) as hdynamicCompilerDirect.
  assert (hdynamicCompiler : RawCoqStandardWitnessTailCompiler
      (fun witnesses =>
        RawCoqRestrictedPADirectEqualityEliminationDynamicTruthLawRootAt
          M (rawDirectStructuralTemplateTranslation M hPA inputs)
          (coqRestrictedPADirectStrongStepEqualityEliminationReadyContext
            (embedPAContext (map witnessedAxiom witnesses))))).
  {
    exact hdynamicCompilerDirect.
  }
  pose proof
    (raw_coqStandardWitnessTailCompiler_and
      (RawCoqRestrictedPADirectEqualityEliminationChildInterfaceRootsAtWitnesses
        M hPA inputs)
      (fun witnesses =>
        RawCoqRestrictedPADirectEqualityEliminationDynamicTruthLawRootAt
          M (rawDirectStructuralTemplateTranslation M hPA inputs)
          (coqRestrictedPADirectStrongStepEqualityEliminationReadyContext
            (embedPAContext (map witnessedAxiom witnesses))))
      (raw_equalityEliminationChildInterfaceRootsAtWitnesses_append_stable
        M hPA inputs)
      hchildrenCompiler hdynamicCompiler) as hallCompiler.
  intros baseWitnesses.
  destruct (hallCompiler baseWitnesses) as
    [suffix [[hequality hmotive] hdynamic]].
  exists suffix.
  unfold
    RawCoqRestrictedPADirectEqualityEliminationSemanticRootsAtWitnesses,
    RawCoqRestrictedPADirectStrongStepEqualityEliminationSemanticRoots.
  cbn zeta.
  exact (conj (conj hequality hmotive) hdynamic).
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationSemanticRootsCompilation.
