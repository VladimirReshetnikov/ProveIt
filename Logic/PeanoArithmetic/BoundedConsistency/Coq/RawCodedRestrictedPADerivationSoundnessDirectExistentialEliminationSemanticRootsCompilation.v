(**
  Compile all four exact Ex-E semantic roots on one standard PA witness tail.

  The recursive part is unconditional: one arithmetically valid opened
  coverage source yields both child interfaces, at their genuinely different
  endpoint contexts, and both interfaces are projected before selecting any
  further witness suffix.  The remaining two truth leaves are obtained from
  the native aligned dynamic-truth sources.  Context truth uses mode one;
  conclusion truth uses mode zero.  Their literal append traces remain the
  only proof-producing row premises at the public aligned boundary.
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
  RawCodedContextStructure
  RawCodedSyntaxConstructors
  RawCodedPALocalProofConjunction
  RawCodedPALocalProofExistential
  RawCodedPALocalProofUniversalIntroductionChain
  RawCodedPAAxiomWitness
  RawCodedPAAxiomWitnessPrefix
  RawCodedRestrictedPAProof
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplatePAEmbedding
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbeddingSelfShiftTail
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateStructuralPAAgreement
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedTemplateLocalProofAffineStandardWitnessTailTransport
  RawCodedPALocalProofUniversalSourceInstance
  RawCodedLtSuccCasesProofCompilation
  RawCodedFourStateTableAppendRowLtSuccCases
  RawCodedFourStateTableAppendProofCompilation
  RawCodedFourStateTableAppendExistentialElimination
  RawCodedFourStateTableAppendTemplateGlobalTraversalAssembly
  RawCodedFourStateTableAppendPermutedTemplateGlobalTraversalAssembly
  RawCodedDynamicTruthSuccessorRowsAppendNormalization
  RawCodedDynamicTruthNativeLocalStagedCallbackCompilation
  RawCodedDynamicTruthNativeAlignedStrongStepLogicalRootsCompilation
  RawCodedDynamicTruthNativeAlignedRootApplicationIdentification
  RawCodedRestrictedPADirectImpIntroductionPositiveBodyAppendProduction
  RawCodedPALocalProofIteratedUnusedAntecedents
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier
  RawCodedRestrictedPADerivationSoundnessDirectStrongStepShell
  RawCodedRestrictedPADerivationSoundnessDirectAssumptionCase
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftRecursiveChildCompilation
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootValidity
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootCompilation
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageValidity
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageCompilation
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageValidity
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionChildCoreExtraction
  RawCodedRestrictedPADerivationSoundnessDirectStandardReadyContextAffinity
  RawCodedRestrictedPADerivationSoundnessSameContextUnaryRecursiveChildCompilation
  RawCodedRestrictedPADerivationSoundnessSameContextUnaryRecursiveChildStandardTailCompilation
  RawCodedRestrictedPADerivationSoundnessSameContextUnaryChildInterfaceOpenedCoverageSource
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionAlignedTruthProduction
  RawCodedRestrictedPADerivationSoundnessDirectAndEliminationAlignedTruthProduction
  RawCodedRestrictedPADerivationSoundnessDirectUniversalRulesAlignedTruthProduction
  RawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationOpenedCoverageDefinitions
  RawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationOpenedCoverageSource.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationSemanticRootsCompilation.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedProof.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedPALocalProofConjunction.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofUniversalIntroductionChain.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateStructuralPAAgreement.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedTemplateLocalProofAffineStandardWitnessTailTransport.
Import PABoundedRawCodedPALocalProofUniversalSourceInstance.
Import PABoundedRawCodedLtSuccCasesProofCompilation.
Import PABoundedRawCodedFourStateTableAppendRowLtSuccCases.
Import PABoundedRawCodedFourStateTableAppendProofCompilation.
Import PABoundedRawCodedFourStateTableAppendExistentialElimination.
Import PABoundedRawCodedFourStateTableAppendTemplateGlobalTraversalAssembly.
Import
  PABoundedRawCodedFourStateTableAppendPermutedTemplateGlobalTraversalAssembly.
Import PABoundedRawCodedDynamicTruthSuccessorRowsAppendNormalization.
Import PABoundedRawCodedDynamicTruthNativeLocalStagedCallbackCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeAlignedStrongStepLogicalRootsCompilation.
Import PABoundedRawCodedDynamicTruthNativeAlignedRootApplicationIdentification.
Import PABoundedRawCodedRestrictedPADirectImpIntroductionPositiveBodyAppendProduction.
Import PABoundedRawCodedPALocalProofIteratedUnusedAntecedents.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectStrongStepShell.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAssumptionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftRecursiveChildCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootValidity.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageValidity.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageValidity.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionChildCoreExtraction.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectStandardReadyContextAffinity.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessSameContextUnaryRecursiveChildCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessSameContextUnaryRecursiveChildStandardTailCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessSameContextUnaryChildInterfaceOpenedCoverageSource.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionAlignedTruthProduction.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndEliminationAlignedTruthProduction.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectUniversalRulesAlignedTruthProduction.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationOpenedCoverageDefinitions.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationOpenedCoverageSource.

(** ------------------------------------------------------------------
    The literal Ex-E ready context and its common-coverage eigencontext. *)

Definition coqRestrictedPADirectExistentialEliminationCoverageEigenContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectOrIntroductionLeftDeepCommonCoverageBodyTemplate ::
    templateContextShift
      (coqRestrictedPADirectStrongStepExistentialEliminationReadyContext
        tail).

Arguments
  coqRestrictedPADirectExistentialEliminationCoverageEigenContext tail
  : clear implicits.

Lemma coqRestrictedPADirectExistentialElimination_ready_standard :
  forall tail,
  coqRestrictedPADirectStrongStepExistentialEliminationReadyContext tail =
  coqRestrictedPADirectStandardReadyContext
    coqRestrictedPADirectAssumptionOuterContextTruthTemplate
    coqRestrictedPADirectAssumptionDeepAdmissibleTemplate
    coqRestrictedPADirectExistentialEliminationCaseTemplate tail.
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectExistentialElimination_ready_restricted_in :
  forall tail,
  In coqRestrictedPADirectAndIntroductionDeepRestrictedTemplate
    (coqRestrictedPADirectStrongStepExistentialEliminationReadyContext tail).
Proof.
  intro tail.
  rewrite coqRestrictedPADirectExistentialElimination_ready_standard.
  unfold coqRestrictedPADirectStandardReadyContext.
  do 3 right.
  rewrite <- raw_coqRestrictedPADirectEndpointDeepContext_shape.
  unfold coqRestrictedPADirectAndIntroductionDeepRestrictedTemplate.
  apply raw_coqTemplateNestedExContext_inherited.
  unfold rawCoqRestrictedPADirectStrongStepEndpointTail.
  left. reflexivity.
Qed.

Lemma coqRestrictedPADirectExistentialElimination_ready_admissible_in :
  forall tail,
  In coqRestrictedPADirectAndIntroductionDeepAdmissibleTemplate
    (coqRestrictedPADirectStrongStepExistentialEliminationReadyContext tail).
Proof.
  intro tail.
  rewrite coqRestrictedPADirectExistentialElimination_ready_standard.
  unfold coqRestrictedPADirectStandardReadyContext.
  right. left. reflexivity.
Qed.

Lemma coqRestrictedPADirectExistentialElimination_ready_case_in :
  forall tail,
  In coqRestrictedPADirectExistentialEliminationCaseTemplate
    (coqRestrictedPADirectStrongStepExistentialEliminationReadyContext tail).
Proof.
  intro tail.
  rewrite coqRestrictedPADirectExistentialElimination_ready_standard.
  unfold coqRestrictedPADirectStandardReadyContext.
  right. right. left. reflexivity.
Qed.

Lemma coqRestrictedPADirectExistentialElimination_eigen_inherited : forall
    tail formula,
  In formula
      (coqRestrictedPADirectStrongStepExistentialEliminationReadyContext
        tail) ->
  In (templateFormulaRename S formula)
    (coqRestrictedPADirectExistentialEliminationCoverageEigenContext tail).
Proof.
  intros tail formula hin. right.
  unfold templateContextShift, templateContextRename.
  apply in_map. exact hin.
Qed.

Lemma
    coqRestrictedPADirectExistentialElimination_eigen_coverage_body_in :
  forall tail,
  In coqRestrictedPADirectOrIntroductionLeftDeepCommonCoverageBodyTemplate
    (coqRestrictedPADirectExistentialEliminationCoverageEigenContext tail).
Proof. intros tail. left. reflexivity. Qed.

Lemma coqRestrictedPADirectExistentialElimination_eigen_restricted_in :
  forall tail,
  In (templateFormulaRename S
      coqRestrictedPADirectAndIntroductionDeepRestrictedTemplate)
    (coqRestrictedPADirectExistentialEliminationCoverageEigenContext tail).
Proof.
  intro tail.
  apply coqRestrictedPADirectExistentialElimination_eigen_inherited.
  apply coqRestrictedPADirectExistentialElimination_ready_restricted_in.
Qed.

Lemma coqRestrictedPADirectExistentialElimination_eigen_admissible_in :
  forall tail,
  In (templateFormulaRename S
      coqRestrictedPADirectAndIntroductionDeepAdmissibleTemplate)
    (coqRestrictedPADirectExistentialEliminationCoverageEigenContext tail).
Proof.
  intro tail.
  apply coqRestrictedPADirectExistentialElimination_eigen_inherited.
  apply coqRestrictedPADirectExistentialElimination_ready_admissible_in.
Qed.

Lemma coqRestrictedPADirectExistentialElimination_eigen_case_in : forall tail,
  In (templateFormulaRename S
      coqRestrictedPADirectExistentialEliminationCaseTemplate)
    (coqRestrictedPADirectExistentialEliminationCoverageEigenContext tail).
Proof.
  intro tail.
  apply coqRestrictedPADirectExistentialElimination_eigen_inherited.
  apply coqRestrictedPADirectExistentialElimination_ready_case_in.
Qed.

Lemma
    coqRestrictedPADirectExistentialEliminationReadyContext_app_witnesses :
  forall witnesses,
  coqRestrictedPADirectStrongStepExistentialEliminationReadyContext
      (embedPAContext (map witnessedAxiom witnesses)) =
  coqRestrictedPADirectStrongStepExistentialEliminationReadyContext [] ++
    embedPAContext (map witnessedAxiom witnesses).
Proof.
  intro witnesses.
  rewrite coqRestrictedPADirectExistentialElimination_ready_standard.
  change
    (coqRestrictedPADirectStandardReadyContext
      coqRestrictedPADirectAssumptionOuterContextTruthTemplate
      coqRestrictedPADirectAssumptionDeepAdmissibleTemplate
      coqRestrictedPADirectExistentialEliminationCaseTemplate
      (embedPAContext (map witnessedAxiom witnesses)) =
    coqRestrictedPADirectStandardReadyContext
      coqRestrictedPADirectAssumptionOuterContextTruthTemplate
      coqRestrictedPADirectAssumptionDeepAdmissibleTemplate
      coqRestrictedPADirectExistentialEliminationCaseTemplate [] ++
      embedPAContext (map witnessedAxiom witnesses)).
  apply coqRestrictedPADirectStandardReadyContext_app_witnesses.
Qed.

Lemma
    coqRestrictedPADirectExistentialEliminationCoverageEigenContext_app_witnesses :
  forall witnesses,
  coqRestrictedPADirectExistentialEliminationCoverageEigenContext
      (embedPAContext (map witnessedAxiom witnesses)) =
  coqRestrictedPADirectExistentialEliminationCoverageEigenContext [] ++
    embedPAContext (map witnessedAxiom witnesses).
Proof.
  intro witnesses.
  unfold
    coqRestrictedPADirectExistentialEliminationCoverageEigenContext.
  rewrite
    coqRestrictedPADirectExistentialEliminationReadyContext_app_witnesses.
  rewrite templateContextShift_app,
    templateContextShift_embedPAAxiomWitnesses_fixed.
  reflexivity.
Qed.

Lemma raw_existentialEliminationCoverageEigenContext_witnessed_code : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation -> forall witnesses,
  rawTemplateContextCode translation
    (coqRestrictedPADirectExistentialEliminationCoverageEigenContext
      (embedPAContext (map witnessedAxiom witnesses))) =
  rawTemplateContextCodeOnTail translation
    (rawStandardPAAxiomWitnessPrefixContextCode M witnesses (raw_zero M))
    (coqRestrictedPADirectExistentialEliminationCoverageEigenContext []).
Proof.
  intros M translation hagreement witnesses.
  rewrite
    coqRestrictedPADirectExistentialEliminationCoverageEigenContext_app_witnesses.
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
    Apply the represented opened source and eliminate its coverage witness. *)

Definition
    RawCoqRestrictedPADirectExistentialEliminationOpenedCoverageCompilerLawRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectExistentialEliminationCoverageEigenContext
          tail))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectExistentialEliminationOpenedCoverageLawTemplate)
      root.

Definition
    RawCoqRestrictedPADirectExistentialEliminationPairedChildInterfaceRootAt
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectStrongStepExistentialEliminationReadyContext
          tail))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectExistentialEliminationChildInterfacesTemplate)
      root.

Arguments
  RawCoqRestrictedPADirectExistentialEliminationOpenedCoverageCompilerLawRoot
  M hPA inputs tail : clear implicits.
Arguments
  RawCoqRestrictedPADirectExistentialEliminationPairedChildInterfaceRootAt
  M hPA inputs tail : clear implicits.

Theorem
    raw_existentialEliminationPairedChildInterfaceRoot_of_openedCoverageCompiler :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectExistentialEliminationOpenedCoverageCompilerLawRoot
    M hPA inputs tail ->
  RawCoqRestrictedPADirectExistentialEliminationPairedChildInterfaceRootAt
    M hPA inputs tail.
Proof.
  intros M hPA inputs tail (openedRoot & hopened).
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  set (readyContext :=
    coqRestrictedPADirectStrongStepExistentialEliminationReadyContext tail).
  set (eigenContext :=
    coqRestrictedPADirectExistentialEliminationCoverageEigenContext tail).
  set (readyCode := rawTemplateContextCode translation readyContext).

  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAssumption
      M hPA translation readyContext
      coqRestrictedPADirectAndIntroductionDeepAdmissibleTemplate
      (coqRestrictedPADirectExistentialElimination_ready_admissible_in tail))
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
      (coqRestrictedPADirectExistentialElimination_eigen_restricted_in tail))
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
      (coqRestrictedPADirectExistentialElimination_eigen_admissible_in tail))
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
      (coqRestrictedPADirectExistentialElimination_eigen_coverage_body_in
        tail)) as hcoverageBody.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAssumption
      M hPA translation eigenContext
      (templateFormulaRename S
        coqRestrictedPADirectExistentialEliminationCaseTemplate)
      (coqRestrictedPADirectExistentialElimination_eigen_case_in tail))
    as hcase.

  unfold
    coqRestrictedPADirectExistentialEliminationOpenedCoverageLawTemplate
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
        coqRestrictedPADirectExistentialEliminationChildInterfacesTemplate)
      (rawTemplateFormula translation
        (templateFormulaRename S
          coqRestrictedPADirectExistentialEliminationChildInterfacesTemplate))
      _ _ hcommonCoverage
      (raw_templateContext_shift M hPA translation readyContext)
      (rawTemplateFormula_shift translation
        coqRestrictedPADirectExistentialEliminationChildInterfacesTemplate)
      hresultShifted) as hresult.
  lazymatch type of hresult with
  | RawCodedPALocalProofOf _ _ _ ?resultRoot =>
      exists resultRoot; exact hresult
  end.
Qed.

(** ------------------------------------------------------------------
    Instantiate the universal PA source and transport it under a prefix. *)

Theorem
    raw_codedPALocalProof_existentialEliminationOpenedCoverageLaw_on_witnessed_base :
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
        (coqRestrictedPADirectExistentialEliminationCoverageEigenContext []))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectExistentialEliminationOpenedCoverageLawTemplate)
      root.
Proof.
  intros M hPA inputs baseWitnessList baseContext hbase.
  exact
    (raw_codedPALocalProof_universalSourceInstance_under_directPrefix
      M hPA inputs baseWitnessList baseContext
      coqRestrictedPADirectExistentialEliminationOpenedCoverageSourceBodyFormula
      (rawDirectTemplateTerm inputs
        coqRestrictedPASoundnessLowerLevelTerm)
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectExistentialEliminationOpenedCoverageLawTemplate)
      (coqRestrictedPADirectExistentialEliminationCoverageEigenContext [])
      hbase
      PA_proves_coqRestrictedPADirectExistentialEliminationOpenedCoverageSource
      (rawDirect_existentialEliminationOpenedCoverageSource_substitution
        M hPA inputs)).
Qed.

Definition
    RawCoqRestrictedPADirectExistentialEliminationPairedChildInterfaceStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawCoqStandardWitnessTailCompiler
    (fun witnesses =>
      RawCoqRestrictedPADirectExistentialEliminationPairedChildInterfaceRootAt
        M hPA inputs (embedPAContext (map witnessedAxiom witnesses))).

Arguments
  RawCoqRestrictedPADirectExistentialEliminationPairedChildInterfaceStandardTailCompiler
  M hPA inputs : clear implicits.

Theorem
    raw_existentialEliminationPairedChildInterface_standardTailCompiler :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectExistentialEliminationPairedChildInterfaceStandardTailCompiler
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
    (raw_codedPALocalProof_existentialEliminationOpenedCoverageLaw_on_witnessed_base
      M hPA inputs (raw_zero M) (raw_zero M) hempty)
    as (sourceWitnesses & sourceRoot & _hwitnessed & hsource).
  assert (hcompiler :
    RawCoqRestrictedPADirectExistentialEliminationOpenedCoverageCompilerLawRoot
      M hPA inputs
      (embedPAContext (map witnessedAxiom sourceWitnesses))).
  {
    exists sourceRoot.
    rewrite
      (raw_existentialEliminationCoverageEigenContext_witnessed_code M
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawDirectStructuralTemplatePAAgreement M hPA inputs)
        sourceWitnesses).
    exact hsource.
  }
  destruct
    (raw_existentialEliminationPairedChildInterfaceRoot_of_openedCoverageCompiler
      M hPA inputs
      (embedPAContext (map witnessedAxiom sourceWitnesses)) hcompiler)
    as [interfaceRoot hinterface].
  rewrite
    coqRestrictedPADirectExistentialEliminationReadyContext_app_witnesses
    in hinterface.
  destruct
    (raw_codedPALocalProof_standardWitnessTail_surround_under_prefix
      M hPA
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      (coqRestrictedPADirectStrongStepExistentialEliminationReadyContext [])
      baseWitnesses sourceWitnesses []
      (rawTemplateFormula
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        coqRestrictedPADirectExistentialEliminationChildInterfacesTemplate)
      interfaceRoot hinterface) as [transportedRoot htransported].
  exists sourceWitnesses, transportedRoot.
  cbn [List.app] in htransported.
  rewrite app_nil_r in htransported.
  rewrite
    coqRestrictedPADirectExistentialEliminationReadyContext_app_witnesses.
  exact htransported.
Qed.

(** ------------------------------------------------------------------
    Project the pair and compile the two exact recursive child laws. *)

Lemma coqRestrictedPADirectExistentialElimination_ready_prefix_in :
  forall tail,
  In coqRestrictedPADirectAndIntroductionDeepStrongPrefixTemplate
    (coqRestrictedPADirectStrongStepExistentialEliminationReadyContext tail).
Proof.
  intro tail.
  rewrite coqRestrictedPADirectExistentialElimination_ready_standard.
  unfold coqRestrictedPADirectStandardReadyContext.
  apply coqRestrictedPASameContextUnary_deep_prefix_in.
Qed.

Lemma
    coqRestrictedPADirectExistentialElimination_existential_child_context_truth_agreement :
  coqRestrictedPADirectAndIntroductionChildContextTruthTemplate
    coqRestrictedPADirectExistentialEliminationExistentialChildTerm
    coqRestrictedPADirectExistentialEliminationExistentialChildContextTerm
    coqRestrictedPADirectExistentialEliminationExistentialChildConclusionTerm =
  coqRestrictedPADirectAssumptionWitnessContextTruthTemplate.
Proof. reflexivity. Qed.

Lemma
    coqRestrictedPADirectExistentialElimination_existential_child_truth_agreement :
  coqRestrictedPADirectAndIntroductionChildTruthTemplate
    coqRestrictedPADirectExistentialEliminationExistentialChildTerm
    coqRestrictedPADirectExistentialEliminationExistentialChildContextTerm
    coqRestrictedPADirectExistentialEliminationExistentialChildConclusionTerm =
  coqRestrictedPADirectExistentialEliminationExistentialTruthTemplate.
Proof. reflexivity. Qed.

Lemma
    coqRestrictedPADirectExistentialElimination_body_child_context_truth_agreement :
  coqRestrictedPADirectAndIntroductionChildContextTruthTemplate
    coqRestrictedPADirectExistentialEliminationBodyChildTerm
    coqRestrictedPADirectExistentialEliminationBodyChildContextTerm
    coqRestrictedPADirectExistentialEliminationBodyChildConclusionTerm =
  coqRestrictedPADirectExistentialEliminationBinderContextTruthTemplate.
Proof. reflexivity. Qed.

Lemma
    coqRestrictedPADirectExistentialElimination_body_child_truth_agreement :
  coqRestrictedPADirectAndIntroductionChildTruthTemplate
    coqRestrictedPADirectExistentialEliminationBodyChildTerm
    coqRestrictedPADirectExistentialEliminationBodyChildContextTerm
    coqRestrictedPADirectExistentialEliminationBodyChildConclusionTerm =
  coqRestrictedPADirectExistentialEliminationShiftedResultTruthTemplate.
Proof. reflexivity. Qed.

Definition
    RawCoqRestrictedPADirectExistentialEliminationChildLawRootsAtWitnesses
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (witnesses : StandardPAAxiomWitnessPrefix) : Prop :=
  let translation := rawDirectStructuralTemplateTranslation M hPA inputs in
  let ready :=
    coqRestrictedPADirectStrongStepExistentialEliminationReadyContext
      (embedPAContext (map witnessedAxiom witnesses)) in
  (exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation ready)
      (rawTemplateFormula translation
        coqRestrictedPADirectExistentialEliminationExistentialChildLawTemplate)
      root) /\
  (exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation ready)
      (rawTemplateFormula translation
        coqRestrictedPADirectExistentialEliminationBodyChildLawTemplate)
      root).

Definition
    RawCoqRestrictedPADirectExistentialEliminationChildLawRootsStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawCoqStandardWitnessTailCompiler
    (RawCoqRestrictedPADirectExistentialEliminationChildLawRootsAtWitnesses
      M hPA inputs).

Arguments
  RawCoqRestrictedPADirectExistentialEliminationChildLawRootsAtWitnesses
  M hPA inputs witnesses : clear implicits.
Arguments
  RawCoqRestrictedPADirectExistentialEliminationChildLawRootsStandardTailCompiler
  M hPA inputs : clear implicits.

Theorem raw_existentialEliminationChildLawRoots_standardTailCompiler :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectExistentialEliminationChildLawRootsStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA inputs baseWitnesses.
  destruct
    (raw_existentialEliminationPairedChildInterface_standardTailCompiler
      M hPA inputs baseWitnesses)
    as [suffix [pairRoot hpair]].
  set (translation := rawDirectStructuralTemplateTranslation M hPA inputs).
  set (allWitnesses := baseWitnesses ++ suffix).
  set (ready :=
    coqRestrictedPADirectStrongStepExistentialEliminationReadyContext
      (embedPAContext (map witnessedAxiom allWitnesses))).
  change (RawCodedPALocalProofOf M
    (rawTemplateContextCode translation ready)
    (rawTemplateFormula translation
      (tfAnd
        coqRestrictedPADirectExistentialEliminationExistentialChildInterfaceTemplate
        coqRestrictedPADirectExistentialEliminationBodyChildInterfaceTemplate))
    pairRoot) in hpair.
  rewrite rawTemplateFormula_and in hpair.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA _ _ _ _ hpair)
    as hexInterface.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA _ _ _ _ hpair)
    as hbodyInterface.
  assert (hexInterfaceRoot :
    RawCoqRestrictedPASameContextUnaryChildInterfaceRootAt M translation ready
      coqRestrictedPADirectExistentialEliminationExistentialChildTerm
      coqRestrictedPADirectExistentialEliminationExistentialChildContextTerm
      coqRestrictedPADirectExistentialEliminationExistentialChildConclusionTerm).
  {
    lazymatch type of hexInterface with
    | RawCodedPALocalProofOf _ _ _ ?root =>
        exists root; exact hexInterface
    end.
  }
  assert (hbodyInterfaceRoot :
    RawCoqRestrictedPASameContextUnaryChildInterfaceRootAt M translation ready
      coqRestrictedPADirectExistentialEliminationBodyChildTerm
      coqRestrictedPADirectExistentialEliminationBodyChildContextTerm
      coqRestrictedPADirectExistentialEliminationBodyChildConclusionTerm).
  {
    lazymatch type of hbodyInterface with
    | RawCodedPALocalProofOf _ _ _ ?root =>
        exists root; exact hbodyInterface
    end.
  }
  destruct
    (raw_sameContextUnary_recursiveChildLawRootAt_of_interface
      M hPA translation ready
      coqRestrictedPADirectExistentialEliminationExistentialChildTerm
      coqRestrictedPADirectExistentialEliminationExistentialChildContextTerm
      coqRestrictedPADirectExistentialEliminationExistentialChildConclusionTerm
      coqRestrictedPADirectExistentialEliminationExistentialEndpointTemplate
      (coqRestrictedPADirectExistentialElimination_ready_prefix_in
        (embedPAContext (map witnessedAxiom allWitnesses)))
      hexInterfaceRoot) as [hexRoot hexLaw].
  destruct
    (raw_sameContextUnary_recursiveChildLawRootAt_of_interface
      M hPA translation ready
      coqRestrictedPADirectExistentialEliminationBodyChildTerm
      coqRestrictedPADirectExistentialEliminationBodyChildContextTerm
      coqRestrictedPADirectExistentialEliminationBodyChildConclusionTerm
      coqRestrictedPADirectExistentialEliminationBodyEndpointTemplate
      (coqRestrictedPADirectExistentialElimination_ready_prefix_in
        (embedPAContext (map witnessedAxiom allWitnesses)))
      hbodyInterfaceRoot) as [hbodyRoot hbodyLaw].
  exists suffix.
  unfold
    RawCoqRestrictedPADirectExistentialEliminationChildLawRootsAtWitnesses.
  cbn zeta.
  split.
  - exists hexRoot.
    rewrite
      coqRestrictedPADirectExistentialElimination_existential_child_context_truth_agreement,
      coqRestrictedPADirectExistentialElimination_existential_child_truth_agreement
      in hexLaw.
    exact hexLaw.
  - exists hbodyRoot.
    rewrite
      coqRestrictedPADirectExistentialElimination_body_child_context_truth_agreement,
      coqRestrictedPADirectExistentialElimination_body_child_truth_agreement
      in hbodyLaw.
    exact hbodyLaw.
Qed.

Theorem raw_existentialEliminationChildLawRootsAtWitnesses_append_stable :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqStandardWitnessTailAppendStable
    (RawCoqRestrictedPADirectExistentialEliminationChildLawRootsAtWitnesses
      M hPA inputs).
Proof.
  intros M hPA inputs.
  unfold
    RawCoqRestrictedPADirectExistentialEliminationChildLawRootsAtWitnesses.
  apply raw_coqStandardWitnessTailAppendStable_and.
  - exact
      (raw_codedPALocalProof_affine_context_root_append_stable
        M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawDirectStructuralTemplatePAAgreement M hPA inputs)
        coqRestrictedPADirectStrongStepExistentialEliminationReadyContext
        coqRestrictedPADirectExistentialEliminationReadyContext_app_witnesses
        (rawDirectTemplateFormula inputs
          coqRestrictedPADirectExistentialEliminationExistentialChildLawTemplate)).
  - exact
      (raw_codedPALocalProof_affine_context_root_append_stable
        M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawDirectStructuralTemplatePAAgreement M hPA inputs)
        coqRestrictedPADirectStrongStepExistentialEliminationReadyContext
        coqRestrictedPADirectExistentialEliminationReadyContext_app_witnesses
        (rawDirectTemplateFormula inputs
          coqRestrictedPADirectExistentialEliminationBodyChildLawTemplate)).
Qed.

(** ------------------------------------------------------------------
    A root-mode-generic append boundary.

    The previously shared compiler exposed mode zero because all of its
    clients asked for conclusion truth.  Ex-E also needs native context
    truth, whose aligned source is mode one.  The append assembly theorem is
    already generic over the two modes, so the following interface merely
    exposes that existing parameter without strengthening its premises. *)

Definition
    RawCoqRestrictedPADirectRootModeAppendConcreteRowStandardTailCompilerAt
    (rootMode : nat)
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (boundName : TemplateParameterName)
    (rootFormula rootAssignmentCode rootAssignmentStep : TemplateTerm)
    (outerPrefix : TemplateContext) : Prop :=
  forall baseWitnesses : StandardPAAxiomWitnessPrefix,
  exists suffix : StandardPAAxiomWitnessPrefix,
  exists modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep : TemplateTerm,
  exists appendRoot rowRoot : M,
  let translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs in
  let allWitnesses := baseWitnesses ++ suffix in
  let sourceContext := rawTemplateContextCode translation
    (embedPAContext (map witnessedAxiom allWitnesses)) in
  let witnessContext := coqFourStateTableAppendWitnessContext
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    (ttParameter boundName) (embedPATerm (Term.numeral rootMode))
    rootFormula rootAssignmentCode rootAssignmentStep outerPrefix in
  let antecedent := coqLtSuccCasesAntecedentTemplate
    (ttVar 4) (ttParameter boundName) in
  let rowLookup :=
    coqFourStateTableAppendEqualityRowLookupTemplate
      coqFourStateTableAppendRowModeParameterName
      coqFourStateTableAppendRowFormulaParameterName
      coqFourStateTableAppendRowAssignmentCodeParameterName
      coqFourStateTableAppendRowAssignmentStepParameterName
      (ttVar 4) (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0) in
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation sourceContext outerPrefix)
    (rawTemplateFormula translation
      (coqFourStateTableAppendExistsTemplate
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        (ttParameter boundName) (embedPATerm (Term.numeral rootMode))
        rootFormula rootAssignmentCode rootAssignmentStep)) appendRoot /\
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation sourceContext
      (templateContextShiftMany 5 witnessContext))
    (rawTemplateFormula translation
      (tfImp antecedent
        (tfImp rowLookup
          (coqFourStateTableAppendConcreteClosedRowProductionTemplate
            coqDynamicTruthSharedSigmaSuccessorRowTemplate
            coqDynamicTruthSharedPiSuccessorRowTemplate)))) rowRoot.

Definition
    RawCoqRestrictedPADirectModeOneAppendConcreteRowStandardTailCompilerAt
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (boundName : TemplateParameterName)
    (rootFormula rootAssignmentCode rootAssignmentStep : TemplateTerm)
    (outerPrefix : TemplateContext) : Prop :=
  RawCoqRestrictedPADirectRootModeAppendConcreteRowStandardTailCompilerAt
    1 M hPA inputs boundName rootFormula rootAssignmentCode
      rootAssignmentStep outerPrefix.

Arguments
  RawCoqRestrictedPADirectRootModeAppendConcreteRowStandardTailCompilerAt
  rootMode M hPA inputs boundName rootFormula rootAssignmentCode
  rootAssignmentStep outerPrefix : clear implicits.
Arguments
  RawCoqRestrictedPADirectModeOneAppendConcreteRowStandardTailCompilerAt
  M hPA inputs boundName rootFormula rootAssignmentCode rootAssignmentStep
  outerPrefix : clear implicits.

Definition
    RawCoqRestrictedPADirectRootModeGlobalSourceStandardTailCompilerAt
    (rootMode : nat)
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (rootFormula rootAssignmentCode rootAssignmentStep : TemplateTerm)
    (outerPrefix : TemplateContext) : Prop :=
  forall baseWitnesses : StandardPAAxiomWitnessPrefix,
  exists suffix : StandardPAAxiomWitnessPrefix,
  exists sourceRoot : M,
  let translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs in
  let sourceContext := rawTemplateContextCode translation
    (embedPAContext (map witnessedAxiom (baseWitnesses ++ suffix))) in
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation sourceContext outerPrefix)
    (rawTemplateFormula translation
      (coqFourStateTableAppendTemplateGlobalSourceAtRootTerms rootMode
        coqDynamicTruthSharedSigmaSuccessorRowTemplate
        coqDynamicTruthSharedPiSuccessorRowTemplate
        rootFormula rootAssignmentCode rootAssignmentStep)) sourceRoot.

Arguments
  RawCoqRestrictedPADirectRootModeGlobalSourceStandardTailCompilerAt
  rootMode M hPA inputs rootFormula rootAssignmentCode rootAssignmentStep
  outerPrefix : clear implicits.

Theorem
    raw_rootModeGlobalSourceStandardTailCompilerAt_of_append_concrete_row :
  forall rootMode (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    boundName rootFormula rootAssignmentCode rootAssignmentStep outerPrefix,
  rootMode = 0 \/ rootMode = 1 ->
  coqFourStateTableAppendOpenedTemplateGlobalRowsAtRootTerms rootMode
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate
      rootFormula rootAssignmentCode rootAssignmentStep
      (ttParameter boundName) =
    coqFourStateTableAppendOpenedTemplateGlobalRows rootMode
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate
      (ttParameter boundName) ->
  RawCoqRestrictedPADirectRootModeAppendConcreteRowStandardTailCompilerAt
    rootMode M hPA inputs boundName rootFormula rootAssignmentCode
      rootAssignmentStep outerPrefix ->
  RawCoqRestrictedPADirectRootModeGlobalSourceStandardTailCompilerAt
    rootMode M hPA inputs rootFormula rootAssignmentCode rootAssignmentStep
      outerPrefix.
Proof.
  intros rootMode M hPA inputs boundName rootFormula rootAssignmentCode
    rootAssignmentStep outerPrefix hrootMode hrowStable hresources
    baseWitnesses.
  unfold
    RawCoqRestrictedPADirectRootModeAppendConcreteRowStandardTailCompilerAt
    in hresources.
  destruct (hresources baseWitnesses) as
    (suffix & modeCode & modeStep & formulaCode & formulaStep &
      assignmentCodeCode & assignmentCodeStep &
      assignmentStepCode & assignmentStepStep &
      appendRoot & rowRoot & happend & hrow).
  cbn zeta in happend, hrow.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  set (allWitnesses := baseWitnesses ++ suffix).
  set (sourceWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      allWitnesses (raw_zero M)).
  set (sourceContext := rawTemplateContextCode translation
    (embedPAContext (map witnessedAxiom allWitnesses))).
  assert (hsource : RawCodedPAAxiomWitnessContext M
      sourceWitnessList sourceContext).
  {
    unfold sourceWitnessList, sourceContext, allWitnesses, translation.
    exact (raw_directEmbeddedPAAxiomWitnessContext
      M hPA inputs (baseWitnesses ++ suffix)).
  }
  destruct
    (raw_codedPALocalProofOf_dynamic_truth_shared_global_at_root_terms_of_append_and_concrete_row_on_witnessed_tail
      M hPA translation
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      sourceWitnessList sourceContext rootMode boundName
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      rootFormula rootAssignmentCode rootAssignmentStep
      outerPrefix appendRoot rowRoot hrootMode hrowStable
      hsource happend hrow) as [sourceRoot hsourceRoot].
  exists suffix, sourceRoot.
  cbn zeta.
  unfold sourceContext, allWitnesses, translation in hsourceRoot.
  exact hsourceRoot.
Qed.

Theorem
    raw_directFormulaStandardTailCompilerAt_of_rootMode_rerooted_append_concrete_row :
  forall rootMode (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    readyContext rootFormula rootAssignmentCode rootAssignmentStep
    consequence,
  rootMode = 0 \/ rootMode = 1 ->
  RawCoqRestrictedPADirectReadyContextStandardWitnessAffine readyContext ->
  coqFourStateTableAppendOpenedTemplateGlobalRowsAtRootTerms rootMode
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate
      rootFormula rootAssignmentCode rootAssignmentStep
      (ttParameter coqDynamicTruthAppendRowBoundParameterName) =
    coqFourStateTableAppendOpenedTemplateGlobalRows rootMode
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate
      (ttParameter coqDynamicTruthAppendRowBoundParameterName) ->
  rawDirectTemplateFormula inputs
      (coqFourStateTableAppendTemplateGlobalSourceAtRootTerms rootMode
        coqDynamicTruthSharedSigmaSuccessorRowTemplate
        coqDynamicTruthSharedPiSuccessorRowTemplate
        rootFormula rootAssignmentCode rootAssignmentStep) =
    rawDirectTemplateFormula inputs consequence ->
  RawCoqRestrictedPADirectRootModeAppendConcreteRowStandardTailCompilerAt
    rootMode M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      rootFormula rootAssignmentCode rootAssignmentStep (readyContext []) ->
  RawCoqRestrictedPADirectFormulaStandardTailCompilerAt
    M hPA inputs readyContext consequence.
Proof.
  intros rootMode M hPA inputs readyContext rootFormula
    rootAssignmentCode rootAssignmentStep consequence hrootMode haffine
    hrows hidentification hresources.
  pose proof
    (raw_rootModeGlobalSourceStandardTailCompilerAt_of_append_concrete_row
      rootMode M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      rootFormula rootAssignmentCode rootAssignmentStep (readyContext [])
      hrootMode hrows hresources) as hglobal.
  intros baseWitnesses.
  destruct (hglobal baseWitnesses) as
    (suffix & sourceRoot & hsourceRoot).
  cbn zeta in hsourceRoot.
  exists suffix, sourceRoot.
  rewrite haffine.
  rewrite rawTemplateContextCode_app_on_tail.
  rewrite <- hidentification.
  exact hsourceRoot.
Qed.

(** ------------------------------------------------------------------
    Native aligned mode-one and mode-zero truth consequences. *)

Definition
    RawCoqRestrictedPADirectExistentialEliminationBinderContextTruthConsequenceStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawCoqRestrictedPADirectFormulaStandardTailCompilerAt
    M hPA inputs
    coqRestrictedPADirectStrongStepExistentialEliminationReadyContext
    coqRestrictedPADirectExistentialEliminationBinderContextTruthTemplate.

Definition
    RawCoqRestrictedPADirectExistentialEliminationResultTruthConsequenceStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawCoqRestrictedPADirectFormulaStandardTailCompilerAt
    M hPA inputs
    coqRestrictedPADirectStrongStepExistentialEliminationReadyContext
    coqRestrictedPADirectExistentialEliminationResultTruthTemplate.

Arguments
  RawCoqRestrictedPADirectExistentialEliminationBinderContextTruthConsequenceStandardTailCompiler
  M hPA inputs : clear implicits.
Arguments
  RawCoqRestrictedPADirectExistentialEliminationResultTruthConsequenceStandardTailCompiler
  M hPA inputs : clear implicits.

(** These finite equalities are deliberately specialized to the two live
    Ex-E tuples.  They are the syntactic side conditions which make the
    append eliminator honest in the presence of opaque successor rows. *)
Lemma
    coqRestrictedPADirectExistentialElimination_mode_one_binder_rows_stable :
  coqFourStateTableAppendOpenedTemplateGlobalRowsAtRootTerms 1
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate
      coqRestrictedPADirectExistentialEliminationBinderContextTerm
      (ttVar 9) (ttVar 8)
      (ttParameter coqDynamicTruthAppendRowBoundParameterName) =
    coqFourStateTableAppendOpenedTemplateGlobalRows 1
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate
      (ttParameter coqDynamicTruthAppendRowBoundParameterName).
Proof. vm_compute. reflexivity. Qed.

Lemma
    coqRestrictedPADirectExistentialElimination_mode_zero_result_rows_stable :
  coqFourStateTableAppendOpenedTemplateGlobalRowsAtRootTerms 0
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate
      coqRestrictedPADirectExistentialEliminationResultFormulaTerm
      (ttVar 9) (ttVar 8)
      (ttParameter coqDynamicTruthAppendRowBoundParameterName) =
    coqFourStateTableAppendOpenedTemplateGlobalRows 0
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate
      (ttParameter coqDynamicTruthAppendRowBoundParameterName).
Proof. vm_compute. reflexivity. Qed.

Lemma raw_existentialElimination_mode_one_binder_source_aligned : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
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
  rawDirectTemplateFormula inputs
      (coqFourStateTableAppendTemplateGlobalSourceAtRootTerms 1
        coqDynamicTruthSharedSigmaSuccessorRowTemplate
        coqDynamicTruthSharedPiSuccessorRowTemplate
        coqRestrictedPADirectExistentialEliminationBinderContextTerm
        (ttVar 9) (ttVar 8)) =
    rawDirectTemplateFormula inputs
      coqRestrictedPADirectExistentialEliminationBinderContextTruthTemplate.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hstructural.
  rewrite (proj2
    (raw_dynamicTruthNativeAligned_global_evidence_reroot
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
      inputs hstructural)
    coqRestrictedPADirectExistentialEliminationBinderContextTerm
    (ttVar 9) (ttVar 8)).
  reflexivity.
Qed.

Lemma raw_existentialElimination_mode_zero_result_source_aligned : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
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
  rawDirectTemplateFormula inputs
      (coqFourStateTableAppendTemplateGlobalSourceAtRootTerms 0
        coqDynamicTruthSharedSigmaSuccessorRowTemplate
        coqDynamicTruthSharedPiSuccessorRowTemplate
        coqRestrictedPADirectExistentialEliminationResultFormulaTerm
        (ttVar 9) (ttVar 8)) =
    rawDirectTemplateFormula inputs
      coqRestrictedPADirectExistentialEliminationResultTruthTemplate.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hstructural.
  rewrite (proj1
    (raw_dynamicTruthNativeAligned_global_evidence_reroot
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
      inputs hstructural)
    coqRestrictedPADirectExistentialEliminationResultFormulaTerm
    (ttVar 9) (ttVar 8)).
  reflexivity.
Qed.

Theorem
    raw_existentialEliminationBinderContextTruthConsequence_standardTailCompiler_of_aligned_append_concrete_row :
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
  RawCoqRestrictedPADirectModeOneAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectExistentialEliminationBinderContextTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepExistentialEliminationReadyContext []) ->
  RawCoqRestrictedPADirectExistentialEliminationBinderContextTruthConsequenceStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hstructural hresources.
  exact
    (raw_directFormulaStandardTailCompilerAt_of_rootMode_rerooted_append_concrete_row
      1 M hPA inputs
      coqRestrictedPADirectStrongStepExistentialEliminationReadyContext
      coqRestrictedPADirectExistentialEliminationBinderContextTerm
      (ttVar 9) (ttVar 8)
      coqRestrictedPADirectExistentialEliminationBinderContextTruthTemplate
      (or_intror eq_refl)
      coqRestrictedPADirectExistentialEliminationReadyContext_app_witnesses
      coqRestrictedPADirectExistentialElimination_mode_one_binder_rows_stable
      (raw_existentialElimination_mode_one_binder_source_aligned
        M hPA tail predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
        inputs hstructural)
      hresources).
Qed.

Theorem
    raw_existentialEliminationResultTruthConsequence_standardTailCompiler_of_aligned_append_concrete_row :
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
      coqRestrictedPADirectExistentialEliminationResultFormulaTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepExistentialEliminationReadyContext []) ->
  RawCoqRestrictedPADirectExistentialEliminationResultTruthConsequenceStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hstructural hresources.
  exact
    (raw_directFormulaStandardTailCompilerAt_of_rerooted_append_concrete_row
      M hPA inputs
      coqRestrictedPADirectStrongStepExistentialEliminationReadyContext
      coqRestrictedPADirectExistentialEliminationResultFormulaTerm
      (ttVar 9) (ttVar 8)
      coqRestrictedPADirectExistentialEliminationResultTruthTemplate
      coqRestrictedPADirectExistentialEliminationReadyContext_app_witnesses
      coqRestrictedPADirectExistentialElimination_mode_zero_result_rows_stable
      (raw_existentialElimination_mode_zero_result_source_aligned
        M hPA tail predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
        inputs hstructural)
      hresources).
Qed.

(** ------------------------------------------------------------------
    Introduce exactly the antecedents displayed by the two public laws. *)

Definition
    coqRestrictedPADirectExistentialEliminationBinderContextAntecedents
    : list TemplateFormula :=
  [coqRestrictedPADirectExistentialEliminationContextShiftTemplate;
   coqRestrictedPADirectAssumptionWitnessContextTruthTemplate;
   coqRestrictedPADirectExistentialEliminationBodyTruthTemplate].

Definition
    coqRestrictedPADirectExistentialEliminationDynamicTruthAntecedents
    : list TemplateFormula :=
  [coqRestrictedPADirectExistentialEliminationFormulaCodeTemplate;
   coqRestrictedPADirectExistentialEliminationConclusionShiftTemplate;
   coqRestrictedPADirectExistentialEliminationExistentialTruthTemplate;
   tfImp coqRestrictedPADirectExistentialEliminationBodyTruthTemplate
     coqRestrictedPADirectExistentialEliminationBinderContextTruthTemplate;
   tfImp coqRestrictedPADirectExistentialEliminationBinderContextTruthTemplate
     coqRestrictedPADirectExistentialEliminationShiftedResultTruthTemplate].

Lemma
    coqRestrictedPADirectExistentialElimination_binder_law_impChain :
  coqTemplateImpChain
      coqRestrictedPADirectExistentialEliminationBinderContextAntecedents
      coqRestrictedPADirectExistentialEliminationBinderContextTruthTemplate =
    coqRestrictedPADirectExistentialEliminationBinderContextTruthLawTemplate.
Proof. reflexivity. Qed.

Lemma
    coqRestrictedPADirectExistentialElimination_dynamic_law_impChain :
  coqTemplateImpChain
      coqRestrictedPADirectExistentialEliminationDynamicTruthAntecedents
      coqRestrictedPADirectExistentialEliminationResultTruthTemplate =
    coqRestrictedPADirectExistentialEliminationDynamicTruthLawTemplate.
Proof. reflexivity. Qed.

Definition
    RawCoqRestrictedPADirectExistentialEliminationBinderContextTruthLawStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawCoqRestrictedPADirectFormulaStandardTailCompilerAt
    M hPA inputs
    coqRestrictedPADirectStrongStepExistentialEliminationReadyContext
    coqRestrictedPADirectExistentialEliminationBinderContextTruthLawTemplate.

Definition
    RawCoqRestrictedPADirectExistentialEliminationDynamicTruthLawStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawCoqRestrictedPADirectFormulaStandardTailCompilerAt
    M hPA inputs
    coqRestrictedPADirectStrongStepExistentialEliminationReadyContext
    coqRestrictedPADirectExistentialEliminationDynamicTruthLawTemplate.

Arguments
  RawCoqRestrictedPADirectExistentialEliminationBinderContextTruthLawStandardTailCompiler
  M hPA inputs : clear implicits.
Arguments
  RawCoqRestrictedPADirectExistentialEliminationDynamicTruthLawStandardTailCompiler
  M hPA inputs : clear implicits.

Theorem
    raw_existentialEliminationBinderContextTruthLaw_standardTailCompiler_of_consequence :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectExistentialEliminationBinderContextTruthConsequenceStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectExistentialEliminationBinderContextTruthLawStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA inputs hconsequence.
  pose proof
    (raw_directImpChainStandardTailCompilerAt_of_consequence
      M hPA inputs
      coqRestrictedPADirectStrongStepExistentialEliminationReadyContext
      coqRestrictedPADirectExistentialEliminationBinderContextAntecedents
      coqRestrictedPADirectExistentialEliminationBinderContextTruthTemplate
      hconsequence) as hchain.
  rewrite
    coqRestrictedPADirectExistentialElimination_binder_law_impChain
    in hchain.
  exact hchain.
Qed.

Theorem
    raw_existentialEliminationDynamicTruthLaw_standardTailCompiler_of_consequence :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectExistentialEliminationResultTruthConsequenceStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectExistentialEliminationDynamicTruthLawStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA inputs hconsequence.
  pose proof
    (raw_directImpChainStandardTailCompilerAt_of_consequence
      M hPA inputs
      coqRestrictedPADirectStrongStepExistentialEliminationReadyContext
      coqRestrictedPADirectExistentialEliminationDynamicTruthAntecedents
      coqRestrictedPADirectExistentialEliminationResultTruthTemplate
      hconsequence) as hchain.
  rewrite
    coqRestrictedPADirectExistentialElimination_dynamic_law_impChain
    in hchain.
  exact hchain.
Qed.

Corollary
    raw_existentialEliminationBinderContextTruthLaw_standardTailCompiler_of_aligned_append_concrete_row :
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
  RawCoqRestrictedPADirectModeOneAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectExistentialEliminationBinderContextTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepExistentialEliminationReadyContext []) ->
  RawCoqRestrictedPADirectExistentialEliminationBinderContextTruthLawStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hstructural hresources.
  apply
    raw_existentialEliminationBinderContextTruthLaw_standardTailCompiler_of_consequence.
  exact
    (raw_existentialEliminationBinderContextTruthConsequence_standardTailCompiler_of_aligned_append_concrete_row
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
      inputs hstructural hresources).
Qed.

Corollary
    raw_existentialEliminationDynamicTruthLaw_standardTailCompiler_of_aligned_append_concrete_row :
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
      coqRestrictedPADirectExistentialEliminationResultFormulaTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepExistentialEliminationReadyContext []) ->
  RawCoqRestrictedPADirectExistentialEliminationDynamicTruthLawStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hstructural hresources.
  apply
    raw_existentialEliminationDynamicTruthLaw_standardTailCompiler_of_consequence.
  exact
    (raw_existentialEliminationResultTruthConsequence_standardTailCompiler_of_aligned_append_concrete_row
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
      inputs hstructural hresources).
Qed.

(** ------------------------------------------------------------------
    Synchronize the four exact roots on one selected witness suffix. *)

Definition
    RawCoqRestrictedPADirectExistentialEliminationBinderContextTruthLawRootAtWitnesses
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (witnesses : StandardPAAxiomWitnessPrefix) : Prop :=
  RawCoqRestrictedPADirectFormulaLocalProofAt
    M hPA inputs
    coqRestrictedPADirectStrongStepExistentialEliminationReadyContext
    coqRestrictedPADirectExistentialEliminationBinderContextTruthLawTemplate
    (embedPAContext (map witnessedAxiom witnesses)).

Definition
    RawCoqRestrictedPADirectExistentialEliminationDynamicTruthLawRootAtWitnesses
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (witnesses : StandardPAAxiomWitnessPrefix) : Prop :=
  RawCoqRestrictedPADirectFormulaLocalProofAt
    M hPA inputs
    coqRestrictedPADirectStrongStepExistentialEliminationReadyContext
    coqRestrictedPADirectExistentialEliminationDynamicTruthLawTemplate
    (embedPAContext (map witnessedAxiom witnesses)).

Definition
    RawCoqRestrictedPADirectExistentialEliminationSemanticRootsAtWitnesses
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (witnesses : StandardPAAxiomWitnessPrefix) : Prop :=
  RawCoqRestrictedPADirectExistentialEliminationSemanticRoots
    M hPA inputs (embedPAContext (map witnessedAxiom witnesses)).

Definition
    RawCoqRestrictedPADirectExistentialEliminationSemanticRootsStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawCoqStandardWitnessTailCompiler
    (RawCoqRestrictedPADirectExistentialEliminationSemanticRootsAtWitnesses
      M hPA inputs).

Arguments
  RawCoqRestrictedPADirectExistentialEliminationBinderContextTruthLawRootAtWitnesses
  M hPA inputs witnesses : clear implicits.
Arguments
  RawCoqRestrictedPADirectExistentialEliminationDynamicTruthLawRootAtWitnesses
  M hPA inputs witnesses : clear implicits.
Arguments
  RawCoqRestrictedPADirectExistentialEliminationSemanticRootsAtWitnesses
  M hPA inputs witnesses : clear implicits.
Arguments
  RawCoqRestrictedPADirectExistentialEliminationSemanticRootsStandardTailCompiler
  M hPA inputs : clear implicits.

Theorem
    raw_existentialEliminationBinderContextTruthLawRootAtWitnesses_append_stable :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqStandardWitnessTailAppendStable
    (RawCoqRestrictedPADirectExistentialEliminationBinderContextTruthLawRootAtWitnesses
      M hPA inputs).
Proof.
  intros M hPA inputs.
  unfold
    RawCoqRestrictedPADirectExistentialEliminationBinderContextTruthLawRootAtWitnesses,
    RawCoqRestrictedPADirectFormulaLocalProofAt.
  exact
    (raw_codedPALocalProof_affine_context_root_append_stable
      M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      coqRestrictedPADirectStrongStepExistentialEliminationReadyContext
      coqRestrictedPADirectExistentialEliminationReadyContext_app_witnesses
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectExistentialEliminationBinderContextTruthLawTemplate)).
Qed.

Theorem
    raw_existentialEliminationDynamicTruthLawRootAtWitnesses_append_stable :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqStandardWitnessTailAppendStable
    (RawCoqRestrictedPADirectExistentialEliminationDynamicTruthLawRootAtWitnesses
      M hPA inputs).
Proof.
  intros M hPA inputs.
  unfold
    RawCoqRestrictedPADirectExistentialEliminationDynamicTruthLawRootAtWitnesses,
    RawCoqRestrictedPADirectFormulaLocalProofAt.
  exact
    (raw_codedPALocalProof_affine_context_root_append_stable
      M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      coqRestrictedPADirectStrongStepExistentialEliminationReadyContext
      coqRestrictedPADirectExistentialEliminationReadyContext_app_witnesses
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectExistentialEliminationDynamicTruthLawTemplate)).
Qed.

Theorem
    raw_existentialEliminationSemanticRootsAtWitnesses_append_stable :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqStandardWitnessTailAppendStable
    (RawCoqRestrictedPADirectExistentialEliminationSemanticRootsAtWitnesses
      M hPA inputs).
Proof.
  intros M hPA inputs witnesses suffix hroots.
  unfold
    RawCoqRestrictedPADirectExistentialEliminationSemanticRootsAtWitnesses,
    RawCoqRestrictedPADirectExistentialEliminationSemanticRoots
    in hroots |- *.
  cbn zeta in hroots |- *.
  destruct hroots as [hex [hbinder [hbody hdynamic]]].
  repeat split.
  - exact
      ((raw_codedPALocalProof_affine_context_root_append_stable
        M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawDirectStructuralTemplatePAAgreement M hPA inputs)
        coqRestrictedPADirectStrongStepExistentialEliminationReadyContext
        coqRestrictedPADirectExistentialEliminationReadyContext_app_witnesses
        (rawDirectTemplateFormula inputs
          coqRestrictedPADirectExistentialEliminationExistentialChildLawTemplate))
        witnesses suffix hex).
  - exact
      (raw_existentialEliminationBinderContextTruthLawRootAtWitnesses_append_stable
        M hPA inputs witnesses suffix hbinder).
  - exact
      ((raw_codedPALocalProof_affine_context_root_append_stable
        M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawDirectStructuralTemplatePAAgreement M hPA inputs)
        coqRestrictedPADirectStrongStepExistentialEliminationReadyContext
        coqRestrictedPADirectExistentialEliminationReadyContext_app_witnesses
        (rawDirectTemplateFormula inputs
          coqRestrictedPADirectExistentialEliminationBodyChildLawTemplate))
        witnesses suffix hbody).
  - exact
      (raw_existentialEliminationDynamicTruthLawRootAtWitnesses_append_stable
        M hPA inputs witnesses suffix hdynamic).
Qed.

(** Public endpoint: the two child laws require no premise.  Structural
    alignment and exactly one literal row compiler for each native truth
    mode supply the binder and result laws. *)
Theorem
    raw_existentialEliminationSemanticRoots_standardTailCompiler_of_aligned_append_concrete_rows :
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
  RawCoqRestrictedPADirectModeOneAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectExistentialEliminationBinderContextTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepExistentialEliminationReadyContext []) ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectExistentialEliminationResultFormulaTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepExistentialEliminationReadyContext []) ->
  RawCoqRestrictedPADirectExistentialEliminationSemanticRootsStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hstructural hbinderResources hresultResources.
  pose proof
    (raw_existentialEliminationChildLawRoots_standardTailCompiler
      M hPA inputs) as hchildrenCompiler.
  pose proof
    (raw_existentialEliminationBinderContextTruthLaw_standardTailCompiler_of_aligned_append_concrete_row
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
      inputs hstructural hbinderResources) as hbinderCompilerDirect.
  pose proof
    (raw_existentialEliminationDynamicTruthLaw_standardTailCompiler_of_aligned_append_concrete_row
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
      inputs hstructural hresultResources) as hdynamicCompilerDirect.

  assert (hbinderCompiler : RawCoqStandardWitnessTailCompiler
      (RawCoqRestrictedPADirectExistentialEliminationBinderContextTruthLawRootAtWitnesses
        M hPA inputs)).
  {
    exact hbinderCompilerDirect.
  }
  assert (hdynamicCompiler : RawCoqStandardWitnessTailCompiler
      (RawCoqRestrictedPADirectExistentialEliminationDynamicTruthLawRootAtWitnesses
        M hPA inputs)).
  {
    exact hdynamicCompilerDirect.
  }
  pose proof
    (raw_coqStandardWitnessTailCompiler_and
      (RawCoqRestrictedPADirectExistentialEliminationChildLawRootsAtWitnesses
        M hPA inputs)
      (RawCoqRestrictedPADirectExistentialEliminationBinderContextTruthLawRootAtWitnesses
        M hPA inputs)
      (raw_existentialEliminationChildLawRootsAtWitnesses_append_stable
        M hPA inputs)
      hchildrenCompiler hbinderCompiler) as hchildBinderCompiler.
  assert (hchildBinderStable :
    RawCoqStandardWitnessTailAppendStable
      (fun witnesses =>
        RawCoqRestrictedPADirectExistentialEliminationChildLawRootsAtWitnesses
          M hPA inputs witnesses /\
        RawCoqRestrictedPADirectExistentialEliminationBinderContextTruthLawRootAtWitnesses
          M hPA inputs witnesses)).
  {
    apply raw_coqStandardWitnessTailAppendStable_and.
    - apply
        raw_existentialEliminationChildLawRootsAtWitnesses_append_stable.
    - apply
        raw_existentialEliminationBinderContextTruthLawRootAtWitnesses_append_stable.
  }
  pose proof
    (raw_coqStandardWitnessTailCompiler_and
      (fun witnesses =>
        RawCoqRestrictedPADirectExistentialEliminationChildLawRootsAtWitnesses
          M hPA inputs witnesses /\
        RawCoqRestrictedPADirectExistentialEliminationBinderContextTruthLawRootAtWitnesses
          M hPA inputs witnesses)
      (RawCoqRestrictedPADirectExistentialEliminationDynamicTruthLawRootAtWitnesses
        M hPA inputs)
      hchildBinderStable hchildBinderCompiler hdynamicCompiler)
    as hallCompiler.
  intros baseWitnesses.
  destruct (hallCompiler baseWitnesses) as
    [suffix [[[hex hbody] hbinder] hdynamic]].
  exists suffix.
  unfold
    RawCoqRestrictedPADirectExistentialEliminationSemanticRootsAtWitnesses,
    RawCoqRestrictedPADirectExistentialEliminationSemanticRoots.
  cbn zeta.
  exact (conj hex (conj hbinder (conj hbody hdynamic))).
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationSemanticRootsCompilation.
