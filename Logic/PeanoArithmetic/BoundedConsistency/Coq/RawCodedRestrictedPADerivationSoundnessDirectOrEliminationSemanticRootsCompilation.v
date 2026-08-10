(**
  Compile the four exact Or-E semantic roots on one standard PA witness tail.

  The represented opened-coverage source is arithmetic and therefore works
  for arbitrary direct structural inputs.  It yields all three recursive
  child interfaces, including the genuine branch endpoint contexts
  [left :: Gamma] and [right :: Gamma].  We retain the resulting three
  generic child laws as an unconditional, append-stable public package.

  The exact Or-E residual has a deliberately different branch spelling:

      endpoint -> Truth(Gamma) -> Truth(disjunct) -> Truth(result).

  For opaque direct inputs, the arithmetic child interface alone cannot turn
  the two latter premises into [Truth(disjunct :: Gamma)]; that requires a
  semantic context-cons coherence law.  At the aligned boundary we need no
  extra public coherence resource: the one literal mode-zero row already
  compiles [Truth(result)].  Unused-antecedent introduction then gives both
  exact branch laws and the dynamic truth law on the very same selected
  tail.  The disjunction-child law continues to come from recursive descent.
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
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageDefinitions
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageSource.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationSemanticRootsCompilation.

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
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageDefinitions.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageSource.

(** ------------------------------------------------------------------
    The literal Or-E ready context and its common-coverage eigencontext. *)

Definition coqRestrictedPADirectOrEliminationCoverageEigenContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectOrIntroductionLeftDeepCommonCoverageBodyTemplate ::
    templateContextShift
      (coqRestrictedPADirectStrongStepOrEliminationReadyContext tail).

Arguments coqRestrictedPADirectOrEliminationCoverageEigenContext tail
  : clear implicits.

Lemma coqRestrictedPADirectOrElimination_ready_standard : forall tail,
  coqRestrictedPADirectStrongStepOrEliminationReadyContext tail =
  coqRestrictedPADirectStandardReadyContext
    coqRestrictedPADirectAssumptionOuterContextTruthTemplate
    coqRestrictedPADirectAssumptionDeepAdmissibleTemplate
    coqRestrictedPADirectOrEliminationCaseTemplate tail.
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectOrElimination_ready_restricted_in : forall tail,
  In coqRestrictedPADirectAndIntroductionDeepRestrictedTemplate
    (coqRestrictedPADirectStrongStepOrEliminationReadyContext tail).
Proof.
  intro tail.
  rewrite coqRestrictedPADirectOrElimination_ready_standard.
  unfold coqRestrictedPADirectStandardReadyContext.
  do 3 right.
  rewrite <- raw_coqRestrictedPADirectEndpointDeepContext_shape.
  unfold coqRestrictedPADirectAndIntroductionDeepRestrictedTemplate.
  apply raw_coqTemplateNestedExContext_inherited.
  unfold rawCoqRestrictedPADirectStrongStepEndpointTail.
  left. reflexivity.
Qed.

Lemma coqRestrictedPADirectOrElimination_ready_admissible_in : forall tail,
  In coqRestrictedPADirectAndIntroductionDeepAdmissibleTemplate
    (coqRestrictedPADirectStrongStepOrEliminationReadyContext tail).
Proof.
  intro tail.
  rewrite coqRestrictedPADirectOrElimination_ready_standard.
  unfold coqRestrictedPADirectStandardReadyContext.
  right. left. reflexivity.
Qed.

Lemma coqRestrictedPADirectOrElimination_ready_case_in : forall tail,
  In coqRestrictedPADirectOrEliminationCaseTemplate
    (coqRestrictedPADirectStrongStepOrEliminationReadyContext tail).
Proof.
  intro tail.
  rewrite coqRestrictedPADirectOrElimination_ready_standard.
  unfold coqRestrictedPADirectStandardReadyContext.
  right. right. left. reflexivity.
Qed.

Lemma coqRestrictedPADirectOrElimination_eigen_inherited : forall
    tail formula,
  In formula (coqRestrictedPADirectStrongStepOrEliminationReadyContext tail) ->
  In (templateFormulaRename S formula)
    (coqRestrictedPADirectOrEliminationCoverageEigenContext tail).
Proof.
  intros tail formula hin. right.
  unfold templateContextShift, templateContextRename.
  apply in_map. exact hin.
Qed.

Lemma coqRestrictedPADirectOrElimination_eigen_coverage_body_in : forall tail,
  In coqRestrictedPADirectOrIntroductionLeftDeepCommonCoverageBodyTemplate
    (coqRestrictedPADirectOrEliminationCoverageEigenContext tail).
Proof. intros tail. left. reflexivity. Qed.

Lemma coqRestrictedPADirectOrElimination_eigen_restricted_in : forall tail,
  In (templateFormulaRename S
      coqRestrictedPADirectAndIntroductionDeepRestrictedTemplate)
    (coqRestrictedPADirectOrEliminationCoverageEigenContext tail).
Proof.
  intro tail.
  apply coqRestrictedPADirectOrElimination_eigen_inherited.
  apply coqRestrictedPADirectOrElimination_ready_restricted_in.
Qed.

Lemma coqRestrictedPADirectOrElimination_eigen_admissible_in : forall tail,
  In (templateFormulaRename S
      coqRestrictedPADirectAndIntroductionDeepAdmissibleTemplate)
    (coqRestrictedPADirectOrEliminationCoverageEigenContext tail).
Proof.
  intro tail.
  apply coqRestrictedPADirectOrElimination_eigen_inherited.
  apply coqRestrictedPADirectOrElimination_ready_admissible_in.
Qed.

Lemma coqRestrictedPADirectOrElimination_eigen_case_in : forall tail,
  In (templateFormulaRename S
      coqRestrictedPADirectOrEliminationCaseTemplate)
    (coqRestrictedPADirectOrEliminationCoverageEigenContext tail).
Proof.
  intro tail.
  apply coqRestrictedPADirectOrElimination_eigen_inherited.
  apply coqRestrictedPADirectOrElimination_ready_case_in.
Qed.

Lemma coqRestrictedPADirectOrEliminationReadyContext_app_witnesses :
    forall witnesses,
  coqRestrictedPADirectStrongStepOrEliminationReadyContext
      (embedPAContext (map witnessedAxiom witnesses)) =
  coqRestrictedPADirectStrongStepOrEliminationReadyContext [] ++
    embedPAContext (map witnessedAxiom witnesses).
Proof.
  intro witnesses.
  rewrite coqRestrictedPADirectOrElimination_ready_standard.
  change
    (coqRestrictedPADirectStandardReadyContext
      coqRestrictedPADirectAssumptionOuterContextTruthTemplate
      coqRestrictedPADirectAssumptionDeepAdmissibleTemplate
      coqRestrictedPADirectOrEliminationCaseTemplate
      (embedPAContext (map witnessedAxiom witnesses)) =
    coqRestrictedPADirectStandardReadyContext
      coqRestrictedPADirectAssumptionOuterContextTruthTemplate
      coqRestrictedPADirectAssumptionDeepAdmissibleTemplate
      coqRestrictedPADirectOrEliminationCaseTemplate [] ++
      embedPAContext (map witnessedAxiom witnesses)).
  apply coqRestrictedPADirectStandardReadyContext_app_witnesses.
Qed.

Lemma coqRestrictedPADirectOrEliminationCoverageEigenContext_app_witnesses :
    forall witnesses,
  coqRestrictedPADirectOrEliminationCoverageEigenContext
      (embedPAContext (map witnessedAxiom witnesses)) =
  coqRestrictedPADirectOrEliminationCoverageEigenContext [] ++
    embedPAContext (map witnessedAxiom witnesses).
Proof.
  intro witnesses.
  unfold coqRestrictedPADirectOrEliminationCoverageEigenContext.
  rewrite coqRestrictedPADirectOrEliminationReadyContext_app_witnesses.
  rewrite templateContextShift_app,
    templateContextShift_embedPAAxiomWitnesses_fixed.
  reflexivity.
Qed.

Lemma raw_orEliminationCoverageEigenContext_witnessed_code : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation -> forall witnesses,
  rawTemplateContextCode translation
    (coqRestrictedPADirectOrEliminationCoverageEigenContext
      (embedPAContext (map witnessedAxiom witnesses))) =
  rawTemplateContextCodeOnTail translation
    (rawStandardPAAxiomWitnessPrefixContextCode M witnesses (raw_zero M))
    (coqRestrictedPADirectOrEliminationCoverageEigenContext []).
Proof.
  intros M translation hagreement witnesses.
  rewrite
    coqRestrictedPADirectOrEliminationCoverageEigenContext_app_witnesses.
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
    RawCoqRestrictedPADirectOrEliminationOpenedCoverageCompilerLawRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectOrEliminationCoverageEigenContext tail))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectOrEliminationOpenedCoverageLawTemplate)
      root.

Definition RawCoqRestrictedPADirectOrEliminationChildInterfacesRootAt
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectStrongStepOrEliminationReadyContext tail))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectOrEliminationChildInterfacesTemplate)
      root.

Arguments
  RawCoqRestrictedPADirectOrEliminationOpenedCoverageCompilerLawRoot
  M hPA inputs tail : clear implicits.
Arguments RawCoqRestrictedPADirectOrEliminationChildInterfacesRootAt
  M hPA inputs tail : clear implicits.

Theorem raw_orEliminationChildInterfacesRoot_of_openedCoverageCompiler :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectOrEliminationOpenedCoverageCompilerLawRoot
    M hPA inputs tail ->
  RawCoqRestrictedPADirectOrEliminationChildInterfacesRootAt
    M hPA inputs tail.
Proof.
  intros M hPA inputs tail (openedRoot & hopened).
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  set (readyContext :=
    coqRestrictedPADirectStrongStepOrEliminationReadyContext tail).
  set (eigenContext :=
    coqRestrictedPADirectOrEliminationCoverageEigenContext tail).
  set (readyCode := rawTemplateContextCode translation readyContext).

  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAssumption
      M hPA translation readyContext
      coqRestrictedPADirectAndIntroductionDeepAdmissibleTemplate
      (coqRestrictedPADirectOrElimination_ready_admissible_in tail))
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
      (coqRestrictedPADirectOrElimination_eigen_restricted_in tail))
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
      (coqRestrictedPADirectOrElimination_eigen_admissible_in tail))
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
      (coqRestrictedPADirectOrElimination_eigen_coverage_body_in tail))
    as hcoverageBody.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAssumption
      M hPA translation eigenContext
      (templateFormulaRename S
        coqRestrictedPADirectOrEliminationCaseTemplate)
      (coqRestrictedPADirectOrElimination_eigen_case_in tail))
    as hcase.

  unfold coqRestrictedPADirectOrEliminationOpenedCoverageLawTemplate
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
        coqRestrictedPADirectOrEliminationChildInterfacesTemplate)
      (rawTemplateFormula translation
        (templateFormulaRename S
          coqRestrictedPADirectOrEliminationChildInterfacesTemplate))
      _ _ hcommonCoverage
      (raw_templateContext_shift M hPA translation readyContext)
      (rawTemplateFormula_shift translation
        coqRestrictedPADirectOrEliminationChildInterfacesTemplate)
      hresultShifted) as hresult.
  lazymatch type of hresult with
  | RawCodedPALocalProofOf _ _ _ ?resultRoot =>
      exists resultRoot; exact hresult
  end.
Qed.

(** ------------------------------------------------------------------
    Instantiate the universal PA source and transport it under a prefix. *)

Theorem raw_codedPALocalProof_orEliminationOpenedCoverageLaw_on_witnessed_base :
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
        (coqRestrictedPADirectOrEliminationCoverageEigenContext []))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectOrEliminationOpenedCoverageLawTemplate)
      root.
Proof.
  intros M hPA inputs baseWitnessList baseContext hbase.
  exact
    (raw_codedPALocalProof_universalSourceInstance_under_directPrefix
      M hPA inputs baseWitnessList baseContext
      coqRestrictedPADirectOrEliminationOpenedCoverageSourceBodyFormula
      (rawDirectTemplateTerm inputs
        coqRestrictedPASoundnessLowerLevelTerm)
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectOrEliminationOpenedCoverageLawTemplate)
      (coqRestrictedPADirectOrEliminationCoverageEigenContext [])
      hbase
      PA_proves_coqRestrictedPADirectOrEliminationOpenedCoverageSource
      (rawDirect_orEliminationOpenedCoverageSource_substitution
        M hPA inputs)).
Qed.

Definition
    RawCoqRestrictedPADirectOrEliminationChildInterfacesStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawCoqStandardWitnessTailCompiler
    (fun witnesses =>
      RawCoqRestrictedPADirectOrEliminationChildInterfacesRootAt
        M hPA inputs (embedPAContext (map witnessedAxiom witnesses))).

Arguments
  RawCoqRestrictedPADirectOrEliminationChildInterfacesStandardTailCompiler
  M hPA inputs : clear implicits.

Theorem raw_orEliminationChildInterfaces_standardTailCompiler : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectOrEliminationChildInterfacesStandardTailCompiler
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
    (raw_codedPALocalProof_orEliminationOpenedCoverageLaw_on_witnessed_base
      M hPA inputs (raw_zero M) (raw_zero M) hempty)
    as (sourceWitnesses & sourceRoot & _hwitnessed & hsource).
  assert (hcompiler :
    RawCoqRestrictedPADirectOrEliminationOpenedCoverageCompilerLawRoot
      M hPA inputs
      (embedPAContext (map witnessedAxiom sourceWitnesses))).
  {
    exists sourceRoot.
    rewrite
      (raw_orEliminationCoverageEigenContext_witnessed_code M
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawDirectStructuralTemplatePAAgreement M hPA inputs)
        sourceWitnesses).
    exact hsource.
  }
  destruct
    (raw_orEliminationChildInterfacesRoot_of_openedCoverageCompiler
      M hPA inputs
      (embedPAContext (map witnessedAxiom sourceWitnesses)) hcompiler)
    as [interfaceRoot hinterface].
  rewrite coqRestrictedPADirectOrEliminationReadyContext_app_witnesses
    in hinterface.
  destruct
    (raw_codedPALocalProof_standardWitnessTail_surround_under_prefix
      M hPA
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      (coqRestrictedPADirectStrongStepOrEliminationReadyContext [])
      baseWitnesses sourceWitnesses []
      (rawTemplateFormula
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        coqRestrictedPADirectOrEliminationChildInterfacesTemplate)
      interfaceRoot hinterface) as [transportedRoot htransported].
  exists sourceWitnesses, transportedRoot.
  cbn [List.app] in htransported.
  rewrite app_nil_r in htransported.
  rewrite coqRestrictedPADirectOrEliminationReadyContext_app_witnesses.
  exact htransported.
Qed.

(** ------------------------------------------------------------------
    Project all three interfaces and retain the honest recursive laws.

    In particular, the two branch formulas below retain their endpoint
    context.  They are stronger structural information than the exact Or-E
    fields in the sense that they expose what recursive descent actually
    consumes; they are not silently rewritten through an unavailable opaque
    context-cons equation. *)

Definition coqRestrictedPADirectOrEliminationChildEndpointTemplate
    (child : CoqRestrictedPAOrEliminationChild) : TemplateFormula :=
  match child with
  | CoqOrEliminationDisjunctionChild =>
      coqRestrictedPADirectOrEliminationDisjunctionEndpointTemplate
  | CoqOrEliminationLeftBranchChild =>
      coqRestrictedPADirectOrEliminationLeftEndpointTemplate
  | CoqOrEliminationRightBranchChild =>
      coqRestrictedPADirectOrEliminationRightEndpointTemplate
  end.

Definition coqRestrictedPADirectOrEliminationRecursiveChildLawTemplate
    (child : CoqRestrictedPAOrEliminationChild) : TemplateFormula :=
  tfImp (coqRestrictedPADirectOrEliminationChildEndpointTemplate child)
    (tfImp
      (coqRestrictedPADirectAndIntroductionChildContextTruthTemplate
        (coqRestrictedPADirectOrEliminationChildTerm child)
        (coqRestrictedPADirectOrEliminationChildContextTerm child)
        (coqRestrictedPADirectOrEliminationChildConclusionTerm child))
      (coqRestrictedPADirectAndIntroductionChildTruthTemplate
        (coqRestrictedPADirectOrEliminationChildTerm child)
        (coqRestrictedPADirectOrEliminationChildContextTerm child)
        (coqRestrictedPADirectOrEliminationChildConclusionTerm child))).

Lemma coqRestrictedPADirectOrElimination_disjunction_recursive_law_agreement :
  coqRestrictedPADirectOrEliminationRecursiveChildLawTemplate
      CoqOrEliminationDisjunctionChild =
    coqRestrictedPADirectOrEliminationDisjunctionChildLawTemplate.
Proof. reflexivity. Qed.

Definition
    RawCoqRestrictedPADirectOrEliminationRecursiveChildLawRootsAtWitnesses
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (witnesses : StandardPAAxiomWitnessPrefix) : Prop :=
  let translation := rawDirectStructuralTemplateTranslation M hPA inputs in
  let ready := coqRestrictedPADirectStrongStepOrEliminationReadyContext
    (embedPAContext (map witnessedAxiom witnesses)) in
  (exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation ready)
      (rawTemplateFormula translation
        (coqRestrictedPADirectOrEliminationRecursiveChildLawTemplate
          CoqOrEliminationDisjunctionChild)) root) /\
  (exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation ready)
      (rawTemplateFormula translation
        (coqRestrictedPADirectOrEliminationRecursiveChildLawTemplate
          CoqOrEliminationLeftBranchChild)) root) /\
  (exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation ready)
      (rawTemplateFormula translation
        (coqRestrictedPADirectOrEliminationRecursiveChildLawTemplate
          CoqOrEliminationRightBranchChild)) root).

Definition
    RawCoqRestrictedPADirectOrEliminationRecursiveChildLawRootsStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawCoqStandardWitnessTailCompiler
    (RawCoqRestrictedPADirectOrEliminationRecursiveChildLawRootsAtWitnesses
      M hPA inputs).

Arguments
  RawCoqRestrictedPADirectOrEliminationRecursiveChildLawRootsAtWitnesses
  M hPA inputs witnesses : clear implicits.
Arguments
  RawCoqRestrictedPADirectOrEliminationRecursiveChildLawRootsStandardTailCompiler
  M hPA inputs : clear implicits.

Lemma coqRestrictedPADirectOrElimination_ready_prefix_in : forall tail,
  In coqRestrictedPADirectAndIntroductionDeepStrongPrefixTemplate
    (coqRestrictedPADirectStrongStepOrEliminationReadyContext tail).
Proof.
  intro tail.
  rewrite coqRestrictedPADirectOrElimination_ready_standard.
  unfold coqRestrictedPADirectStandardReadyContext.
  apply coqRestrictedPASameContextUnary_deep_prefix_in.
Qed.

Theorem raw_orEliminationRecursiveChildLawRoots_standardTailCompiler :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectOrEliminationRecursiveChildLawRootsStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA inputs baseWitnesses.
  destruct
    (raw_orEliminationChildInterfaces_standardTailCompiler
      M hPA inputs baseWitnesses)
    as [suffix [interfacesRoot hinterfaces]].
  set (translation := rawDirectStructuralTemplateTranslation M hPA inputs).
  set (allWitnesses := baseWitnesses ++ suffix).
  set (ready := coqRestrictedPADirectStrongStepOrEliminationReadyContext
    (embedPAContext (map witnessedAxiom allWitnesses))).
  change (RawCodedPALocalProofOf M
    (rawTemplateContextCode translation ready)
    (rawTemplateFormula translation
      (tfAnd
        (coqRestrictedPADirectOrEliminationChildInterfaceTemplate
          CoqOrEliminationDisjunctionChild)
        (tfAnd
          (coqRestrictedPADirectOrEliminationChildInterfaceTemplate
            CoqOrEliminationLeftBranchChild)
          (coqRestrictedPADirectOrEliminationChildInterfaceTemplate
            CoqOrEliminationRightBranchChild))))
    interfacesRoot) in hinterfaces.
  rewrite rawTemplateFormula_and in hinterfaces.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA _ _ _ _ hinterfaces)
    as hdisjunctionInterface.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA _ _ _ _ hinterfaces)
    as hbranchInterfaces.
  rewrite rawTemplateFormula_and in hbranchInterfaces.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA _ _ _ _
    hbranchInterfaces) as hleftInterface.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA _ _ _ _
    hbranchInterfaces) as hrightInterface.

  assert (hdisjunctionInterfaceRoot :
    RawCoqRestrictedPASameContextUnaryChildInterfaceRootAt M
      translation ready
      (coqRestrictedPADirectOrEliminationChildTerm
        CoqOrEliminationDisjunctionChild)
      (coqRestrictedPADirectOrEliminationChildContextTerm
        CoqOrEliminationDisjunctionChild)
      (coqRestrictedPADirectOrEliminationChildConclusionTerm
        CoqOrEliminationDisjunctionChild)).
  {
    lazymatch type of hdisjunctionInterface with
    | RawCodedPALocalProofOf _ _ _ ?root =>
        exists root; exact hdisjunctionInterface
    end.
  }
  assert (hleftInterfaceRoot :
    RawCoqRestrictedPASameContextUnaryChildInterfaceRootAt M
      translation ready
      (coqRestrictedPADirectOrEliminationChildTerm
        CoqOrEliminationLeftBranchChild)
      (coqRestrictedPADirectOrEliminationChildContextTerm
        CoqOrEliminationLeftBranchChild)
      (coqRestrictedPADirectOrEliminationChildConclusionTerm
        CoqOrEliminationLeftBranchChild)).
  {
    lazymatch type of hleftInterface with
    | RawCodedPALocalProofOf _ _ _ ?root =>
        exists root; exact hleftInterface
    end.
  }
  assert (hrightInterfaceRoot :
    RawCoqRestrictedPASameContextUnaryChildInterfaceRootAt M
      translation ready
      (coqRestrictedPADirectOrEliminationChildTerm
        CoqOrEliminationRightBranchChild)
      (coqRestrictedPADirectOrEliminationChildContextTerm
        CoqOrEliminationRightBranchChild)
      (coqRestrictedPADirectOrEliminationChildConclusionTerm
        CoqOrEliminationRightBranchChild)).
  {
    lazymatch type of hrightInterface with
    | RawCodedPALocalProofOf _ _ _ ?root =>
        exists root; exact hrightInterface
    end.
  }

  destruct
    (raw_sameContextUnary_recursiveChildLawRootAt_of_interface
      M hPA translation ready
      (coqRestrictedPADirectOrEliminationChildTerm
        CoqOrEliminationDisjunctionChild)
      (coqRestrictedPADirectOrEliminationChildContextTerm
        CoqOrEliminationDisjunctionChild)
      (coqRestrictedPADirectOrEliminationChildConclusionTerm
        CoqOrEliminationDisjunctionChild)
      (coqRestrictedPADirectOrEliminationChildEndpointTemplate
        CoqOrEliminationDisjunctionChild)
      (coqRestrictedPADirectOrElimination_ready_prefix_in
        (embedPAContext (map witnessedAxiom allWitnesses)))
      hdisjunctionInterfaceRoot) as [disjunctionRoot hdisjunctionLaw].
  destruct
    (raw_sameContextUnary_recursiveChildLawRootAt_of_interface
      M hPA translation ready
      (coqRestrictedPADirectOrEliminationChildTerm
        CoqOrEliminationLeftBranchChild)
      (coqRestrictedPADirectOrEliminationChildContextTerm
        CoqOrEliminationLeftBranchChild)
      (coqRestrictedPADirectOrEliminationChildConclusionTerm
        CoqOrEliminationLeftBranchChild)
      (coqRestrictedPADirectOrEliminationChildEndpointTemplate
        CoqOrEliminationLeftBranchChild)
      (coqRestrictedPADirectOrElimination_ready_prefix_in
        (embedPAContext (map witnessedAxiom allWitnesses)))
      hleftInterfaceRoot) as [leftRoot hleftLaw].
  destruct
    (raw_sameContextUnary_recursiveChildLawRootAt_of_interface
      M hPA translation ready
      (coqRestrictedPADirectOrEliminationChildTerm
        CoqOrEliminationRightBranchChild)
      (coqRestrictedPADirectOrEliminationChildContextTerm
        CoqOrEliminationRightBranchChild)
      (coqRestrictedPADirectOrEliminationChildConclusionTerm
        CoqOrEliminationRightBranchChild)
      (coqRestrictedPADirectOrEliminationChildEndpointTemplate
        CoqOrEliminationRightBranchChild)
      (coqRestrictedPADirectOrElimination_ready_prefix_in
        (embedPAContext (map witnessedAxiom allWitnesses)))
      hrightInterfaceRoot) as [rightRoot hrightLaw].
  exists suffix.
  unfold
    RawCoqRestrictedPADirectOrEliminationRecursiveChildLawRootsAtWitnesses.
  cbn zeta.
  split.
  - exists disjunctionRoot. exact hdisjunctionLaw.
  - split.
    + exists leftRoot. exact hleftLaw.
    + exists rightRoot. exact hrightLaw.
Qed.

Theorem
    raw_orEliminationRecursiveChildLawRootsAtWitnesses_append_stable :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqStandardWitnessTailAppendStable
    (RawCoqRestrictedPADirectOrEliminationRecursiveChildLawRootsAtWitnesses
      M hPA inputs).
Proof.
  intros M hPA inputs.
  unfold
    RawCoqRestrictedPADirectOrEliminationRecursiveChildLawRootsAtWitnesses.
  cbn zeta.
  apply raw_coqStandardWitnessTailAppendStable_and.
  - exact
      (raw_codedPALocalProof_affine_context_root_append_stable
        M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawDirectStructuralTemplatePAAgreement M hPA inputs)
        coqRestrictedPADirectStrongStepOrEliminationReadyContext
        coqRestrictedPADirectOrEliminationReadyContext_app_witnesses
        (rawDirectTemplateFormula inputs
          (coqRestrictedPADirectOrEliminationRecursiveChildLawTemplate
            CoqOrEliminationDisjunctionChild))).
  - apply raw_coqStandardWitnessTailAppendStable_and.
    + exact
        (raw_codedPALocalProof_affine_context_root_append_stable
          M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
          (rawDirectStructuralTemplatePAAgreement M hPA inputs)
          coqRestrictedPADirectStrongStepOrEliminationReadyContext
          coqRestrictedPADirectOrEliminationReadyContext_app_witnesses
          (rawDirectTemplateFormula inputs
            (coqRestrictedPADirectOrEliminationRecursiveChildLawTemplate
              CoqOrEliminationLeftBranchChild))).
    + exact
        (raw_codedPALocalProof_affine_context_root_append_stable
          M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
          (rawDirectStructuralTemplatePAAgreement M hPA inputs)
          coqRestrictedPADirectStrongStepOrEliminationReadyContext
          coqRestrictedPADirectOrEliminationReadyContext_app_witnesses
          (rawDirectTemplateFormula inputs
            (coqRestrictedPADirectOrEliminationRecursiveChildLawTemplate
              CoqOrEliminationRightBranchChild))).
Qed.

(** ------------------------------------------------------------------
    Compile result truth from the one aligned mode-zero row. *)

Definition RawCoqRestrictedPADirectOrEliminationResultTruthStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawCoqRestrictedPADirectFormulaStandardTailCompilerAt
    M hPA inputs
    coqRestrictedPADirectStrongStepOrEliminationReadyContext
    coqRestrictedPADirectOrEliminationResultTruthTemplate.

Definition RawCoqRestrictedPADirectOrEliminationLeftChildLawStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawCoqRestrictedPADirectFormulaStandardTailCompilerAt
    M hPA inputs
    coqRestrictedPADirectStrongStepOrEliminationReadyContext
    coqRestrictedPADirectOrEliminationLeftChildLawTemplate.

Definition RawCoqRestrictedPADirectOrEliminationRightChildLawStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawCoqRestrictedPADirectFormulaStandardTailCompilerAt
    M hPA inputs
    coqRestrictedPADirectStrongStepOrEliminationReadyContext
    coqRestrictedPADirectOrEliminationRightChildLawTemplate.

Definition RawCoqRestrictedPADirectOrEliminationDynamicTruthLawStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawCoqRestrictedPADirectFormulaStandardTailCompilerAt
    M hPA inputs
    coqRestrictedPADirectStrongStepOrEliminationReadyContext
    coqRestrictedPADirectOrEliminationDynamicTruthLawTemplate.

Arguments
  RawCoqRestrictedPADirectOrEliminationResultTruthStandardTailCompiler
  M hPA inputs : clear implicits.
Arguments
  RawCoqRestrictedPADirectOrEliminationLeftChildLawStandardTailCompiler
  M hPA inputs : clear implicits.
Arguments
  RawCoqRestrictedPADirectOrEliminationRightChildLawStandardTailCompiler
  M hPA inputs : clear implicits.
Arguments
  RawCoqRestrictedPADirectOrEliminationDynamicTruthLawStandardTailCompiler
  M hPA inputs : clear implicits.

Lemma coqRestrictedPADirectOrElimination_mode_zero_result_rows_stable :
  coqFourStateTableAppendOpenedTemplateGlobalRowsAtRootTerms 0
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate
      coqRestrictedPADirectOrEliminationResultFormulaTerm
      (ttVar 9) (ttVar 8)
      (ttParameter coqDynamicTruthAppendRowBoundParameterName) =
    coqFourStateTableAppendOpenedTemplateGlobalRows 0
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate
      (ttParameter coqDynamicTruthAppendRowBoundParameterName).
Proof. vm_compute. reflexivity. Qed.

Lemma raw_orElimination_mode_zero_result_source_aligned : forall
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
        coqRestrictedPADirectOrEliminationResultFormulaTerm
        (ttVar 9) (ttVar 8)) =
    rawDirectTemplateFormula inputs
      coqRestrictedPADirectOrEliminationResultTruthTemplate.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hstructural.
  rewrite (proj1
    (raw_dynamicTruthNativeAligned_global_evidence_reroot
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
      inputs hstructural)
    coqRestrictedPADirectOrEliminationResultFormulaTerm
    (ttVar 9) (ttVar 8)).
  reflexivity.
Qed.

Theorem
    raw_orEliminationResultTruth_standardTailCompiler_of_aligned_append_concrete_row :
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
      coqRestrictedPADirectOrEliminationResultFormulaTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepOrEliminationReadyContext []) ->
  RawCoqRestrictedPADirectOrEliminationResultTruthStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hstructural hresources.
  exact
    (raw_directFormulaStandardTailCompilerAt_of_rerooted_append_concrete_row
      M hPA inputs
      coqRestrictedPADirectStrongStepOrEliminationReadyContext
      coqRestrictedPADirectOrEliminationResultFormulaTerm
      (ttVar 9) (ttVar 8)
      coqRestrictedPADirectOrEliminationResultTruthTemplate
      coqRestrictedPADirectOrEliminationReadyContext_app_witnesses
      coqRestrictedPADirectOrElimination_mode_zero_result_rows_stable
      (raw_orElimination_mode_zero_result_source_aligned
        M hPA tail predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
        inputs hstructural)
      hresources).
Qed.

(** The three exact non-disjunction residuals are all K-lifts of result
    truth.  These standalone adapters are useful independently, while the
    final synchronizer below constructs all three from one invocation of the
    consequence compiler so no additional witness suffix is selected. *)

Lemma coqRestrictedPADirectOrElimination_left_child_law_imp_chain :
  coqTemplateImpChain
      [coqRestrictedPADirectOrEliminationLeftEndpointTemplate;
       coqRestrictedPADirectAssumptionWitnessContextTruthTemplate;
       coqRestrictedPADirectOrEliminationLeftTruthTemplate]
      coqRestrictedPADirectOrEliminationResultTruthTemplate =
    coqRestrictedPADirectOrEliminationLeftChildLawTemplate.
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectOrElimination_right_child_law_imp_chain :
  coqTemplateImpChain
      [coqRestrictedPADirectOrEliminationRightEndpointTemplate;
       coqRestrictedPADirectAssumptionWitnessContextTruthTemplate;
       coqRestrictedPADirectOrEliminationRightTruthTemplate]
      coqRestrictedPADirectOrEliminationResultTruthTemplate =
    coqRestrictedPADirectOrEliminationRightChildLawTemplate.
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectOrElimination_dynamic_truth_law_imp_chain :
  coqTemplateImpChain
      [coqRestrictedPADirectOrEliminationFormulaCodeTemplate;
       coqRestrictedPADirectOrEliminationDisjunctionTruthTemplate;
       tfImp coqRestrictedPADirectOrEliminationLeftTruthTemplate
         coqRestrictedPADirectOrEliminationResultTruthTemplate;
       tfImp coqRestrictedPADirectOrEliminationRightTruthTemplate
         coqRestrictedPADirectOrEliminationResultTruthTemplate]
      coqRestrictedPADirectOrEliminationResultTruthTemplate =
    coqRestrictedPADirectOrEliminationDynamicTruthLawTemplate.
Proof. reflexivity. Qed.

Theorem raw_orEliminationLeftChildLaw_standardTailCompiler_of_result_truth :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectOrEliminationResultTruthStandardTailCompiler
      M hPA inputs ->
  RawCoqRestrictedPADirectOrEliminationLeftChildLawStandardTailCompiler
      M hPA inputs.
Proof.
  intros M hPA inputs htruth.
  unfold
    RawCoqRestrictedPADirectOrEliminationLeftChildLawStandardTailCompiler.
  rewrite <- coqRestrictedPADirectOrElimination_left_child_law_imp_chain.
  exact
    (raw_directImpChainStandardTailCompilerAt_of_consequence
      M hPA inputs
      coqRestrictedPADirectStrongStepOrEliminationReadyContext
      [coqRestrictedPADirectOrEliminationLeftEndpointTemplate;
       coqRestrictedPADirectAssumptionWitnessContextTruthTemplate;
       coqRestrictedPADirectOrEliminationLeftTruthTemplate]
      coqRestrictedPADirectOrEliminationResultTruthTemplate htruth).
Qed.

Theorem raw_orEliminationRightChildLaw_standardTailCompiler_of_result_truth :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectOrEliminationResultTruthStandardTailCompiler
      M hPA inputs ->
  RawCoqRestrictedPADirectOrEliminationRightChildLawStandardTailCompiler
      M hPA inputs.
Proof.
  intros M hPA inputs htruth.
  unfold
    RawCoqRestrictedPADirectOrEliminationRightChildLawStandardTailCompiler.
  rewrite <- coqRestrictedPADirectOrElimination_right_child_law_imp_chain.
  exact
    (raw_directImpChainStandardTailCompilerAt_of_consequence
      M hPA inputs
      coqRestrictedPADirectStrongStepOrEliminationReadyContext
      [coqRestrictedPADirectOrEliminationRightEndpointTemplate;
       coqRestrictedPADirectAssumptionWitnessContextTruthTemplate;
       coqRestrictedPADirectOrEliminationRightTruthTemplate]
      coqRestrictedPADirectOrEliminationResultTruthTemplate htruth).
Qed.

Theorem raw_orEliminationDynamicTruthLaw_standardTailCompiler_of_result_truth :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectOrEliminationResultTruthStandardTailCompiler
      M hPA inputs ->
  RawCoqRestrictedPADirectOrEliminationDynamicTruthLawStandardTailCompiler
      M hPA inputs.
Proof.
  intros M hPA inputs htruth.
  unfold
    RawCoqRestrictedPADirectOrEliminationDynamicTruthLawStandardTailCompiler.
  rewrite <- coqRestrictedPADirectOrElimination_dynamic_truth_law_imp_chain.
  exact
    (raw_directImpChainStandardTailCompilerAt_of_consequence
      M hPA inputs
      coqRestrictedPADirectStrongStepOrEliminationReadyContext
      [coqRestrictedPADirectOrEliminationFormulaCodeTemplate;
       coqRestrictedPADirectOrEliminationDisjunctionTruthTemplate;
       tfImp coqRestrictedPADirectOrEliminationLeftTruthTemplate
         coqRestrictedPADirectOrEliminationResultTruthTemplate;
       tfImp coqRestrictedPADirectOrEliminationRightTruthTemplate
         coqRestrictedPADirectOrEliminationResultTruthTemplate]
      coqRestrictedPADirectOrEliminationResultTruthTemplate htruth).
Qed.

(** ------------------------------------------------------------------
    Synchronize the exact four-field public residual. *)

Definition RawCoqRestrictedPADirectOrEliminationResultTruthRootAtWitnesses
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (witnesses : StandardPAAxiomWitnessPrefix) : Prop :=
  RawCoqRestrictedPADirectFormulaLocalProofAt
    M hPA inputs
    coqRestrictedPADirectStrongStepOrEliminationReadyContext
    coqRestrictedPADirectOrEliminationResultTruthTemplate
    (embedPAContext (map witnessedAxiom witnesses)).

Definition RawCoqRestrictedPADirectOrEliminationSemanticRootsAtWitnesses
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (witnesses : StandardPAAxiomWitnessPrefix) : Prop :=
  RawCoqRestrictedPADirectOrEliminationSemanticRoots
    M hPA inputs (embedPAContext (map witnessedAxiom witnesses)).

Definition
    RawCoqRestrictedPADirectOrEliminationSemanticRootsStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawCoqStandardWitnessTailCompiler
    (RawCoqRestrictedPADirectOrEliminationSemanticRootsAtWitnesses
      M hPA inputs).

Arguments RawCoqRestrictedPADirectOrEliminationResultTruthRootAtWitnesses
  M hPA inputs witnesses : clear implicits.
Arguments RawCoqRestrictedPADirectOrEliminationSemanticRootsAtWitnesses
  M hPA inputs witnesses : clear implicits.
Arguments
  RawCoqRestrictedPADirectOrEliminationSemanticRootsStandardTailCompiler
  M hPA inputs : clear implicits.

Theorem raw_orEliminationSemanticRootsAtWitnesses_append_stable : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqStandardWitnessTailAppendStable
    (RawCoqRestrictedPADirectOrEliminationSemanticRootsAtWitnesses
      M hPA inputs).
Proof.
  intros M hPA inputs witnesses suffix hroots.
  unfold RawCoqRestrictedPADirectOrEliminationSemanticRootsAtWitnesses,
    RawCoqRestrictedPADirectOrEliminationSemanticRoots in hroots |- *.
  cbn zeta in hroots |- *.
  destruct hroots as [hdisjunction [hleft [hright hdynamic]]].
  repeat split.
  - exact
      ((raw_codedPALocalProof_affine_context_root_append_stable
        M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawDirectStructuralTemplatePAAgreement M hPA inputs)
        coqRestrictedPADirectStrongStepOrEliminationReadyContext
        coqRestrictedPADirectOrEliminationReadyContext_app_witnesses
        (rawDirectTemplateFormula inputs
          coqRestrictedPADirectOrEliminationDisjunctionChildLawTemplate))
        witnesses suffix hdisjunction).
  - exact
      ((raw_codedPALocalProof_affine_context_root_append_stable
        M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawDirectStructuralTemplatePAAgreement M hPA inputs)
        coqRestrictedPADirectStrongStepOrEliminationReadyContext
        coqRestrictedPADirectOrEliminationReadyContext_app_witnesses
        (rawDirectTemplateFormula inputs
          coqRestrictedPADirectOrEliminationLeftChildLawTemplate))
        witnesses suffix hleft).
  - exact
      ((raw_codedPALocalProof_affine_context_root_append_stable
        M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawDirectStructuralTemplatePAAgreement M hPA inputs)
        coqRestrictedPADirectStrongStepOrEliminationReadyContext
        coqRestrictedPADirectOrEliminationReadyContext_app_witnesses
        (rawDirectTemplateFormula inputs
          coqRestrictedPADirectOrEliminationRightChildLawTemplate))
        witnesses suffix hright).
  - exact
      ((raw_codedPALocalProof_affine_context_root_append_stable
        M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawDirectStructuralTemplatePAAgreement M hPA inputs)
        coqRestrictedPADirectStrongStepOrEliminationReadyContext
        coqRestrictedPADirectOrEliminationReadyContext_app_witnesses
        (rawDirectTemplateFormula inputs
          coqRestrictedPADirectOrEliminationDynamicTruthLawTemplate))
        witnesses suffix hdynamic).
Qed.

(** Exact public endpoint.  Its only non-structural premise is the literal
    mode-zero concrete row for the Or result formula. *)
Theorem
    raw_orEliminationSemanticRoots_standardTailCompiler_of_aligned_append_concrete_row :
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
      coqRestrictedPADirectOrEliminationResultFormulaTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepOrEliminationReadyContext []) ->
  RawCoqRestrictedPADirectOrEliminationSemanticRootsStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hstructural hresources.
  pose proof
    (raw_orEliminationRecursiveChildLawRoots_standardTailCompiler
      M hPA inputs) as hchildrenCompiler.
  pose proof
    (raw_orEliminationResultTruth_standardTailCompiler_of_aligned_append_concrete_row
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
      inputs hstructural hresources) as hresultCompilerDirect.
  assert (hresultCompiler : RawCoqStandardWitnessTailCompiler
      (RawCoqRestrictedPADirectOrEliminationResultTruthRootAtWitnesses
        M hPA inputs)).
  {
    exact hresultCompilerDirect.
  }
  pose proof
    (raw_coqStandardWitnessTailCompiler_and
      (RawCoqRestrictedPADirectOrEliminationRecursiveChildLawRootsAtWitnesses
        M hPA inputs)
      (RawCoqRestrictedPADirectOrEliminationResultTruthRootAtWitnesses
        M hPA inputs)
      (raw_orEliminationRecursiveChildLawRootsAtWitnesses_append_stable
        M hPA inputs)
      hchildrenCompiler hresultCompiler) as hpairedCompiler.
  intros baseWitnesses.
  destruct (hpairedCompiler baseWitnesses) as
    [suffix [hchildren hresultPackage]].
  unfold
    RawCoqRestrictedPADirectOrEliminationRecursiveChildLawRootsAtWitnesses
    in hchildren.
  cbn zeta in hchildren.
  destruct hchildren as
    [(disjunctionRoot & hdisjunction)
      [(leftGenericRoot & _hleftGeneric)
        (rightGenericRoot & _hrightGeneric)]].
  unfold RawCoqRestrictedPADirectOrEliminationResultTruthRootAtWitnesses,
    RawCoqRestrictedPADirectFormulaLocalProofAt in hresultPackage.
  destruct hresultPackage as [resultRoot hresult].
  set (translation := rawDirectStructuralTemplateTranslation M hPA inputs).
  set (allWitnesses := baseWitnesses ++ suffix).
  set (ready := coqRestrictedPADirectStrongStepOrEliminationReadyContext
    (embedPAContext (map witnessedAxiom allWitnesses))).
  change (RawCodedPALocalProofOf M
    (rawTemplateContextCode translation ready)
    (rawTemplateFormula translation
      coqRestrictedPADirectOrEliminationResultTruthTemplate)
    resultRoot) in hresult.

  destruct
    (raw_codedPALocalProofOf_iterated_unused_antecedents
      M hPA translation ready
      [coqRestrictedPADirectOrEliminationLeftEndpointTemplate;
       coqRestrictedPADirectAssumptionWitnessContextTruthTemplate;
       coqRestrictedPADirectOrEliminationLeftTruthTemplate]
      coqRestrictedPADirectOrEliminationResultTruthTemplate
      resultRoot hresult) as [leftRoot hleft].
  rewrite coqRestrictedPADirectOrElimination_left_child_law_imp_chain
    in hleft.
  destruct
    (raw_codedPALocalProofOf_iterated_unused_antecedents
      M hPA translation ready
      [coqRestrictedPADirectOrEliminationRightEndpointTemplate;
       coqRestrictedPADirectAssumptionWitnessContextTruthTemplate;
       coqRestrictedPADirectOrEliminationRightTruthTemplate]
      coqRestrictedPADirectOrEliminationResultTruthTemplate
      resultRoot hresult) as [rightRoot hright].
  rewrite coqRestrictedPADirectOrElimination_right_child_law_imp_chain
    in hright.
  destruct
    (raw_codedPALocalProofOf_iterated_unused_antecedents
      M hPA translation ready
      [coqRestrictedPADirectOrEliminationFormulaCodeTemplate;
       coqRestrictedPADirectOrEliminationDisjunctionTruthTemplate;
       tfImp coqRestrictedPADirectOrEliminationLeftTruthTemplate
         coqRestrictedPADirectOrEliminationResultTruthTemplate;
       tfImp coqRestrictedPADirectOrEliminationRightTruthTemplate
         coqRestrictedPADirectOrEliminationResultTruthTemplate]
      coqRestrictedPADirectOrEliminationResultTruthTemplate
      resultRoot hresult) as [dynamicRoot hdynamic].
  rewrite coqRestrictedPADirectOrElimination_dynamic_truth_law_imp_chain
    in hdynamic.
  rewrite
    coqRestrictedPADirectOrElimination_disjunction_recursive_law_agreement
    in hdisjunction.
  exists suffix.
  unfold RawCoqRestrictedPADirectOrEliminationSemanticRootsAtWitnesses,
    RawCoqRestrictedPADirectOrEliminationSemanticRoots.
  cbn zeta.
  split.
  - exists disjunctionRoot. exact hdisjunction.
  - split.
    + exists leftRoot. exact hleft.
    + split.
      * exists rightRoot. exact hright.
      * exists dynamicRoot. exact hdynamic.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationSemanticRootsCompilation.
