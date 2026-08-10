(**
  Represented compilation of the shared All-E / Ex-I child interface.

  The companion source proves the arithmetic opened-coverage implication
  for each of the two genuine quantifier constructor rows.  Here we compile
  that source under an arbitrary standard PA-witness prefix, eliminate the
  common coverage eigenvariable, and obtain the identical four-field child
  interface in the exact rule ready context.

  Two finite adapters then discharge the public residuals:

  - All-E combines the interface with the inherited strong prefix and adds
    its displayed endpoint antecedent;
  - Ex-I adds its six advertised antecedents by represented K proofs.  This
    is sound because the interface was already derived from the literal
    ready-context assumptions by the arithmetic source, not postulated.
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
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier
  RawCodedRestrictedPADerivationSoundnessDirectStrongStepShell
  RawCodedRestrictedPADerivationSoundnessDirectAssumptionCase
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectUniversalEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectExistentialIntroductionCase
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
  RawCodedRestrictedPADerivationSoundnessQuantifierUnaryChildInterfaceOpenedCoverageSource.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessQuantifierUnaryChildInterfaceOpenedCoverageCompilation.

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
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectStrongStepShell.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAssumptionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectUniversalEliminationCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialIntroductionCase.
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
  PABoundedRawCodedRestrictedPADerivationSoundnessQuantifierUnaryChildInterfaceOpenedCoverageSource.

(** ------------------------------------------------------------------
    One literal ready context and its common-coverage eigencontext. *)

Definition coqRestrictedPAQuantifierUnaryReadyContext
    (rule : CoqRestrictedPAQuantifierUnaryRule)
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectStandardReadyContext
    coqRestrictedPADirectAssumptionOuterContextTruthTemplate
    coqRestrictedPADirectAssumptionDeepAdmissibleTemplate
    (coqRestrictedPAQuantifierUnaryCaseTemplate rule)
    tail.

Definition coqRestrictedPAQuantifierUnaryCoverageEigenContext
    (rule : CoqRestrictedPAQuantifierUnaryRule)
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectOrIntroductionLeftDeepCommonCoverageBodyTemplate ::
    templateContextShift
      (coqRestrictedPAQuantifierUnaryReadyContext rule tail).

Arguments coqRestrictedPAQuantifierUnaryReadyContext rule tail
  : clear implicits.
Arguments coqRestrictedPAQuantifierUnaryCoverageEigenContext rule tail
  : clear implicits.

Lemma coqRestrictedPAQuantifierUnary_ready_universalElimination : forall tail,
  coqRestrictedPAQuantifierUnaryReadyContext
      CoqQuantifierUniversalElimination tail =
  coqRestrictedPADirectStrongStepUniversalEliminationReadyContext tail.
Proof. reflexivity. Qed.

Lemma
    coqRestrictedPAQuantifierUnary_ready_existentialIntroduction : forall tail,
  coqRestrictedPAQuantifierUnaryReadyContext
      CoqQuantifierExistentialIntroduction tail =
  coqRestrictedPADirectStrongStepExistentialIntroductionReadyContext tail.
Proof. reflexivity. Qed.

Lemma coqRestrictedPAQuantifierUnary_ready_restricted_in : forall rule tail,
  In coqRestrictedPADirectAndIntroductionDeepRestrictedTemplate
    (coqRestrictedPAQuantifierUnaryReadyContext rule tail).
Proof.
  intros rule tail.
  unfold coqRestrictedPAQuantifierUnaryReadyContext,
    coqRestrictedPADirectStandardReadyContext.
  do 3 right.
  rewrite <- raw_coqRestrictedPADirectEndpointDeepContext_shape.
  unfold coqRestrictedPADirectAndIntroductionDeepRestrictedTemplate.
  apply raw_coqTemplateNestedExContext_inherited.
  unfold rawCoqRestrictedPADirectStrongStepEndpointTail.
  left. reflexivity.
Qed.

Lemma coqRestrictedPAQuantifierUnary_ready_admissible_in : forall rule tail,
  In coqRestrictedPADirectAndIntroductionDeepAdmissibleTemplate
    (coqRestrictedPAQuantifierUnaryReadyContext rule tail).
Proof.
  intros rule tail.
  unfold coqRestrictedPAQuantifierUnaryReadyContext,
    coqRestrictedPADirectStandardReadyContext.
  right. left. reflexivity.
Qed.

Lemma coqRestrictedPAQuantifierUnary_ready_case_in : forall rule tail,
  In (coqRestrictedPAQuantifierUnaryCaseTemplate rule)
    (coqRestrictedPAQuantifierUnaryReadyContext rule tail).
Proof.
  intros rule tail.
  unfold coqRestrictedPAQuantifierUnaryReadyContext,
    coqRestrictedPADirectStandardReadyContext.
  right. right. left. reflexivity.
Qed.

Lemma coqRestrictedPAQuantifierUnary_eigen_inherited : forall
    rule tail formula,
  In formula (coqRestrictedPAQuantifierUnaryReadyContext rule tail) ->
  In (templateFormulaRename S formula)
    (coqRestrictedPAQuantifierUnaryCoverageEigenContext rule tail).
Proof.
  intros rule tail formula hin. right.
  unfold templateContextShift, templateContextRename.
  apply in_map. exact hin.
Qed.

Lemma coqRestrictedPAQuantifierUnary_eigen_coverage_body_in : forall
    rule tail,
  In coqRestrictedPADirectOrIntroductionLeftDeepCommonCoverageBodyTemplate
    (coqRestrictedPAQuantifierUnaryCoverageEigenContext rule tail).
Proof. intros rule tail. left. reflexivity. Qed.

Lemma coqRestrictedPAQuantifierUnary_eigen_restricted_in : forall rule tail,
  In (templateFormulaRename S
      coqRestrictedPADirectAndIntroductionDeepRestrictedTemplate)
    (coqRestrictedPAQuantifierUnaryCoverageEigenContext rule tail).
Proof.
  intros rule tail.
  apply coqRestrictedPAQuantifierUnary_eigen_inherited.
  apply coqRestrictedPAQuantifierUnary_ready_restricted_in.
Qed.

Lemma coqRestrictedPAQuantifierUnary_eigen_admissible_in : forall rule tail,
  In (templateFormulaRename S
      coqRestrictedPADirectAndIntroductionDeepAdmissibleTemplate)
    (coqRestrictedPAQuantifierUnaryCoverageEigenContext rule tail).
Proof.
  intros rule tail.
  apply coqRestrictedPAQuantifierUnary_eigen_inherited.
  apply coqRestrictedPAQuantifierUnary_ready_admissible_in.
Qed.

Lemma coqRestrictedPAQuantifierUnary_eigen_case_in : forall rule tail,
  In (templateFormulaRename S
      (coqRestrictedPAQuantifierUnaryCaseTemplate rule))
    (coqRestrictedPAQuantifierUnaryCoverageEigenContext rule tail).
Proof.
  intros rule tail.
  apply coqRestrictedPAQuantifierUnary_eigen_inherited.
  apply coqRestrictedPAQuantifierUnary_ready_case_in.
Qed.

Lemma coqRestrictedPAQuantifierUnaryReadyContext_app_witnesses : forall
    rule witnesses,
  coqRestrictedPAQuantifierUnaryReadyContext rule
      (embedPAContext (map witnessedAxiom witnesses)) =
  coqRestrictedPAQuantifierUnaryReadyContext rule [] ++
    embedPAContext (map witnessedAxiom witnesses).
Proof.
  intros rule witnesses.
  unfold coqRestrictedPAQuantifierUnaryReadyContext.
  apply coqRestrictedPADirectStandardReadyContext_app_witnesses.
Qed.

Lemma coqRestrictedPAQuantifierUnaryCoverageEigenContext_app_witnesses :
    forall rule witnesses,
  coqRestrictedPAQuantifierUnaryCoverageEigenContext rule
      (embedPAContext (map witnessedAxiom witnesses)) =
  coqRestrictedPAQuantifierUnaryCoverageEigenContext rule [] ++
    embedPAContext (map witnessedAxiom witnesses).
Proof.
  intros rule witnesses.
  unfold coqRestrictedPAQuantifierUnaryCoverageEigenContext.
  rewrite coqRestrictedPAQuantifierUnaryReadyContext_app_witnesses.
  rewrite templateContextShift_app,
    templateContextShift_embedPAAxiomWitnesses_fixed.
  reflexivity.
Qed.

Lemma raw_quantifierUnaryCoverageEigenContext_witnessed_code : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation -> forall rule witnesses,
  rawTemplateContextCode translation
    (coqRestrictedPAQuantifierUnaryCoverageEigenContext rule
      (embedPAContext (map witnessedAxiom witnesses))) =
  rawTemplateContextCodeOnTail translation
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M))
    (coqRestrictedPAQuantifierUnaryCoverageEigenContext rule []).
Proof.
  intros M translation hagreement rule witnesses.
  rewrite
    coqRestrictedPAQuantifierUnaryCoverageEigenContext_app_witnesses.
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
    The rule-independent represented extraction kernel. *)

Definition RawCoqRestrictedPAQuantifierUnaryOpenedCoverageCompilerLawRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (rule : CoqRestrictedPAQuantifierUnaryRule)
    (tail : TemplateContext) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPAQuantifierUnaryCoverageEigenContext rule tail))
      (rawDirectTemplateFormula inputs
        (coqRestrictedPAQuantifierUnaryOpenedCoverageLawTemplate rule))
      root.

Arguments RawCoqRestrictedPAQuantifierUnaryOpenedCoverageCompilerLawRoot
  M hPA inputs rule tail : clear implicits.

Theorem raw_quantifierUnaryChildInterfaceRoot_of_openedCoverageCompiler :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M) rule tail,
  RawCoqRestrictedPAQuantifierUnaryOpenedCoverageCompilerLawRoot
    M hPA inputs rule tail ->
  RawCoqRestrictedPASameContextUnaryChildInterfaceRootAt M
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    (coqRestrictedPAQuantifierUnaryReadyContext rule tail)
    coqRestrictedPAQuantifierUnaryChildTerm
    coqRestrictedPAQuantifierUnaryWitnessContextTerm
    coqRestrictedPAQuantifierUnaryChildConclusionTerm.
Proof.
  intros M hPA inputs rule tail (openedRoot & hopened).
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  set (readyContext :=
    coqRestrictedPAQuantifierUnaryReadyContext rule tail).
  set (eigenContext :=
    coqRestrictedPAQuantifierUnaryCoverageEigenContext rule tail).
  set (readyCode := rawTemplateContextCode translation readyContext).

  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAssumption
      M hPA translation readyContext
      coqRestrictedPADirectAndIntroductionDeepAdmissibleTemplate
      (coqRestrictedPAQuantifierUnary_ready_admissible_in rule tail))
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
      (coqRestrictedPAQuantifierUnary_eigen_restricted_in rule tail))
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
      (coqRestrictedPAQuantifierUnary_eigen_admissible_in rule tail))
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
      (coqRestrictedPAQuantifierUnary_eigen_coverage_body_in rule tail))
    as hcoverageBody.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAssumption
      M hPA translation eigenContext
      (templateFormulaRename S
        (coqRestrictedPAQuantifierUnaryCaseTemplate rule))
      (coqRestrictedPAQuantifierUnary_eigen_case_in rule tail))
    as hcase.

  unfold coqRestrictedPAQuantifierUnaryOpenedCoverageLawTemplate in hopened.
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
        coqRestrictedPAQuantifierUnaryChildInterfaceTemplate)
      (rawTemplateFormula translation
        (templateFormulaRename S
          coqRestrictedPAQuantifierUnaryChildInterfaceTemplate))
      _ _ hcommonCoverage
      (raw_templateContext_shift M hPA translation readyContext)
      (rawTemplateFormula_shift translation
        coqRestrictedPAQuantifierUnaryChildInterfaceTemplate)
      hresultShifted) as hresult.
  lazymatch type of hresult with
  | RawCodedPALocalProofOf _ _ _ ?resultRoot =>
      exists resultRoot; exact hresult
  end.
Qed.

(** ------------------------------------------------------------------
    Instantiate the PA source and make it prefix-composable. *)

Theorem
    raw_codedPALocalProof_quantifierUnaryOpenedCoverageLaw_on_witnessed_base :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M) rule
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
        (coqRestrictedPAQuantifierUnaryCoverageEigenContext rule []))
      (rawDirectTemplateFormula inputs
        (coqRestrictedPAQuantifierUnaryOpenedCoverageLawTemplate rule))
      root.
Proof.
  intros M hPA inputs rule baseWitnessList baseContext hbase.
  exact
    (raw_codedPALocalProof_universalSourceInstance_under_directPrefix
      M hPA inputs baseWitnessList baseContext
      (coqRestrictedPAQuantifierUnaryOpenedCoverageSourceBodyFormula rule)
      (rawDirectTemplateTerm inputs
        coqRestrictedPASoundnessLowerLevelTerm)
      (rawDirectTemplateFormula inputs
        (coqRestrictedPAQuantifierUnaryOpenedCoverageLawTemplate rule))
      (coqRestrictedPAQuantifierUnaryCoverageEigenContext rule [])
      hbase
      (PA_proves_coqRestrictedPAQuantifierUnaryOpenedCoverageSource rule)
      (rawDirect_quantifierUnaryOpenedCoverageSource_substitution
        M hPA inputs rule)).
Qed.

Definition
    RawCoqRestrictedPAQuantifierUnaryChildInterfaceStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (rule : CoqRestrictedPAQuantifierUnaryRule) : Prop :=
  RawCoqRestrictedPASameContextUnaryChildInterfaceStandardTailCompilerAt
    M hPA inputs
    (coqRestrictedPAQuantifierUnaryReadyContext rule)
    coqRestrictedPAQuantifierUnaryChildTerm
    coqRestrictedPAQuantifierUnaryWitnessContextTerm
    coqRestrictedPAQuantifierUnaryChildConclusionTerm.

Arguments RawCoqRestrictedPAQuantifierUnaryChildInterfaceStandardTailCompiler
  M hPA inputs rule : clear implicits.

Theorem raw_quantifierUnaryChildInterface_standardTailCompiler : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M) rule,
  RawCoqRestrictedPAQuantifierUnaryChildInterfaceStandardTailCompiler
    M hPA inputs rule.
Proof.
  intros M hPA inputs rule baseWitnesses.
  assert (hempty : RawCodedPAAxiomWitnessContext M
      (raw_zero M) (raw_zero M)).
  {
    pose proof (raw_codedPAAxiomWitnessContext_standard M hPA []) as h.
    cbn [rawQuotedPAAxiomWitnessList rawListCode map] in h.
    exact h.
  }
  destruct
    (raw_codedPALocalProof_quantifierUnaryOpenedCoverageLaw_on_witnessed_base
      M hPA inputs rule (raw_zero M) (raw_zero M) hempty)
    as (sourceWitnesses & sourceRoot & _hwitnessed & hsource).
  assert (hcompiler :
    RawCoqRestrictedPAQuantifierUnaryOpenedCoverageCompilerLawRoot
      M hPA inputs rule
      (embedPAContext (map witnessedAxiom sourceWitnesses))).
  {
    exists sourceRoot.
    rewrite (raw_quantifierUnaryCoverageEigenContext_witnessed_code M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      rule sourceWitnesses).
    exact hsource.
  }
  destruct
    (raw_quantifierUnaryChildInterfaceRoot_of_openedCoverageCompiler
      M hPA inputs rule
      (embedPAContext (map witnessedAxiom sourceWitnesses)) hcompiler)
    as [interfaceRoot hinterface].
  rewrite coqRestrictedPAQuantifierUnaryReadyContext_app_witnesses
    in hinterface.
  destruct
    (raw_codedPALocalProof_standardWitnessTail_surround_under_prefix
      M hPA
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      (coqRestrictedPAQuantifierUnaryReadyContext rule [])
      baseWitnesses sourceWitnesses []
      (rawTemplateFormula
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        coqRestrictedPAQuantifierUnaryChildInterfaceTemplate)
      interfaceRoot hinterface) as [transportedRoot htransported].
  exists sourceWitnesses.
  unfold RawCoqRestrictedPASameContextUnaryChildInterfaceRootAt.
  exists transportedRoot.
  cbn [List.app] in htransported.
  rewrite app_nil_r in htransported.
  rewrite coqRestrictedPAQuantifierUnaryReadyContext_app_witnesses.
  exact htransported.
Qed.

(** ------------------------------------------------------------------
    All-E: interface -> exact recursive-child residual. *)

Lemma coqRestrictedPAQuantifierUnary_ready_prefix_in : forall rule tail,
  In coqRestrictedPADirectAndIntroductionDeepStrongPrefixTemplate
    (coqRestrictedPAQuantifierUnaryReadyContext rule tail).
Proof.
  intros rule tail.
  unfold coqRestrictedPAQuantifierUnaryReadyContext,
    coqRestrictedPADirectStandardReadyContext.
  apply coqRestrictedPASameContextUnary_deep_prefix_in.
Qed.

Lemma
    coqRestrictedPADirectUniversalElimination_child_context_truth_agreement :
  coqRestrictedPADirectAndIntroductionChildContextTruthTemplate
    coqRestrictedPAQuantifierUnaryChildTerm
    coqRestrictedPAQuantifierUnaryWitnessContextTerm
    coqRestrictedPAQuantifierUnaryChildConclusionTerm =
  coqRestrictedPADirectAssumptionWitnessContextTruthTemplate.
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectUniversalElimination_child_truth_agreement :
  coqRestrictedPADirectAndIntroductionChildTruthTemplate
    coqRestrictedPAQuantifierUnaryChildTerm
    coqRestrictedPAQuantifierUnaryWitnessContextTerm
    coqRestrictedPAQuantifierUnaryChildConclusionTerm =
  coqRestrictedPADirectUniversalEliminationFormulaTruthTemplate.
Proof. reflexivity. Qed.

Definition
    RawCoqRestrictedPADirectUniversalEliminationRecursiveChildAtWitnesses
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (witnesses : StandardPAAxiomWitnessPrefix) : Prop :=
  RawCoqRestrictedPADirectUniversalEliminationRecursiveChildLawRoot
    M hPA inputs (embedPAContext (map witnessedAxiom witnesses)).

Definition
    RawCoqRestrictedPADirectUniversalEliminationRecursiveChildStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawCoqStandardWitnessTailCompiler
    (RawCoqRestrictedPADirectUniversalEliminationRecursiveChildAtWitnesses
      M hPA inputs).

Arguments
  RawCoqRestrictedPADirectUniversalEliminationRecursiveChildAtWitnesses
  M hPA inputs witnesses : clear implicits.
Arguments
  RawCoqRestrictedPADirectUniversalEliminationRecursiveChildStandardTailCompiler
  M hPA inputs : clear implicits.

Theorem
    raw_universalEliminationRecursiveChild_standardTailCompiler : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectUniversalEliminationRecursiveChildStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA inputs baseWitnesses.
  destruct (raw_quantifierUnaryChildInterface_standardTailCompiler
    M hPA inputs CoqQuantifierUniversalElimination baseWitnesses)
    as [suffix hinterface].
  exists suffix.
  destruct
    (raw_sameContextUnary_recursiveChildLawRootAt_of_interface
      M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqRestrictedPAQuantifierUnaryReadyContext
        CoqQuantifierUniversalElimination
        (embedPAContext (map witnessedAxiom (baseWitnesses ++ suffix))))
      coqRestrictedPAQuantifierUnaryChildTerm
      coqRestrictedPAQuantifierUnaryWitnessContextTerm
      coqRestrictedPAQuantifierUnaryChildConclusionTerm
      coqRestrictedPADirectUniversalEliminationChildEndpointTemplate
      (coqRestrictedPAQuantifierUnary_ready_prefix_in
        CoqQuantifierUniversalElimination
        (embedPAContext (map witnessedAxiom (baseWitnesses ++ suffix))))
      hinterface) as [lawRoot hlaw].
  unfold
    RawCoqRestrictedPADirectUniversalEliminationRecursiveChildAtWitnesses,
    RawCoqRestrictedPADirectUniversalEliminationRecursiveChildLawRoot.
  exists lawRoot.
  rewrite
    coqRestrictedPAQuantifierUnary_ready_universalElimination in hlaw.
  rewrite
    coqRestrictedPADirectUniversalElimination_child_context_truth_agreement,
    coqRestrictedPADirectUniversalElimination_child_truth_agreement in hlaw.
  exact hlaw.
Qed.

Lemma
    coqRestrictedPADirectUniversalEliminationReadyContext_app_witnesses_from_quantifierUnary :
  forall witnesses,
  coqRestrictedPADirectStrongStepUniversalEliminationReadyContext
      (embedPAContext (map witnessedAxiom witnesses)) =
  coqRestrictedPADirectStrongStepUniversalEliminationReadyContext [] ++
    embedPAContext (map witnessedAxiom witnesses).
Proof.
  intro witnesses.
  rewrite <- coqRestrictedPAQuantifierUnary_ready_universalElimination.
  apply coqRestrictedPAQuantifierUnaryReadyContext_app_witnesses.
Qed.

Theorem
    raw_universalEliminationRecursiveChildAtWitnesses_append_stable :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqStandardWitnessTailAppendStable
    (RawCoqRestrictedPADirectUniversalEliminationRecursiveChildAtWitnesses
      M hPA inputs).
Proof.
  intros M hPA inputs.
  unfold
    RawCoqRestrictedPADirectUniversalEliminationRecursiveChildAtWitnesses,
    RawCoqRestrictedPADirectUniversalEliminationRecursiveChildLawRoot.
  exact
    (raw_codedPALocalProof_affine_context_root_append_stable
      M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      coqRestrictedPADirectStrongStepUniversalEliminationReadyContext
      coqRestrictedPADirectUniversalEliminationReadyContext_app_witnesses_from_quantifierUnary
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectUniversalEliminationRecursiveChildLawTemplate)).
Qed.

(** ------------------------------------------------------------------
    Ex-I: direct interface -> exact six-antecedent interface law. *)

Definition
    RawCoqRestrictedPADirectExistentialIntroductionChildInterfaceLawAtWitnesses
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (witnesses : StandardPAAxiomWitnessPrefix) : Prop :=
  RawCoqRestrictedPADirectExistentialIntroductionChildInterfaceLawRootAt
    M (rawDirectStructuralTemplateTranslation M hPA inputs)
    (coqRestrictedPADirectStrongStepExistentialIntroductionReadyContext
      (embedPAContext (map witnessedAxiom witnesses))).

Definition
    RawCoqRestrictedPADirectExistentialIntroductionChildInterfaceLawStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawCoqStandardWitnessTailCompiler
    (RawCoqRestrictedPADirectExistentialIntroductionChildInterfaceLawAtWitnesses
      M hPA inputs).

Arguments
  RawCoqRestrictedPADirectExistentialIntroductionChildInterfaceLawAtWitnesses
  M hPA inputs witnesses : clear implicits.
Arguments
  RawCoqRestrictedPADirectExistentialIntroductionChildInterfaceLawStandardTailCompiler
  M hPA inputs : clear implicits.

Theorem
    raw_existentialIntroductionChildInterfaceLaw_standardTailCompiler :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectExistentialIntroductionChildInterfaceLawStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA inputs baseWitnesses.
  destruct (raw_quantifierUnaryChildInterface_standardTailCompiler
    M hPA inputs CoqQuantifierExistentialIntroduction baseWitnesses)
    as [suffix [interfaceRoot hinterface]].
  exists suffix.
  unfold
    RawCoqRestrictedPADirectExistentialIntroductionChildInterfaceLawAtWitnesses.
  set (translation := rawDirectStructuralTemplateTranslation M hPA inputs).
  set (tail :=
    embedPAContext (map witnessedAxiom (baseWitnesses ++ suffix))).
  set (ready :=
    coqRestrictedPADirectStrongStepExistentialIntroductionReadyContext tail).
  change (RawCodedPALocalProofOf M
    (rawTemplateContextCode translation ready)
    (rawTemplateFormula translation
      coqRestrictedPADirectExistentialIntroductionChildInterfaceResultTemplate)
    interfaceRoot) in hinterface.

  destruct (raw_codedPALocalProofOf_sameContextUnary_add_unused_antecedent
    M hPA translation ready
    coqRestrictedPADirectExistentialIntroductionChildInterfaceResultTemplate
    coqRestrictedPADirectExistentialIntroductionDeepAdmissibleTemplate
    interfaceRoot hinterface) as [root1 hroot1].
  destruct (raw_codedPALocalProofOf_sameContextUnary_add_unused_antecedent
    M hPA translation ready
    (tfImp coqRestrictedPADirectExistentialIntroductionDeepAdmissibleTemplate
      coqRestrictedPADirectExistentialIntroductionChildInterfaceResultTemplate)
    coqRestrictedPADirectExistentialIntroductionChildEndpointTemplate
    root1 hroot1) as [root2 hroot2].
  destruct (raw_codedPALocalProofOf_sameContextUnary_add_unused_antecedent
    M hPA translation ready
    (tfImp coqRestrictedPADirectExistentialIntroductionChildEndpointTemplate
      (tfImp
        coqRestrictedPADirectExistentialIntroductionDeepAdmissibleTemplate
        coqRestrictedPADirectExistentialIntroductionChildInterfaceResultTemplate))
    coqRestrictedPADirectExistentialIntroductionSubstitutionTemplate
    root2 hroot2) as [root3 hroot3].
  destruct (raw_codedPALocalProofOf_sameContextUnary_add_unused_antecedent
    M hPA translation ready
    (tfImp coqRestrictedPADirectExistentialIntroductionSubstitutionTemplate
      (tfImp
        coqRestrictedPADirectExistentialIntroductionChildEndpointTemplate
        (tfImp
          coqRestrictedPADirectExistentialIntroductionDeepAdmissibleTemplate
          coqRestrictedPADirectExistentialIntroductionChildInterfaceResultTemplate)))
    coqRestrictedPADirectExistentialIntroductionFormulaCodeTemplate
    root3 hroot3) as [root4 hroot4].
  destruct (raw_codedPALocalProofOf_sameContextUnary_add_unused_antecedent
    M hPA translation ready
    (tfImp coqRestrictedPADirectExistentialIntroductionFormulaCodeTemplate
      (tfImp
        coqRestrictedPADirectExistentialIntroductionSubstitutionTemplate
        (tfImp
          coqRestrictedPADirectExistentialIntroductionChildEndpointTemplate
          (tfImp
            coqRestrictedPADirectExistentialIntroductionDeepAdmissibleTemplate
            coqRestrictedPADirectExistentialIntroductionChildInterfaceResultTemplate))))
    coqRestrictedPADirectExistentialIntroductionCodeEqualityTemplate
    root4 hroot4) as [root5 hroot5].
  destruct (raw_codedPALocalProofOf_sameContextUnary_add_unused_antecedent
    M hPA translation ready
    (tfImp coqRestrictedPADirectExistentialIntroductionCodeEqualityTemplate
      (tfImp
        coqRestrictedPADirectExistentialIntroductionFormulaCodeTemplate
        (tfImp
          coqRestrictedPADirectExistentialIntroductionSubstitutionTemplate
          (tfImp
            coqRestrictedPADirectExistentialIntroductionChildEndpointTemplate
            (tfImp
              coqRestrictedPADirectExistentialIntroductionDeepAdmissibleTemplate
              coqRestrictedPADirectExistentialIntroductionChildInterfaceResultTemplate)))))
    coqRestrictedPADirectExistentialIntroductionDeepRestrictedTemplate
    root5 hroot5) as [lawRoot hlaw].
  unfold
    RawCoqRestrictedPADirectExistentialIntroductionChildInterfaceLawRootAt.
  exists lawRoot.
  unfold coqRestrictedPADirectExistentialIntroductionChildInterfaceLawTemplate.
  exact hlaw.
Qed.

Lemma
    coqRestrictedPADirectExistentialIntroductionReadyContext_app_witnesses_from_quantifierUnary :
  forall witnesses,
  coqRestrictedPADirectStrongStepExistentialIntroductionReadyContext
      (embedPAContext (map witnessedAxiom witnesses)) =
  coqRestrictedPADirectStrongStepExistentialIntroductionReadyContext [] ++
    embedPAContext (map witnessedAxiom witnesses).
Proof.
  intro witnesses.
  rewrite <-
    coqRestrictedPAQuantifierUnary_ready_existentialIntroduction.
  apply coqRestrictedPAQuantifierUnaryReadyContext_app_witnesses.
Qed.

Theorem
    raw_existentialIntroductionChildInterfaceLawAtWitnesses_append_stable :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqStandardWitnessTailAppendStable
    (RawCoqRestrictedPADirectExistentialIntroductionChildInterfaceLawAtWitnesses
      M hPA inputs).
Proof.
  intros M hPA inputs.
  unfold
    RawCoqRestrictedPADirectExistentialIntroductionChildInterfaceLawAtWitnesses,
    RawCoqRestrictedPADirectExistentialIntroductionChildInterfaceLawRootAt.
  exact
    (raw_codedPALocalProof_affine_context_root_append_stable
      M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      coqRestrictedPADirectStrongStepExistentialIntroductionReadyContext
      coqRestrictedPADirectExistentialIntroductionReadyContext_app_witnesses_from_quantifierUnary
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectExistentialIntroductionChildInterfaceLawTemplate)).
Qed.

(** The two public roots can be selected on one synchronized standard
    witness tail.  This is the form consumed by a later seven-field
    continuation assembler. *)
Definition RawCoqRestrictedPAQuantifierUnaryChildRootsAtWitnesses
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (witnesses : StandardPAAxiomWitnessPrefix) : Prop :=
  RawCoqRestrictedPADirectUniversalEliminationRecursiveChildAtWitnesses
      M hPA inputs witnesses /\
  RawCoqRestrictedPADirectExistentialIntroductionChildInterfaceLawAtWitnesses
      M hPA inputs witnesses.

Definition RawCoqRestrictedPAQuantifierUnaryChildRootsStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawCoqStandardWitnessTailCompiler
    (RawCoqRestrictedPAQuantifierUnaryChildRootsAtWitnesses M hPA inputs).

Arguments RawCoqRestrictedPAQuantifierUnaryChildRootsAtWitnesses
  M hPA inputs witnesses : clear implicits.
Arguments RawCoqRestrictedPAQuantifierUnaryChildRootsStandardTailCompiler
  M hPA inputs : clear implicits.

Theorem raw_quantifierUnaryChildRootsAtWitnesses_append_stable :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqStandardWitnessTailAppendStable
    (RawCoqRestrictedPAQuantifierUnaryChildRootsAtWitnesses M hPA inputs).
Proof.
  intros M hPA inputs.
  unfold RawCoqRestrictedPAQuantifierUnaryChildRootsAtWitnesses.
  apply raw_coqStandardWitnessTailAppendStable_and.
  - apply raw_universalEliminationRecursiveChildAtWitnesses_append_stable.
  - apply
      raw_existentialIntroductionChildInterfaceLawAtWitnesses_append_stable.
Qed.

Theorem raw_quantifierUnaryChildRoots_standardTailCompiler :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPAQuantifierUnaryChildRootsStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA inputs.
  unfold RawCoqRestrictedPAQuantifierUnaryChildRootsStandardTailCompiler,
    RawCoqRestrictedPAQuantifierUnaryChildRootsAtWitnesses.
  apply raw_coqStandardWitnessTailCompiler_and.
  - apply raw_universalEliminationRecursiveChildAtWitnesses_append_stable.
  - apply raw_universalEliminationRecursiveChild_standardTailCompiler.
  - apply raw_existentialIntroductionChildInterfaceLaw_standardTailCompiler.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessQuantifierUnaryChildInterfaceOpenedCoverageCompilation.
