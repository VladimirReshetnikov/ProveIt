(**
  Represented compilation of the common same-context unary child source.

  The source module proves, once for four literal rule rows, the arithmetic
  implication from an opened parent certificate to the sole child's complete
  recursive interface.  This module performs the proof-code work shared by
  all four instances:

  - instantiate that PA theorem at the carrier-valued hierarchy level;
  - open the parent's common formula-coverage witness by represented Ex-E;
  - apply the seven literal antecedents in the resulting eigencontext;
  - eliminate the eigenvariable and recover the child interface in the exact
    branch ready context; and
  - surround the selected finite PA-axiom batch by an arbitrary pre-existing
    standard witness prefix.

  The final three corollaries discharge precisely the arithmetic compiler
  hypotheses left for And-E-left, And-E-right, and Or-I-right.  Or-I-left is
  retained in the generic family as an independently compiled regression
  instance, even though its recursive law was completed earlier.
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
  RawCodedRestrictedPADerivationSoundnessDirectAndEliminationLeftCase
  RawCodedRestrictedPADerivationSoundnessDirectAndEliminationRightCase
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftCase
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionRightCase
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftRecursiveChildCompilation
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootCompilation
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageCompilation
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageValidity
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionChildCoreExtraction
  RawCodedRestrictedPADerivationSoundnessSameContextUnaryRecursiveChildCompilation
  RawCodedRestrictedPADerivationSoundnessDirectStandardReadyContextAffinity
  RawCodedRestrictedPADerivationSoundnessSameContextUnaryRecursiveChildStandardTailCompilation
  RawCodedRestrictedPADerivationSoundnessSameContextUnaryChildInterfaceOpenedCoverageSource.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessSameContextUnaryChildInterfaceOpenedCoverageCompilation.

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
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndEliminationLeftCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndEliminationRightCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionRightCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftRecursiveChildCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageValidity.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionChildCoreExtraction.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessSameContextUnaryRecursiveChildCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectStandardReadyContextAffinity.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessSameContextUnaryRecursiveChildStandardTailCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessSameContextUnaryChildInterfaceOpenedCoverageSource.

(** ------------------------------------------------------------------
    One literal ready context and one coverage eigencontext. *)

(** Every client has the same ready-context skeleton.  Only the literal
    constructor row varies, so keeping that row as data avoids four copies of
    all later membership and affine-context calculations. *)
Definition coqRestrictedPASameContextUnaryReadyContext
    (rule : CoqRestrictedPASameContextUnaryRule)
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectStandardReadyContext
    coqRestrictedPADirectAssumptionOuterContextTruthTemplate
    coqRestrictedPADirectAssumptionDeepAdmissibleTemplate
    (coqRestrictedPASameContextUnaryCaseTemplate rule)
    tail.

Definition coqRestrictedPASameContextUnaryCoverageEigenContext
    (rule : CoqRestrictedPASameContextUnaryRule)
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectOrIntroductionLeftDeepCommonCoverageBodyTemplate ::
    templateContextShift
      (coqRestrictedPASameContextUnaryReadyContext rule tail).

Arguments coqRestrictedPASameContextUnaryReadyContext rule tail
  : clear implicits.
Arguments coqRestrictedPASameContextUnaryCoverageEigenContext rule tail
  : clear implicits.

(** These equations are intentionally definitional.  They are the final
    audit that the generic source lands in the exact public branch contexts,
    rather than in merely extensionally equivalent lists. *)
Lemma coqRestrictedPASameContextUnary_ready_andEliminationLeft : forall tail,
  coqRestrictedPASameContextUnaryReadyContext
      CoqSameContextAndEliminationLeft tail =
  coqRestrictedPADirectStrongStepAndEliminationLeftReadyContext tail.
Proof. reflexivity. Qed.

Lemma coqRestrictedPASameContextUnary_ready_andEliminationRight : forall tail,
  coqRestrictedPASameContextUnaryReadyContext
      CoqSameContextAndEliminationRight tail =
  coqRestrictedPADirectStrongStepAndEliminationRightReadyContext tail.
Proof. reflexivity. Qed.

Lemma coqRestrictedPASameContextUnary_ready_orIntroductionLeft : forall tail,
  coqRestrictedPASameContextUnaryReadyContext
      CoqSameContextOrIntroductionLeft tail =
  coqRestrictedPADirectStrongStepOrIntroductionLeftReadyContext tail.
Proof. reflexivity. Qed.

Lemma coqRestrictedPASameContextUnary_ready_orIntroductionRight : forall tail,
  coqRestrictedPASameContextUnaryReadyContext
      CoqSameContextOrIntroductionRight tail =
  coqRestrictedPADirectStrongStepOrIntroductionRightReadyContext tail.
Proof. reflexivity. Qed.

Lemma coqRestrictedPASameContextUnary_ready_restricted_in : forall rule tail,
  In coqRestrictedPADirectAndIntroductionDeepRestrictedTemplate
    (coqRestrictedPASameContextUnaryReadyContext rule tail).
Proof.
  intros rule tail.
  unfold coqRestrictedPASameContextUnaryReadyContext,
    coqRestrictedPADirectStandardReadyContext.
  do 3 right.
  rewrite <- raw_coqRestrictedPADirectEndpointDeepContext_shape.
  unfold coqRestrictedPADirectAndIntroductionDeepRestrictedTemplate.
  apply raw_coqTemplateNestedExContext_inherited.
  unfold rawCoqRestrictedPADirectStrongStepEndpointTail.
  left. reflexivity.
Qed.

Lemma coqRestrictedPASameContextUnary_ready_admissible_in : forall rule tail,
  In coqRestrictedPADirectAndIntroductionDeepAdmissibleTemplate
    (coqRestrictedPASameContextUnaryReadyContext rule tail).
Proof.
  intros rule tail.
  unfold coqRestrictedPASameContextUnaryReadyContext,
    coqRestrictedPADirectStandardReadyContext.
  right. left. reflexivity.
Qed.

Lemma coqRestrictedPASameContextUnary_ready_case_in : forall rule tail,
  In (coqRestrictedPASameContextUnaryCaseTemplate rule)
    (coqRestrictedPASameContextUnaryReadyContext rule tail).
Proof.
  intros rule tail.
  unfold coqRestrictedPASameContextUnaryReadyContext,
    coqRestrictedPADirectStandardReadyContext.
  right. right. left. reflexivity.
Qed.

Lemma coqRestrictedPASameContextUnary_eigen_inherited : forall
    rule tail formula,
  In formula (coqRestrictedPASameContextUnaryReadyContext rule tail) ->
  In (templateFormulaRename S formula)
    (coqRestrictedPASameContextUnaryCoverageEigenContext rule tail).
Proof.
  intros rule tail formula hin. right.
  unfold templateContextShift, templateContextRename.
  apply in_map. exact hin.
Qed.

Lemma coqRestrictedPASameContextUnary_eigen_coverage_body_in : forall
    rule tail,
  In coqRestrictedPADirectOrIntroductionLeftDeepCommonCoverageBodyTemplate
    (coqRestrictedPASameContextUnaryCoverageEigenContext rule tail).
Proof. intros rule tail. left. reflexivity. Qed.

Lemma coqRestrictedPASameContextUnary_eigen_restricted_in : forall rule tail,
  In (templateFormulaRename S
      coqRestrictedPADirectAndIntroductionDeepRestrictedTemplate)
    (coqRestrictedPASameContextUnaryCoverageEigenContext rule tail).
Proof.
  intros rule tail.
  apply coqRestrictedPASameContextUnary_eigen_inherited.
  apply coqRestrictedPASameContextUnary_ready_restricted_in.
Qed.

Lemma coqRestrictedPASameContextUnary_eigen_admissible_in : forall rule tail,
  In (templateFormulaRename S
      coqRestrictedPADirectAndIntroductionDeepAdmissibleTemplate)
    (coqRestrictedPASameContextUnaryCoverageEigenContext rule tail).
Proof.
  intros rule tail.
  apply coqRestrictedPASameContextUnary_eigen_inherited.
  apply coqRestrictedPASameContextUnary_ready_admissible_in.
Qed.

Lemma coqRestrictedPASameContextUnary_eigen_case_in : forall rule tail,
  In (templateFormulaRename S
      (coqRestrictedPASameContextUnaryCaseTemplate rule))
    (coqRestrictedPASameContextUnaryCoverageEigenContext rule tail).
Proof.
  intros rule tail.
  apply coqRestrictedPASameContextUnary_eigen_inherited.
  apply coqRestrictedPASameContextUnary_ready_case_in.
Qed.

(** Embedded PA axioms are sentences.  Consequently neither the thirteen
    inherited endpoint shifts nor the extra coverage-witness shift changes a
    standard tail. *)
Lemma coqRestrictedPASameContextUnaryReadyContext_app_witnesses : forall
    rule witnesses,
  coqRestrictedPASameContextUnaryReadyContext rule
      (embedPAContext (map witnessedAxiom witnesses)) =
  coqRestrictedPASameContextUnaryReadyContext rule [] ++
    embedPAContext (map witnessedAxiom witnesses).
Proof.
  intros rule witnesses.
  unfold coqRestrictedPASameContextUnaryReadyContext.
  apply coqRestrictedPADirectStandardReadyContext_app_witnesses.
Qed.

Lemma coqRestrictedPASameContextUnaryCoverageEigenContext_app_witnesses :
    forall rule witnesses,
  coqRestrictedPASameContextUnaryCoverageEigenContext rule
      (embedPAContext (map witnessedAxiom witnesses)) =
  coqRestrictedPASameContextUnaryCoverageEigenContext rule [] ++
    embedPAContext (map witnessedAxiom witnesses).
Proof.
  intros rule witnesses.
  unfold coqRestrictedPASameContextUnaryCoverageEigenContext.
  rewrite coqRestrictedPASameContextUnaryReadyContext_app_witnesses.
  rewrite templateContextShift_app,
    templateContextShift_embedPAAxiomWitnesses_fixed.
  reflexivity.
Qed.

Lemma raw_sameContextUnaryCoverageEigenContext_witnessed_code : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation -> forall rule witnesses,
  rawTemplateContextCode translation
    (coqRestrictedPASameContextUnaryCoverageEigenContext rule
      (embedPAContext (map witnessedAxiom witnesses))) =
  rawTemplateContextCodeOnTail translation
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M))
    (coqRestrictedPASameContextUnaryCoverageEigenContext rule []).
Proof.
  intros M translation hagreement rule witnesses.
  rewrite
    coqRestrictedPASameContextUnaryCoverageEigenContext_app_witnesses.
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
    Opened law root and represented single-child extraction. *)

Definition RawCoqRestrictedPASameContextUnaryOpenedCoverageCompilerLawRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (rule : CoqRestrictedPASameContextUnaryRule)
    (tail : TemplateContext) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPASameContextUnaryCoverageEigenContext rule tail))
      (rawDirectTemplateFormula inputs
        (coqRestrictedPASameContextUnaryOpenedCoverageLawTemplate rule))
      root.

Arguments RawCoqRestrictedPASameContextUnaryOpenedCoverageCompilerLawRoot
  M hPA inputs rule tail : clear implicits.

Theorem raw_sameContextUnaryChildInterfaceRoot_of_openedCoverageCompiler :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M) rule tail,
  RawCoqRestrictedPASameContextUnaryOpenedCoverageCompilerLawRoot
    M hPA inputs rule tail ->
  RawCoqRestrictedPASameContextUnaryChildInterfaceRootAt M
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    (coqRestrictedPASameContextUnaryReadyContext rule tail)
    (coqRestrictedPASameContextUnaryChildTerm rule)
    (coqRestrictedPASameContextUnaryWitnessContextTerm rule)
    (coqRestrictedPASameContextUnaryChildConclusionTerm rule).
Proof.
  intros M hPA inputs rule tail (openedRoot & hopened).
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  set (readyContext :=
    coqRestrictedPASameContextUnaryReadyContext rule tail).
  set (eigenContext :=
    coqRestrictedPASameContextUnaryCoverageEigenContext rule tail).
  set (readyCode := rawTemplateContextCode translation readyContext).

  (** First expose the common coverage existential in the unshifted ready
      context. *)
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAssumption
      M hPA translation readyContext
      coqRestrictedPADirectAndIntroductionDeepAdmissibleTemplate
      (coqRestrictedPASameContextUnary_ready_admissible_in rule tail))
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

  (** Project the four proof-wide parent certificates in the eigencontext. *)
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAssumption
      M hPA translation eigenContext
      (templateFormulaRename S
        coqRestrictedPADirectAndIntroductionDeepRestrictedTemplate)
      (coqRestrictedPASameContextUnary_eigen_restricted_in rule tail))
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

  (** The first half of admissibility is inherited.  Its second half is the
      existential whose body is now the eigencontext's head assumption. *)
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAssumption
      M hPA translation eigenContext
      (templateFormulaRename S
        coqRestrictedPADirectAndIntroductionDeepAdmissibleTemplate)
      (coqRestrictedPASameContextUnary_eigen_admissible_in rule tail))
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
      (coqRestrictedPASameContextUnary_eigen_coverage_body_in rule tail))
    as hcoverageBody.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAssumption
      M hPA translation eigenContext
      (templateFormulaRename S
        (coqRestrictedPASameContextUnaryCaseTemplate rule))
      (coqRestrictedPASameContextUnary_eigen_case_in rule tail))
    as hcase.

  (** Apply the reified arithmetic theorem.  The seven steps are shared by
      every rule; only [hcase] and the final child terms depend on [rule]. *)
  unfold coqRestrictedPASameContextUnaryOpenedCoverageLawTemplate in hopened.
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

  (** Ex-E removes the fresh coverage-bound variable.  Structural formula
      shift identifies the shifted result produced above with the required
      eigenbranch conclusion. *)
  pose proof
    (raw_codedPALocalProofOf_exE M hPA readyCode
      (rawTemplateContextCode translation
        (templateContextShift readyContext))
      (rawTemplateFormula translation
        coqRestrictedPADirectOrIntroductionLeftDeepCommonCoverageBodyTemplate)
      (rawTemplateFormula translation
        (coqRestrictedPASameContextUnaryChildInterfaceTemplate rule))
      (rawTemplateFormula translation
        (templateFormulaRename S
          (coqRestrictedPASameContextUnaryChildInterfaceTemplate rule)))
      _ _ hcommonCoverage
      (raw_templateContext_shift M hPA translation readyContext)
      (rawTemplateFormula_shift translation
        (coqRestrictedPASameContextUnaryChildInterfaceTemplate rule))
      hresultShifted) as hresult.
  lazymatch type of hresult with
  | RawCodedPALocalProofOf _ _ _ ?resultRoot =>
      exists resultRoot; exact hresult
  end.
Qed.

(** ------------------------------------------------------------------
    Instantiate the universal source and select one witnessed tail. *)

Theorem
    raw_codedPALocalProof_sameContextUnaryOpenedCoverageLaw_on_witnessed_base :
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
        (coqRestrictedPASameContextUnaryCoverageEigenContext rule []))
      (rawDirectTemplateFormula inputs
        (coqRestrictedPASameContextUnaryOpenedCoverageLawTemplate rule))
      root.
Proof.
  intros M hPA inputs rule baseWitnessList baseContext hbase.
  exact
    (raw_codedPALocalProof_universalSourceInstance_under_directPrefix
      M hPA inputs baseWitnessList baseContext
      (coqRestrictedPASameContextUnaryOpenedCoverageSourceBodyFormula rule)
      (rawDirectTemplateTerm inputs
        coqRestrictedPASoundnessLowerLevelTerm)
      (rawDirectTemplateFormula inputs
        (coqRestrictedPASameContextUnaryOpenedCoverageLawTemplate rule))
      (coqRestrictedPASameContextUnaryCoverageEigenContext rule [])
      hbase
      (PA_proves_coqRestrictedPASameContextUnaryOpenedCoverageSource rule)
      (rawDirect_sameContextUnaryOpenedCoverageSource_substitution
        M hPA inputs rule)).
Qed.

Definition RawCoqRestrictedPADirectSelectedSameContextUnaryChildInterfaceTail
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (rule : CoqRestrictedPASameContextUnaryRule) : Prop :=
  exists witnesses : StandardPAAxiomWitnessPrefix,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (embedPAContext (map witnessedAxiom witnesses))) /\
    RawCoqRestrictedPASameContextUnaryChildInterfaceRootAt M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqRestrictedPASameContextUnaryReadyContext rule
        (embedPAContext (map witnessedAxiom witnesses)))
      (coqRestrictedPASameContextUnaryChildTerm rule)
      (coqRestrictedPASameContextUnaryWitnessContextTerm rule)
      (coqRestrictedPASameContextUnaryChildConclusionTerm rule).

Arguments
  RawCoqRestrictedPADirectSelectedSameContextUnaryChildInterfaceTail
  M hPA inputs rule : clear implicits.

Theorem raw_selectedSameContextUnaryChildInterfaceTail : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M) rule,
  RawCoqRestrictedPADirectSelectedSameContextUnaryChildInterfaceTail
    M hPA inputs rule.
Proof.
  intros M hPA inputs rule.
  assert (hempty : RawCodedPAAxiomWitnessContext M
      (raw_zero M) (raw_zero M)).
  {
    pose proof (raw_codedPAAxiomWitnessContext_standard M hPA []) as h.
    cbn [rawQuotedPAAxiomWitnessList rawListCode map] in h.
    exact h.
  }
  destruct
    (raw_codedPALocalProof_sameContextUnaryOpenedCoverageLaw_on_witnessed_base
      M hPA inputs rule (raw_zero M) (raw_zero M) hempty)
    as (witnesses & root & hwitnessed & hroot).
  exists witnesses. split.
  - rewrite rawTemplateContextCode_as_on_tail.
    rewrite (raw_templateContextCodeOnTail_embedPAAxiomWitnesses M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      witnesses (raw_zero M)).
    exact hwitnessed.
  - apply raw_sameContextUnaryChildInterfaceRoot_of_openedCoverageCompiler.
    exists root.
    rewrite (raw_sameContextUnaryCoverageEigenContext_witnessed_code M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      rule witnesses).
    exact hroot.
Qed.

(** The selected source batch can be placed after an arbitrary batch already
    chosen by another compiler.  This direction is important: a standard
    tail compiler promises [base ++ suffix], whereas PA source compilation
    initially selects only its own finite witness list. *)
Theorem raw_sameContextUnaryChildInterface_standardTailCompiler : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M) rule,
  RawCoqRestrictedPASameContextUnaryChildInterfaceStandardTailCompilerAt
    M hPA inputs
    (coqRestrictedPASameContextUnaryReadyContext rule)
    (coqRestrictedPASameContextUnaryChildTerm rule)
    (coqRestrictedPASameContextUnaryWitnessContextTerm rule)
    (coqRestrictedPASameContextUnaryChildConclusionTerm rule).
Proof.
  intros M hPA inputs rule baseWitnesses.
  destruct (raw_selectedSameContextUnaryChildInterfaceTail
    M hPA inputs rule) as
    (sourceWitnesses & _hwitnessed & interfaceRoot & hinterface).
  rewrite coqRestrictedPASameContextUnaryReadyContext_app_witnesses
    in hinterface.
  destruct
    (raw_codedPALocalProof_standardWitnessTail_surround_under_prefix
      M hPA
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      (coqRestrictedPASameContextUnaryReadyContext rule [])
      baseWitnesses sourceWitnesses []
      (rawTemplateFormula
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPASameContextUnaryChildInterfaceTemplate rule))
      interfaceRoot hinterface) as [transportedRoot htransported].
  exists sourceWitnesses.
  unfold RawCoqRestrictedPASameContextUnaryChildInterfaceRootAt.
  exists transportedRoot.
  cbn [List.app] in htransported.
  rewrite app_nil_r in htransported.
  rewrite coqRestrictedPASameContextUnaryReadyContext_app_witnesses.
  exact htransported.
Qed.

(** ------------------------------------------------------------------
    Exact public residuals. *)

Corollary
    raw_andEliminationLeftChildInterface_standardTailCompiler : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectAndEliminationLeftChildInterfaceStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA inputs.
  unfold
    RawCoqRestrictedPADirectAndEliminationLeftChildInterfaceStandardTailCompiler.
  change
    (RawCoqRestrictedPASameContextUnaryChildInterfaceStandardTailCompilerAt
      M hPA inputs
      (coqRestrictedPASameContextUnaryReadyContext
        CoqSameContextAndEliminationLeft)
      (coqRestrictedPASameContextUnaryChildTerm
        CoqSameContextAndEliminationLeft)
      (coqRestrictedPASameContextUnaryWitnessContextTerm
        CoqSameContextAndEliminationLeft)
      (coqRestrictedPASameContextUnaryChildConclusionTerm
        CoqSameContextAndEliminationLeft)).
  apply raw_sameContextUnaryChildInterface_standardTailCompiler.
Qed.

Corollary
    raw_andEliminationRightChildInterface_standardTailCompiler : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectAndEliminationRightChildInterfaceStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA inputs.
  unfold
    RawCoqRestrictedPADirectAndEliminationRightChildInterfaceStandardTailCompiler.
  change
    (RawCoqRestrictedPASameContextUnaryChildInterfaceStandardTailCompilerAt
      M hPA inputs
      (coqRestrictedPASameContextUnaryReadyContext
        CoqSameContextAndEliminationRight)
      (coqRestrictedPASameContextUnaryChildTerm
        CoqSameContextAndEliminationRight)
      (coqRestrictedPASameContextUnaryWitnessContextTerm
        CoqSameContextAndEliminationRight)
      (coqRestrictedPASameContextUnaryChildConclusionTerm
        CoqSameContextAndEliminationRight)).
  apply raw_sameContextUnaryChildInterface_standardTailCompiler.
Qed.

Corollary
    raw_orIntroductionRightChildInterface_standardTailCompiler : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectOrIntroductionRightChildInterfaceStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA inputs.
  unfold
    RawCoqRestrictedPADirectOrIntroductionRightChildInterfaceStandardTailCompiler.
  change
    (RawCoqRestrictedPASameContextUnaryChildInterfaceStandardTailCompilerAt
      M hPA inputs
      (coqRestrictedPASameContextUnaryReadyContext
        CoqSameContextOrIntroductionRight)
      (coqRestrictedPASameContextUnaryChildTerm
        CoqSameContextOrIntroductionRight)
      (coqRestrictedPASameContextUnaryWitnessContextTerm
        CoqSameContextOrIntroductionRight)
      (coqRestrictedPASameContextUnaryChildConclusionTerm
        CoqSameContextOrIntroductionRight)).
  apply raw_sameContextUnaryChildInterface_standardTailCompiler.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessSameContextUnaryChildInterfaceOpenedCoverageCompilation.
