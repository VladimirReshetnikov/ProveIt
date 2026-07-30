(**
  The eigenvariable-sensitive universal-introduction constructor case for
  the direct derivation-soundness strong step.

  At the exact eight-witness endpoint depth the dispatcher exposes

    outerConclusion = All(body),
    shiftedContext = shift(witnessContext),
    endpoint(child, shiftedContext, body).

  The proof below preserves those literal codes and projects every field.
  The endpoint witness equality transports the outer context-truth premise
  to [witnessContext].  What is not yet available as a compiled coded-PA
  operation is precisely the eigenvariable step: transport truth through
  the represented context shift under an assignment prepend, invoke the
  recursive child uniformly at that assignment, normalize the hidden
  prepend on [body], and construct truth of [All(body)].

  That single semantic boundary is stated below as an implication-valued
  eigen root.  Its conclusion is first [AllCode -> outer truth], so the
  literal All-code projection remains an independently checked final input.
  No desired branch, desired conclusion, or strong-step root is assumed.
  Rule projections, available outer-to-witness context transport, modus
  ponens, and exact arbitrary-tail implication wrapping are all compiled as
  model-coded PA proofs.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedContextLists
  RawCodedContextShift
  RawCodedProofConstructors
  RawCodedProofEndpoints
  RawCodedProofBinaryConstructors
  RawCodedProofImpIConstructor
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofPropositionalRules
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProjectionSchemas
  RawCodedTemplateDirectStructuralTranslation
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixInductionShell
  RawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier
  RawCodedRestrictedPADerivationSoundnessDirectStrongStepShell
  RawCodedRestrictedPADerivationSoundnessDirectAssumptionCase.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectUniversalIntroductionCase.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedProofImpIConstructor.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProjectionSchemas.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixInductionShell.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectStrongStepShell.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAssumptionCase.

(** ------------------------------------------------------------------
    Literal branch fields. *)

Definition coqRestrictedPADirectUniversalIntroductionCodeEqualityTemplate
    : TemplateFormula :=
  embedPAFormula
    (pEq (liftTerm 8 (tVar 4))
      (proofAllICodeTerm (tVar 7) (tVar 6) (tVar 2))).

Definition coqRestrictedPADirectUniversalIntroductionFormulaCodeTemplate
    : TemplateFormula :=
  embedPAFormula
    (formulaAllCodeTermAt (liftTerm 8 (tVar 2)) (tVar 6)).

Definition coqRestrictedPADirectUniversalIntroductionContextShiftTemplate
    : TemplateFormula :=
  embedPAFormula (contextShiftTermAt (tVar 7) (tVar 5)).

Definition coqRestrictedPADirectUniversalIntroductionChildEndpointTemplate
    : TemplateFormula :=
  embedPAFormula
    (proofEndpointTermAt (tVar 2) (tVar 5) (tVar 6)).

Definition coqRestrictedPADirectUniversalIntroductionTerminalTruthTemplate
    : TemplateFormula :=
  embedPAFormula (pEq tZero tZero).

Definition coqRestrictedPADirectUniversalIntroductionChildSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectUniversalIntroductionChildEndpointTemplate
    coqRestrictedPADirectUniversalIntroductionTerminalTruthTemplate.

Definition coqRestrictedPADirectUniversalIntroductionShiftSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectUniversalIntroductionContextShiftTemplate
    coqRestrictedPADirectUniversalIntroductionChildSuffixTemplate.

Definition coqRestrictedPADirectUniversalIntroductionFormulaSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectUniversalIntroductionFormulaCodeTemplate
    coqRestrictedPADirectUniversalIntroductionShiftSuffixTemplate.

Definition coqRestrictedPADirectUniversalIntroductionCaseTemplate
    : TemplateFormula :=
  rawCoqRestrictedPAProofRuleCaseTemplate rawCoqRuleAllIntroduction
    (liftTerm 8 (tVar 4)) (tVar 7) (liftTerm 8 (tVar 2))
    (tVar 6) (tVar 5) (tVar 4) (tVar 3)
    (tVar 2) (tVar 1) (tVar 0).

Lemma coqRestrictedPADirectUniversalIntroduction_case_shape :
  coqRestrictedPADirectUniversalIntroductionCaseTemplate =
  tfAnd coqRestrictedPADirectUniversalIntroductionCodeEqualityTemplate
    coqRestrictedPADirectUniversalIntroductionFormulaSuffixTemplate.
Proof. reflexivity. Qed.

(** ------------------------------------------------------------------
    Outer truth and the exact eigenvariable residual. *)

Definition coqRestrictedPADirectUniversalIntroductionResultTruthTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate.

Lemma coqRestrictedPADirectUniversalIntroduction_result_truth_shape :
  coqRestrictedPADirectUniversalIntroductionResultTruthTemplate =
  tfOpaque coqRestrictedPAConclusionTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     embedPATerm (liftTerm 8 (tVar 2)); ttVar 9; ttVar 8].
Proof.
  unfold coqRestrictedPADirectUniversalIntroductionResultTruthTemplate.
  rewrite coqRestrictedPADirectAssumption_outer_conclusion_truth_shape.
  reflexivity.
Qed.

(** The implication-valued intermediate is intentional.  The eigen root
    performs only the unavailable binder/context/recursive operation; the
    literal [formulaAllCodeTermAt] field is still applied by the checked
    proof spine below. *)
Definition coqRestrictedPADirectUniversalIntroductionUniversalClosureTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectUniversalIntroductionFormulaCodeTemplate
    coqRestrictedPADirectUniversalIntroductionResultTruthTemplate.

Definition coqRestrictedPADirectUniversalIntroductionEigenSemanticLawTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectUniversalIntroductionContextShiftTemplate
    (tfImp coqRestrictedPADirectUniversalIntroductionChildEndpointTemplate
    (tfImp coqRestrictedPADirectAssumptionWitnessContextTruthTemplate
      coqRestrictedPADirectUniversalIntroductionUniversalClosureTemplate)).

Lemma rawTemplateFormula_universalIntroductionEigenSemanticLaw_view : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  rawTemplateFormula translation
    coqRestrictedPADirectUniversalIntroductionEigenSemanticLawTemplate =
  rawFormulaImpCode M
    (rawTemplateFormula translation
      coqRestrictedPADirectUniversalIntroductionContextShiftTemplate)
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectUniversalIntroductionChildEndpointTemplate)
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          coqRestrictedPADirectAssumptionWitnessContextTruthTemplate)
        (rawFormulaImpCode M
          (rawTemplateFormula translation
            coqRestrictedPADirectUniversalIntroductionFormulaCodeTemplate)
          (rawTemplateFormula translation
            coqRestrictedPADirectUniversalIntroductionResultTruthTemplate)))).
Proof.
  intros M translation.
  unfold coqRestrictedPADirectUniversalIntroductionEigenSemanticLawTemplate,
    coqRestrictedPADirectUniversalIntroductionUniversalClosureTemplate.
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectUniversalIntroductionContextShiftTemplate
    (tfImp coqRestrictedPADirectUniversalIntroductionChildEndpointTemplate
      (tfImp coqRestrictedPADirectAssumptionWitnessContextTruthTemplate
        (tfImp coqRestrictedPADirectUniversalIntroductionFormulaCodeTemplate
          coqRestrictedPADirectUniversalIntroductionResultTruthTemplate)))).
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectUniversalIntroductionChildEndpointTemplate
    (tfImp coqRestrictedPADirectAssumptionWitnessContextTruthTemplate
      (tfImp coqRestrictedPADirectUniversalIntroductionFormulaCodeTemplate
        coqRestrictedPADirectUniversalIntroductionResultTruthTemplate))).
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectAssumptionWitnessContextTruthTemplate
    (tfImp coqRestrictedPADirectUniversalIntroductionFormulaCodeTemplate
      coqRestrictedPADirectUniversalIntroductionResultTruthTemplate)).
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectUniversalIntroductionFormulaCodeTemplate
    coqRestrictedPADirectUniversalIntroductionResultTruthTemplate).
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    Exact shell contexts and residual root interfaces. *)

Definition
    coqRestrictedPADirectStrongStepUniversalIntroductionDeepEndpointContext
    (tail : TemplateContext) : TemplateContext :=
  rawCoqRestrictedPADirectEndpointWitnessBodyTemplate ::
    rawCoqRestrictedPADirectEndpointDeepTail
      (rawCoqRestrictedPADirectStrongStepEndpointTail tail).

Definition coqRestrictedPADirectStrongStepUniversalIntroductionCaseContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectUniversalIntroductionCaseTemplate ::
    coqRestrictedPADirectStrongStepUniversalIntroductionDeepEndpointContext
      tail.

Definition
    coqRestrictedPADirectStrongStepUniversalIntroductionAdmissibleContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectAssumptionDeepAdmissibleTemplate ::
    coqRestrictedPADirectStrongStepUniversalIntroductionCaseContext tail.

Definition coqRestrictedPADirectStrongStepUniversalIntroductionReadyContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectAssumptionOuterContextTruthTemplate ::
    coqRestrictedPADirectStrongStepUniversalIntroductionAdmissibleContext tail.

Arguments
  coqRestrictedPADirectStrongStepUniversalIntroductionDeepEndpointContext
  tail : clear implicits.
Arguments coqRestrictedPADirectStrongStepUniversalIntroductionCaseContext
  tail : clear implicits.
Arguments
  coqRestrictedPADirectStrongStepUniversalIntroductionAdmissibleContext
  tail : clear implicits.
Arguments coqRestrictedPADirectStrongStepUniversalIntroductionReadyContext
  tail : clear implicits.

Definition RawCoqRestrictedPADirectUniversalIntroductionSemanticRoots
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectStrongStepUniversalIntroductionReadyContext tail))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectUniversalIntroductionEigenSemanticLawTemplate)
      root.

Arguments RawCoqRestrictedPADirectUniversalIntroductionSemanticRoots
  M hPA inputs tail : clear implicits.

(** ------------------------------------------------------------------
    Parameterized finite branch projections. *)

Definition coqRestrictedPADirectUniversalIntroductionCaseRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAss context coqRestrictedPADirectUniversalIntroductionCaseTemplate.

Definition coqRestrictedPADirectUniversalIntroductionCodeEqualityRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectUniversalIntroductionCodeEqualityTemplate
    coqRestrictedPADirectUniversalIntroductionFormulaSuffixTemplate
    (coqRestrictedPADirectUniversalIntroductionCaseRootAt context).

Definition coqRestrictedPADirectUniversalIntroductionFormulaSuffixRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE2 context
    coqRestrictedPADirectUniversalIntroductionCodeEqualityTemplate
    coqRestrictedPADirectUniversalIntroductionFormulaSuffixTemplate
    (coqRestrictedPADirectUniversalIntroductionCaseRootAt context).

Definition coqRestrictedPADirectUniversalIntroductionFormulaCodeRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectUniversalIntroductionFormulaCodeTemplate
    coqRestrictedPADirectUniversalIntroductionShiftSuffixTemplate
    (coqRestrictedPADirectUniversalIntroductionFormulaSuffixRootAt context).

Definition coqRestrictedPADirectUniversalIntroductionShiftSuffixRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE2 context
    coqRestrictedPADirectUniversalIntroductionFormulaCodeTemplate
    coqRestrictedPADirectUniversalIntroductionShiftSuffixTemplate
    (coqRestrictedPADirectUniversalIntroductionFormulaSuffixRootAt context).

Definition coqRestrictedPADirectUniversalIntroductionContextShiftRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectUniversalIntroductionContextShiftTemplate
    coqRestrictedPADirectUniversalIntroductionChildSuffixTemplate
    (coqRestrictedPADirectUniversalIntroductionShiftSuffixRootAt context).

Definition coqRestrictedPADirectUniversalIntroductionChildSuffixRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE2 context
    coqRestrictedPADirectUniversalIntroductionContextShiftTemplate
    coqRestrictedPADirectUniversalIntroductionChildSuffixTemplate
    (coqRestrictedPADirectUniversalIntroductionShiftSuffixRootAt context).

Definition coqRestrictedPADirectUniversalIntroductionChildEndpointRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectUniversalIntroductionChildEndpointTemplate
    coqRestrictedPADirectUniversalIntroductionTerminalTruthTemplate
    (coqRestrictedPADirectUniversalIntroductionChildSuffixRootAt context).

Lemma coqRestrictedPADirectUniversalIntroductionCaseRootAt_valid :
  forall context,
  In coqRestrictedPADirectUniversalIntroductionCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectUniversalIntroductionCaseTemplate
    (coqRestrictedPADirectUniversalIntroductionCaseRootAt context).
Proof.
  intros context hin. apply templateRawDerives_assumption. exact hin.
Qed.

Lemma coqRestrictedPADirectUniversalIntroductionCodeEqualityRootAt_valid :
  forall context,
  In coqRestrictedPADirectUniversalIntroductionCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectUniversalIntroductionCodeEqualityTemplate
    (coqRestrictedPADirectUniversalIntroductionCodeEqualityRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectUniversalIntroductionCodeEqualityRootAt.
  apply templateAndLeftFrom_derives.
  rewrite <- coqRestrictedPADirectUniversalIntroduction_case_shape.
  apply coqRestrictedPADirectUniversalIntroductionCaseRootAt_valid. exact hin.
Qed.

Lemma coqRestrictedPADirectUniversalIntroductionFormulaSuffixRootAt_valid :
  forall context,
  In coqRestrictedPADirectUniversalIntroductionCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectUniversalIntroductionFormulaSuffixTemplate
    (coqRestrictedPADirectUniversalIntroductionFormulaSuffixRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectUniversalIntroductionFormulaSuffixRootAt.
  apply templateAndRightFrom_derives.
  rewrite <- coqRestrictedPADirectUniversalIntroduction_case_shape.
  apply coqRestrictedPADirectUniversalIntroductionCaseRootAt_valid. exact hin.
Qed.

Lemma coqRestrictedPADirectUniversalIntroductionFormulaCodeRootAt_valid :
  forall context,
  In coqRestrictedPADirectUniversalIntroductionCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectUniversalIntroductionFormulaCodeTemplate
    (coqRestrictedPADirectUniversalIntroductionFormulaCodeRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectUniversalIntroductionFormulaCodeRootAt.
  apply templateAndLeftFrom_derives.
  apply coqRestrictedPADirectUniversalIntroductionFormulaSuffixRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectUniversalIntroductionShiftSuffixRootAt_valid :
  forall context,
  In coqRestrictedPADirectUniversalIntroductionCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectUniversalIntroductionShiftSuffixTemplate
    (coqRestrictedPADirectUniversalIntroductionShiftSuffixRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectUniversalIntroductionShiftSuffixRootAt.
  apply templateAndRightFrom_derives.
  apply coqRestrictedPADirectUniversalIntroductionFormulaSuffixRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectUniversalIntroductionContextShiftRootAt_valid :
  forall context,
  In coqRestrictedPADirectUniversalIntroductionCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectUniversalIntroductionContextShiftTemplate
    (coqRestrictedPADirectUniversalIntroductionContextShiftRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectUniversalIntroductionContextShiftRootAt.
  apply templateAndLeftFrom_derives.
  apply coqRestrictedPADirectUniversalIntroductionShiftSuffixRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectUniversalIntroductionChildSuffixRootAt_valid :
  forall context,
  In coqRestrictedPADirectUniversalIntroductionCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectUniversalIntroductionChildSuffixTemplate
    (coqRestrictedPADirectUniversalIntroductionChildSuffixRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectUniversalIntroductionChildSuffixRootAt.
  apply templateAndRightFrom_derives.
  apply coqRestrictedPADirectUniversalIntroductionShiftSuffixRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectUniversalIntroductionChildEndpointRootAt_valid :
  forall context,
  In coqRestrictedPADirectUniversalIntroductionCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectUniversalIntroductionChildEndpointTemplate
    (coqRestrictedPADirectUniversalIntroductionChildEndpointRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectUniversalIntroductionChildEndpointRootAt.
  apply templateAndLeftFrom_derives.
  apply coqRestrictedPADirectUniversalIntroductionChildSuffixRootAt_valid.
  exact hin.
Qed.

(** ------------------------------------------------------------------
    Compile the eigen residual and all finite plumbing. *)

Theorem
    raw_codedPALocalProofOf_coqRestrictedPADirectUniversalIntroductionConclusion
    : forall (M : RawPAModel) (hPA : RawPASatisfies M)
      (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectUniversalIntroductionSemanticRoots
    M hPA inputs tail ->
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectStrongStepUniversalIntroductionReadyContext tail))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate)
      root.
Proof.
  intros M hPA inputs tail
    (eigenSemanticRoot & heigenSemantic).
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  set (readyContext :=
    coqRestrictedPADirectStrongStepUniversalIntroductionReadyContext tail).
  set (readyContextCode :=
    rawTemplateContextCode translation readyContext).

  assert (hcase :
    In coqRestrictedPADirectUniversalIntroductionCaseTemplate readyContext).
  {
    unfold readyContext,
      coqRestrictedPADirectStrongStepUniversalIntroductionReadyContext,
      coqRestrictedPADirectStrongStepUniversalIntroductionAdmissibleContext,
      coqRestrictedPADirectStrongStepUniversalIntroductionCaseContext.
    right. right. left. reflexivity.
  }
  assert (hendpointBody :
    In rawCoqRestrictedPADirectEndpointWitnessBodyTemplate readyContext).
  {
    unfold readyContext,
      coqRestrictedPADirectStrongStepUniversalIntroductionReadyContext,
      coqRestrictedPADirectStrongStepUniversalIntroductionAdmissibleContext,
      coqRestrictedPADirectStrongStepUniversalIntroductionCaseContext,
      coqRestrictedPADirectStrongStepUniversalIntroductionDeepEndpointContext.
    do 3 right. left. reflexivity.
  }
  assert (houterContextTruth :
    In coqRestrictedPADirectAssumptionOuterContextTruthTemplate
      readyContext).
  {
    unfold readyContext,
      coqRestrictedPADirectStrongStepUniversalIntroductionReadyContext.
    left. reflexivity.
  }

  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectUniversalIntroductionFormulaCodeRootAt readyContext)
    (proj1
      (coqRestrictedPADirectUniversalIntroductionFormulaCodeRootAt_valid
        readyContext hcase))) as hformulaCode.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectUniversalIntroductionContextShiftRootAt
      readyContext)
    (proj1
      (coqRestrictedPADirectUniversalIntroductionContextShiftRootAt_valid
        readyContext hcase))) as hcontextShift.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectUniversalIntroductionChildEndpointRootAt readyContext)
    (proj1
      (coqRestrictedPADirectUniversalIntroductionChildEndpointRootAt_valid
        readyContext hcase))) as hchildEndpoint.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt readyContext)
    (proj1
      (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt_valid
        readyContext hendpointBody houterContextTruth)))
    as hwitnessContextTruth.

  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectUniversalIntroductionFormulaCodeTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectUniversalIntroductionFormulaCodeRootAt
        readyContext))) in hformulaCode.
  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectUniversalIntroductionContextShiftTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectUniversalIntroductionContextShiftRootAt
        readyContext))) in hcontextShift.
  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectUniversalIntroductionChildEndpointTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectUniversalIntroductionChildEndpointRootAt
        readyContext))) in hchildEndpoint.
  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectAssumptionWitnessContextTruthTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt
        readyContext))) in hwitnessContextTruth.

  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectUniversalIntroductionEigenSemanticLawTemplate)
    eigenSemanticRoot) in heigenSemantic.
  rewrite rawTemplateFormula_universalIntroductionEigenSemanticLaw_view
    in heigenSemantic.

  set (contextShiftCode := rawTemplateFormula translation
    coqRestrictedPADirectUniversalIntroductionContextShiftTemplate).
  set (childEndpointCode := rawTemplateFormula translation
    coqRestrictedPADirectUniversalIntroductionChildEndpointTemplate).
  set (witnessContextTruthCode := rawTemplateFormula translation
    coqRestrictedPADirectAssumptionWitnessContextTruthTemplate).
  set (formulaCodeRelation := rawTemplateFormula translation
    coqRestrictedPADirectUniversalIntroductionFormulaCodeTemplate).
  set (resultTruthCode := rawTemplateFormula translation
    coqRestrictedPADirectUniversalIntroductionResultTruthTemplate).

  (** Apply the eigen operation only after all three semantic inputs have
      been independently projected or transported. *)
  set (eigenAfterShiftRoot := rawProofImpERoot M readyContextCode
    contextShiftCode
    (rawFormulaImpCode M childEndpointCode
      (rawFormulaImpCode M witnessContextTruthCode
        (rawFormulaImpCode M formulaCodeRelation resultTruthCode)))
    eigenSemanticRoot
    (rawTemplateProofCode translation
      (coqRestrictedPADirectUniversalIntroductionContextShiftRootAt
        readyContext))).
  assert (heigenAfterShift : RawCodedPALocalProofOf M readyContextCode
    (rawFormulaImpCode M childEndpointCode
      (rawFormulaImpCode M witnessContextTruthCode
        (rawFormulaImpCode M formulaCodeRelation resultTruthCode)))
    eigenAfterShiftRoot).
  {
    unfold eigenAfterShiftRoot.
    apply (raw_codedPALocalProofOf_impE M hPA readyContextCode
      contextShiftCode
      (rawFormulaImpCode M childEndpointCode
        (rawFormulaImpCode M witnessContextTruthCode
          (rawFormulaImpCode M formulaCodeRelation resultTruthCode)))
      eigenSemanticRoot
      (rawTemplateProofCode translation
        (coqRestrictedPADirectUniversalIntroductionContextShiftRootAt
          readyContext))).
    - exact heigenSemantic.
    - unfold contextShiftCode. exact hcontextShift.
  }

  set (eigenAfterEndpointRoot := rawProofImpERoot M readyContextCode
    childEndpointCode
    (rawFormulaImpCode M witnessContextTruthCode
      (rawFormulaImpCode M formulaCodeRelation resultTruthCode))
    eigenAfterShiftRoot
    (rawTemplateProofCode translation
      (coqRestrictedPADirectUniversalIntroductionChildEndpointRootAt
        readyContext))).
  assert (heigenAfterEndpoint : RawCodedPALocalProofOf M readyContextCode
    (rawFormulaImpCode M witnessContextTruthCode
      (rawFormulaImpCode M formulaCodeRelation resultTruthCode))
    eigenAfterEndpointRoot).
  {
    unfold eigenAfterEndpointRoot.
    apply (raw_codedPALocalProofOf_impE M hPA readyContextCode
      childEndpointCode
      (rawFormulaImpCode M witnessContextTruthCode
        (rawFormulaImpCode M formulaCodeRelation resultTruthCode))
      eigenAfterShiftRoot
      (rawTemplateProofCode translation
        (coqRestrictedPADirectUniversalIntroductionChildEndpointRootAt
          readyContext))).
    - exact heigenAfterShift.
    - unfold childEndpointCode. exact hchildEndpoint.
  }

  set (universalClosureRoot := rawProofImpERoot M readyContextCode
    witnessContextTruthCode
    (rawFormulaImpCode M formulaCodeRelation resultTruthCode)
    eigenAfterEndpointRoot
    (rawTemplateProofCode translation
      (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt
        readyContext))).
  assert (huniversalClosure : RawCodedPALocalProofOf M readyContextCode
    (rawFormulaImpCode M formulaCodeRelation resultTruthCode)
    universalClosureRoot).
  {
    unfold universalClosureRoot.
    apply (raw_codedPALocalProofOf_impE M hPA readyContextCode
      witnessContextTruthCode
      (rawFormulaImpCode M formulaCodeRelation resultTruthCode)
      eigenAfterEndpointRoot
      (rawTemplateProofCode translation
        (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt
          readyContext))).
    - exact heigenAfterEndpoint.
    - unfold witnessContextTruthCode. exact hwitnessContextTruth.
  }

  set (resultTruthRoot := rawProofImpERoot M readyContextCode
    formulaCodeRelation resultTruthCode universalClosureRoot
    (rawTemplateProofCode translation
      (coqRestrictedPADirectUniversalIntroductionFormulaCodeRootAt
        readyContext))).
  assert (hresultTruth : RawCodedPALocalProofOf M readyContextCode
    resultTruthCode resultTruthRoot).
  {
    unfold resultTruthRoot.
    apply (raw_codedPALocalProofOf_impE M hPA readyContextCode
      formulaCodeRelation resultTruthCode universalClosureRoot
      (rawTemplateProofCode translation
        (coqRestrictedPADirectUniversalIntroductionFormulaCodeRootAt
          readyContext))).
    - exact huniversalClosure.
    - unfold formulaCodeRelation. exact hformulaCode.
  }

  exists resultTruthRoot.
  unfold resultTruthCode in hresultTruth.
  exact hresultTruth.
Qed.

(** ------------------------------------------------------------------
    Exact public slot of the seventeen-case strong-step family. *)

Theorem raw_coqRestrictedPADirectStrongStepUniversalIntroductionCaseRoot :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectUniversalIntroductionSemanticRoots
    M hPA inputs tail ->
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawCoqRestrictedPADirectEndpointWitnessBodyTemplate ::
          rawCoqRestrictedPADirectEndpointDeepTail
            (rawCoqRestrictedPADirectStrongStepEndpointTail tail)))
      (rawFormulaImpCode M
        (rawDirectTemplateFormula inputs
          (rawCoqRestrictedPAProofRuleCaseTemplate
            rawCoqRuleAllIntroduction
            (liftTerm 8 (tVar 4)) (tVar 7) (liftTerm 8 (tVar 2))
            (tVar 6) (tVar 5) (tVar 4) (tVar 3)
            (tVar 2) (tVar 1) (tVar 0)))
        (rawDirectTemplateFormula inputs
          (rawCoqTemplateRenameN 8
            rawCoqRestrictedPADirectStrongStepRemainingTemplate)))
      root.
Proof.
  intros M hPA inputs tail hsemanticRoots.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  set (baseContext :=
    coqRestrictedPADirectStrongStepUniversalIntroductionDeepEndpointContext
      tail).
  set (caseContext :=
    coqRestrictedPADirectStrongStepUniversalIntroductionCaseContext tail).
  set (admissibleContext :=
    coqRestrictedPADirectStrongStepUniversalIntroductionAdmissibleContext tail).
  set (readyContext :=
    coqRestrictedPADirectStrongStepUniversalIntroductionReadyContext tail).
  destruct
    (raw_codedPALocalProofOf_coqRestrictedPADirectUniversalIntroductionConclusion
      M hPA inputs tail hsemanticRoots) as
    [conclusionRoot hconclusion].

  set (baseContextCode := rawTemplateContextCode translation baseContext).
  set (caseContextCode := rawTemplateContextCode translation caseContext).
  set (admissibleContextCode :=
    rawTemplateContextCode translation admissibleContext).
  set (readyContextCode := rawTemplateContextCode translation readyContext).
  set (caseCode := rawTemplateFormula translation
    coqRestrictedPADirectUniversalIntroductionCaseTemplate).
  set (admissibleCode := rawTemplateFormula translation
    coqRestrictedPADirectAssumptionDeepAdmissibleTemplate).
  set (contextTruthCode := rawTemplateFormula translation
    coqRestrictedPADirectAssumptionOuterContextTruthTemplate).
  set (conclusionTruthCode := rawTemplateFormula translation
    coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate).

  set (contextImpRoot := rawProofImpIRoot M admissibleContextCode
    contextTruthCode conclusionTruthCode conclusionRoot).
  assert (hcontextImp : RawCodedPALocalProofOf M admissibleContextCode
    (rawFormulaImpCode M contextTruthCode conclusionTruthCode)
    contextImpRoot).
  {
    unfold contextImpRoot.
    apply (raw_codedPALocalProofOf_impI M hPA admissibleContextCode
      contextTruthCode conclusionTruthCode conclusionRoot).
    change (RawCodedPALocalProofOf M readyContextCode
      conclusionTruthCode conclusionRoot).
    exact hconclusion.
  }

  set (admissibleImpRoot := rawProofImpIRoot M caseContextCode
    admissibleCode
    (rawFormulaImpCode M contextTruthCode conclusionTruthCode)
    contextImpRoot).
  assert (hadmissibleImp : RawCodedPALocalProofOf M caseContextCode
    (rawFormulaImpCode M admissibleCode
      (rawFormulaImpCode M contextTruthCode conclusionTruthCode))
    admissibleImpRoot).
  {
    unfold admissibleImpRoot.
    apply (raw_codedPALocalProofOf_impI M hPA caseContextCode
      admissibleCode
      (rawFormulaImpCode M contextTruthCode conclusionTruthCode)
      contextImpRoot).
    change (RawCodedPALocalProofOf M admissibleContextCode
      (rawFormulaImpCode M contextTruthCode conclusionTruthCode)
      contextImpRoot).
    exact hcontextImp.
  }

  set (caseImpRoot := rawProofImpIRoot M baseContextCode caseCode
    (rawFormulaImpCode M admissibleCode
      (rawFormulaImpCode M contextTruthCode conclusionTruthCode))
    admissibleImpRoot).
  exists caseImpRoot.
  rewrite coqRestrictedPADirectAssumption_strong_step_remaining_shape.
  change (RawCodedPALocalProofOf M baseContextCode
    (rawFormulaImpCode M caseCode
      (rawFormulaImpCode M admissibleCode
        (rawFormulaImpCode M contextTruthCode conclusionTruthCode)))
    caseImpRoot).
  unfold caseImpRoot.
  apply (raw_codedPALocalProofOf_impI M hPA baseContextCode caseCode
    (rawFormulaImpCode M admissibleCode
      (rawFormulaImpCode M contextTruthCode conclusionTruthCode))
    admissibleImpRoot).
  change (RawCodedPALocalProofOf M caseContextCode
    (rawFormulaImpCode M admissibleCode
      (rawFormulaImpCode M contextTruthCode conclusionTruthCode))
    admissibleImpRoot).
  exact hadmissibleImp.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectUniversalIntroductionCase.
