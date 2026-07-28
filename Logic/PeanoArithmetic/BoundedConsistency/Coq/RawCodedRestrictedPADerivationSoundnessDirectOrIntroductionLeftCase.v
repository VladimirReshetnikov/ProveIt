(**
  The genuine left-disjunction-introduction constructor case for the direct
  derivation-soundness strong step.

  At the eight-witness endpoint depth this branch displays

    outerConclusion = Or(left, right),
    endpoint(child, witnessContext, left).

  The proof below projects the displayed formula-code and endpoint fields.
  It transports the
  outer context-truth assumption to [witnessContext] using the endpoint
  witness equality, invokes a sharply stated recursive-child law to obtain
  truth of [left], and invokes only the left-disjunction-introduction Tarski
  law to obtain truth of [outerConclusion].

  Thus only two mathematical seams remain:

  - recursive-child soundness at the displayed child endpoint;
  - the dynamic truth law introducing a displayed disjunction from truth of
    its left component.

  No branch-result root, outer-conclusion proof, strong-step proof, or
  dynamic conclusion premise is assumed.  All constructor projections,
  context transport, modus ponens, and shell implication introductions are
  compiled as model-coded PA proofs.
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
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftCase.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
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

Definition coqRestrictedPADirectOrIntroductionLeftCodeEqualityTemplate
    : TemplateFormula :=
  embedPAFormula
    (pEq (liftTerm 8 (tVar 4))
      (proofOrI1CodeTerm (tVar 7) (tVar 6) (tVar 5) (tVar 2))).

Definition coqRestrictedPADirectOrIntroductionLeftFormulaCodeTemplate
    : TemplateFormula :=
  embedPAFormula
    (formulaOrCodeTermAt (liftTerm 8 (tVar 2)) (tVar 6) (tVar 5)).

Definition coqRestrictedPADirectOrIntroductionLeftChildEndpointTemplate
    : TemplateFormula :=
  embedPAFormula
    (proofEndpointTermAt (tVar 2) (tVar 7) (tVar 6)).

Definition coqRestrictedPADirectOrIntroductionLeftTerminalTruthTemplate
    : TemplateFormula :=
  embedPAFormula (pEq tZero tZero).

Definition coqRestrictedPADirectOrIntroductionLeftChildSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectOrIntroductionLeftChildEndpointTemplate
    coqRestrictedPADirectOrIntroductionLeftTerminalTruthTemplate.

Definition coqRestrictedPADirectOrIntroductionLeftFormulaSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectOrIntroductionLeftFormulaCodeTemplate
    coqRestrictedPADirectOrIntroductionLeftChildSuffixTemplate.

Definition coqRestrictedPADirectOrIntroductionLeftCaseTemplate
    : TemplateFormula :=
  rawCoqRestrictedPAProofRuleCaseTemplate rawCoqRuleOrIntroductionLeft
    (liftTerm 8 (tVar 4)) (tVar 7) (liftTerm 8 (tVar 2))
    (tVar 6) (tVar 5) (tVar 4) (tVar 3)
    (tVar 2) (tVar 1) (tVar 0).

Lemma coqRestrictedPADirectOrIntroductionLeft_case_shape :
  coqRestrictedPADirectOrIntroductionLeftCaseTemplate =
  tfAnd coqRestrictedPADirectOrIntroductionLeftCodeEqualityTemplate
    coqRestrictedPADirectOrIntroductionLeftFormulaSuffixTemplate.
Proof. reflexivity. Qed.

(** ------------------------------------------------------------------
    Truth leaves and the two exact residual laws. *)

Definition coqRestrictedPADirectOrIntroductionLeftFormulaTruthTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAssumptionWitnessFormulaTruthTemplate.

Definition coqRestrictedPADirectOrIntroductionLeftResultTruthTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate.

Lemma coqRestrictedPADirectOrIntroductionLeft_result_truth_shape :
  coqRestrictedPADirectOrIntroductionLeftResultTruthTemplate =
  tfOpaque coqRestrictedPAConclusionTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     embedPATerm (liftTerm 8 (tVar 2)); ttVar 9; ttVar 8].
Proof.
  unfold coqRestrictedPADirectOrIntroductionLeftResultTruthTemplate.
  rewrite coqRestrictedPADirectAssumption_outer_conclusion_truth_shape.
  reflexivity.
Qed.

Definition coqRestrictedPADirectOrIntroductionLeftRecursiveChildLawTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectOrIntroductionLeftChildEndpointTemplate
    (tfImp coqRestrictedPADirectAssumptionWitnessContextTruthTemplate
      coqRestrictedPADirectOrIntroductionLeftFormulaTruthTemplate).

Definition coqRestrictedPADirectOrIntroductionLeftDynamicTruthLawTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectOrIntroductionLeftFormulaCodeTemplate
    (tfImp coqRestrictedPADirectOrIntroductionLeftFormulaTruthTemplate
      coqRestrictedPADirectOrIntroductionLeftResultTruthTemplate).

Lemma rawTemplateFormula_orIntroductionLeftRecursiveChildLaw_view : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  rawTemplateFormula translation
    coqRestrictedPADirectOrIntroductionLeftRecursiveChildLawTemplate =
  rawFormulaImpCode M
    (rawTemplateFormula translation
      coqRestrictedPADirectOrIntroductionLeftChildEndpointTemplate)
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionWitnessContextTruthTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectOrIntroductionLeftFormulaTruthTemplate)).
Proof.
  intros M translation.
  unfold coqRestrictedPADirectOrIntroductionLeftRecursiveChildLawTemplate.
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectOrIntroductionLeftChildEndpointTemplate
    (tfImp coqRestrictedPADirectAssumptionWitnessContextTruthTemplate
      coqRestrictedPADirectOrIntroductionLeftFormulaTruthTemplate)).
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectAssumptionWitnessContextTruthTemplate
    coqRestrictedPADirectOrIntroductionLeftFormulaTruthTemplate).
  reflexivity.
Qed.

Lemma rawTemplateFormula_orIntroductionLeftDynamicTruthLaw_view : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  rawTemplateFormula translation
    coqRestrictedPADirectOrIntroductionLeftDynamicTruthLawTemplate =
  rawFormulaImpCode M
    (rawTemplateFormula translation
      coqRestrictedPADirectOrIntroductionLeftFormulaCodeTemplate)
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectOrIntroductionLeftFormulaTruthTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectOrIntroductionLeftResultTruthTemplate)).
Proof.
  intros M translation.
  unfold coqRestrictedPADirectOrIntroductionLeftDynamicTruthLawTemplate.
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectOrIntroductionLeftFormulaCodeTemplate
    (tfImp coqRestrictedPADirectOrIntroductionLeftFormulaTruthTemplate
      coqRestrictedPADirectOrIntroductionLeftResultTruthTemplate)).
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectOrIntroductionLeftFormulaTruthTemplate
    coqRestrictedPADirectOrIntroductionLeftResultTruthTemplate).
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    Exact shell contexts and residual root interfaces. *)

Definition
    coqRestrictedPADirectStrongStepOrIntroductionLeftDeepEndpointContext
    (tail : TemplateContext) : TemplateContext :=
  rawCoqRestrictedPADirectEndpointWitnessBodyTemplate ::
    rawCoqRestrictedPADirectEndpointDeepTail
      (rawCoqRestrictedPADirectStrongStepEndpointTail tail).

Definition coqRestrictedPADirectStrongStepOrIntroductionLeftCaseContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectOrIntroductionLeftCaseTemplate ::
    coqRestrictedPADirectStrongStepOrIntroductionLeftDeepEndpointContext
      tail.

Definition
    coqRestrictedPADirectStrongStepOrIntroductionLeftAdmissibleContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectAssumptionDeepAdmissibleTemplate ::
    coqRestrictedPADirectStrongStepOrIntroductionLeftCaseContext tail.

Definition coqRestrictedPADirectStrongStepOrIntroductionLeftReadyContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectAssumptionOuterContextTruthTemplate ::
    coqRestrictedPADirectStrongStepOrIntroductionLeftAdmissibleContext tail.

Arguments
  coqRestrictedPADirectStrongStepOrIntroductionLeftDeepEndpointContext
  tail : clear implicits.
Arguments coqRestrictedPADirectStrongStepOrIntroductionLeftCaseContext
  tail : clear implicits.
Arguments
  coqRestrictedPADirectStrongStepOrIntroductionLeftAdmissibleContext
  tail : clear implicits.
Arguments coqRestrictedPADirectStrongStepOrIntroductionLeftReadyContext
  tail : clear implicits.

Definition RawCoqRestrictedPADirectOrIntroductionLeftRecursiveChildLawRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectStrongStepOrIntroductionLeftReadyContext tail))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectOrIntroductionLeftRecursiveChildLawTemplate)
      root.

Definition RawCoqRestrictedPADirectOrIntroductionLeftDynamicTruthLawRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectStrongStepOrIntroductionLeftReadyContext tail))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectOrIntroductionLeftDynamicTruthLawTemplate)
      root.

Arguments RawCoqRestrictedPADirectOrIntroductionLeftRecursiveChildLawRoot
  M hPA inputs tail : clear implicits.
Arguments RawCoqRestrictedPADirectOrIntroductionLeftDynamicTruthLawRoot
  M hPA inputs tail : clear implicits.

(** ------------------------------------------------------------------
    Parameterized finite branch projections. *)

Definition coqRestrictedPADirectOrIntroductionLeftCaseRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAss context coqRestrictedPADirectOrIntroductionLeftCaseTemplate.

Definition coqRestrictedPADirectOrIntroductionLeftCodeEqualityRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectOrIntroductionLeftCodeEqualityTemplate
    coqRestrictedPADirectOrIntroductionLeftFormulaSuffixTemplate
    (coqRestrictedPADirectOrIntroductionLeftCaseRootAt context).

Definition coqRestrictedPADirectOrIntroductionLeftFormulaSuffixRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE2 context
    coqRestrictedPADirectOrIntroductionLeftCodeEqualityTemplate
    coqRestrictedPADirectOrIntroductionLeftFormulaSuffixTemplate
    (coqRestrictedPADirectOrIntroductionLeftCaseRootAt context).

Definition coqRestrictedPADirectOrIntroductionLeftFormulaCodeRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectOrIntroductionLeftFormulaCodeTemplate
    coqRestrictedPADirectOrIntroductionLeftChildSuffixTemplate
    (coqRestrictedPADirectOrIntroductionLeftFormulaSuffixRootAt context).

Definition coqRestrictedPADirectOrIntroductionLeftChildSuffixRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE2 context
    coqRestrictedPADirectOrIntroductionLeftFormulaCodeTemplate
    coqRestrictedPADirectOrIntroductionLeftChildSuffixTemplate
    (coqRestrictedPADirectOrIntroductionLeftFormulaSuffixRootAt context).

Definition coqRestrictedPADirectOrIntroductionLeftChildEndpointRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectOrIntroductionLeftChildEndpointTemplate
    coqRestrictedPADirectOrIntroductionLeftTerminalTruthTemplate
    (coqRestrictedPADirectOrIntroductionLeftChildSuffixRootAt context).

Lemma coqRestrictedPADirectOrIntroductionLeftCaseRootAt_valid :
  forall context,
  In coqRestrictedPADirectOrIntroductionLeftCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectOrIntroductionLeftCaseTemplate
    (coqRestrictedPADirectOrIntroductionLeftCaseRootAt context).
Proof.
  intros context hin. apply templateRawDerives_assumption. exact hin.
Qed.

Lemma coqRestrictedPADirectOrIntroductionLeftCodeEqualityRootAt_valid :
  forall context,
  In coqRestrictedPADirectOrIntroductionLeftCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectOrIntroductionLeftCodeEqualityTemplate
    (coqRestrictedPADirectOrIntroductionLeftCodeEqualityRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectOrIntroductionLeftCodeEqualityRootAt.
  apply templateAndLeftFrom_derives.
  rewrite <- coqRestrictedPADirectOrIntroductionLeft_case_shape.
  apply coqRestrictedPADirectOrIntroductionLeftCaseRootAt_valid. exact hin.
Qed.

Lemma coqRestrictedPADirectOrIntroductionLeftFormulaSuffixRootAt_valid :
  forall context,
  In coqRestrictedPADirectOrIntroductionLeftCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectOrIntroductionLeftFormulaSuffixTemplate
    (coqRestrictedPADirectOrIntroductionLeftFormulaSuffixRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectOrIntroductionLeftFormulaSuffixRootAt.
  apply templateAndRightFrom_derives.
  rewrite <- coqRestrictedPADirectOrIntroductionLeft_case_shape.
  apply coqRestrictedPADirectOrIntroductionLeftCaseRootAt_valid. exact hin.
Qed.

Lemma coqRestrictedPADirectOrIntroductionLeftFormulaCodeRootAt_valid :
  forall context,
  In coqRestrictedPADirectOrIntroductionLeftCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectOrIntroductionLeftFormulaCodeTemplate
    (coqRestrictedPADirectOrIntroductionLeftFormulaCodeRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectOrIntroductionLeftFormulaCodeRootAt.
  apply templateAndLeftFrom_derives.
  apply coqRestrictedPADirectOrIntroductionLeftFormulaSuffixRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectOrIntroductionLeftChildSuffixRootAt_valid :
  forall context,
  In coqRestrictedPADirectOrIntroductionLeftCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectOrIntroductionLeftChildSuffixTemplate
    (coqRestrictedPADirectOrIntroductionLeftChildSuffixRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectOrIntroductionLeftChildSuffixRootAt.
  apply templateAndRightFrom_derives.
  apply coqRestrictedPADirectOrIntroductionLeftFormulaSuffixRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectOrIntroductionLeftChildEndpointRootAt_valid :
  forall context,
  In coqRestrictedPADirectOrIntroductionLeftCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectOrIntroductionLeftChildEndpointTemplate
    (coqRestrictedPADirectOrIntroductionLeftChildEndpointRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectOrIntroductionLeftChildEndpointRootAt.
  apply templateAndLeftFrom_derives.
  apply coqRestrictedPADirectOrIntroductionLeftChildSuffixRootAt_valid.
  exact hin.
Qed.

(** ------------------------------------------------------------------
    Compile the two residual laws and all finite plumbing. *)

Theorem
    raw_codedPALocalProofOf_coqRestrictedPADirectOrIntroductionLeftConclusion
    : forall (M : RawPAModel) (hPA : RawPASatisfies M)
      (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectOrIntroductionLeftRecursiveChildLawRoot
    M hPA inputs tail ->
  RawCoqRestrictedPADirectOrIntroductionLeftDynamicTruthLawRoot
    M hPA inputs tail ->
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectStrongStepOrIntroductionLeftReadyContext tail))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate)
      root.
Proof.
  intros M hPA inputs tail
    (recursiveLawRoot & hrecursiveLaw)
    (dynamicLawRoot & hdynamicLaw).
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  set (readyContext :=
    coqRestrictedPADirectStrongStepOrIntroductionLeftReadyContext tail).
  set (readyContextCode :=
    rawTemplateContextCode translation readyContext).

  assert (hcase :
    In coqRestrictedPADirectOrIntroductionLeftCaseTemplate readyContext).
  {
    unfold readyContext,
      coqRestrictedPADirectStrongStepOrIntroductionLeftReadyContext,
      coqRestrictedPADirectStrongStepOrIntroductionLeftAdmissibleContext,
      coqRestrictedPADirectStrongStepOrIntroductionLeftCaseContext.
    right. right. left. reflexivity.
  }
  assert (hendpointBody :
    In rawCoqRestrictedPADirectEndpointWitnessBodyTemplate readyContext).
  {
    unfold readyContext,
      coqRestrictedPADirectStrongStepOrIntroductionLeftReadyContext,
      coqRestrictedPADirectStrongStepOrIntroductionLeftAdmissibleContext,
      coqRestrictedPADirectStrongStepOrIntroductionLeftCaseContext,
      coqRestrictedPADirectStrongStepOrIntroductionLeftDeepEndpointContext.
    do 3 right. left. reflexivity.
  }
  assert (houterContextTruth :
    In coqRestrictedPADirectAssumptionOuterContextTruthTemplate
      readyContext).
  {
    unfold readyContext,
      coqRestrictedPADirectStrongStepOrIntroductionLeftReadyContext.
    left. reflexivity.
  }

  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectOrIntroductionLeftFormulaCodeRootAt readyContext)
    (proj1
      (coqRestrictedPADirectOrIntroductionLeftFormulaCodeRootAt_valid
        readyContext hcase))) as hformulaCode.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectOrIntroductionLeftChildEndpointRootAt readyContext)
    (proj1
      (coqRestrictedPADirectOrIntroductionLeftChildEndpointRootAt_valid
        readyContext hcase))) as hchildEndpoint.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt readyContext)
    (proj1
      (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt_valid
        readyContext hendpointBody houterContextTruth)))
    as hwitnessContextTruth.

  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectOrIntroductionLeftFormulaCodeTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectOrIntroductionLeftFormulaCodeRootAt
        readyContext))) in hformulaCode.
  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectOrIntroductionLeftChildEndpointTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectOrIntroductionLeftChildEndpointRootAt
        readyContext))) in hchildEndpoint.
  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectAssumptionWitnessContextTruthTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt
        readyContext))) in hwitnessContextTruth.

  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectOrIntroductionLeftRecursiveChildLawTemplate)
    recursiveLawRoot) in hrecursiveLaw.
  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectOrIntroductionLeftDynamicTruthLawTemplate)
    dynamicLawRoot) in hdynamicLaw.
  rewrite rawTemplateFormula_orIntroductionLeftRecursiveChildLaw_view
    in hrecursiveLaw.
  rewrite rawTemplateFormula_orIntroductionLeftDynamicTruthLaw_view
    in hdynamicLaw.

  set (childEndpointCode := rawTemplateFormula translation
    coqRestrictedPADirectOrIntroductionLeftChildEndpointTemplate).
  set (witnessContextTruthCode := rawTemplateFormula translation
    coqRestrictedPADirectAssumptionWitnessContextTruthTemplate).
  set (formulaTruthCode := rawTemplateFormula translation
    coqRestrictedPADirectOrIntroductionLeftFormulaTruthTemplate).
  set (formulaCodeRelation := rawTemplateFormula translation
    coqRestrictedPADirectOrIntroductionLeftFormulaCodeTemplate).
  set (resultTruthCode := rawTemplateFormula translation
    coqRestrictedPADirectOrIntroductionLeftResultTruthTemplate).

  set (recursiveAfterEndpointRoot := rawProofImpERoot M readyContextCode
    childEndpointCode
    (rawFormulaImpCode M witnessContextTruthCode formulaTruthCode)
    recursiveLawRoot
    (rawTemplateProofCode translation
      (coqRestrictedPADirectOrIntroductionLeftChildEndpointRootAt
        readyContext))).
  assert (hrecursiveAfterEndpoint : RawCodedPALocalProofOf M
    readyContextCode
    (rawFormulaImpCode M witnessContextTruthCode formulaTruthCode)
    recursiveAfterEndpointRoot).
  {
    unfold recursiveAfterEndpointRoot.
    apply (raw_codedPALocalProofOf_impE M hPA readyContextCode
      childEndpointCode
      (rawFormulaImpCode M witnessContextTruthCode formulaTruthCode)
      recursiveLawRoot
      (rawTemplateProofCode translation
        (coqRestrictedPADirectOrIntroductionLeftChildEndpointRootAt
          readyContext))).
    - exact hrecursiveLaw.
    - unfold childEndpointCode. exact hchildEndpoint.
  }

  set (formulaTruthRoot := rawProofImpERoot M readyContextCode
    witnessContextTruthCode formulaTruthCode recursiveAfterEndpointRoot
    (rawTemplateProofCode translation
      (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt
        readyContext))).
  assert (hformulaTruth : RawCodedPALocalProofOf M readyContextCode
    formulaTruthCode formulaTruthRoot).
  {
    unfold formulaTruthRoot.
    apply (raw_codedPALocalProofOf_impE M hPA readyContextCode
      witnessContextTruthCode formulaTruthCode recursiveAfterEndpointRoot
      (rawTemplateProofCode translation
        (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt
          readyContext))).
    - exact hrecursiveAfterEndpoint.
    - unfold witnessContextTruthCode. exact hwitnessContextTruth.
  }

  set (dynamicAfterFormulaRoot := rawProofImpERoot M readyContextCode
    formulaCodeRelation
    (rawFormulaImpCode M formulaTruthCode resultTruthCode)
    dynamicLawRoot
    (rawTemplateProofCode translation
      (coqRestrictedPADirectOrIntroductionLeftFormulaCodeRootAt
        readyContext))).
  assert (hdynamicAfterFormula : RawCodedPALocalProofOf M readyContextCode
    (rawFormulaImpCode M formulaTruthCode resultTruthCode)
    dynamicAfterFormulaRoot).
  {
    unfold dynamicAfterFormulaRoot.
    apply (raw_codedPALocalProofOf_impE M hPA readyContextCode
      formulaCodeRelation
      (rawFormulaImpCode M formulaTruthCode resultTruthCode)
      dynamicLawRoot
      (rawTemplateProofCode translation
        (coqRestrictedPADirectOrIntroductionLeftFormulaCodeRootAt
          readyContext))).
    - exact hdynamicLaw.
    - unfold formulaCodeRelation. exact hformulaCode.
  }

  set (resultTruthRoot := rawProofImpERoot M readyContextCode
    formulaTruthCode resultTruthCode dynamicAfterFormulaRoot
    formulaTruthRoot).
  assert (hresultTruth : RawCodedPALocalProofOf M readyContextCode
    resultTruthCode resultTruthRoot).
  {
    unfold resultTruthRoot.
    apply (raw_codedPALocalProofOf_impE M hPA readyContextCode
      formulaTruthCode resultTruthCode dynamicAfterFormulaRoot
      formulaTruthRoot).
    - exact hdynamicAfterFormula.
    - exact hformulaTruth.
  }

  exists resultTruthRoot.
  unfold resultTruthCode in hresultTruth.
  exact hresultTruth.
Qed.

(** ------------------------------------------------------------------
    Exact public slot of the seventeen-case strong-step family. *)

Theorem raw_coqRestrictedPADirectStrongStepOrIntroductionLeftCaseRoot :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectOrIntroductionLeftRecursiveChildLawRoot
    M hPA inputs tail ->
  RawCoqRestrictedPADirectOrIntroductionLeftDynamicTruthLawRoot
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
            rawCoqRuleOrIntroductionLeft
            (liftTerm 8 (tVar 4)) (tVar 7) (liftTerm 8 (tVar 2))
            (tVar 6) (tVar 5) (tVar 4) (tVar 3)
            (tVar 2) (tVar 1) (tVar 0)))
        (rawDirectTemplateFormula inputs
          (rawCoqTemplateRenameN 8
            rawCoqRestrictedPADirectStrongStepRemainingTemplate)))
      root.
Proof.
  intros M hPA inputs tail hrecursiveLaw hdynamicLaw.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  set (baseContext :=
    coqRestrictedPADirectStrongStepOrIntroductionLeftDeepEndpointContext
      tail).
  set (caseContext :=
    coqRestrictedPADirectStrongStepOrIntroductionLeftCaseContext tail).
  set (admissibleContext :=
    coqRestrictedPADirectStrongStepOrIntroductionLeftAdmissibleContext tail).
  set (readyContext :=
    coqRestrictedPADirectStrongStepOrIntroductionLeftReadyContext tail).
  destruct
    (raw_codedPALocalProofOf_coqRestrictedPADirectOrIntroductionLeftConclusion
      M hPA inputs tail hrecursiveLaw hdynamicLaw) as
    [conclusionRoot hconclusion].

  set (baseContextCode := rawTemplateContextCode translation baseContext).
  set (caseContextCode := rawTemplateContextCode translation caseContext).
  set (admissibleContextCode :=
    rawTemplateContextCode translation admissibleContext).
  set (readyContextCode := rawTemplateContextCode translation readyContext).
  set (caseCode := rawTemplateFormula translation
    coqRestrictedPADirectOrIntroductionLeftCaseTemplate).
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
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftCase.
