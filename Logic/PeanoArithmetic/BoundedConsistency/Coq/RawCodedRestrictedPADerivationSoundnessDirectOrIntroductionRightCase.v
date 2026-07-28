(**
  The genuine right-disjunction-introduction constructor case for the direct
  derivation-soundness strong step.

  At the eight-witness endpoint depth this branch displays

    outerConclusion = Or(left, right),
    endpoint(child, witnessContext, right).

  The proof below projects the displayed formula-code and endpoint fields.
  It transports the outer context-truth assumption to [witnessContext] using
  the endpoint witness equality, invokes a sharply stated recursive-child law to obtain
  truth of [right], and invokes only the right-disjunction-introduction Tarski
  law to obtain truth of [outerConclusion].

  Thus only two mathematical seams remain:

  - recursive-child soundness at the displayed child endpoint;
  - the dynamic truth law introducing a displayed disjunction from truth of
    its right component.

  No branch-result root, outer-conclusion proof, strong-step proof, or
  dynamic conclusion premise is assumed.  The constructor-code equality,
  disjunction-code relation, child endpoint, context transport, modus ponens,
  and shell implication introductions are compiled as model-coded PA proofs.
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
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionRightCase.

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

Definition coqRestrictedPADirectOrIntroductionRightCodeEqualityTemplate
    : TemplateFormula :=
  embedPAFormula
    (pEq (liftTerm 8 (tVar 4))
      (proofOrI2CodeTerm (tVar 7) (tVar 6) (tVar 5) (tVar 2))).

Definition coqRestrictedPADirectOrIntroductionRightFormulaCodeTemplate
    : TemplateFormula :=
  embedPAFormula
    (formulaOrCodeTermAt (liftTerm 8 (tVar 2)) (tVar 6) (tVar 5)).

Definition coqRestrictedPADirectOrIntroductionRightChildEndpointTemplate
    : TemplateFormula :=
  embedPAFormula
    (proofEndpointTermAt (tVar 2) (tVar 7) (tVar 5)).

Definition coqRestrictedPADirectOrIntroductionRightTerminalTruthTemplate
    : TemplateFormula :=
  embedPAFormula (pEq tZero tZero).

Definition coqRestrictedPADirectOrIntroductionRightChildSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectOrIntroductionRightChildEndpointTemplate
    coqRestrictedPADirectOrIntroductionRightTerminalTruthTemplate.

Definition coqRestrictedPADirectOrIntroductionRightFormulaSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectOrIntroductionRightFormulaCodeTemplate
    coqRestrictedPADirectOrIntroductionRightChildSuffixTemplate.

Definition coqRestrictedPADirectOrIntroductionRightCaseTemplate
    : TemplateFormula :=
  rawCoqRestrictedPAProofRuleCaseTemplate rawCoqRuleOrIntroductionRight
    (liftTerm 8 (tVar 4)) (tVar 7) (liftTerm 8 (tVar 2))
    (tVar 6) (tVar 5) (tVar 4) (tVar 3)
    (tVar 2) (tVar 1) (tVar 0).

Lemma coqRestrictedPADirectOrIntroductionRight_case_shape :
  coqRestrictedPADirectOrIntroductionRightCaseTemplate =
  tfAnd coqRestrictedPADirectOrIntroductionRightCodeEqualityTemplate
    coqRestrictedPADirectOrIntroductionRightFormulaSuffixTemplate.
Proof. reflexivity. Qed.

(** ------------------------------------------------------------------
    Truth leaves and the two exact residual laws. *)

(** The selected formula is the right disjunct [b], whose endpoint
    witness is [ttVar 5].  It is deliberately not the assumption-case
    witness formula [ttVar 6], which denotes the left disjunct [a]. *)
Definition coqRestrictedPADirectOrIntroductionRightFormulaTerm
    : TemplateTerm := ttVar 5.

Definition coqRestrictedPADirectOrIntroductionRightFormulaTruthTemplate
    : TemplateFormula :=
  tfOpaque coqRestrictedPAConclusionTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     coqRestrictedPADirectOrIntroductionRightFormulaTerm;
     ttVar 9; ttVar 8].

Lemma coqRestrictedPADirectOrIntroductionRight_formula_truth_shape :
  coqRestrictedPADirectOrIntroductionRightFormulaTruthTemplate =
  tfOpaque coqRestrictedPAConclusionTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     ttVar 5; ttVar 9; ttVar 8].
Proof. reflexivity. Qed.

Definition coqRestrictedPADirectOrIntroductionRightResultTruthTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate.

Lemma coqRestrictedPADirectOrIntroductionRight_result_truth_shape :
  coqRestrictedPADirectOrIntroductionRightResultTruthTemplate =
  tfOpaque coqRestrictedPAConclusionTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     embedPATerm (liftTerm 8 (tVar 2)); ttVar 9; ttVar 8].
Proof.
  unfold coqRestrictedPADirectOrIntroductionRightResultTruthTemplate.
  rewrite coqRestrictedPADirectAssumption_outer_conclusion_truth_shape.
  reflexivity.
Qed.

Definition coqRestrictedPADirectOrIntroductionRightRecursiveChildLawTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectOrIntroductionRightChildEndpointTemplate
    (tfImp coqRestrictedPADirectAssumptionWitnessContextTruthTemplate
      coqRestrictedPADirectOrIntroductionRightFormulaTruthTemplate).

Definition coqRestrictedPADirectOrIntroductionRightDynamicTruthLawTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectOrIntroductionRightFormulaCodeTemplate
    (tfImp coqRestrictedPADirectOrIntroductionRightFormulaTruthTemplate
      coqRestrictedPADirectOrIntroductionRightResultTruthTemplate).

Lemma rawTemplateFormula_orIntroductionRightRecursiveChildLaw_view : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  rawTemplateFormula translation
    coqRestrictedPADirectOrIntroductionRightRecursiveChildLawTemplate =
  rawFormulaImpCode M
    (rawTemplateFormula translation
      coqRestrictedPADirectOrIntroductionRightChildEndpointTemplate)
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionWitnessContextTruthTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectOrIntroductionRightFormulaTruthTemplate)).
Proof.
  intros M translation.
  unfold coqRestrictedPADirectOrIntroductionRightRecursiveChildLawTemplate.
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectOrIntroductionRightChildEndpointTemplate
    (tfImp coqRestrictedPADirectAssumptionWitnessContextTruthTemplate
      coqRestrictedPADirectOrIntroductionRightFormulaTruthTemplate)).
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectAssumptionWitnessContextTruthTemplate
    coqRestrictedPADirectOrIntroductionRightFormulaTruthTemplate).
  reflexivity.
Qed.

Lemma rawTemplateFormula_orIntroductionRightDynamicTruthLaw_view : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  rawTemplateFormula translation
    coqRestrictedPADirectOrIntroductionRightDynamicTruthLawTemplate =
  rawFormulaImpCode M
    (rawTemplateFormula translation
      coqRestrictedPADirectOrIntroductionRightFormulaCodeTemplate)
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectOrIntroductionRightFormulaTruthTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectOrIntroductionRightResultTruthTemplate)).
Proof.
  intros M translation.
  unfold coqRestrictedPADirectOrIntroductionRightDynamicTruthLawTemplate.
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectOrIntroductionRightFormulaCodeTemplate
    (tfImp coqRestrictedPADirectOrIntroductionRightFormulaTruthTemplate
      coqRestrictedPADirectOrIntroductionRightResultTruthTemplate)).
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectOrIntroductionRightFormulaTruthTemplate
    coqRestrictedPADirectOrIntroductionRightResultTruthTemplate).
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    Exact shell contexts and residual root interfaces. *)

Definition
    coqRestrictedPADirectStrongStepOrIntroductionRightDeepEndpointContext
    (tail : TemplateContext) : TemplateContext :=
  rawCoqRestrictedPADirectEndpointWitnessBodyTemplate ::
    rawCoqRestrictedPADirectEndpointDeepTail
      (rawCoqRestrictedPADirectStrongStepEndpointTail tail).

Definition coqRestrictedPADirectStrongStepOrIntroductionRightCaseContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectOrIntroductionRightCaseTemplate ::
    coqRestrictedPADirectStrongStepOrIntroductionRightDeepEndpointContext
      tail.

Definition
    coqRestrictedPADirectStrongStepOrIntroductionRightAdmissibleContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectAssumptionDeepAdmissibleTemplate ::
    coqRestrictedPADirectStrongStepOrIntroductionRightCaseContext tail.

Definition coqRestrictedPADirectStrongStepOrIntroductionRightReadyContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectAssumptionOuterContextTruthTemplate ::
    coqRestrictedPADirectStrongStepOrIntroductionRightAdmissibleContext tail.

Arguments
  coqRestrictedPADirectStrongStepOrIntroductionRightDeepEndpointContext
  tail : clear implicits.
Arguments coqRestrictedPADirectStrongStepOrIntroductionRightCaseContext
  tail : clear implicits.
Arguments
  coqRestrictedPADirectStrongStepOrIntroductionRightAdmissibleContext
  tail : clear implicits.
Arguments coqRestrictedPADirectStrongStepOrIntroductionRightReadyContext
  tail : clear implicits.

Definition RawCoqRestrictedPADirectOrIntroductionRightRecursiveChildLawRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectStrongStepOrIntroductionRightReadyContext tail))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectOrIntroductionRightRecursiveChildLawTemplate)
      root.

Definition RawCoqRestrictedPADirectOrIntroductionRightDynamicTruthLawRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectStrongStepOrIntroductionRightReadyContext tail))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectOrIntroductionRightDynamicTruthLawTemplate)
      root.

Arguments RawCoqRestrictedPADirectOrIntroductionRightRecursiveChildLawRoot
  M hPA inputs tail : clear implicits.
Arguments RawCoqRestrictedPADirectOrIntroductionRightDynamicTruthLawRoot
  M hPA inputs tail : clear implicits.

(** ------------------------------------------------------------------
    Parameterized finite branch projections. *)

Definition coqRestrictedPADirectOrIntroductionRightCaseRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAss context coqRestrictedPADirectOrIntroductionRightCaseTemplate.

Definition coqRestrictedPADirectOrIntroductionRightCodeEqualityRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectOrIntroductionRightCodeEqualityTemplate
    coqRestrictedPADirectOrIntroductionRightFormulaSuffixTemplate
    (coqRestrictedPADirectOrIntroductionRightCaseRootAt context).

Definition coqRestrictedPADirectOrIntroductionRightFormulaSuffixRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE2 context
    coqRestrictedPADirectOrIntroductionRightCodeEqualityTemplate
    coqRestrictedPADirectOrIntroductionRightFormulaSuffixTemplate
    (coqRestrictedPADirectOrIntroductionRightCaseRootAt context).

Definition coqRestrictedPADirectOrIntroductionRightFormulaCodeRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectOrIntroductionRightFormulaCodeTemplate
    coqRestrictedPADirectOrIntroductionRightChildSuffixTemplate
    (coqRestrictedPADirectOrIntroductionRightFormulaSuffixRootAt context).

Definition coqRestrictedPADirectOrIntroductionRightChildSuffixRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE2 context
    coqRestrictedPADirectOrIntroductionRightFormulaCodeTemplate
    coqRestrictedPADirectOrIntroductionRightChildSuffixTemplate
    (coqRestrictedPADirectOrIntroductionRightFormulaSuffixRootAt context).

Definition coqRestrictedPADirectOrIntroductionRightChildEndpointRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectOrIntroductionRightChildEndpointTemplate
    coqRestrictedPADirectOrIntroductionRightTerminalTruthTemplate
    (coqRestrictedPADirectOrIntroductionRightChildSuffixRootAt context).

Lemma coqRestrictedPADirectOrIntroductionRightCaseRootAt_valid :
  forall context,
  In coqRestrictedPADirectOrIntroductionRightCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectOrIntroductionRightCaseTemplate
    (coqRestrictedPADirectOrIntroductionRightCaseRootAt context).
Proof.
  intros context hin. apply templateRawDerives_assumption. exact hin.
Qed.

Lemma coqRestrictedPADirectOrIntroductionRightCodeEqualityRootAt_valid :
  forall context,
  In coqRestrictedPADirectOrIntroductionRightCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectOrIntroductionRightCodeEqualityTemplate
    (coqRestrictedPADirectOrIntroductionRightCodeEqualityRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectOrIntroductionRightCodeEqualityRootAt.
  apply templateAndLeftFrom_derives.
  rewrite <- coqRestrictedPADirectOrIntroductionRight_case_shape.
  apply coqRestrictedPADirectOrIntroductionRightCaseRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectOrIntroductionRightFormulaSuffixRootAt_valid :
  forall context,
  In coqRestrictedPADirectOrIntroductionRightCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectOrIntroductionRightFormulaSuffixTemplate
    (coqRestrictedPADirectOrIntroductionRightFormulaSuffixRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectOrIntroductionRightFormulaSuffixRootAt.
  apply templateAndRightFrom_derives.
  rewrite <- coqRestrictedPADirectOrIntroductionRight_case_shape.
  apply coqRestrictedPADirectOrIntroductionRightCaseRootAt_valid. exact hin.
Qed.

Lemma coqRestrictedPADirectOrIntroductionRightFormulaCodeRootAt_valid :
  forall context,
  In coqRestrictedPADirectOrIntroductionRightCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectOrIntroductionRightFormulaCodeTemplate
    (coqRestrictedPADirectOrIntroductionRightFormulaCodeRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectOrIntroductionRightFormulaCodeRootAt.
  apply templateAndLeftFrom_derives.
  apply coqRestrictedPADirectOrIntroductionRightFormulaSuffixRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectOrIntroductionRightChildSuffixRootAt_valid :
  forall context,
  In coqRestrictedPADirectOrIntroductionRightCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectOrIntroductionRightChildSuffixTemplate
    (coqRestrictedPADirectOrIntroductionRightChildSuffixRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectOrIntroductionRightChildSuffixRootAt.
  apply templateAndRightFrom_derives.
  apply coqRestrictedPADirectOrIntroductionRightFormulaSuffixRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectOrIntroductionRightChildEndpointRootAt_valid :
  forall context,
  In coqRestrictedPADirectOrIntroductionRightCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectOrIntroductionRightChildEndpointTemplate
    (coqRestrictedPADirectOrIntroductionRightChildEndpointRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectOrIntroductionRightChildEndpointRootAt.
  apply templateAndLeftFrom_derives.
  apply coqRestrictedPADirectOrIntroductionRightChildSuffixRootAt_valid.
  exact hin.
Qed.

(** ------------------------------------------------------------------
    Compile the two residual laws and all finite plumbing. *)

Theorem
    raw_codedPALocalProofOf_coqRestrictedPADirectOrIntroductionRightConclusion
    : forall (M : RawPAModel) (hPA : RawPASatisfies M)
      (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectOrIntroductionRightRecursiveChildLawRoot
    M hPA inputs tail ->
  RawCoqRestrictedPADirectOrIntroductionRightDynamicTruthLawRoot
    M hPA inputs tail ->
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectStrongStepOrIntroductionRightReadyContext tail))
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
    coqRestrictedPADirectStrongStepOrIntroductionRightReadyContext tail).
  set (readyContextCode :=
    rawTemplateContextCode translation readyContext).

  assert (hcase :
    In coqRestrictedPADirectOrIntroductionRightCaseTemplate readyContext).
  {
    unfold readyContext,
      coqRestrictedPADirectStrongStepOrIntroductionRightReadyContext,
      coqRestrictedPADirectStrongStepOrIntroductionRightAdmissibleContext,
      coqRestrictedPADirectStrongStepOrIntroductionRightCaseContext.
    right. right. left. reflexivity.
  }
  assert (hendpointBody :
    In rawCoqRestrictedPADirectEndpointWitnessBodyTemplate readyContext).
  {
    unfold readyContext,
      coqRestrictedPADirectStrongStepOrIntroductionRightReadyContext,
      coqRestrictedPADirectStrongStepOrIntroductionRightAdmissibleContext,
      coqRestrictedPADirectStrongStepOrIntroductionRightCaseContext,
      coqRestrictedPADirectStrongStepOrIntroductionRightDeepEndpointContext.
    do 3 right. left. reflexivity.
  }
  assert (houterContextTruth :
    In coqRestrictedPADirectAssumptionOuterContextTruthTemplate
      readyContext).
  {
    unfold readyContext,
      coqRestrictedPADirectStrongStepOrIntroductionRightReadyContext.
    left. reflexivity.
  }

  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectOrIntroductionRightFormulaCodeRootAt readyContext)
    (proj1
      (coqRestrictedPADirectOrIntroductionRightFormulaCodeRootAt_valid
        readyContext hcase))) as hformulaCode.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectOrIntroductionRightChildEndpointRootAt readyContext)
    (proj1
      (coqRestrictedPADirectOrIntroductionRightChildEndpointRootAt_valid
        readyContext hcase))) as hchildEndpoint.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt readyContext)
    (proj1
      (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt_valid
        readyContext hendpointBody houterContextTruth)))
    as hwitnessContextTruth.

  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectOrIntroductionRightFormulaCodeTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectOrIntroductionRightFormulaCodeRootAt
        readyContext))) in hformulaCode.
  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectOrIntroductionRightChildEndpointTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectOrIntroductionRightChildEndpointRootAt
        readyContext))) in hchildEndpoint.
  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectAssumptionWitnessContextTruthTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt
        readyContext))) in hwitnessContextTruth.

  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectOrIntroductionRightRecursiveChildLawTemplate)
    recursiveLawRoot) in hrecursiveLaw.
  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectOrIntroductionRightDynamicTruthLawTemplate)
    dynamicLawRoot) in hdynamicLaw.
  rewrite rawTemplateFormula_orIntroductionRightRecursiveChildLaw_view
    in hrecursiveLaw.
  rewrite rawTemplateFormula_orIntroductionRightDynamicTruthLaw_view
    in hdynamicLaw.

  set (childEndpointCode := rawTemplateFormula translation
    coqRestrictedPADirectOrIntroductionRightChildEndpointTemplate).
  set (witnessContextTruthCode := rawTemplateFormula translation
    coqRestrictedPADirectAssumptionWitnessContextTruthTemplate).
  set (formulaTruthCode := rawTemplateFormula translation
    coqRestrictedPADirectOrIntroductionRightFormulaTruthTemplate).
  set (formulaCodeRelation := rawTemplateFormula translation
    coqRestrictedPADirectOrIntroductionRightFormulaCodeTemplate).
  set (resultTruthCode := rawTemplateFormula translation
    coqRestrictedPADirectOrIntroductionRightResultTruthTemplate).

  set (recursiveAfterEndpointRoot := rawProofImpERoot M readyContextCode
    childEndpointCode
    (rawFormulaImpCode M witnessContextTruthCode formulaTruthCode)
    recursiveLawRoot
    (rawTemplateProofCode translation
      (coqRestrictedPADirectOrIntroductionRightChildEndpointRootAt
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
        (coqRestrictedPADirectOrIntroductionRightChildEndpointRootAt
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
      (coqRestrictedPADirectOrIntroductionRightFormulaCodeRootAt
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
        (coqRestrictedPADirectOrIntroductionRightFormulaCodeRootAt
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

Theorem raw_coqRestrictedPADirectStrongStepOrIntroductionRightCaseRoot :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectOrIntroductionRightRecursiveChildLawRoot
    M hPA inputs tail ->
  RawCoqRestrictedPADirectOrIntroductionRightDynamicTruthLawRoot
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
            rawCoqRuleOrIntroductionRight
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
    coqRestrictedPADirectStrongStepOrIntroductionRightDeepEndpointContext
      tail).
  set (caseContext :=
    coqRestrictedPADirectStrongStepOrIntroductionRightCaseContext tail).
  set (admissibleContext :=
    coqRestrictedPADirectStrongStepOrIntroductionRightAdmissibleContext tail).
  set (readyContext :=
    coqRestrictedPADirectStrongStepOrIntroductionRightReadyContext tail).
  destruct
    (raw_codedPALocalProofOf_coqRestrictedPADirectOrIntroductionRightConclusion
      M hPA inputs tail hrecursiveLaw hdynamicLaw) as
    [conclusionRoot hconclusion].

  set (baseContextCode := rawTemplateContextCode translation baseContext).
  set (caseContextCode := rawTemplateContextCode translation caseContext).
  set (admissibleContextCode :=
    rawTemplateContextCode translation admissibleContext).
  set (readyContextCode := rawTemplateContextCode translation readyContext).
  set (caseCode := rawTemplateFormula translation
    coqRestrictedPADirectOrIntroductionRightCaseTemplate).
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
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionRightCase.
