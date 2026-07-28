(**
  The genuine implication-introduction constructor case for the direct
  derivation-soundness strong step.

  After the endpoint relation has opened its eight witnesses, this branch
  supplies three facts:

    root = ImpI(witnessContext, antecedent, consequent, child),
    outerConclusion = Imp(antecedent, consequent),
    endpoint(child, antecedent :: witnessContext, consequent).

  The finite work in this file is deliberately explicit.  We project the
  latter two fields from the literal right-associated branch conjunction;
  transport the already-assumed outer context truth along the endpoint's
  equality [witnessContext = outerContext]; feed the child endpoint and the
  transported truth to a recursive-child law; feed the resulting
  [truth(antecedent) -> truth(consequent)] and the formula-code field to the
  dynamic implication law; and finally introduce the context-truth,
  admissibility, and branch implications in the exact shell order.

  Two mathematical seams remain, and only those two:

  - recursive-child soundness below the current root, including formation
    of truth for [antecedent :: witnessContext] from witness-context truth
    and assumed antecedent truth;
  - the dynamic Tarski law turning truth preservation from antecedent to
    consequent into truth of the displayed implication code.

  Neither seam is a result root for this branch, a proof of the outer
  conclusion, or the whole strong step.  Their ambient context is the exact
  semantically ready dispatcher context, so a later native compiler can use
  the strong prefix, restricted-proof premise, and projected rule data
  already available there.
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
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectImpIntroductionCase.

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
    Literal branch fields at the eight-witness depth. *)

Definition coqRestrictedPADirectImpIntroductionCodeEqualityTemplate
    : TemplateFormula :=
  embedPAFormula
    (pEq (liftTerm 8 (tVar 4))
      (proofImpICodeTerm (tVar 7) (tVar 6) (tVar 5) (tVar 2))).

Definition coqRestrictedPADirectImpIntroductionFormulaCodeTemplate
    : TemplateFormula :=
  embedPAFormula
    (formulaImpCodeTermAt
      (liftTerm 8 (tVar 2)) (tVar 6) (tVar 5)).

Definition coqRestrictedPADirectImpIntroductionChildEndpointTemplate
    : TemplateFormula :=
  embedPAFormula
    (proofEndpointTermAt (tVar 2)
      (nodeTerm (tVar 6) (tVar 7)) (tVar 5)).

Definition coqRestrictedPADirectImpIntroductionTerminalTruthTemplate
    : TemplateFormula :=
  embedPAFormula (pEq tZero tZero).

Definition coqRestrictedPADirectImpIntroductionChildSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectImpIntroductionChildEndpointTemplate
    coqRestrictedPADirectImpIntroductionTerminalTruthTemplate.

Definition coqRestrictedPADirectImpIntroductionFormulaSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectImpIntroductionFormulaCodeTemplate
    coqRestrictedPADirectImpIntroductionChildSuffixTemplate.

Definition coqRestrictedPADirectImpIntroductionCaseTemplate
    : TemplateFormula :=
  rawCoqRestrictedPAProofRuleCaseTemplate rawCoqRuleImpIntroduction
    (liftTerm 8 (tVar 4)) (tVar 7) (liftTerm 8 (tVar 2))
    (tVar 6) (tVar 5) (tVar 4) (tVar 3)
    (tVar 2) (tVar 1) (tVar 0).

Lemma coqRestrictedPADirectImpIntroduction_case_shape :
  coqRestrictedPADirectImpIntroductionCaseTemplate =
  tfAnd coqRestrictedPADirectImpIntroductionCodeEqualityTemplate
    coqRestrictedPADirectImpIntroductionFormulaSuffixTemplate.
Proof. reflexivity. Qed.

(** ------------------------------------------------------------------
    Truth leaves needed by this constructor.

    The assignment code and assignment step were [#1] and [#0] before the
    endpoint witnesses were opened, hence are [#9] and [#8] here. *)

Definition coqRestrictedPADirectImpIntroductionAntecedentTruthTemplate
    : TemplateFormula :=
  tfOpaque coqRestrictedPAConclusionTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     ttVar 6; ttVar 9; ttVar 8].

Definition coqRestrictedPADirectImpIntroductionConsequentTruthTemplate
    : TemplateFormula :=
  tfOpaque coqRestrictedPAConclusionTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     ttVar 5; ttVar 9; ttVar 8].

(** The first seam is precisely the recursive child call.  Its formula
    exposes the child endpoint and the correctly transported witness-context
    truth before returning the implication needed by Imp-I semantics. *)
Definition coqRestrictedPADirectImpIntroductionRecursiveChildLawTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectImpIntroductionChildEndpointTemplate
    (tfImp coqRestrictedPADirectAssumptionWitnessContextTruthTemplate
      (tfImp
        coqRestrictedPADirectImpIntroductionAntecedentTruthTemplate
        coqRestrictedPADirectImpIntroductionConsequentTruthTemplate)).

(** The second seam is only the dynamic implication Tarski law.  The
    formula-code relation is kept as an antecedent rather than silently
    identifying the outer conclusion with an implication code. *)
Definition coqRestrictedPADirectImpIntroductionDynamicTruthLawTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectImpIntroductionFormulaCodeTemplate
    (tfImp
      (tfImp coqRestrictedPADirectImpIntroductionAntecedentTruthTemplate
        coqRestrictedPADirectImpIntroductionConsequentTruthTemplate)
      coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate).

(** Structural code views avoid broad rewrite tactics over the very large
    exact dispatcher context. *)
Lemma rawTemplateFormula_impIntroductionRecursiveChildLaw_view : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  rawTemplateFormula translation
    coqRestrictedPADirectImpIntroductionRecursiveChildLawTemplate =
  rawFormulaImpCode M
    (rawTemplateFormula translation
      coqRestrictedPADirectImpIntroductionChildEndpointTemplate)
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionWitnessContextTruthTemplate)
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          coqRestrictedPADirectImpIntroductionAntecedentTruthTemplate)
        (rawTemplateFormula translation
          coqRestrictedPADirectImpIntroductionConsequentTruthTemplate))).
Proof.
  intros M translation.
  unfold coqRestrictedPADirectImpIntroductionRecursiveChildLawTemplate.
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectImpIntroductionChildEndpointTemplate
    (tfImp coqRestrictedPADirectAssumptionWitnessContextTruthTemplate
      (tfImp
        coqRestrictedPADirectImpIntroductionAntecedentTruthTemplate
        coqRestrictedPADirectImpIntroductionConsequentTruthTemplate))).
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectAssumptionWitnessContextTruthTemplate
    (tfImp
      coqRestrictedPADirectImpIntroductionAntecedentTruthTemplate
      coqRestrictedPADirectImpIntroductionConsequentTruthTemplate)).
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectImpIntroductionAntecedentTruthTemplate
    coqRestrictedPADirectImpIntroductionConsequentTruthTemplate).
  reflexivity.
Qed.

Lemma rawTemplateFormula_impIntroductionDynamicTruthLaw_view : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  rawTemplateFormula translation
    coqRestrictedPADirectImpIntroductionDynamicTruthLawTemplate =
  rawFormulaImpCode M
    (rawTemplateFormula translation
      coqRestrictedPADirectImpIntroductionFormulaCodeTemplate)
    (rawFormulaImpCode M
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          coqRestrictedPADirectImpIntroductionAntecedentTruthTemplate)
        (rawTemplateFormula translation
          coqRestrictedPADirectImpIntroductionConsequentTruthTemplate))
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate)).
Proof.
  intros M translation.
  unfold coqRestrictedPADirectImpIntroductionDynamicTruthLawTemplate.
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectImpIntroductionFormulaCodeTemplate
    (tfImp
      (tfImp coqRestrictedPADirectImpIntroductionAntecedentTruthTemplate
        coqRestrictedPADirectImpIntroductionConsequentTruthTemplate)
      coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate)).
  rewrite (rawTemplateFormula_imp translation
    (tfImp coqRestrictedPADirectImpIntroductionAntecedentTruthTemplate
      coqRestrictedPADirectImpIntroductionConsequentTruthTemplate)
    coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate).
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectImpIntroductionAntecedentTruthTemplate
    coqRestrictedPADirectImpIntroductionConsequentTruthTemplate).
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    Exact shell contexts. *)

Definition coqRestrictedPADirectStrongStepImpIntroductionDeepEndpointContext
    (tail : TemplateContext) : TemplateContext :=
  rawCoqRestrictedPADirectEndpointWitnessBodyTemplate ::
    rawCoqRestrictedPADirectEndpointDeepTail
      (rawCoqRestrictedPADirectStrongStepEndpointTail tail).

Definition coqRestrictedPADirectStrongStepImpIntroductionCaseContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectImpIntroductionCaseTemplate ::
    coqRestrictedPADirectStrongStepImpIntroductionDeepEndpointContext tail.

Definition coqRestrictedPADirectStrongStepImpIntroductionAdmissibleContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectAssumptionDeepAdmissibleTemplate ::
    coqRestrictedPADirectStrongStepImpIntroductionCaseContext tail.

Definition coqRestrictedPADirectStrongStepImpIntroductionReadyContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectAssumptionOuterContextTruthTemplate ::
    coqRestrictedPADirectStrongStepImpIntroductionAdmissibleContext tail.

Arguments coqRestrictedPADirectStrongStepImpIntroductionDeepEndpointContext
  tail : clear implicits.
Arguments coqRestrictedPADirectStrongStepImpIntroductionCaseContext
  tail : clear implicits.
Arguments coqRestrictedPADirectStrongStepImpIntroductionAdmissibleContext
  tail : clear implicits.
Arguments coqRestrictedPADirectStrongStepImpIntroductionReadyContext
  tail : clear implicits.

Definition RawCoqRestrictedPADirectImpIntroductionRecursiveChildLawRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectStrongStepImpIntroductionReadyContext tail))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectImpIntroductionRecursiveChildLawTemplate)
      root.

Definition RawCoqRestrictedPADirectImpIntroductionDynamicTruthLawRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectStrongStepImpIntroductionReadyContext tail))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectImpIntroductionDynamicTruthLawTemplate)
      root.

Arguments RawCoqRestrictedPADirectImpIntroductionRecursiveChildLawRoot
  M hPA inputs tail : clear implicits.
Arguments RawCoqRestrictedPADirectImpIntroductionDynamicTruthLawRoot
  M hPA inputs tail : clear implicits.

(** ------------------------------------------------------------------
    Literal conjunction projections in an arbitrary context. *)

Definition coqRestrictedPADirectImpIntroductionCaseRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAss context coqRestrictedPADirectImpIntroductionCaseTemplate.

Definition coqRestrictedPADirectImpIntroductionFormulaSuffixRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE2 context
    coqRestrictedPADirectImpIntroductionCodeEqualityTemplate
    coqRestrictedPADirectImpIntroductionFormulaSuffixTemplate
    (coqRestrictedPADirectImpIntroductionCaseRootAt context).

Definition coqRestrictedPADirectImpIntroductionFormulaCodeRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectImpIntroductionFormulaCodeTemplate
    coqRestrictedPADirectImpIntroductionChildSuffixTemplate
    (coqRestrictedPADirectImpIntroductionFormulaSuffixRootAt context).

Definition coqRestrictedPADirectImpIntroductionChildSuffixRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE2 context
    coqRestrictedPADirectImpIntroductionFormulaCodeTemplate
    coqRestrictedPADirectImpIntroductionChildSuffixTemplate
    (coqRestrictedPADirectImpIntroductionFormulaSuffixRootAt context).

Definition coqRestrictedPADirectImpIntroductionChildEndpointRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectImpIntroductionChildEndpointTemplate
    coqRestrictedPADirectImpIntroductionTerminalTruthTemplate
    (coqRestrictedPADirectImpIntroductionChildSuffixRootAt context).

Lemma coqRestrictedPADirectImpIntroductionCaseRootAt_valid : forall context,
  In coqRestrictedPADirectImpIntroductionCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectImpIntroductionCaseTemplate
    (coqRestrictedPADirectImpIntroductionCaseRootAt context).
Proof.
  intros context hin. apply templateRawDerives_assumption. exact hin.
Qed.

Lemma coqRestrictedPADirectImpIntroductionFormulaSuffixRootAt_valid :
  forall context,
  In coqRestrictedPADirectImpIntroductionCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectImpIntroductionFormulaSuffixTemplate
    (coqRestrictedPADirectImpIntroductionFormulaSuffixRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectImpIntroductionFormulaSuffixRootAt.
  apply templateAndRightFrom_derives.
  rewrite <- coqRestrictedPADirectImpIntroduction_case_shape.
  apply coqRestrictedPADirectImpIntroductionCaseRootAt_valid. exact hin.
Qed.

Lemma coqRestrictedPADirectImpIntroductionFormulaCodeRootAt_valid :
  forall context,
  In coqRestrictedPADirectImpIntroductionCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectImpIntroductionFormulaCodeTemplate
    (coqRestrictedPADirectImpIntroductionFormulaCodeRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectImpIntroductionFormulaCodeRootAt.
  apply templateAndLeftFrom_derives.
  apply coqRestrictedPADirectImpIntroductionFormulaSuffixRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectImpIntroductionChildSuffixRootAt_valid :
  forall context,
  In coqRestrictedPADirectImpIntroductionCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectImpIntroductionChildSuffixTemplate
    (coqRestrictedPADirectImpIntroductionChildSuffixRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectImpIntroductionChildSuffixRootAt.
  apply templateAndRightFrom_derives.
  apply coqRestrictedPADirectImpIntroductionFormulaSuffixRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectImpIntroductionChildEndpointRootAt_valid :
  forall context,
  In coqRestrictedPADirectImpIntroductionCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectImpIntroductionChildEndpointTemplate
    (coqRestrictedPADirectImpIntroductionChildEndpointRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectImpIntroductionChildEndpointRootAt.
  apply templateAndLeftFrom_derives.
  apply coqRestrictedPADirectImpIntroductionChildSuffixRootAt_valid.
  exact hin.
Qed.

(** ------------------------------------------------------------------
    Compile the semantic core in the exact ready context. *)

Theorem raw_codedPALocalProofOf_coqRestrictedPADirectImpIntroductionConclusion :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectImpIntroductionRecursiveChildLawRoot
    M hPA inputs tail ->
  RawCoqRestrictedPADirectImpIntroductionDynamicTruthLawRoot
    M hPA inputs tail ->
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectStrongStepImpIntroductionReadyContext tail))
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
    coqRestrictedPADirectStrongStepImpIntroductionReadyContext tail).
  set (readyContextCode :=
    rawTemplateContextCode translation readyContext).

  assert (hcase :
    In coqRestrictedPADirectImpIntroductionCaseTemplate readyContext).
  {
    unfold readyContext,
      coqRestrictedPADirectStrongStepImpIntroductionReadyContext,
      coqRestrictedPADirectStrongStepImpIntroductionAdmissibleContext,
      coqRestrictedPADirectStrongStepImpIntroductionCaseContext.
    right. right. left. reflexivity.
  }
  assert (hendpointBody :
    In rawCoqRestrictedPADirectEndpointWitnessBodyTemplate readyContext).
  {
    unfold readyContext,
      coqRestrictedPADirectStrongStepImpIntroductionReadyContext,
      coqRestrictedPADirectStrongStepImpIntroductionAdmissibleContext,
      coqRestrictedPADirectStrongStepImpIntroductionCaseContext,
      coqRestrictedPADirectStrongStepImpIntroductionDeepEndpointContext.
    do 3 right. left. reflexivity.
  }
  assert (houterContextTruth :
    In coqRestrictedPADirectAssumptionOuterContextTruthTemplate
      readyContext).
  {
    unfold readyContext,
      coqRestrictedPADirectStrongStepImpIntroductionReadyContext.
    left. reflexivity.
  }

  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectImpIntroductionFormulaCodeRootAt readyContext)
    (proj1
      (coqRestrictedPADirectImpIntroductionFormulaCodeRootAt_valid
        readyContext hcase))) as hformulaCode.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectImpIntroductionChildEndpointRootAt readyContext)
    (proj1
      (coqRestrictedPADirectImpIntroductionChildEndpointRootAt_valid
        readyContext hcase))) as hchildEndpoint.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt readyContext)
    (proj1
      (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt_valid
        readyContext hendpointBody houterContextTruth)))
    as hwitnessContextTruth.

  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectImpIntroductionFormulaCodeTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectImpIntroductionFormulaCodeRootAt readyContext)))
    in hformulaCode.
  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectImpIntroductionChildEndpointTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectImpIntroductionChildEndpointRootAt
        readyContext))) in hchildEndpoint.
  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectAssumptionWitnessContextTruthTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt
        readyContext))) in hwitnessContextTruth.

  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectImpIntroductionRecursiveChildLawTemplate)
    recursiveLawRoot) in hrecursiveLaw.
  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectImpIntroductionDynamicTruthLawTemplate)
    dynamicLawRoot) in hdynamicLaw.

  rewrite rawTemplateFormula_impIntroductionRecursiveChildLaw_view
    in hrecursiveLaw.
  rewrite rawTemplateFormula_impIntroductionDynamicTruthLaw_view
    in hdynamicLaw.

  set (childEndpointCode := rawTemplateFormula translation
    coqRestrictedPADirectImpIntroductionChildEndpointTemplate).
  set (witnessContextTruthCode := rawTemplateFormula translation
    coqRestrictedPADirectAssumptionWitnessContextTruthTemplate).
  set (antecedentTruthCode := rawTemplateFormula translation
    coqRestrictedPADirectImpIntroductionAntecedentTruthTemplate).
  set (consequentTruthCode := rawTemplateFormula translation
    coqRestrictedPADirectImpIntroductionConsequentTruthTemplate).
  set (formulaCodeRelation := rawTemplateFormula translation
    coqRestrictedPADirectImpIntroductionFormulaCodeTemplate).
  set (outerConclusionTruthCode := rawTemplateFormula translation
    coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate).
  set (truthImplicationCode := rawFormulaImpCode M
    antecedentTruthCode consequentTruthCode).

  set (recursiveAfterEndpointRoot := rawProofImpERoot M readyContextCode
    childEndpointCode
    (rawFormulaImpCode M witnessContextTruthCode truthImplicationCode)
    recursiveLawRoot
    (rawTemplateProofCode translation
      (coqRestrictedPADirectImpIntroductionChildEndpointRootAt
        readyContext))).
  assert (hrecursiveAfterEndpoint : RawCodedPALocalProofOf M
    readyContextCode
    (rawFormulaImpCode M witnessContextTruthCode truthImplicationCode)
    recursiveAfterEndpointRoot).
  {
    unfold recursiveAfterEndpointRoot.
    apply (raw_codedPALocalProofOf_impE M hPA readyContextCode
      childEndpointCode
      (rawFormulaImpCode M witnessContextTruthCode truthImplicationCode)
      recursiveLawRoot
      (rawTemplateProofCode translation
        (coqRestrictedPADirectImpIntroductionChildEndpointRootAt
          readyContext))).
    - exact hrecursiveLaw.
    - unfold childEndpointCode. exact hchildEndpoint.
  }

  set (truthImplicationRoot := rawProofImpERoot M readyContextCode
    witnessContextTruthCode truthImplicationCode
    recursiveAfterEndpointRoot
    (rawTemplateProofCode translation
      (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt
        readyContext))).
  assert (htruthImplication : RawCodedPALocalProofOf M readyContextCode
    truthImplicationCode truthImplicationRoot).
  {
    unfold truthImplicationRoot.
    apply (raw_codedPALocalProofOf_impE M hPA readyContextCode
      witnessContextTruthCode truthImplicationCode
      recursiveAfterEndpointRoot
      (rawTemplateProofCode translation
        (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt
          readyContext))).
    - exact hrecursiveAfterEndpoint.
    - unfold witnessContextTruthCode. exact hwitnessContextTruth.
  }

  set (dynamicAfterFormulaRoot := rawProofImpERoot M readyContextCode
    formulaCodeRelation
    (rawFormulaImpCode M truthImplicationCode outerConclusionTruthCode)
    dynamicLawRoot
    (rawTemplateProofCode translation
      (coqRestrictedPADirectImpIntroductionFormulaCodeRootAt readyContext))).
  assert (hdynamicAfterFormula : RawCodedPALocalProofOf M readyContextCode
    (rawFormulaImpCode M truthImplicationCode outerConclusionTruthCode)
    dynamicAfterFormulaRoot).
  {
    unfold dynamicAfterFormulaRoot.
    apply (raw_codedPALocalProofOf_impE M hPA readyContextCode
      formulaCodeRelation
      (rawFormulaImpCode M truthImplicationCode outerConclusionTruthCode)
      dynamicLawRoot
      (rawTemplateProofCode translation
        (coqRestrictedPADirectImpIntroductionFormulaCodeRootAt
          readyContext))).
    - exact hdynamicLaw.
    - unfold formulaCodeRelation. exact hformulaCode.
  }

  exists (rawProofImpERoot M readyContextCode truthImplicationCode
    outerConclusionTruthCode dynamicAfterFormulaRoot truthImplicationRoot).
  apply (raw_codedPALocalProofOf_impE M hPA readyContextCode
    truthImplicationCode outerConclusionTruthCode
    dynamicAfterFormulaRoot truthImplicationRoot).
  - exact hdynamicAfterFormula.
  - exact htruthImplication.
Qed.

(** ------------------------------------------------------------------
    Introduce the exact remaining suffix and expose the public shell slot. *)

Theorem raw_coqRestrictedPADirectStrongStepImpIntroductionCaseRoot :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectImpIntroductionRecursiveChildLawRoot
    M hPA inputs tail ->
  RawCoqRestrictedPADirectImpIntroductionDynamicTruthLawRoot
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
          (rawCoqRestrictedPAProofRuleCaseTemplate rawCoqRuleImpIntroduction
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
    coqRestrictedPADirectStrongStepImpIntroductionDeepEndpointContext tail).
  set (caseContext :=
    coqRestrictedPADirectStrongStepImpIntroductionCaseContext tail).
  set (admissibleContext :=
    coqRestrictedPADirectStrongStepImpIntroductionAdmissibleContext tail).
  set (readyContext :=
    coqRestrictedPADirectStrongStepImpIntroductionReadyContext tail).
  destruct
    (raw_codedPALocalProofOf_coqRestrictedPADirectImpIntroductionConclusion
      M hPA inputs tail hrecursiveLaw hdynamicLaw) as
    [conclusionRoot hconclusion].

  set (baseContextCode := rawTemplateContextCode translation baseContext).
  set (caseContextCode := rawTemplateContextCode translation caseContext).
  set (admissibleContextCode :=
    rawTemplateContextCode translation admissibleContext).
  set (readyContextCode := rawTemplateContextCode translation readyContext).
  set (caseCode := rawTemplateFormula translation
    coqRestrictedPADirectImpIntroductionCaseTemplate).
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
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectImpIntroductionCase.
