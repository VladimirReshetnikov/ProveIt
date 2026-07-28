(**
  The genuine right-conjunction-elimination constructor case for the direct
  derivation-soundness strong step.

  At the eight-witness endpoint depth this branch displays

    outerConclusion = right,
    displayedConjunction = And(left, right),
    endpoint(child, witnessContext, displayedConjunction).

  The proof below projects those three literal fields.  It transports the
  outer context-truth assumption to [witnessContext] using the endpoint
  witness equality, invokes a sharply stated recursive-child law to obtain
  truth of [displayedConjunction], invokes only the right-conjunction Tarski
  law to obtain truth of [right], and finally transports that truth backwards
  along [outerConclusion = right] with an explicit equality-elimination
  proof.

  Thus only two mathematical seams remain:

  - recursive-child soundness at the displayed child endpoint;
  - the dynamic truth law eliminating the right component of a displayed
    conjunction code.

  No branch-result root, outer-conclusion proof, strong-step proof, or
  equality-transport premise is assumed.  All conjunction projections,
  equality symmetry/elimination, modus ponens, and shell implication
  introductions are compiled as model-coded PA proofs.
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
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndEliminationRightCase.

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

Definition coqRestrictedPADirectAndEliminationRightCodeEqualityTemplate
    : TemplateFormula :=
  embedPAFormula
    (pEq (liftTerm 8 (tVar 4))
      (proofAndE2CodeTerm (tVar 7) (tVar 6) (tVar 5) (tVar 2))).

(** The right conjunct occupies witness slot five.  This is deliberately a
    separate term from the assumption branch's slot-six witness formula: the
    latter happens to coincide with the *left* conjunct in the common
    eight-witness layout. *)
Definition coqRestrictedPADirectAndEliminationRightResultFormulaTerm
    : TemplateTerm := ttVar 5.

Definition coqRestrictedPADirectAndEliminationRightConclusionEqualityTemplate
    : TemplateFormula :=
  tfEq coqRestrictedPADirectAssumptionOuterConclusionTerm
    coqRestrictedPADirectAndEliminationRightResultFormulaTerm.

Definition coqRestrictedPADirectAndEliminationRightFormulaCodeTemplate
    : TemplateFormula :=
  embedPAFormula
    (formulaAndCodeTermAt (tVar 4) (tVar 6) (tVar 5)).

Definition coqRestrictedPADirectAndEliminationRightChildEndpointTemplate
    : TemplateFormula :=
  embedPAFormula
    (proofEndpointTermAt (tVar 2) (tVar 7) (tVar 4)).

Definition coqRestrictedPADirectAndEliminationRightTerminalTruthTemplate
    : TemplateFormula :=
  embedPAFormula (pEq tZero tZero).

Definition coqRestrictedPADirectAndEliminationRightChildSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectAndEliminationRightChildEndpointTemplate
    coqRestrictedPADirectAndEliminationRightTerminalTruthTemplate.

Definition coqRestrictedPADirectAndEliminationRightFormulaSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectAndEliminationRightFormulaCodeTemplate
    coqRestrictedPADirectAndEliminationRightChildSuffixTemplate.

Definition coqRestrictedPADirectAndEliminationRightConclusionSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectAndEliminationRightConclusionEqualityTemplate
    coqRestrictedPADirectAndEliminationRightFormulaSuffixTemplate.

Definition coqRestrictedPADirectAndEliminationRightCaseTemplate
    : TemplateFormula :=
  rawCoqRestrictedPAProofRuleCaseTemplate rawCoqRuleAndEliminationRight
    (liftTerm 8 (tVar 4)) (tVar 7) (liftTerm 8 (tVar 2))
    (tVar 6) (tVar 5) (tVar 4) (tVar 3)
    (tVar 2) (tVar 1) (tVar 0).

Lemma coqRestrictedPADirectAndEliminationRight_case_shape :
  coqRestrictedPADirectAndEliminationRightCaseTemplate =
  tfAnd coqRestrictedPADirectAndEliminationRightCodeEqualityTemplate
    coqRestrictedPADirectAndEliminationRightConclusionSuffixTemplate.
Proof. reflexivity. Qed.

(** ------------------------------------------------------------------
    Truth leaves and the two exact residual laws. *)

Definition coqRestrictedPADirectAndEliminationRightFormulaTruthTemplate
    : TemplateFormula :=
  tfOpaque coqRestrictedPAConclusionTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     ttVar 4; ttVar 9; ttVar 8].

Definition coqRestrictedPADirectAndEliminationRightResultTruthTemplate
    : TemplateFormula :=
  tfOpaque coqRestrictedPAConclusionTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     coqRestrictedPADirectAndEliminationRightResultFormulaTerm;
     ttVar 9; ttVar 8].

Lemma coqRestrictedPADirectAndEliminationRight_result_truth_shape :
  coqRestrictedPADirectAndEliminationRightResultTruthTemplate =
  tfOpaque coqRestrictedPAConclusionTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     ttVar 5; ttVar 9; ttVar 8].
Proof. reflexivity. Qed.

(** Equality elimination opens its motive at the right-conjunct term.  This
    small literal lemma prevents the transport proof from accidentally
    reusing the assumption branch's slot-six specialization. *)
Lemma coqRestrictedPADirectAndEliminationRight_conclusion_motive_result :
  templateFormulaOpen
    coqRestrictedPADirectAndEliminationRightResultFormulaTerm
    coqRestrictedPADirectAssumptionConclusionTruthMotive =
  coqRestrictedPADirectAndEliminationRightResultTruthTemplate.
Proof. reflexivity. Qed.

Definition coqRestrictedPADirectAndEliminationRightRecursiveChildLawTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectAndEliminationRightChildEndpointTemplate
    (tfImp coqRestrictedPADirectAssumptionWitnessContextTruthTemplate
      coqRestrictedPADirectAndEliminationRightFormulaTruthTemplate).

Definition coqRestrictedPADirectAndEliminationRightDynamicTruthLawTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectAndEliminationRightFormulaCodeTemplate
    (tfImp coqRestrictedPADirectAndEliminationRightFormulaTruthTemplate
      coqRestrictedPADirectAndEliminationRightResultTruthTemplate).

Lemma rawTemplateFormula_andEliminationRightRecursiveChildLaw_view : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  rawTemplateFormula translation
    coqRestrictedPADirectAndEliminationRightRecursiveChildLawTemplate =
  rawFormulaImpCode M
    (rawTemplateFormula translation
      coqRestrictedPADirectAndEliminationRightChildEndpointTemplate)
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionWitnessContextTruthTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectAndEliminationRightFormulaTruthTemplate)).
Proof.
  intros M translation.
  unfold coqRestrictedPADirectAndEliminationRightRecursiveChildLawTemplate.
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectAndEliminationRightChildEndpointTemplate
    (tfImp coqRestrictedPADirectAssumptionWitnessContextTruthTemplate
      coqRestrictedPADirectAndEliminationRightFormulaTruthTemplate)).
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectAssumptionWitnessContextTruthTemplate
    coqRestrictedPADirectAndEliminationRightFormulaTruthTemplate).
  reflexivity.
Qed.

Lemma rawTemplateFormula_andEliminationRightDynamicTruthLaw_view : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  rawTemplateFormula translation
    coqRestrictedPADirectAndEliminationRightDynamicTruthLawTemplate =
  rawFormulaImpCode M
    (rawTemplateFormula translation
      coqRestrictedPADirectAndEliminationRightFormulaCodeTemplate)
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectAndEliminationRightFormulaTruthTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectAndEliminationRightResultTruthTemplate)).
Proof.
  intros M translation.
  unfold coqRestrictedPADirectAndEliminationRightDynamicTruthLawTemplate.
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectAndEliminationRightFormulaCodeTemplate
    (tfImp coqRestrictedPADirectAndEliminationRightFormulaTruthTemplate
      coqRestrictedPADirectAndEliminationRightResultTruthTemplate)).
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectAndEliminationRightFormulaTruthTemplate
    coqRestrictedPADirectAndEliminationRightResultTruthTemplate).
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    Exact shell contexts and residual root interfaces. *)

Definition
    coqRestrictedPADirectStrongStepAndEliminationRightDeepEndpointContext
    (tail : TemplateContext) : TemplateContext :=
  rawCoqRestrictedPADirectEndpointWitnessBodyTemplate ::
    rawCoqRestrictedPADirectEndpointDeepTail
      (rawCoqRestrictedPADirectStrongStepEndpointTail tail).

Definition coqRestrictedPADirectStrongStepAndEliminationRightCaseContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectAndEliminationRightCaseTemplate ::
    coqRestrictedPADirectStrongStepAndEliminationRightDeepEndpointContext
      tail.

Definition
    coqRestrictedPADirectStrongStepAndEliminationRightAdmissibleContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectAssumptionDeepAdmissibleTemplate ::
    coqRestrictedPADirectStrongStepAndEliminationRightCaseContext tail.

Definition coqRestrictedPADirectStrongStepAndEliminationRightReadyContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectAssumptionOuterContextTruthTemplate ::
    coqRestrictedPADirectStrongStepAndEliminationRightAdmissibleContext tail.

Arguments
  coqRestrictedPADirectStrongStepAndEliminationRightDeepEndpointContext
  tail : clear implicits.
Arguments coqRestrictedPADirectStrongStepAndEliminationRightCaseContext
  tail : clear implicits.
Arguments
  coqRestrictedPADirectStrongStepAndEliminationRightAdmissibleContext
  tail : clear implicits.
Arguments coqRestrictedPADirectStrongStepAndEliminationRightReadyContext
  tail : clear implicits.

Definition RawCoqRestrictedPADirectAndEliminationRightRecursiveChildLawRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectStrongStepAndEliminationRightReadyContext tail))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectAndEliminationRightRecursiveChildLawTemplate)
      root.

Definition RawCoqRestrictedPADirectAndEliminationRightDynamicTruthLawRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectStrongStepAndEliminationRightReadyContext tail))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectAndEliminationRightDynamicTruthLawTemplate)
      root.

Arguments RawCoqRestrictedPADirectAndEliminationRightRecursiveChildLawRoot
  M hPA inputs tail : clear implicits.
Arguments RawCoqRestrictedPADirectAndEliminationRightDynamicTruthLawRoot
  M hPA inputs tail : clear implicits.

(** ------------------------------------------------------------------
    Parameterized finite branch projections. *)

Definition coqRestrictedPADirectAndEliminationRightCaseRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAss context coqRestrictedPADirectAndEliminationRightCaseTemplate.

Definition coqRestrictedPADirectAndEliminationRightConclusionSuffixRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE2 context
    coqRestrictedPADirectAndEliminationRightCodeEqualityTemplate
    coqRestrictedPADirectAndEliminationRightConclusionSuffixTemplate
    (coqRestrictedPADirectAndEliminationRightCaseRootAt context).

Definition coqRestrictedPADirectAndEliminationRightConclusionEqualityRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectAndEliminationRightConclusionEqualityTemplate
    coqRestrictedPADirectAndEliminationRightFormulaSuffixTemplate
    (coqRestrictedPADirectAndEliminationRightConclusionSuffixRootAt context).

Definition coqRestrictedPADirectAndEliminationRightFormulaSuffixRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE2 context
    coqRestrictedPADirectAndEliminationRightConclusionEqualityTemplate
    coqRestrictedPADirectAndEliminationRightFormulaSuffixTemplate
    (coqRestrictedPADirectAndEliminationRightConclusionSuffixRootAt context).

Definition coqRestrictedPADirectAndEliminationRightFormulaCodeRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectAndEliminationRightFormulaCodeTemplate
    coqRestrictedPADirectAndEliminationRightChildSuffixTemplate
    (coqRestrictedPADirectAndEliminationRightFormulaSuffixRootAt context).

Definition coqRestrictedPADirectAndEliminationRightChildSuffixRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE2 context
    coqRestrictedPADirectAndEliminationRightFormulaCodeTemplate
    coqRestrictedPADirectAndEliminationRightChildSuffixTemplate
    (coqRestrictedPADirectAndEliminationRightFormulaSuffixRootAt context).

Definition coqRestrictedPADirectAndEliminationRightChildEndpointRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectAndEliminationRightChildEndpointTemplate
    coqRestrictedPADirectAndEliminationRightTerminalTruthTemplate
    (coqRestrictedPADirectAndEliminationRightChildSuffixRootAt context).

Lemma coqRestrictedPADirectAndEliminationRightCaseRootAt_valid :
  forall context,
  In coqRestrictedPADirectAndEliminationRightCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectAndEliminationRightCaseTemplate
    (coqRestrictedPADirectAndEliminationRightCaseRootAt context).
Proof.
  intros context hin. apply templateRawDerives_assumption. exact hin.
Qed.

Lemma coqRestrictedPADirectAndEliminationRightConclusionSuffixRootAt_valid :
  forall context,
  In coqRestrictedPADirectAndEliminationRightCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectAndEliminationRightConclusionSuffixTemplate
    (coqRestrictedPADirectAndEliminationRightConclusionSuffixRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectAndEliminationRightConclusionSuffixRootAt.
  apply templateAndRightFrom_derives.
  rewrite <- coqRestrictedPADirectAndEliminationRight_case_shape.
  apply coqRestrictedPADirectAndEliminationRightCaseRootAt_valid. exact hin.
Qed.

Lemma coqRestrictedPADirectAndEliminationRightConclusionEqualityRootAt_valid :
  forall context,
  In coqRestrictedPADirectAndEliminationRightCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectAndEliminationRightConclusionEqualityTemplate
    (coqRestrictedPADirectAndEliminationRightConclusionEqualityRootAt
      context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectAndEliminationRightConclusionEqualityRootAt.
  apply templateAndLeftFrom_derives.
  apply coqRestrictedPADirectAndEliminationRightConclusionSuffixRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectAndEliminationRightFormulaSuffixRootAt_valid :
  forall context,
  In coqRestrictedPADirectAndEliminationRightCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectAndEliminationRightFormulaSuffixTemplate
    (coqRestrictedPADirectAndEliminationRightFormulaSuffixRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectAndEliminationRightFormulaSuffixRootAt.
  apply templateAndRightFrom_derives.
  apply coqRestrictedPADirectAndEliminationRightConclusionSuffixRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectAndEliminationRightFormulaCodeRootAt_valid :
  forall context,
  In coqRestrictedPADirectAndEliminationRightCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectAndEliminationRightFormulaCodeTemplate
    (coqRestrictedPADirectAndEliminationRightFormulaCodeRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectAndEliminationRightFormulaCodeRootAt.
  apply templateAndLeftFrom_derives.
  apply coqRestrictedPADirectAndEliminationRightFormulaSuffixRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectAndEliminationRightChildSuffixRootAt_valid :
  forall context,
  In coqRestrictedPADirectAndEliminationRightCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectAndEliminationRightChildSuffixTemplate
    (coqRestrictedPADirectAndEliminationRightChildSuffixRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectAndEliminationRightChildSuffixRootAt.
  apply templateAndRightFrom_derives.
  apply coqRestrictedPADirectAndEliminationRightFormulaSuffixRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectAndEliminationRightChildEndpointRootAt_valid :
  forall context,
  In coqRestrictedPADirectAndEliminationRightCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectAndEliminationRightChildEndpointTemplate
    (coqRestrictedPADirectAndEliminationRightChildEndpointRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectAndEliminationRightChildEndpointRootAt.
  apply templateAndLeftFrom_derives.
  apply coqRestrictedPADirectAndEliminationRightChildSuffixRootAt_valid.
  exact hin.
Qed.

(** ------------------------------------------------------------------
    A fully compiled truth transport along [outerConclusion = right]. *)

Definition coqRestrictedPADirectAndEliminationRightTransportChildContext
    (context : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectAndEliminationRightResultTruthTemplate :: context.

Definition coqRestrictedPADirectAndEliminationRightConclusionSymmetryRootAt
    (context : TemplateContext) : TemplateRawProof :=
  coqRestrictedPADirectEqSymmetryRoot context
    coqRestrictedPADirectAssumptionOuterConclusionTerm
    coqRestrictedPADirectAndEliminationRightResultFormulaTerm
    (coqRestrictedPADirectAndEliminationRightConclusionEqualityRootAt
      context).

Definition coqRestrictedPADirectAndEliminationRightResultTruthRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAss context coqRestrictedPADirectAndEliminationRightResultTruthTemplate.

Definition coqRestrictedPADirectAndEliminationRightOuterTruthChildRootAt
    (context : TemplateContext) : TemplateRawProof :=
  let childContext :=
    coqRestrictedPADirectAndEliminationRightTransportChildContext context in
  trpEqElim childContext
    coqRestrictedPADirectAndEliminationRightResultFormulaTerm
    coqRestrictedPADirectAssumptionOuterConclusionTerm
    coqRestrictedPADirectAssumptionConclusionTruthMotive
    (coqRestrictedPADirectAndEliminationRightConclusionSymmetryRootAt
      childContext)
    (coqRestrictedPADirectAndEliminationRightResultTruthRootAt childContext).

Definition coqRestrictedPADirectAndEliminationRightConclusionTransportRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpImpI context
    coqRestrictedPADirectAndEliminationRightResultTruthTemplate
    coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate
    (coqRestrictedPADirectAndEliminationRightOuterTruthChildRootAt context).

Lemma coqRestrictedPADirectAndEliminationRightConclusionSymmetryRootAt_valid :
  forall context,
  In coqRestrictedPADirectAndEliminationRightCaseTemplate context ->
  TemplateRawDerives context
    (tfEq coqRestrictedPADirectAndEliminationRightResultFormulaTerm
      coqRestrictedPADirectAssumptionOuterConclusionTerm)
    (coqRestrictedPADirectAndEliminationRightConclusionSymmetryRootAt
      context).
Proof.
  intros context hin.
  apply coqRestrictedPADirectEqSymmetryRoot_valid.
  apply coqRestrictedPADirectAndEliminationRightConclusionEqualityRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectAndEliminationRightConclusionTransportRootAt_valid :
  forall context,
  In coqRestrictedPADirectAndEliminationRightCaseTemplate context ->
  TemplateRawDerives context
    (tfImp coqRestrictedPADirectAndEliminationRightResultTruthTemplate
      coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate)
    (coqRestrictedPADirectAndEliminationRightConclusionTransportRootAt
      context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectAndEliminationRightConclusionTransportRootAt,
    coqRestrictedPADirectAndEliminationRightOuterTruthChildRootAt.
  cbn zeta.
  apply coqRestrictedPADirect_templateRawDerives_impI.
  rewrite <- coqRestrictedPADirectAssumption_conclusion_motive_outer.
  apply coqRestrictedPADirect_templateRawDerives_eqElim.
  - apply
      coqRestrictedPADirectAndEliminationRightConclusionSymmetryRootAt_valid.
    right. exact hin.
  - rewrite
      coqRestrictedPADirectAndEliminationRight_conclusion_motive_result.
    apply templateRawDerives_assumption. left. reflexivity.
Qed.

(** ------------------------------------------------------------------
    Compile the two residual laws and all finite plumbing. *)

Theorem
    raw_codedPALocalProofOf_coqRestrictedPADirectAndEliminationRightConclusion
    : forall (M : RawPAModel) (hPA : RawPASatisfies M)
      (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectAndEliminationRightRecursiveChildLawRoot
    M hPA inputs tail ->
  RawCoqRestrictedPADirectAndEliminationRightDynamicTruthLawRoot
    M hPA inputs tail ->
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectStrongStepAndEliminationRightReadyContext tail))
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
    coqRestrictedPADirectStrongStepAndEliminationRightReadyContext tail).
  set (readyContextCode :=
    rawTemplateContextCode translation readyContext).

  assert (hcase :
    In coqRestrictedPADirectAndEliminationRightCaseTemplate readyContext).
  {
    unfold readyContext,
      coqRestrictedPADirectStrongStepAndEliminationRightReadyContext,
      coqRestrictedPADirectStrongStepAndEliminationRightAdmissibleContext,
      coqRestrictedPADirectStrongStepAndEliminationRightCaseContext.
    right. right. left. reflexivity.
  }
  assert (hendpointBody :
    In rawCoqRestrictedPADirectEndpointWitnessBodyTemplate readyContext).
  {
    unfold readyContext,
      coqRestrictedPADirectStrongStepAndEliminationRightReadyContext,
      coqRestrictedPADirectStrongStepAndEliminationRightAdmissibleContext,
      coqRestrictedPADirectStrongStepAndEliminationRightCaseContext,
      coqRestrictedPADirectStrongStepAndEliminationRightDeepEndpointContext.
    do 3 right. left. reflexivity.
  }
  assert (houterContextTruth :
    In coqRestrictedPADirectAssumptionOuterContextTruthTemplate
      readyContext).
  {
    unfold readyContext,
      coqRestrictedPADirectStrongStepAndEliminationRightReadyContext.
    left. reflexivity.
  }

  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectAndEliminationRightFormulaCodeRootAt readyContext)
    (proj1
      (coqRestrictedPADirectAndEliminationRightFormulaCodeRootAt_valid
        readyContext hcase))) as hformulaCode.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectAndEliminationRightChildEndpointRootAt readyContext)
    (proj1
      (coqRestrictedPADirectAndEliminationRightChildEndpointRootAt_valid
        readyContext hcase))) as hchildEndpoint.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt readyContext)
    (proj1
      (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt_valid
        readyContext hendpointBody houterContextTruth)))
    as hwitnessContextTruth.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectAndEliminationRightConclusionTransportRootAt
      readyContext)
    (proj1
      (coqRestrictedPADirectAndEliminationRightConclusionTransportRootAt_valid
        readyContext hcase))) as htransport.

  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectAndEliminationRightFormulaCodeTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectAndEliminationRightFormulaCodeRootAt
        readyContext))) in hformulaCode.
  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectAndEliminationRightChildEndpointTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectAndEliminationRightChildEndpointRootAt
        readyContext))) in hchildEndpoint.
  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectAssumptionWitnessContextTruthTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt
        readyContext))) in hwitnessContextTruth.
  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      (tfImp coqRestrictedPADirectAndEliminationRightResultTruthTemplate
        coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate))
    (rawTemplateProofCode translation
      (coqRestrictedPADirectAndEliminationRightConclusionTransportRootAt
        readyContext))) in htransport.
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectAndEliminationRightResultTruthTemplate
    coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate)
    in htransport.

  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectAndEliminationRightRecursiveChildLawTemplate)
    recursiveLawRoot) in hrecursiveLaw.
  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectAndEliminationRightDynamicTruthLawTemplate)
    dynamicLawRoot) in hdynamicLaw.
  rewrite rawTemplateFormula_andEliminationRightRecursiveChildLaw_view
    in hrecursiveLaw.
  rewrite rawTemplateFormula_andEliminationRightDynamicTruthLaw_view
    in hdynamicLaw.

  set (childEndpointCode := rawTemplateFormula translation
    coqRestrictedPADirectAndEliminationRightChildEndpointTemplate).
  set (witnessContextTruthCode := rawTemplateFormula translation
    coqRestrictedPADirectAssumptionWitnessContextTruthTemplate).
  set (formulaTruthCode := rawTemplateFormula translation
    coqRestrictedPADirectAndEliminationRightFormulaTruthTemplate).
  set (formulaCodeRelation := rawTemplateFormula translation
    coqRestrictedPADirectAndEliminationRightFormulaCodeTemplate).
  set (resultTruthCode := rawTemplateFormula translation
    coqRestrictedPADirectAndEliminationRightResultTruthTemplate).
  set (outerConclusionTruthCode := rawTemplateFormula translation
    coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate).

  set (recursiveAfterEndpointRoot := rawProofImpERoot M readyContextCode
    childEndpointCode
    (rawFormulaImpCode M witnessContextTruthCode formulaTruthCode)
    recursiveLawRoot
    (rawTemplateProofCode translation
      (coqRestrictedPADirectAndEliminationRightChildEndpointRootAt
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
        (coqRestrictedPADirectAndEliminationRightChildEndpointRootAt
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
      (coqRestrictedPADirectAndEliminationRightFormulaCodeRootAt
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
        (coqRestrictedPADirectAndEliminationRightFormulaCodeRootAt
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

  exists (rawProofImpERoot M readyContextCode resultTruthCode
    outerConclusionTruthCode
    (rawTemplateProofCode translation
      (coqRestrictedPADirectAndEliminationRightConclusionTransportRootAt
        readyContext))
    resultTruthRoot).
  apply (raw_codedPALocalProofOf_impE M hPA readyContextCode
    resultTruthCode outerConclusionTruthCode
    (rawTemplateProofCode translation
      (coqRestrictedPADirectAndEliminationRightConclusionTransportRootAt
        readyContext))
    resultTruthRoot).
  - exact htransport.
  - exact hresultTruth.
Qed.

(** ------------------------------------------------------------------
    Exact public slot of the seventeen-case strong-step family. *)

Theorem raw_coqRestrictedPADirectStrongStepAndEliminationRightCaseRoot :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectAndEliminationRightRecursiveChildLawRoot
    M hPA inputs tail ->
  RawCoqRestrictedPADirectAndEliminationRightDynamicTruthLawRoot
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
            rawCoqRuleAndEliminationRight
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
    coqRestrictedPADirectStrongStepAndEliminationRightDeepEndpointContext
      tail).
  set (caseContext :=
    coqRestrictedPADirectStrongStepAndEliminationRightCaseContext tail).
  set (admissibleContext :=
    coqRestrictedPADirectStrongStepAndEliminationRightAdmissibleContext tail).
  set (readyContext :=
    coqRestrictedPADirectStrongStepAndEliminationRightReadyContext tail).
  destruct
    (raw_codedPALocalProofOf_coqRestrictedPADirectAndEliminationRightConclusion
      M hPA inputs tail hrecursiveLaw hdynamicLaw) as
    [conclusionRoot hconclusion].

  set (baseContextCode := rawTemplateContextCode translation baseContext).
  set (caseContextCode := rawTemplateContextCode translation caseContext).
  set (admissibleContextCode :=
    rawTemplateContextCode translation admissibleContext).
  set (readyContextCode := rawTemplateContextCode translation readyContext).
  set (caseCode := rawTemplateFormula translation
    coqRestrictedPADirectAndEliminationRightCaseTemplate).
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
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndEliminationRightCase.
