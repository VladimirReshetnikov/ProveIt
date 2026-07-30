(**
  The genuine left-conjunction-elimination constructor case for the direct
  derivation-soundness strong step.

  At the eight-witness endpoint depth this branch displays

    outerConclusion = left,
    displayedConjunction = And(left, right),
    endpoint(child, witnessContext, displayedConjunction).

  The proof below projects those three literal fields.  It transports the
  outer context-truth assumption to [witnessContext] using the endpoint
  witness equality, invokes a sharply stated recursive-child law to obtain
  truth of [displayedConjunction], invokes only the left-conjunction Tarski
  law to obtain truth of [left], and finally transports that truth backwards
  along [outerConclusion = left] with an explicit equality-elimination proof.

  Thus only two mathematical seams remain:

  - recursive-child soundness at the displayed child endpoint;
  - the dynamic truth law eliminating the left component of a displayed
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
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndEliminationLeftCase.

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

Definition coqRestrictedPADirectAndEliminationLeftCodeEqualityTemplate
    : TemplateFormula :=
  embedPAFormula
    (pEq (liftTerm 8 (tVar 4))
      (proofAndE1CodeTerm (tVar 7) (tVar 6) (tVar 5) (tVar 2))).

Definition coqRestrictedPADirectAndEliminationLeftConclusionEqualityTemplate
    : TemplateFormula :=
  tfEq coqRestrictedPADirectAssumptionOuterConclusionTerm
    coqRestrictedPADirectAssumptionWitnessFormulaTerm.

Definition coqRestrictedPADirectAndEliminationLeftFormulaCodeTemplate
    : TemplateFormula :=
  embedPAFormula
    (formulaAndCodeTermAt (tVar 4) (tVar 6) (tVar 5)).

Definition coqRestrictedPADirectAndEliminationLeftChildEndpointTemplate
    : TemplateFormula :=
  embedPAFormula
    (proofEndpointTermAt (tVar 2) (tVar 7) (tVar 4)).

Definition coqRestrictedPADirectAndEliminationLeftTerminalTruthTemplate
    : TemplateFormula :=
  embedPAFormula (pEq tZero tZero).

Definition coqRestrictedPADirectAndEliminationLeftChildSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectAndEliminationLeftChildEndpointTemplate
    coqRestrictedPADirectAndEliminationLeftTerminalTruthTemplate.

Definition coqRestrictedPADirectAndEliminationLeftFormulaSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectAndEliminationLeftFormulaCodeTemplate
    coqRestrictedPADirectAndEliminationLeftChildSuffixTemplate.

Definition coqRestrictedPADirectAndEliminationLeftConclusionSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectAndEliminationLeftConclusionEqualityTemplate
    coqRestrictedPADirectAndEliminationLeftFormulaSuffixTemplate.

Definition coqRestrictedPADirectAndEliminationLeftCaseTemplate
    : TemplateFormula :=
  rawCoqRestrictedPAProofRuleCaseTemplate rawCoqRuleAndEliminationLeft
    (liftTerm 8 (tVar 4)) (tVar 7) (liftTerm 8 (tVar 2))
    (tVar 6) (tVar 5) (tVar 4) (tVar 3)
    (tVar 2) (tVar 1) (tVar 0).

Lemma coqRestrictedPADirectAndEliminationLeft_case_shape :
  coqRestrictedPADirectAndEliminationLeftCaseTemplate =
  tfAnd coqRestrictedPADirectAndEliminationLeftCodeEqualityTemplate
    coqRestrictedPADirectAndEliminationLeftConclusionSuffixTemplate.
Proof. reflexivity. Qed.

(** ------------------------------------------------------------------
    Truth leaves and the two exact residual laws. *)

Definition coqRestrictedPADirectAndEliminationLeftFormulaTruthTemplate
    : TemplateFormula :=
  tfOpaque coqRestrictedPAConclusionTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     ttVar 4; ttVar 9; ttVar 8].

Definition coqRestrictedPADirectAndEliminationLeftResultTruthTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAssumptionWitnessFormulaTruthTemplate.

Lemma coqRestrictedPADirectAndEliminationLeft_result_truth_shape :
  coqRestrictedPADirectAndEliminationLeftResultTruthTemplate =
  tfOpaque coqRestrictedPAConclusionTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     ttVar 6; ttVar 9; ttVar 8].
Proof. reflexivity. Qed.

Definition coqRestrictedPADirectAndEliminationLeftRecursiveChildLawTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectAndEliminationLeftChildEndpointTemplate
    (tfImp coqRestrictedPADirectAssumptionWitnessContextTruthTemplate
      coqRestrictedPADirectAndEliminationLeftFormulaTruthTemplate).

Definition coqRestrictedPADirectAndEliminationLeftDynamicTruthLawTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectAndEliminationLeftFormulaCodeTemplate
    (tfImp coqRestrictedPADirectAndEliminationLeftFormulaTruthTemplate
      coqRestrictedPADirectAndEliminationLeftResultTruthTemplate).

Lemma rawTemplateFormula_andEliminationLeftRecursiveChildLaw_view : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  rawTemplateFormula translation
    coqRestrictedPADirectAndEliminationLeftRecursiveChildLawTemplate =
  rawFormulaImpCode M
    (rawTemplateFormula translation
      coqRestrictedPADirectAndEliminationLeftChildEndpointTemplate)
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionWitnessContextTruthTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectAndEliminationLeftFormulaTruthTemplate)).
Proof.
  intros M translation.
  unfold coqRestrictedPADirectAndEliminationLeftRecursiveChildLawTemplate.
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectAndEliminationLeftChildEndpointTemplate
    (tfImp coqRestrictedPADirectAssumptionWitnessContextTruthTemplate
      coqRestrictedPADirectAndEliminationLeftFormulaTruthTemplate)).
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectAssumptionWitnessContextTruthTemplate
    coqRestrictedPADirectAndEliminationLeftFormulaTruthTemplate).
  reflexivity.
Qed.

Lemma rawTemplateFormula_andEliminationLeftDynamicTruthLaw_view : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  rawTemplateFormula translation
    coqRestrictedPADirectAndEliminationLeftDynamicTruthLawTemplate =
  rawFormulaImpCode M
    (rawTemplateFormula translation
      coqRestrictedPADirectAndEliminationLeftFormulaCodeTemplate)
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectAndEliminationLeftFormulaTruthTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectAndEliminationLeftResultTruthTemplate)).
Proof.
  intros M translation.
  unfold coqRestrictedPADirectAndEliminationLeftDynamicTruthLawTemplate.
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectAndEliminationLeftFormulaCodeTemplate
    (tfImp coqRestrictedPADirectAndEliminationLeftFormulaTruthTemplate
      coqRestrictedPADirectAndEliminationLeftResultTruthTemplate)).
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectAndEliminationLeftFormulaTruthTemplate
    coqRestrictedPADirectAndEliminationLeftResultTruthTemplate).
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    Exact shell contexts and residual root interfaces. *)

Definition
    coqRestrictedPADirectStrongStepAndEliminationLeftDeepEndpointContext
    (tail : TemplateContext) : TemplateContext :=
  rawCoqRestrictedPADirectEndpointWitnessBodyTemplate ::
    rawCoqRestrictedPADirectEndpointDeepTail
      (rawCoqRestrictedPADirectStrongStepEndpointTail tail).

Definition coqRestrictedPADirectStrongStepAndEliminationLeftCaseContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectAndEliminationLeftCaseTemplate ::
    coqRestrictedPADirectStrongStepAndEliminationLeftDeepEndpointContext
      tail.

Definition
    coqRestrictedPADirectStrongStepAndEliminationLeftAdmissibleContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectAssumptionDeepAdmissibleTemplate ::
    coqRestrictedPADirectStrongStepAndEliminationLeftCaseContext tail.

Definition coqRestrictedPADirectStrongStepAndEliminationLeftReadyContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectAssumptionOuterContextTruthTemplate ::
    coqRestrictedPADirectStrongStepAndEliminationLeftAdmissibleContext tail.

Arguments
  coqRestrictedPADirectStrongStepAndEliminationLeftDeepEndpointContext
  tail : clear implicits.
Arguments coqRestrictedPADirectStrongStepAndEliminationLeftCaseContext
  tail : clear implicits.
Arguments
  coqRestrictedPADirectStrongStepAndEliminationLeftAdmissibleContext
  tail : clear implicits.
Arguments coqRestrictedPADirectStrongStepAndEliminationLeftReadyContext
  tail : clear implicits.

Definition RawCoqRestrictedPADirectAndEliminationLeftRecursiveChildLawRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectStrongStepAndEliminationLeftReadyContext tail))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectAndEliminationLeftRecursiveChildLawTemplate)
      root.

Definition RawCoqRestrictedPADirectAndEliminationLeftDynamicTruthLawRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectStrongStepAndEliminationLeftReadyContext tail))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectAndEliminationLeftDynamicTruthLawTemplate)
      root.

Arguments RawCoqRestrictedPADirectAndEliminationLeftRecursiveChildLawRoot
  M hPA inputs tail : clear implicits.
Arguments RawCoqRestrictedPADirectAndEliminationLeftDynamicTruthLawRoot
  M hPA inputs tail : clear implicits.

(** ------------------------------------------------------------------
    Parameterized finite branch projections. *)

Definition coqRestrictedPADirectAndEliminationLeftCaseRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAss context coqRestrictedPADirectAndEliminationLeftCaseTemplate.

Definition coqRestrictedPADirectAndEliminationLeftConclusionSuffixRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE2 context
    coqRestrictedPADirectAndEliminationLeftCodeEqualityTemplate
    coqRestrictedPADirectAndEliminationLeftConclusionSuffixTemplate
    (coqRestrictedPADirectAndEliminationLeftCaseRootAt context).

Definition coqRestrictedPADirectAndEliminationLeftConclusionEqualityRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectAndEliminationLeftConclusionEqualityTemplate
    coqRestrictedPADirectAndEliminationLeftFormulaSuffixTemplate
    (coqRestrictedPADirectAndEliminationLeftConclusionSuffixRootAt context).

Definition coqRestrictedPADirectAndEliminationLeftFormulaSuffixRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE2 context
    coqRestrictedPADirectAndEliminationLeftConclusionEqualityTemplate
    coqRestrictedPADirectAndEliminationLeftFormulaSuffixTemplate
    (coqRestrictedPADirectAndEliminationLeftConclusionSuffixRootAt context).

Definition coqRestrictedPADirectAndEliminationLeftFormulaCodeRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectAndEliminationLeftFormulaCodeTemplate
    coqRestrictedPADirectAndEliminationLeftChildSuffixTemplate
    (coqRestrictedPADirectAndEliminationLeftFormulaSuffixRootAt context).

Definition coqRestrictedPADirectAndEliminationLeftChildSuffixRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE2 context
    coqRestrictedPADirectAndEliminationLeftFormulaCodeTemplate
    coqRestrictedPADirectAndEliminationLeftChildSuffixTemplate
    (coqRestrictedPADirectAndEliminationLeftFormulaSuffixRootAt context).

Definition coqRestrictedPADirectAndEliminationLeftChildEndpointRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectAndEliminationLeftChildEndpointTemplate
    coqRestrictedPADirectAndEliminationLeftTerminalTruthTemplate
    (coqRestrictedPADirectAndEliminationLeftChildSuffixRootAt context).

Lemma coqRestrictedPADirectAndEliminationLeftCaseRootAt_valid :
  forall context,
  In coqRestrictedPADirectAndEliminationLeftCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectAndEliminationLeftCaseTemplate
    (coqRestrictedPADirectAndEliminationLeftCaseRootAt context).
Proof.
  intros context hin. apply templateRawDerives_assumption. exact hin.
Qed.

Lemma coqRestrictedPADirectAndEliminationLeftConclusionSuffixRootAt_valid :
  forall context,
  In coqRestrictedPADirectAndEliminationLeftCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectAndEliminationLeftConclusionSuffixTemplate
    (coqRestrictedPADirectAndEliminationLeftConclusionSuffixRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectAndEliminationLeftConclusionSuffixRootAt.
  apply templateAndRightFrom_derives.
  rewrite <- coqRestrictedPADirectAndEliminationLeft_case_shape.
  apply coqRestrictedPADirectAndEliminationLeftCaseRootAt_valid. exact hin.
Qed.

Lemma coqRestrictedPADirectAndEliminationLeftConclusionEqualityRootAt_valid :
  forall context,
  In coqRestrictedPADirectAndEliminationLeftCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectAndEliminationLeftConclusionEqualityTemplate
    (coqRestrictedPADirectAndEliminationLeftConclusionEqualityRootAt
      context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectAndEliminationLeftConclusionEqualityRootAt.
  apply templateAndLeftFrom_derives.
  apply coqRestrictedPADirectAndEliminationLeftConclusionSuffixRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectAndEliminationLeftFormulaSuffixRootAt_valid :
  forall context,
  In coqRestrictedPADirectAndEliminationLeftCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectAndEliminationLeftFormulaSuffixTemplate
    (coqRestrictedPADirectAndEliminationLeftFormulaSuffixRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectAndEliminationLeftFormulaSuffixRootAt.
  apply templateAndRightFrom_derives.
  apply coqRestrictedPADirectAndEliminationLeftConclusionSuffixRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectAndEliminationLeftFormulaCodeRootAt_valid :
  forall context,
  In coqRestrictedPADirectAndEliminationLeftCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectAndEliminationLeftFormulaCodeTemplate
    (coqRestrictedPADirectAndEliminationLeftFormulaCodeRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectAndEliminationLeftFormulaCodeRootAt.
  apply templateAndLeftFrom_derives.
  apply coqRestrictedPADirectAndEliminationLeftFormulaSuffixRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectAndEliminationLeftChildSuffixRootAt_valid :
  forall context,
  In coqRestrictedPADirectAndEliminationLeftCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectAndEliminationLeftChildSuffixTemplate
    (coqRestrictedPADirectAndEliminationLeftChildSuffixRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectAndEliminationLeftChildSuffixRootAt.
  apply templateAndRightFrom_derives.
  apply coqRestrictedPADirectAndEliminationLeftFormulaSuffixRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectAndEliminationLeftChildEndpointRootAt_valid :
  forall context,
  In coqRestrictedPADirectAndEliminationLeftCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectAndEliminationLeftChildEndpointTemplate
    (coqRestrictedPADirectAndEliminationLeftChildEndpointRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectAndEliminationLeftChildEndpointRootAt.
  apply templateAndLeftFrom_derives.
  apply coqRestrictedPADirectAndEliminationLeftChildSuffixRootAt_valid.
  exact hin.
Qed.

(** ------------------------------------------------------------------
    A fully compiled truth transport along [outerConclusion = left]. *)

Definition coqRestrictedPADirectAndEliminationLeftTransportChildContext
    (context : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectAndEliminationLeftResultTruthTemplate :: context.

Definition coqRestrictedPADirectAndEliminationLeftConclusionSymmetryRootAt
    (context : TemplateContext) : TemplateRawProof :=
  coqRestrictedPADirectEqSymmetryRoot context
    coqRestrictedPADirectAssumptionOuterConclusionTerm
    coqRestrictedPADirectAssumptionWitnessFormulaTerm
    (coqRestrictedPADirectAndEliminationLeftConclusionEqualityRootAt
      context).

Definition coqRestrictedPADirectAndEliminationLeftResultTruthRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAss context coqRestrictedPADirectAndEliminationLeftResultTruthTemplate.

Definition coqRestrictedPADirectAndEliminationLeftOuterTruthChildRootAt
    (context : TemplateContext) : TemplateRawProof :=
  let childContext :=
    coqRestrictedPADirectAndEliminationLeftTransportChildContext context in
  trpEqElim childContext
    coqRestrictedPADirectAssumptionWitnessFormulaTerm
    coqRestrictedPADirectAssumptionOuterConclusionTerm
    coqRestrictedPADirectAssumptionConclusionTruthMotive
    (coqRestrictedPADirectAndEliminationLeftConclusionSymmetryRootAt
      childContext)
    (coqRestrictedPADirectAndEliminationLeftResultTruthRootAt childContext).

Definition coqRestrictedPADirectAndEliminationLeftConclusionTransportRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpImpI context
    coqRestrictedPADirectAndEliminationLeftResultTruthTemplate
    coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate
    (coqRestrictedPADirectAndEliminationLeftOuterTruthChildRootAt context).

Lemma coqRestrictedPADirectAndEliminationLeftConclusionSymmetryRootAt_valid :
  forall context,
  In coqRestrictedPADirectAndEliminationLeftCaseTemplate context ->
  TemplateRawDerives context
    (tfEq coqRestrictedPADirectAssumptionWitnessFormulaTerm
      coqRestrictedPADirectAssumptionOuterConclusionTerm)
    (coqRestrictedPADirectAndEliminationLeftConclusionSymmetryRootAt
      context).
Proof.
  intros context hin.
  apply coqRestrictedPADirectEqSymmetryRoot_valid.
  apply coqRestrictedPADirectAndEliminationLeftConclusionEqualityRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectAndEliminationLeftConclusionTransportRootAt_valid :
  forall context,
  In coqRestrictedPADirectAndEliminationLeftCaseTemplate context ->
  TemplateRawDerives context
    (tfImp coqRestrictedPADirectAndEliminationLeftResultTruthTemplate
      coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate)
    (coqRestrictedPADirectAndEliminationLeftConclusionTransportRootAt
      context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectAndEliminationLeftConclusionTransportRootAt,
    coqRestrictedPADirectAndEliminationLeftOuterTruthChildRootAt.
  cbn zeta.
  apply coqRestrictedPADirect_templateRawDerives_impI.
  rewrite <- coqRestrictedPADirectAssumption_conclusion_motive_outer.
  apply coqRestrictedPADirect_templateRawDerives_eqElim.
  - apply
      coqRestrictedPADirectAndEliminationLeftConclusionSymmetryRootAt_valid.
    right. exact hin.
  - rewrite coqRestrictedPADirectAssumption_conclusion_motive_witness.
    apply templateRawDerives_assumption. left. reflexivity.
Qed.

(** ------------------------------------------------------------------
    Compile the two residual laws and all finite plumbing. *)

Theorem
    raw_codedPALocalProofOf_coqRestrictedPADirectAndEliminationLeftConclusion
    : forall (M : RawPAModel) (hPA : RawPASatisfies M)
      (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectAndEliminationLeftRecursiveChildLawRoot
    M hPA inputs tail ->
  RawCoqRestrictedPADirectAndEliminationLeftDynamicTruthLawRoot
    M hPA inputs tail ->
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectStrongStepAndEliminationLeftReadyContext tail))
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
    coqRestrictedPADirectStrongStepAndEliminationLeftReadyContext tail).
  set (readyContextCode :=
    rawTemplateContextCode translation readyContext).

  assert (hcase :
    In coqRestrictedPADirectAndEliminationLeftCaseTemplate readyContext).
  {
    unfold readyContext,
      coqRestrictedPADirectStrongStepAndEliminationLeftReadyContext,
      coqRestrictedPADirectStrongStepAndEliminationLeftAdmissibleContext,
      coqRestrictedPADirectStrongStepAndEliminationLeftCaseContext.
    right. right. left. reflexivity.
  }
  assert (hendpointBody :
    In rawCoqRestrictedPADirectEndpointWitnessBodyTemplate readyContext).
  {
    unfold readyContext,
      coqRestrictedPADirectStrongStepAndEliminationLeftReadyContext,
      coqRestrictedPADirectStrongStepAndEliminationLeftAdmissibleContext,
      coqRestrictedPADirectStrongStepAndEliminationLeftCaseContext,
      coqRestrictedPADirectStrongStepAndEliminationLeftDeepEndpointContext.
    do 3 right. left. reflexivity.
  }
  assert (houterContextTruth :
    In coqRestrictedPADirectAssumptionOuterContextTruthTemplate
      readyContext).
  {
    unfold readyContext,
      coqRestrictedPADirectStrongStepAndEliminationLeftReadyContext.
    left. reflexivity.
  }

  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectAndEliminationLeftFormulaCodeRootAt readyContext)
    (proj1
      (coqRestrictedPADirectAndEliminationLeftFormulaCodeRootAt_valid
        readyContext hcase))) as hformulaCode.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectAndEliminationLeftChildEndpointRootAt readyContext)
    (proj1
      (coqRestrictedPADirectAndEliminationLeftChildEndpointRootAt_valid
        readyContext hcase))) as hchildEndpoint.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt readyContext)
    (proj1
      (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt_valid
        readyContext hendpointBody houterContextTruth)))
    as hwitnessContextTruth.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectAndEliminationLeftConclusionTransportRootAt
      readyContext)
    (proj1
      (coqRestrictedPADirectAndEliminationLeftConclusionTransportRootAt_valid
        readyContext hcase))) as htransport.

  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectAndEliminationLeftFormulaCodeTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectAndEliminationLeftFormulaCodeRootAt
        readyContext))) in hformulaCode.
  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectAndEliminationLeftChildEndpointTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectAndEliminationLeftChildEndpointRootAt
        readyContext))) in hchildEndpoint.
  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectAssumptionWitnessContextTruthTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt
        readyContext))) in hwitnessContextTruth.
  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      (tfImp coqRestrictedPADirectAndEliminationLeftResultTruthTemplate
        coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate))
    (rawTemplateProofCode translation
      (coqRestrictedPADirectAndEliminationLeftConclusionTransportRootAt
        readyContext))) in htransport.
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectAndEliminationLeftResultTruthTemplate
    coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate)
    in htransport.

  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectAndEliminationLeftRecursiveChildLawTemplate)
    recursiveLawRoot) in hrecursiveLaw.
  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectAndEliminationLeftDynamicTruthLawTemplate)
    dynamicLawRoot) in hdynamicLaw.
  rewrite rawTemplateFormula_andEliminationLeftRecursiveChildLaw_view
    in hrecursiveLaw.
  rewrite rawTemplateFormula_andEliminationLeftDynamicTruthLaw_view
    in hdynamicLaw.

  set (childEndpointCode := rawTemplateFormula translation
    coqRestrictedPADirectAndEliminationLeftChildEndpointTemplate).
  set (witnessContextTruthCode := rawTemplateFormula translation
    coqRestrictedPADirectAssumptionWitnessContextTruthTemplate).
  set (formulaTruthCode := rawTemplateFormula translation
    coqRestrictedPADirectAndEliminationLeftFormulaTruthTemplate).
  set (formulaCodeRelation := rawTemplateFormula translation
    coqRestrictedPADirectAndEliminationLeftFormulaCodeTemplate).
  set (resultTruthCode := rawTemplateFormula translation
    coqRestrictedPADirectAndEliminationLeftResultTruthTemplate).
  set (outerConclusionTruthCode := rawTemplateFormula translation
    coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate).

  set (recursiveAfterEndpointRoot := rawProofImpERoot M readyContextCode
    childEndpointCode
    (rawFormulaImpCode M witnessContextTruthCode formulaTruthCode)
    recursiveLawRoot
    (rawTemplateProofCode translation
      (coqRestrictedPADirectAndEliminationLeftChildEndpointRootAt
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
        (coqRestrictedPADirectAndEliminationLeftChildEndpointRootAt
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
      (coqRestrictedPADirectAndEliminationLeftFormulaCodeRootAt
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
        (coqRestrictedPADirectAndEliminationLeftFormulaCodeRootAt
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
      (coqRestrictedPADirectAndEliminationLeftConclusionTransportRootAt
        readyContext))
    resultTruthRoot).
  apply (raw_codedPALocalProofOf_impE M hPA readyContextCode
    resultTruthCode outerConclusionTruthCode
    (rawTemplateProofCode translation
      (coqRestrictedPADirectAndEliminationLeftConclusionTransportRootAt
        readyContext))
    resultTruthRoot).
  - exact htransport.
  - exact hresultTruth.
Qed.

(** ------------------------------------------------------------------
    Exact public slot of the seventeen-case strong-step family. *)

Theorem raw_coqRestrictedPADirectStrongStepAndEliminationLeftCaseRoot :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectAndEliminationLeftRecursiveChildLawRoot
    M hPA inputs tail ->
  RawCoqRestrictedPADirectAndEliminationLeftDynamicTruthLawRoot
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
            rawCoqRuleAndEliminationLeft
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
    coqRestrictedPADirectStrongStepAndEliminationLeftDeepEndpointContext
      tail).
  set (caseContext :=
    coqRestrictedPADirectStrongStepAndEliminationLeftCaseContext tail).
  set (admissibleContext :=
    coqRestrictedPADirectStrongStepAndEliminationLeftAdmissibleContext tail).
  set (readyContext :=
    coqRestrictedPADirectStrongStepAndEliminationLeftReadyContext tail).
  destruct
    (raw_codedPALocalProofOf_coqRestrictedPADirectAndEliminationLeftConclusion
      M hPA inputs tail hrecursiveLaw hdynamicLaw) as
    [conclusionRoot hconclusion].

  set (baseContextCode := rawTemplateContextCode translation baseContext).
  set (caseContextCode := rawTemplateContextCode translation caseContext).
  set (admissibleContextCode :=
    rawTemplateContextCode translation admissibleContext).
  set (readyContextCode := rawTemplateContextCode translation readyContext).
  set (caseCode := rawTemplateFormula translation
    coqRestrictedPADirectAndEliminationLeftCaseTemplate).
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
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndEliminationLeftCase.
