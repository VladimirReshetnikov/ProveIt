(**
  The genuine universal-elimination constructor case for the direct
  derivation-soundness strong step.

  At the eight-witness endpoint depth this branch displays

    substitution(replacement, body, outerConclusion),
    universalFormula = All(body),
    endpoint(child, witnessContext, universalFormula).

  The proof below projects every literal constructor field.  It transports
  outer context truth to [witnessContext] using the endpoint witness
  equality, invokes recursive-child soundness to obtain truth of the
  displayed universal formula, and applies only the dynamic Tarski law which
  opens that universal formula at the displayed replacement term.

  The substitution graph already names [outerConclusion] as its output.
  Consequently there is no independent formula-code equality along which a
  separate equality elimination could honestly transport conclusion truth:
  that final opening/conclusion transport is precisely the second residual
  law below.

  No branch-result root, outer-conclusion proof, strong-step proof, or
  dynamic conclusion premise is assumed.  Constructor projections, endpoint
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
  RawCodedFormulaOperations
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
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectUniversalEliminationCase.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
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

Definition coqRestrictedPADirectUniversalEliminationCodeEqualityTemplate
    : TemplateFormula :=
  embedPAFormula
    (pEq (liftTerm 8 (tVar 4))
      (proofAllECodeTerm (tVar 7) (tVar 6) (tVar 3) (tVar 2))).

Definition coqRestrictedPADirectUniversalEliminationSubstitutionTemplate
    : TemplateFormula :=
  embedPAFormula
    (codedFormulaSingleSubstitutionTermAt
      (tVar 3) (tVar 6) (liftTerm 8 (tVar 2))).

Definition coqRestrictedPADirectUniversalEliminationFormulaCodeTemplate
    : TemplateFormula :=
  embedPAFormula
    (formulaAllCodeTermAt (tVar 5) (tVar 6)).

Definition coqRestrictedPADirectUniversalEliminationChildEndpointTemplate
    : TemplateFormula :=
  embedPAFormula
    (proofEndpointTermAt (tVar 2) (tVar 7) (tVar 5)).

Definition coqRestrictedPADirectUniversalEliminationTerminalTruthTemplate
    : TemplateFormula :=
  embedPAFormula (pEq tZero tZero).

Definition coqRestrictedPADirectUniversalEliminationChildSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectUniversalEliminationChildEndpointTemplate
    coqRestrictedPADirectUniversalEliminationTerminalTruthTemplate.

Definition coqRestrictedPADirectUniversalEliminationFormulaSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectUniversalEliminationFormulaCodeTemplate
    coqRestrictedPADirectUniversalEliminationChildSuffixTemplate.

Definition coqRestrictedPADirectUniversalEliminationSubstitutionSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectUniversalEliminationSubstitutionTemplate
    coqRestrictedPADirectUniversalEliminationFormulaSuffixTemplate.

Definition coqRestrictedPADirectUniversalEliminationCaseTemplate
    : TemplateFormula :=
  rawCoqRestrictedPAProofRuleCaseTemplate rawCoqRuleAllElimination
    (liftTerm 8 (tVar 4)) (tVar 7) (liftTerm 8 (tVar 2))
    (tVar 6) (tVar 5) (tVar 4) (tVar 3)
    (tVar 2) (tVar 1) (tVar 0).

Lemma coqRestrictedPADirectUniversalElimination_case_shape :
  coqRestrictedPADirectUniversalEliminationCaseTemplate =
  tfAnd coqRestrictedPADirectUniversalEliminationCodeEqualityTemplate
    coqRestrictedPADirectUniversalEliminationSubstitutionSuffixTemplate.
Proof. reflexivity. Qed.

(** ------------------------------------------------------------------
    Truth leaves and the two exact residual laws. *)

(** The child conclusion is the universal-formula witness [b] in slot five.
    Slot six is its open body [a], so the generic assumption-case formula
    truth leaf cannot be reused here. *)
Definition coqRestrictedPADirectUniversalEliminationFormulaTerm
    : TemplateTerm := ttVar 5.

Definition coqRestrictedPADirectUniversalEliminationFormulaTruthTemplate
    : TemplateFormula :=
  tfOpaque coqRestrictedPAConclusionTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     coqRestrictedPADirectUniversalEliminationFormulaTerm;
     ttVar 9; ttVar 8].

Lemma coqRestrictedPADirectUniversalElimination_formula_truth_shape :
  coqRestrictedPADirectUniversalEliminationFormulaTruthTemplate =
  tfOpaque coqRestrictedPAConclusionTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     ttVar 5; ttVar 9; ttVar 8].
Proof. reflexivity. Qed.

Definition coqRestrictedPADirectUniversalEliminationResultTruthTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate.

Lemma coqRestrictedPADirectUniversalElimination_result_truth_shape :
  coqRestrictedPADirectUniversalEliminationResultTruthTemplate =
  tfOpaque coqRestrictedPAConclusionTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     embedPATerm (liftTerm 8 (tVar 2)); ttVar 9; ttVar 8].
Proof.
  unfold coqRestrictedPADirectUniversalEliminationResultTruthTemplate.
  rewrite coqRestrictedPADirectAssumption_outer_conclusion_truth_shape.
  reflexivity.
Qed.

(** The substitution field is parameterized directly by the lifted outer
    conclusion term.  Thus, after the dynamic opening law has produced
    [ResultTruth], the final handoff to the shell's conclusion-truth formula
    is a definitional transport.  We nevertheless compile that transport as
    an explicit implication so the conclusion boundary remains auditable. *)
Definition coqRestrictedPADirectUniversalEliminationTransportChildContext
    (context : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectUniversalEliminationResultTruthTemplate :: context.

Definition coqRestrictedPADirectUniversalEliminationResultTruthRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAss context coqRestrictedPADirectUniversalEliminationResultTruthTemplate.

Definition coqRestrictedPADirectUniversalEliminationConclusionTransportRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpImpI context
    coqRestrictedPADirectUniversalEliminationResultTruthTemplate
    coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate
    (coqRestrictedPADirectUniversalEliminationResultTruthRootAt
      (coqRestrictedPADirectUniversalEliminationTransportChildContext
        context)).

Lemma
    coqRestrictedPADirectUniversalEliminationConclusionTransportRootAt_valid :
  forall context,
  TemplateRawDerives context
    (tfImp coqRestrictedPADirectUniversalEliminationResultTruthTemplate
      coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate)
    (coqRestrictedPADirectUniversalEliminationConclusionTransportRootAt
      context).
Proof.
  intros context.
  unfold
    coqRestrictedPADirectUniversalEliminationConclusionTransportRootAt.
  apply coqRestrictedPADirect_templateRawDerives_impI.
  apply templateRawDerives_assumption.
  left. reflexivity.
Qed.

Definition coqRestrictedPADirectUniversalEliminationRecursiveChildLawTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectUniversalEliminationChildEndpointTemplate
    (tfImp coqRestrictedPADirectAssumptionWitnessContextTruthTemplate
      coqRestrictedPADirectUniversalEliminationFormulaTruthTemplate).

Definition coqRestrictedPADirectUniversalEliminationDynamicTruthLawTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectUniversalEliminationSubstitutionTemplate
    (tfImp coqRestrictedPADirectUniversalEliminationFormulaCodeTemplate
      (tfImp coqRestrictedPADirectUniversalEliminationFormulaTruthTemplate
        coqRestrictedPADirectUniversalEliminationResultTruthTemplate)).

Lemma rawTemplateFormula_universalEliminationRecursiveChildLaw_view : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  rawTemplateFormula translation
    coqRestrictedPADirectUniversalEliminationRecursiveChildLawTemplate =
  rawFormulaImpCode M
    (rawTemplateFormula translation
      coqRestrictedPADirectUniversalEliminationChildEndpointTemplate)
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionWitnessContextTruthTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectUniversalEliminationFormulaTruthTemplate)).
Proof.
  intros M translation.
  unfold coqRestrictedPADirectUniversalEliminationRecursiveChildLawTemplate.
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectUniversalEliminationChildEndpointTemplate
    (tfImp coqRestrictedPADirectAssumptionWitnessContextTruthTemplate
      coqRestrictedPADirectUniversalEliminationFormulaTruthTemplate)).
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectAssumptionWitnessContextTruthTemplate
    coqRestrictedPADirectUniversalEliminationFormulaTruthTemplate).
  reflexivity.
Qed.

Lemma rawTemplateFormula_universalEliminationDynamicTruthLaw_view : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  rawTemplateFormula translation
    coqRestrictedPADirectUniversalEliminationDynamicTruthLawTemplate =
  rawFormulaImpCode M
    (rawTemplateFormula translation
      coqRestrictedPADirectUniversalEliminationSubstitutionTemplate)
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectUniversalEliminationFormulaCodeTemplate)
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          coqRestrictedPADirectUniversalEliminationFormulaTruthTemplate)
        (rawTemplateFormula translation
          coqRestrictedPADirectUniversalEliminationResultTruthTemplate))).
Proof.
  intros M translation.
  unfold coqRestrictedPADirectUniversalEliminationDynamicTruthLawTemplate.
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectUniversalEliminationSubstitutionTemplate
    (tfImp coqRestrictedPADirectUniversalEliminationFormulaCodeTemplate
      (tfImp coqRestrictedPADirectUniversalEliminationFormulaTruthTemplate
        coqRestrictedPADirectUniversalEliminationResultTruthTemplate))).
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectUniversalEliminationFormulaCodeTemplate
    (tfImp coqRestrictedPADirectUniversalEliminationFormulaTruthTemplate
      coqRestrictedPADirectUniversalEliminationResultTruthTemplate)).
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectUniversalEliminationFormulaTruthTemplate
    coqRestrictedPADirectUniversalEliminationResultTruthTemplate).
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    Exact shell contexts and residual root interfaces. *)

Definition
    coqRestrictedPADirectStrongStepUniversalEliminationDeepEndpointContext
    (tail : TemplateContext) : TemplateContext :=
  rawCoqRestrictedPADirectEndpointWitnessBodyTemplate ::
    rawCoqRestrictedPADirectEndpointDeepTail
      (rawCoqRestrictedPADirectStrongStepEndpointTail tail).

Definition coqRestrictedPADirectStrongStepUniversalEliminationCaseContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectUniversalEliminationCaseTemplate ::
    coqRestrictedPADirectStrongStepUniversalEliminationDeepEndpointContext
      tail.

Definition
    coqRestrictedPADirectStrongStepUniversalEliminationAdmissibleContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectAssumptionDeepAdmissibleTemplate ::
    coqRestrictedPADirectStrongStepUniversalEliminationCaseContext tail.

Definition coqRestrictedPADirectStrongStepUniversalEliminationReadyContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectAssumptionOuterContextTruthTemplate ::
    coqRestrictedPADirectStrongStepUniversalEliminationAdmissibleContext tail.

Arguments
  coqRestrictedPADirectStrongStepUniversalEliminationDeepEndpointContext
  tail : clear implicits.
Arguments coqRestrictedPADirectStrongStepUniversalEliminationCaseContext
  tail : clear implicits.
Arguments
  coqRestrictedPADirectStrongStepUniversalEliminationAdmissibleContext
  tail : clear implicits.
Arguments coqRestrictedPADirectStrongStepUniversalEliminationReadyContext
  tail : clear implicits.

Definition RawCoqRestrictedPADirectUniversalEliminationRecursiveChildLawRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectStrongStepUniversalEliminationReadyContext tail))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectUniversalEliminationRecursiveChildLawTemplate)
      root.

Definition RawCoqRestrictedPADirectUniversalEliminationDynamicTruthLawRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectStrongStepUniversalEliminationReadyContext tail))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectUniversalEliminationDynamicTruthLawTemplate)
      root.

Arguments RawCoqRestrictedPADirectUniversalEliminationRecursiveChildLawRoot
  M hPA inputs tail : clear implicits.
Arguments RawCoqRestrictedPADirectUniversalEliminationDynamicTruthLawRoot
  M hPA inputs tail : clear implicits.

(** ------------------------------------------------------------------
    Parameterized finite branch projections. *)

Definition coqRestrictedPADirectUniversalEliminationCaseRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAss context coqRestrictedPADirectUniversalEliminationCaseTemplate.

Definition coqRestrictedPADirectUniversalEliminationCodeEqualityRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectUniversalEliminationCodeEqualityTemplate
    coqRestrictedPADirectUniversalEliminationSubstitutionSuffixTemplate
    (coqRestrictedPADirectUniversalEliminationCaseRootAt context).

Definition coqRestrictedPADirectUniversalEliminationSubstitutionSuffixRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE2 context
    coqRestrictedPADirectUniversalEliminationCodeEqualityTemplate
    coqRestrictedPADirectUniversalEliminationSubstitutionSuffixTemplate
    (coqRestrictedPADirectUniversalEliminationCaseRootAt context).

Definition coqRestrictedPADirectUniversalEliminationSubstitutionRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectUniversalEliminationSubstitutionTemplate
    coqRestrictedPADirectUniversalEliminationFormulaSuffixTemplate
    (coqRestrictedPADirectUniversalEliminationSubstitutionSuffixRootAt
      context).

Definition coqRestrictedPADirectUniversalEliminationFormulaSuffixRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE2 context
    coqRestrictedPADirectUniversalEliminationSubstitutionTemplate
    coqRestrictedPADirectUniversalEliminationFormulaSuffixTemplate
    (coqRestrictedPADirectUniversalEliminationSubstitutionSuffixRootAt
      context).

Definition coqRestrictedPADirectUniversalEliminationFormulaCodeRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectUniversalEliminationFormulaCodeTemplate
    coqRestrictedPADirectUniversalEliminationChildSuffixTemplate
    (coqRestrictedPADirectUniversalEliminationFormulaSuffixRootAt context).

Definition coqRestrictedPADirectUniversalEliminationChildSuffixRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE2 context
    coqRestrictedPADirectUniversalEliminationFormulaCodeTemplate
    coqRestrictedPADirectUniversalEliminationChildSuffixTemplate
    (coqRestrictedPADirectUniversalEliminationFormulaSuffixRootAt context).

Definition coqRestrictedPADirectUniversalEliminationChildEndpointRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectUniversalEliminationChildEndpointTemplate
    coqRestrictedPADirectUniversalEliminationTerminalTruthTemplate
    (coqRestrictedPADirectUniversalEliminationChildSuffixRootAt context).

Definition coqRestrictedPADirectUniversalEliminationTerminalTruthRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE2 context
    coqRestrictedPADirectUniversalEliminationChildEndpointTemplate
    coqRestrictedPADirectUniversalEliminationTerminalTruthTemplate
    (coqRestrictedPADirectUniversalEliminationChildSuffixRootAt context).

Lemma coqRestrictedPADirectUniversalEliminationCaseRootAt_valid :
  forall context,
  In coqRestrictedPADirectUniversalEliminationCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectUniversalEliminationCaseTemplate
    (coqRestrictedPADirectUniversalEliminationCaseRootAt context).
Proof.
  intros context hin. apply templateRawDerives_assumption. exact hin.
Qed.

Lemma coqRestrictedPADirectUniversalEliminationCodeEqualityRootAt_valid :
  forall context,
  In coqRestrictedPADirectUniversalEliminationCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectUniversalEliminationCodeEqualityTemplate
    (coqRestrictedPADirectUniversalEliminationCodeEqualityRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectUniversalEliminationCodeEqualityRootAt.
  apply templateAndLeftFrom_derives.
  rewrite <- coqRestrictedPADirectUniversalElimination_case_shape.
  apply coqRestrictedPADirectUniversalEliminationCaseRootAt_valid.
  exact hin.
Qed.

Lemma
    coqRestrictedPADirectUniversalEliminationSubstitutionSuffixRootAt_valid :
  forall context,
  In coqRestrictedPADirectUniversalEliminationCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectUniversalEliminationSubstitutionSuffixTemplate
    (coqRestrictedPADirectUniversalEliminationSubstitutionSuffixRootAt
      context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectUniversalEliminationSubstitutionSuffixRootAt.
  apply templateAndRightFrom_derives.
  rewrite <- coqRestrictedPADirectUniversalElimination_case_shape.
  apply coqRestrictedPADirectUniversalEliminationCaseRootAt_valid. exact hin.
Qed.

Lemma coqRestrictedPADirectUniversalEliminationSubstitutionRootAt_valid :
  forall context,
  In coqRestrictedPADirectUniversalEliminationCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectUniversalEliminationSubstitutionTemplate
    (coqRestrictedPADirectUniversalEliminationSubstitutionRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectUniversalEliminationSubstitutionRootAt.
  apply templateAndLeftFrom_derives.
  apply
    coqRestrictedPADirectUniversalEliminationSubstitutionSuffixRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectUniversalEliminationFormulaSuffixRootAt_valid :
  forall context,
  In coqRestrictedPADirectUniversalEliminationCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectUniversalEliminationFormulaSuffixTemplate
    (coqRestrictedPADirectUniversalEliminationFormulaSuffixRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectUniversalEliminationFormulaSuffixRootAt.
  apply templateAndRightFrom_derives.
  apply
    coqRestrictedPADirectUniversalEliminationSubstitutionSuffixRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectUniversalEliminationFormulaCodeRootAt_valid :
  forall context,
  In coqRestrictedPADirectUniversalEliminationCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectUniversalEliminationFormulaCodeTemplate
    (coqRestrictedPADirectUniversalEliminationFormulaCodeRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectUniversalEliminationFormulaCodeRootAt.
  apply templateAndLeftFrom_derives.
  apply coqRestrictedPADirectUniversalEliminationFormulaSuffixRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectUniversalEliminationChildSuffixRootAt_valid :
  forall context,
  In coqRestrictedPADirectUniversalEliminationCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectUniversalEliminationChildSuffixTemplate
    (coqRestrictedPADirectUniversalEliminationChildSuffixRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectUniversalEliminationChildSuffixRootAt.
  apply templateAndRightFrom_derives.
  apply coqRestrictedPADirectUniversalEliminationFormulaSuffixRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectUniversalEliminationChildEndpointRootAt_valid :
  forall context,
  In coqRestrictedPADirectUniversalEliminationCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectUniversalEliminationChildEndpointTemplate
    (coqRestrictedPADirectUniversalEliminationChildEndpointRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectUniversalEliminationChildEndpointRootAt.
  apply templateAndLeftFrom_derives.
  apply coqRestrictedPADirectUniversalEliminationChildSuffixRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectUniversalEliminationTerminalTruthRootAt_valid :
  forall context,
  In coqRestrictedPADirectUniversalEliminationCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectUniversalEliminationTerminalTruthTemplate
    (coqRestrictedPADirectUniversalEliminationTerminalTruthRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectUniversalEliminationTerminalTruthRootAt.
  apply templateAndRightFrom_derives.
  apply coqRestrictedPADirectUniversalEliminationChildSuffixRootAt_valid.
  exact hin.
Qed.

(** ------------------------------------------------------------------
    Compile the two residual laws and all finite plumbing. *)

Theorem
    raw_codedPALocalProofOf_coqRestrictedPADirectUniversalEliminationConclusion
    : forall (M : RawPAModel) (hPA : RawPASatisfies M)
      (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectUniversalEliminationRecursiveChildLawRoot
    M hPA inputs tail ->
  RawCoqRestrictedPADirectUniversalEliminationDynamicTruthLawRoot
    M hPA inputs tail ->
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectStrongStepUniversalEliminationReadyContext tail))
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
    coqRestrictedPADirectStrongStepUniversalEliminationReadyContext tail).
  set (readyContextCode :=
    rawTemplateContextCode translation readyContext).

  assert (hcase :
    In coqRestrictedPADirectUniversalEliminationCaseTemplate readyContext).
  {
    unfold readyContext,
      coqRestrictedPADirectStrongStepUniversalEliminationReadyContext,
      coqRestrictedPADirectStrongStepUniversalEliminationAdmissibleContext,
      coqRestrictedPADirectStrongStepUniversalEliminationCaseContext.
    right. right. left. reflexivity.
  }
  assert (hendpointBody :
    In rawCoqRestrictedPADirectEndpointWitnessBodyTemplate readyContext).
  {
    unfold readyContext,
      coqRestrictedPADirectStrongStepUniversalEliminationReadyContext,
      coqRestrictedPADirectStrongStepUniversalEliminationAdmissibleContext,
      coqRestrictedPADirectStrongStepUniversalEliminationCaseContext,
      coqRestrictedPADirectStrongStepUniversalEliminationDeepEndpointContext.
    do 3 right. left. reflexivity.
  }
  assert (houterContextTruth :
    In coqRestrictedPADirectAssumptionOuterContextTruthTemplate
      readyContext).
  {
    unfold readyContext,
      coqRestrictedPADirectStrongStepUniversalEliminationReadyContext.
    left. reflexivity.
  }

  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectUniversalEliminationSubstitutionRootAt
      readyContext)
    (proj1
      (coqRestrictedPADirectUniversalEliminationSubstitutionRootAt_valid
        readyContext hcase))) as hsubstitution.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectUniversalEliminationFormulaCodeRootAt readyContext)
    (proj1
      (coqRestrictedPADirectUniversalEliminationFormulaCodeRootAt_valid
        readyContext hcase))) as hformulaCode.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectUniversalEliminationChildEndpointRootAt readyContext)
    (proj1
      (coqRestrictedPADirectUniversalEliminationChildEndpointRootAt_valid
        readyContext hcase))) as hchildEndpoint.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt readyContext)
    (proj1
      (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt_valid
        readyContext hendpointBody houterContextTruth)))
    as hwitnessContextTruth.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectUniversalEliminationConclusionTransportRootAt
      readyContext)
    (proj1
      (coqRestrictedPADirectUniversalEliminationConclusionTransportRootAt_valid
        readyContext))) as htransport.

  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectUniversalEliminationSubstitutionTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectUniversalEliminationSubstitutionRootAt
        readyContext))) in hsubstitution.
  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectUniversalEliminationFormulaCodeTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectUniversalEliminationFormulaCodeRootAt
        readyContext))) in hformulaCode.
  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectUniversalEliminationChildEndpointTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectUniversalEliminationChildEndpointRootAt
        readyContext))) in hchildEndpoint.
  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectAssumptionWitnessContextTruthTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt
        readyContext))) in hwitnessContextTruth.
  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      (tfImp coqRestrictedPADirectUniversalEliminationResultTruthTemplate
        coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate))
    (rawTemplateProofCode translation
      (coqRestrictedPADirectUniversalEliminationConclusionTransportRootAt
        readyContext))) in htransport.
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectUniversalEliminationResultTruthTemplate
    coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate)
    in htransport.

  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectUniversalEliminationRecursiveChildLawTemplate)
    recursiveLawRoot) in hrecursiveLaw.
  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectUniversalEliminationDynamicTruthLawTemplate)
    dynamicLawRoot) in hdynamicLaw.
  rewrite rawTemplateFormula_universalEliminationRecursiveChildLaw_view
    in hrecursiveLaw.
  rewrite rawTemplateFormula_universalEliminationDynamicTruthLaw_view
    in hdynamicLaw.

  set (childEndpointCode := rawTemplateFormula translation
    coqRestrictedPADirectUniversalEliminationChildEndpointTemplate).
  set (witnessContextTruthCode := rawTemplateFormula translation
    coqRestrictedPADirectAssumptionWitnessContextTruthTemplate).
  set (formulaTruthCode := rawTemplateFormula translation
    coqRestrictedPADirectUniversalEliminationFormulaTruthTemplate).
  set (substitutionCode := rawTemplateFormula translation
    coqRestrictedPADirectUniversalEliminationSubstitutionTemplate).
  set (formulaCodeRelation := rawTemplateFormula translation
    coqRestrictedPADirectUniversalEliminationFormulaCodeTemplate).
  set (resultTruthCode := rawTemplateFormula translation
    coqRestrictedPADirectUniversalEliminationResultTruthTemplate).
  set (outerConclusionTruthCode := rawTemplateFormula translation
    coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate).

  set (recursiveAfterEndpointRoot := rawProofImpERoot M readyContextCode
    childEndpointCode
    (rawFormulaImpCode M witnessContextTruthCode formulaTruthCode)
    recursiveLawRoot
    (rawTemplateProofCode translation
      (coqRestrictedPADirectUniversalEliminationChildEndpointRootAt
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
        (coqRestrictedPADirectUniversalEliminationChildEndpointRootAt
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

  set (dynamicAfterSubstitutionRoot := rawProofImpERoot M readyContextCode
    substitutionCode
    (rawFormulaImpCode M formulaCodeRelation
      (rawFormulaImpCode M formulaTruthCode resultTruthCode))
    dynamicLawRoot
    (rawTemplateProofCode translation
      (coqRestrictedPADirectUniversalEliminationSubstitutionRootAt
        readyContext))).
  assert (hdynamicAfterSubstitution : RawCodedPALocalProofOf M
    readyContextCode
    (rawFormulaImpCode M formulaCodeRelation
      (rawFormulaImpCode M formulaTruthCode resultTruthCode))
    dynamicAfterSubstitutionRoot).
  {
    unfold dynamicAfterSubstitutionRoot.
    apply (raw_codedPALocalProofOf_impE M hPA readyContextCode
      substitutionCode
      (rawFormulaImpCode M formulaCodeRelation
        (rawFormulaImpCode M formulaTruthCode resultTruthCode))
      dynamicLawRoot
      (rawTemplateProofCode translation
        (coqRestrictedPADirectUniversalEliminationSubstitutionRootAt
          readyContext))).
    - exact hdynamicLaw.
    - unfold substitutionCode. exact hsubstitution.
  }

  set (dynamicAfterFormulaRoot := rawProofImpERoot M readyContextCode
    formulaCodeRelation
    (rawFormulaImpCode M formulaTruthCode resultTruthCode)
    dynamicAfterSubstitutionRoot
    (rawTemplateProofCode translation
      (coqRestrictedPADirectUniversalEliminationFormulaCodeRootAt
        readyContext))).
  assert (hdynamicAfterFormula : RawCodedPALocalProofOf M readyContextCode
    (rawFormulaImpCode M formulaTruthCode resultTruthCode)
    dynamicAfterFormulaRoot).
  {
    unfold dynamicAfterFormulaRoot.
    apply (raw_codedPALocalProofOf_impE M hPA readyContextCode
      formulaCodeRelation
      (rawFormulaImpCode M formulaTruthCode resultTruthCode)
      dynamicAfterSubstitutionRoot
      (rawTemplateProofCode translation
        (coqRestrictedPADirectUniversalEliminationFormulaCodeRootAt
          readyContext))).
    - exact hdynamicAfterSubstitution.
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
      (coqRestrictedPADirectUniversalEliminationConclusionTransportRootAt
        readyContext))
    resultTruthRoot).
  apply (raw_codedPALocalProofOf_impE M hPA readyContextCode
    resultTruthCode outerConclusionTruthCode
    (rawTemplateProofCode translation
      (coqRestrictedPADirectUniversalEliminationConclusionTransportRootAt
        readyContext))
    resultTruthRoot).
  - exact htransport.
  - exact hresultTruth.
Qed.

(** ------------------------------------------------------------------
    Exact public slot of the seventeen-case strong-step family. *)

Theorem raw_coqRestrictedPADirectStrongStepUniversalEliminationCaseRoot :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectUniversalEliminationRecursiveChildLawRoot
    M hPA inputs tail ->
  RawCoqRestrictedPADirectUniversalEliminationDynamicTruthLawRoot
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
            rawCoqRuleAllElimination
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
    coqRestrictedPADirectStrongStepUniversalEliminationDeepEndpointContext
      tail).
  set (caseContext :=
    coqRestrictedPADirectStrongStepUniversalEliminationCaseContext tail).
  set (admissibleContext :=
    coqRestrictedPADirectStrongStepUniversalEliminationAdmissibleContext tail).
  set (readyContext :=
    coqRestrictedPADirectStrongStepUniversalEliminationReadyContext tail).
  destruct
    (raw_codedPALocalProofOf_coqRestrictedPADirectUniversalEliminationConclusion
      M hPA inputs tail hrecursiveLaw hdynamicLaw) as
    [conclusionRoot hconclusion].

  set (baseContextCode := rawTemplateContextCode translation baseContext).
  set (caseContextCode := rawTemplateContextCode translation caseContext).
  set (admissibleContextCode :=
    rawTemplateContextCode translation admissibleContext).
  set (readyContextCode := rawTemplateContextCode translation readyContext).
  set (caseCode := rawTemplateFormula translation
    coqRestrictedPADirectUniversalEliminationCaseTemplate).
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
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectUniversalEliminationCase.
