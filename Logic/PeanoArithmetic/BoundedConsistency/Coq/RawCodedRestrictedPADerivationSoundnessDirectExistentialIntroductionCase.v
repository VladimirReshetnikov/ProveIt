(**
  The exact existential-introduction branch of the direct strong step.

  At the eight endpoint witnesses the constructor exposes a body formula
  [a], witness term [t], substituted child conclusion [b], and one child:

    root = ExI(witnessContext, a, t, child),
    outerConclusion = Ex(a),
    substitute(t, a) = b,
    endpoint(child, witnessContext, b).

  This module projects all four fields, transports outer context truth to
  the endpoint witness context, and applies the inherited strong prefix to
  the recursive child.  The child predicate is opened at its context,
  conclusion, assignment code, and assignment step in the literal source
  order.  The shell's case, admissibility, and context-truth implications
  are then introduced explicitly.

  Only two semantic operations remain open.  A recursive-child interface
  produces descent, restrictedness, full child rule validity, and inherited
  child admissibility.  A dynamic existential-introduction truth interface
  consumes the displayed existential code, substitution relation, and
  child truth.  Neither interface assumes the desired branch implication,
  the outer conclusion by itself, or the strong step.
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
  RawCodedProofRules
  RawCodedProofBinaryConstructors
  RawCodedProofImpIConstructor
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofPropositionalRules
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateDirectStructuralTranslation
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixInductionShell
  RawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier
  RawCodedRestrictedPADerivationSoundnessDirectStrongStepShell
  RawCodedRestrictedPADerivationSoundnessDirectAssumptionCase
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialIntroductionCase.

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
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedProofImpIConstructor.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
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
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase.

(** ------------------------------------------------------------------
    Literal constructor fields at endpoint-witness depth eight. *)

Definition coqRestrictedPADirectExistentialIntroductionWitnessContextTerm
    : TemplateTerm := ttVar 7.

Definition coqRestrictedPADirectExistentialIntroductionBodyFormulaTerm
    : TemplateTerm := ttVar 6.

Definition coqRestrictedPADirectExistentialIntroductionChildConclusionTerm
    : TemplateTerm := ttVar 5.

Definition coqRestrictedPADirectExistentialIntroductionWitnessTerm
    : TemplateTerm := ttVar 3.

Definition coqRestrictedPADirectExistentialIntroductionChildTerm
    : TemplateTerm := ttVar 2.

Definition coqRestrictedPADirectExistentialIntroductionCodeEqualityTemplate
    : TemplateFormula :=
  embedPAFormula
    (pEq (liftTerm 8 (tVar 4))
      (proofExICodeTerm (tVar 7) (tVar 6) (tVar 3) (tVar 2))).

Definition coqRestrictedPADirectExistentialIntroductionFormulaCodeTemplate
    : TemplateFormula :=
  embedPAFormula
    (formulaExCodeTermAt (liftTerm 8 (tVar 2)) (tVar 6)).

Definition coqRestrictedPADirectExistentialIntroductionSubstitutionTemplate
    : TemplateFormula :=
  embedPAFormula
    (codedFormulaSingleSubstitutionTermAt
      (tVar 3) (tVar 6) (tVar 5)).

Definition coqRestrictedPADirectExistentialIntroductionChildEndpointTemplate
    : TemplateFormula :=
  embedPAFormula
    (proofEndpointTermAt (tVar 2) (tVar 7) (tVar 5)).

Definition coqRestrictedPADirectExistentialIntroductionTerminalTruthTemplate
    : TemplateFormula := embedPAFormula (pEq tZero tZero).

Definition
    coqRestrictedPADirectExistentialIntroductionChildEndpointSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectExistentialIntroductionChildEndpointTemplate
    coqRestrictedPADirectExistentialIntroductionTerminalTruthTemplate.

Definition
    coqRestrictedPADirectExistentialIntroductionSubstitutionSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectExistentialIntroductionSubstitutionTemplate
    coqRestrictedPADirectExistentialIntroductionChildEndpointSuffixTemplate.

Definition
    coqRestrictedPADirectExistentialIntroductionFormulaCodeSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectExistentialIntroductionFormulaCodeTemplate
    coqRestrictedPADirectExistentialIntroductionSubstitutionSuffixTemplate.

Definition coqRestrictedPADirectExistentialIntroductionCaseTemplate
    : TemplateFormula :=
  rawCoqRestrictedPAProofRuleCaseTemplate rawCoqRuleExIntroduction
    (liftTerm 8 (tVar 4)) (tVar 7) (liftTerm 8 (tVar 2))
    (tVar 6) (tVar 5) (tVar 4) (tVar 3)
    (tVar 2) (tVar 1) (tVar 0).

Lemma coqRestrictedPADirectExistentialIntroduction_case_shape :
  coqRestrictedPADirectExistentialIntroductionCaseTemplate =
  tfAnd coqRestrictedPADirectExistentialIntroductionCodeEqualityTemplate
    coqRestrictedPADirectExistentialIntroductionFormulaCodeSuffixTemplate.
Proof. reflexivity. Qed.

(** ------------------------------------------------------------------
    Child-predicate components inherited from the generic strong-prefix
    application proved for conjunction introduction. *)

Definition coqRestrictedPADirectExistentialIntroductionChildBelowTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildBelowTemplate
    coqRestrictedPADirectExistentialIntroductionChildTerm.

Definition coqRestrictedPADirectExistentialIntroductionChildRestrictedTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildRestrictedTemplate
    coqRestrictedPADirectExistentialIntroductionChildTerm
    coqRestrictedPADirectExistentialIntroductionWitnessContextTerm
    coqRestrictedPADirectExistentialIntroductionChildConclusionTerm.

Definition coqRestrictedPADirectExistentialIntroductionChildRuleValidTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildEndpointTemplate
    coqRestrictedPADirectExistentialIntroductionChildTerm
    coqRestrictedPADirectExistentialIntroductionWitnessContextTerm
    coqRestrictedPADirectExistentialIntroductionChildConclusionTerm.

Definition coqRestrictedPADirectExistentialIntroductionChildAdmissibleTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildAdmissibleTemplate
    coqRestrictedPADirectExistentialIntroductionChildTerm
    coqRestrictedPADirectExistentialIntroductionWitnessContextTerm
    coqRestrictedPADirectExistentialIntroductionChildConclusionTerm.

Definition
    coqRestrictedPADirectExistentialIntroductionChildContextTruthTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildContextTruthTemplate
    coqRestrictedPADirectExistentialIntroductionChildTerm
    coqRestrictedPADirectExistentialIntroductionWitnessContextTerm
    coqRestrictedPADirectExistentialIntroductionChildConclusionTerm.

Definition coqRestrictedPADirectExistentialIntroductionChildTruthTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildTruthTemplate
    coqRestrictedPADirectExistentialIntroductionChildTerm
    coqRestrictedPADirectExistentialIntroductionWitnessContextTerm
    coqRestrictedPADirectExistentialIntroductionChildConclusionTerm.

Definition coqRestrictedPADirectExistentialIntroductionOuterContextTruthTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionOuterContextTruthTemplate.

Definition
    coqRestrictedPADirectExistentialIntroductionOuterConclusionTruthTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionOuterConclusionTruthTemplate.

Definition coqRestrictedPADirectExistentialIntroductionDeepRestrictedTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionDeepRestrictedTemplate.

Definition coqRestrictedPADirectExistentialIntroductionDeepAdmissibleTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionDeepAdmissibleTemplate.

Definition coqRestrictedPADirectExistentialIntroductionDeepStrongPrefixTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionDeepStrongPrefixTemplate.

Lemma
    coqRestrictedPADirectExistentialIntroduction_context_truth_agreement :
  coqRestrictedPADirectExistentialIntroductionChildContextTruthTemplate =
  coqRestrictedPADirectAssumptionWitnessContextTruthTemplate.
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectExistentialIntroduction_remaining_shape :
  rawCoqTemplateRenameN 8
    rawCoqRestrictedPADirectStrongStepRemainingTemplate =
  tfImp coqRestrictedPADirectExistentialIntroductionDeepAdmissibleTemplate
    (tfImp
      coqRestrictedPADirectExistentialIntroductionOuterContextTruthTemplate
      coqRestrictedPADirectExistentialIntroductionOuterConclusionTruthTemplate).
Proof. reflexivity. Qed.

(** ------------------------------------------------------------------
    Exact arbitrary-tail shell contexts and inherited assumptions. *)

Definition coqRestrictedPADirectStrongStepExistentialIntroductionBaseContext
    (tail : TemplateContext) : TemplateContext :=
  rawCoqRestrictedPADirectEndpointWitnessBodyTemplate ::
    rawCoqRestrictedPADirectEndpointDeepTail
      (rawCoqRestrictedPADirectStrongStepEndpointTail tail).

Definition coqRestrictedPADirectStrongStepExistentialIntroductionCaseContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectExistentialIntroductionCaseTemplate ::
    coqRestrictedPADirectStrongStepExistentialIntroductionBaseContext tail.

Definition
    coqRestrictedPADirectStrongStepExistentialIntroductionAdmissibleContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectExistentialIntroductionDeepAdmissibleTemplate ::
    coqRestrictedPADirectStrongStepExistentialIntroductionCaseContext tail.

Definition coqRestrictedPADirectStrongStepExistentialIntroductionReadyContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectExistentialIntroductionOuterContextTruthTemplate ::
    coqRestrictedPADirectStrongStepExistentialIntroductionAdmissibleContext
      tail.

Arguments coqRestrictedPADirectStrongStepExistentialIntroductionBaseContext
  tail : clear implicits.
Arguments coqRestrictedPADirectStrongStepExistentialIntroductionCaseContext
  tail : clear implicits.
Arguments
  coqRestrictedPADirectStrongStepExistentialIntroductionAdmissibleContext
  tail : clear implicits.
Arguments coqRestrictedPADirectStrongStepExistentialIntroductionReadyContext
  tail : clear implicits.

Lemma coqRestrictedPADirectExistentialIntroduction_ready_endpoint_in :
    forall tail,
  In rawCoqRestrictedPADirectEndpointWitnessBodyTemplate
    (coqRestrictedPADirectStrongStepExistentialIntroductionReadyContext tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectStrongStepExistentialIntroductionReadyContext,
    coqRestrictedPADirectStrongStepExistentialIntroductionAdmissibleContext,
    coqRestrictedPADirectStrongStepExistentialIntroductionCaseContext,
    coqRestrictedPADirectStrongStepExistentialIntroductionBaseContext.
  do 3 right. left. reflexivity.
Qed.

Lemma coqRestrictedPADirectExistentialIntroduction_ready_case_in : forall tail,
  In coqRestrictedPADirectExistentialIntroductionCaseTemplate
    (coqRestrictedPADirectStrongStepExistentialIntroductionReadyContext tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectStrongStepExistentialIntroductionReadyContext,
    coqRestrictedPADirectStrongStepExistentialIntroductionAdmissibleContext,
    coqRestrictedPADirectStrongStepExistentialIntroductionCaseContext.
  right. right. left. reflexivity.
Qed.

Lemma coqRestrictedPADirectExistentialIntroduction_ready_admissible_in :
    forall tail,
  In coqRestrictedPADirectExistentialIntroductionDeepAdmissibleTemplate
    (coqRestrictedPADirectStrongStepExistentialIntroductionReadyContext tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectStrongStepExistentialIntroductionReadyContext,
    coqRestrictedPADirectStrongStepExistentialIntroductionAdmissibleContext.
  right. left. reflexivity.
Qed.

Lemma coqRestrictedPADirectExistentialIntroduction_ready_context_truth_in :
    forall tail,
  In coqRestrictedPADirectExistentialIntroductionOuterContextTruthTemplate
    (coqRestrictedPADirectStrongStepExistentialIntroductionReadyContext tail).
Proof. intro tail. left. reflexivity. Qed.

Lemma coqRestrictedPADirectExistentialIntroduction_ready_restricted_in :
    forall tail,
  In coqRestrictedPADirectExistentialIntroductionDeepRestrictedTemplate
    (coqRestrictedPADirectStrongStepExistentialIntroductionReadyContext tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectStrongStepExistentialIntroductionReadyContext,
    coqRestrictedPADirectStrongStepExistentialIntroductionAdmissibleContext,
    coqRestrictedPADirectStrongStepExistentialIntroductionCaseContext,
    coqRestrictedPADirectStrongStepExistentialIntroductionBaseContext.
  do 3 right.
  rewrite <- raw_coqRestrictedPADirectEndpointDeepContext_shape.
  unfold coqRestrictedPADirectExistentialIntroductionDeepRestrictedTemplate,
    coqRestrictedPADirectAndIntroductionDeepRestrictedTemplate.
  apply raw_coqTemplateNestedExContext_inherited.
  unfold rawCoqRestrictedPADirectStrongStepEndpointTail.
  left. reflexivity.
Qed.

Lemma coqRestrictedPADirectExistentialIntroduction_ready_prefix_in :
    forall tail,
  In coqRestrictedPADirectExistentialIntroductionDeepStrongPrefixTemplate
    (coqRestrictedPADirectStrongStepExistentialIntroductionReadyContext tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectStrongStepExistentialIntroductionReadyContext,
    coqRestrictedPADirectStrongStepExistentialIntroductionAdmissibleContext,
    coqRestrictedPADirectStrongStepExistentialIntroductionCaseContext,
    coqRestrictedPADirectStrongStepExistentialIntroductionBaseContext.
  do 3 right.
  rewrite <- raw_coqRestrictedPADirectEndpointDeepContext_shape.
  unfold coqRestrictedPADirectExistentialIntroductionDeepStrongPrefixTemplate,
    coqRestrictedPADirectAndIntroductionDeepStrongPrefixTemplate.
  apply raw_coqTemplateNestedExContext_inherited.
  unfold rawCoqRestrictedPADirectStrongStepEndpointTail.
  right.
  unfold rawCoqRestrictedPADirectStrongStepFourBinderContext.
  apply coqRestrictedPADirectAndIntroduction_contextShiftN_head.
Qed.

(** ------------------------------------------------------------------
    Context-generic finite projections of every constructor field. *)

Definition coqRestrictedPADirectExistentialIntroductionCaseRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAss context coqRestrictedPADirectExistentialIntroductionCaseTemplate.

Definition coqRestrictedPADirectExistentialIntroductionCodeEqualityRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectExistentialIntroductionCodeEqualityTemplate
    coqRestrictedPADirectExistentialIntroductionFormulaCodeSuffixTemplate
    (coqRestrictedPADirectExistentialIntroductionCaseRootAt context).

Definition
    coqRestrictedPADirectExistentialIntroductionFormulaCodeSuffixRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE2 context
    coqRestrictedPADirectExistentialIntroductionCodeEqualityTemplate
    coqRestrictedPADirectExistentialIntroductionFormulaCodeSuffixTemplate
    (coqRestrictedPADirectExistentialIntroductionCaseRootAt context).

Definition coqRestrictedPADirectExistentialIntroductionFormulaCodeRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectExistentialIntroductionFormulaCodeTemplate
    coqRestrictedPADirectExistentialIntroductionSubstitutionSuffixTemplate
    (coqRestrictedPADirectExistentialIntroductionFormulaCodeSuffixRootAt
      context).

Definition
    coqRestrictedPADirectExistentialIntroductionSubstitutionSuffixRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE2 context
    coqRestrictedPADirectExistentialIntroductionFormulaCodeTemplate
    coqRestrictedPADirectExistentialIntroductionSubstitutionSuffixTemplate
    (coqRestrictedPADirectExistentialIntroductionFormulaCodeSuffixRootAt
      context).

Definition coqRestrictedPADirectExistentialIntroductionSubstitutionRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectExistentialIntroductionSubstitutionTemplate
    coqRestrictedPADirectExistentialIntroductionChildEndpointSuffixTemplate
    (coqRestrictedPADirectExistentialIntroductionSubstitutionSuffixRootAt
      context).

Definition
    coqRestrictedPADirectExistentialIntroductionChildEndpointSuffixRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE2 context
    coqRestrictedPADirectExistentialIntroductionSubstitutionTemplate
    coqRestrictedPADirectExistentialIntroductionChildEndpointSuffixTemplate
    (coqRestrictedPADirectExistentialIntroductionSubstitutionSuffixRootAt
      context).

Definition coqRestrictedPADirectExistentialIntroductionChildEndpointRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectExistentialIntroductionChildEndpointTemplate
    coqRestrictedPADirectExistentialIntroductionTerminalTruthTemplate
    (coqRestrictedPADirectExistentialIntroductionChildEndpointSuffixRootAt
      context).

Lemma coqRestrictedPADirectExistentialIntroductionCaseRootAt_valid : forall
    context,
  In coqRestrictedPADirectExistentialIntroductionCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectExistentialIntroductionCaseTemplate
    (coqRestrictedPADirectExistentialIntroductionCaseRootAt context).
Proof. intros context hin. apply templateRawDerives_assumption. exact hin. Qed.

Lemma coqRestrictedPADirectExistentialIntroductionCodeEqualityRootAt_valid :
    forall context,
  In coqRestrictedPADirectExistentialIntroductionCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectExistentialIntroductionCodeEqualityTemplate
    (coqRestrictedPADirectExistentialIntroductionCodeEqualityRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectExistentialIntroductionCodeEqualityRootAt.
  apply coqRestrictedPADirect_templateRawDerives_andE1.
  rewrite <- coqRestrictedPADirectExistentialIntroduction_case_shape.
  apply coqRestrictedPADirectExistentialIntroductionCaseRootAt_valid.
  exact hin.
Qed.

Lemma
    coqRestrictedPADirectExistentialIntroductionFormulaCodeSuffixRootAt_valid :
    forall context,
  In coqRestrictedPADirectExistentialIntroductionCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectExistentialIntroductionFormulaCodeSuffixTemplate
    (coqRestrictedPADirectExistentialIntroductionFormulaCodeSuffixRootAt
      context).
Proof.
  intros context hin.
  unfold
    coqRestrictedPADirectExistentialIntroductionFormulaCodeSuffixRootAt.
  apply coqRestrictedPADirect_templateRawDerives_andE2.
  rewrite <- coqRestrictedPADirectExistentialIntroduction_case_shape.
  apply coqRestrictedPADirectExistentialIntroductionCaseRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectExistentialIntroductionFormulaCodeRootAt_valid :
    forall context,
  In coqRestrictedPADirectExistentialIntroductionCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectExistentialIntroductionFormulaCodeTemplate
    (coqRestrictedPADirectExistentialIntroductionFormulaCodeRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectExistentialIntroductionFormulaCodeRootAt.
  apply coqRestrictedPADirect_templateRawDerives_andE1.
  apply
    coqRestrictedPADirectExistentialIntroductionFormulaCodeSuffixRootAt_valid.
  exact hin.
Qed.

Lemma
    coqRestrictedPADirectExistentialIntroductionSubstitutionSuffixRootAt_valid :
    forall context,
  In coqRestrictedPADirectExistentialIntroductionCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectExistentialIntroductionSubstitutionSuffixTemplate
    (coqRestrictedPADirectExistentialIntroductionSubstitutionSuffixRootAt
      context).
Proof.
  intros context hin.
  unfold
    coqRestrictedPADirectExistentialIntroductionSubstitutionSuffixRootAt.
  apply coqRestrictedPADirect_templateRawDerives_andE2.
  apply
    coqRestrictedPADirectExistentialIntroductionFormulaCodeSuffixRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectExistentialIntroductionSubstitutionRootAt_valid :
    forall context,
  In coqRestrictedPADirectExistentialIntroductionCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectExistentialIntroductionSubstitutionTemplate
    (coqRestrictedPADirectExistentialIntroductionSubstitutionRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectExistentialIntroductionSubstitutionRootAt.
  apply coqRestrictedPADirect_templateRawDerives_andE1.
  apply
    coqRestrictedPADirectExistentialIntroductionSubstitutionSuffixRootAt_valid.
  exact hin.
Qed.

Lemma
    coqRestrictedPADirectExistentialIntroductionChildEndpointSuffixRootAt_valid :
    forall context,
  In coqRestrictedPADirectExistentialIntroductionCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectExistentialIntroductionChildEndpointSuffixTemplate
    (coqRestrictedPADirectExistentialIntroductionChildEndpointSuffixRootAt
      context).
Proof.
  intros context hin.
  unfold
    coqRestrictedPADirectExistentialIntroductionChildEndpointSuffixRootAt.
  apply coqRestrictedPADirect_templateRawDerives_andE2.
  apply
    coqRestrictedPADirectExistentialIntroductionSubstitutionSuffixRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectExistentialIntroductionChildEndpointRootAt_valid :
    forall context,
  In coqRestrictedPADirectExistentialIntroductionCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectExistentialIntroductionChildEndpointTemplate
    (coqRestrictedPADirectExistentialIntroductionChildEndpointRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectExistentialIntroductionChildEndpointRootAt.
  apply coqRestrictedPADirect_templateRawDerives_andE1.
  apply
    coqRestrictedPADirectExistentialIntroductionChildEndpointSuffixRootAt_valid.
  exact hin.
Qed.

(** ------------------------------------------------------------------
    Honest semantic operation interfaces. *)

Definition
    coqRestrictedPADirectExistentialIntroductionChildInterfaceResultTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildInterfaceResultTemplate
    coqRestrictedPADirectExistentialIntroductionChildTerm
    coqRestrictedPADirectExistentialIntroductionWitnessContextTerm
    coqRestrictedPADirectExistentialIntroductionChildConclusionTerm.

Definition
    coqRestrictedPADirectExistentialIntroductionChildInterfaceLawTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectExistentialIntroductionDeepRestrictedTemplate
    (tfImp coqRestrictedPADirectExistentialIntroductionCodeEqualityTemplate
      (tfImp coqRestrictedPADirectExistentialIntroductionFormulaCodeTemplate
        (tfImp
          coqRestrictedPADirectExistentialIntroductionSubstitutionTemplate
          (tfImp
            coqRestrictedPADirectExistentialIntroductionChildEndpointTemplate
            (tfImp
              coqRestrictedPADirectExistentialIntroductionDeepAdmissibleTemplate
              coqRestrictedPADirectExistentialIntroductionChildInterfaceResultTemplate))))).

Definition coqRestrictedPADirectExistentialIntroductionDynamicTruthLawTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectExistentialIntroductionFormulaCodeTemplate
    (tfImp coqRestrictedPADirectExistentialIntroductionSubstitutionTemplate
      (tfImp coqRestrictedPADirectExistentialIntroductionChildTruthTemplate
        coqRestrictedPADirectExistentialIntroductionOuterConclusionTruthTemplate)).

Definition
    RawCoqRestrictedPADirectExistentialIntroductionChildInterfaceLawRootAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (context : TemplateContext) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation context)
      (rawTemplateFormula translation
        coqRestrictedPADirectExistentialIntroductionChildInterfaceLawTemplate)
      root.

Arguments
  RawCoqRestrictedPADirectExistentialIntroductionChildInterfaceLawRootAt
  M translation context : clear implicits.

Definition
    RawCoqRestrictedPADirectExistentialIntroductionDynamicTruthLawRootAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (context : TemplateContext) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation context)
      (rawTemplateFormula translation
        coqRestrictedPADirectExistentialIntroductionDynamicTruthLawTemplate)
      root.

Arguments
  RawCoqRestrictedPADirectExistentialIntroductionDynamicTruthLawRootAt
  M translation context : clear implicits.

Definition
    RawCoqRestrictedPADirectStrongStepExistentialIntroductionSemanticRoots
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop :=
  let translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs in
  let ready :=
    coqRestrictedPADirectStrongStepExistentialIntroductionReadyContext tail in
  RawCoqRestrictedPADirectExistentialIntroductionChildInterfaceLawRootAt
      M translation ready /\
  RawCoqRestrictedPADirectExistentialIntroductionDynamicTruthLawRootAt
      M translation ready.

Arguments
  RawCoqRestrictedPADirectStrongStepExistentialIntroductionSemanticRoots
  M hPA inputs tail : clear implicits.

(** ------------------------------------------------------------------
    Apply the recursive-child operation to the six constructor facts it is
    permitted to inspect.  Every modus-ponens node is constructed here. *)

Theorem
    raw_codedPALocalProofOf_coqRestrictedPADirectExistentialIntroductionChildInterface :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (translation : RawCodedTemplateTranslation M) context
    lawRoot restrictedRoot codeEqualityRoot formulaCodeRoot substitutionRoot
    displayedEndpointRoot admissibleRoot,
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation context)
    (rawTemplateFormula translation
      coqRestrictedPADirectExistentialIntroductionChildInterfaceLawTemplate)
    lawRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation context)
    (rawTemplateFormula translation
      coqRestrictedPADirectExistentialIntroductionDeepRestrictedTemplate)
    restrictedRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation context)
    (rawTemplateFormula translation
      coqRestrictedPADirectExistentialIntroductionCodeEqualityTemplate)
    codeEqualityRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation context)
    (rawTemplateFormula translation
      coqRestrictedPADirectExistentialIntroductionFormulaCodeTemplate)
    formulaCodeRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation context)
    (rawTemplateFormula translation
      coqRestrictedPADirectExistentialIntroductionSubstitutionTemplate)
    substitutionRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation context)
    (rawTemplateFormula translation
      coqRestrictedPADirectExistentialIntroductionChildEndpointTemplate)
    displayedEndpointRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation context)
    (rawTemplateFormula translation
      coqRestrictedPADirectExistentialIntroductionDeepAdmissibleTemplate)
    admissibleRoot ->
  exists resultRoot : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation context)
      (rawTemplateFormula translation
        coqRestrictedPADirectExistentialIntroductionChildInterfaceResultTemplate)
      resultRoot.
Proof.
  intros M hPA translation context lawRoot restrictedRoot
    codeEqualityRoot formulaCodeRoot substitutionRoot displayedEndpointRoot
    admissibleRoot hlaw hrestricted hcodeEquality hformulaCode hsubstitution
    hdisplayedEndpoint hadmissible.
  unfold
    coqRestrictedPADirectExistentialIntroductionChildInterfaceLawTemplate
    in hlaw.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation context _ _ lawRoot restrictedRoot
      hlaw hrestricted) as h1.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation context _ _ _ codeEqualityRoot
      h1 hcodeEquality) as h2.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation context _ _ _ formulaCodeRoot
      h2 hformulaCode) as h3.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation context _ _ _ substitutionRoot
      h3 hsubstitution) as h4.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation context _ _ _ displayedEndpointRoot
      h4 hdisplayedEndpoint) as h5.
  eexists.
  exact
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation context _ _ _ admissibleRoot h5 hadmissible).
Qed.

(** ------------------------------------------------------------------
    Constructor-local conclusion in the fully introduced ready context. *)

Theorem
    raw_codedPALocalProofOf_coqRestrictedPADirectExistentialIntroductionConclusionAt :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (translation : RawCodedTemplateTranslation M) tail,
  RawCoqRestrictedPADirectExistentialIntroductionChildInterfaceLawRootAt
    M translation
    (coqRestrictedPADirectStrongStepExistentialIntroductionReadyContext tail) ->
  RawCoqRestrictedPADirectExistentialIntroductionDynamicTruthLawRootAt
    M translation
    (coqRestrictedPADirectStrongStepExistentialIntroductionReadyContext tail) ->
  exists conclusionRoot : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation
        (coqRestrictedPADirectStrongStepExistentialIntroductionReadyContext
          tail))
      (rawTemplateFormula translation
        coqRestrictedPADirectExistentialIntroductionOuterConclusionTruthTemplate)
      conclusionRoot.
Proof.
  intros M hPA translation tail
    [childLawRoot hchildLaw] [truthLawRoot htruthLaw].
  set (ready :=
    coqRestrictedPADirectStrongStepExistentialIntroductionReadyContext tail).
  set (readyCode := rawTemplateContextCode translation ready).
  assert (hcase :
    In coqRestrictedPADirectExistentialIntroductionCaseTemplate ready).
  {
    unfold ready.
    apply coqRestrictedPADirectExistentialIntroduction_ready_case_in.
  }

  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectExistentialIntroductionCodeEqualityRootAt ready)
    (proj1
      (coqRestrictedPADirectExistentialIntroductionCodeEqualityRootAt_valid
        ready hcase))) as hcodeEquality.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectExistentialIntroductionFormulaCodeRootAt ready)
    (proj1
      (coqRestrictedPADirectExistentialIntroductionFormulaCodeRootAt_valid
        ready hcase))) as hformulaCode.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectExistentialIntroductionSubstitutionRootAt ready)
    (proj1
      (coqRestrictedPADirectExistentialIntroductionSubstitutionRootAt_valid
        ready hcase))) as hsubstitution.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectExistentialIntroductionChildEndpointRootAt ready)
    (proj1
      (coqRestrictedPADirectExistentialIntroductionChildEndpointRootAt_valid
        ready hcase))) as hdisplayedEndpoint.

  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAssumption
      M hPA translation ready
      coqRestrictedPADirectExistentialIntroductionDeepRestrictedTemplate
      (coqRestrictedPADirectExistentialIntroduction_ready_restricted_in tail))
    as hrestricted.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAssumption
      M hPA translation ready
      coqRestrictedPADirectExistentialIntroductionDeepAdmissibleTemplate
      (coqRestrictedPADirectExistentialIntroduction_ready_admissible_in tail))
    as hadmissible.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAssumption
      M hPA translation ready
      coqRestrictedPADirectExistentialIntroductionDeepStrongPrefixTemplate
      (coqRestrictedPADirectExistentialIntroduction_ready_prefix_in tail))
    as hprefix.

  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt ready)
    (proj1
      (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt_valid
        ready
        (coqRestrictedPADirectExistentialIntroduction_ready_endpoint_in tail)
        (coqRestrictedPADirectExistentialIntroduction_ready_context_truth_in
          tail)))) as hwitnessContextTruth.

  (** Normalize compiler endpoints without unfolding the full endpoint
      disjunction.  Capturing each concrete root avoids existential
      metavariables in [change]. *)
  lazymatch type of hcodeEquality with
  | RawCodedPALocalProofOf _ _ _ ?root =>
      change (RawCodedPALocalProofOf M readyCode
        (rawTemplateFormula translation
          coqRestrictedPADirectExistentialIntroductionCodeEqualityTemplate)
        root) in hcodeEquality
  end.
  lazymatch type of hformulaCode with
  | RawCodedPALocalProofOf _ _ _ ?root =>
      change (RawCodedPALocalProofOf M readyCode
        (rawTemplateFormula translation
          coqRestrictedPADirectExistentialIntroductionFormulaCodeTemplate)
        root) in hformulaCode
  end.
  lazymatch type of hsubstitution with
  | RawCodedPALocalProofOf _ _ _ ?root =>
      change (RawCodedPALocalProofOf M readyCode
        (rawTemplateFormula translation
          coqRestrictedPADirectExistentialIntroductionSubstitutionTemplate)
        root) in hsubstitution
  end.
  lazymatch type of hdisplayedEndpoint with
  | RawCodedPALocalProofOf _ _ _ ?root =>
      change (RawCodedPALocalProofOf M readyCode
        (rawTemplateFormula translation
          coqRestrictedPADirectExistentialIntroductionChildEndpointTemplate)
        root) in hdisplayedEndpoint
  end.
  lazymatch type of hrestricted with
  | RawCodedPALocalProofOf _ _ _ ?root =>
      change (RawCodedPALocalProofOf M readyCode
        (rawTemplateFormula translation
          coqRestrictedPADirectExistentialIntroductionDeepRestrictedTemplate)
        root) in hrestricted
  end.
  lazymatch type of hadmissible with
  | RawCodedPALocalProofOf _ _ _ ?root =>
      change (RawCodedPALocalProofOf M readyCode
        (rawTemplateFormula translation
          coqRestrictedPADirectExistentialIntroductionDeepAdmissibleTemplate)
        root) in hadmissible
  end.
  lazymatch type of hprefix with
  | RawCodedPALocalProofOf _ _ _ ?root =>
      change (RawCodedPALocalProofOf M readyCode
        (rawTemplateFormula translation
          coqRestrictedPADirectExistentialIntroductionDeepStrongPrefixTemplate)
        root) in hprefix
  end.
  lazymatch type of hwitnessContextTruth with
  | RawCodedPALocalProofOf _ _ _ ?root =>
      change (RawCodedPALocalProofOf M readyCode
        (rawTemplateFormula translation
          coqRestrictedPADirectAssumptionWitnessContextTruthTemplate)
        root) in hwitnessContextTruth
  end.

  destruct
    (raw_codedPALocalProofOf_coqRestrictedPADirectExistentialIntroductionChildInterface
      M hPA translation ready childLawRoot _ _ _ _ _ _
      hchildLaw hrestricted hcodeEquality hformulaCode hsubstitution
      hdisplayedEndpoint hadmissible)
    as [childInterfaceRoot hchildInterface].

  assert (hchildContextTruth : RawCodedPALocalProofOf M readyCode
    (rawTemplateFormula translation
      coqRestrictedPADirectExistentialIntroductionChildContextTruthTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt ready))).
  {
    rewrite
      coqRestrictedPADirectExistentialIntroduction_context_truth_agreement.
    exact hwitnessContextTruth.
  }

  destruct
    (raw_codedPALocalProofOf_coqRestrictedPADirectAndIntroductionChildTruth
      M hPA translation ready
      coqRestrictedPADirectExistentialIntroductionChildTerm
      coqRestrictedPADirectExistentialIntroductionWitnessContextTerm
      coqRestrictedPADirectExistentialIntroductionChildConclusionTerm
      childInterfaceRoot _ _
      hchildInterface hprefix hchildContextTruth)
    as [childTruthRoot hchildTruth].

  unfold coqRestrictedPADirectExistentialIntroductionDynamicTruthLawTemplate
    in htruthLaw.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation ready _ _ truthLawRoot _
      htruthLaw hformulaCode) as htruthAfterFormulaCode.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation ready _ _ _ _
      htruthAfterFormulaCode hsubstitution) as htruthAfterSubstitution.
  eexists.
  exact
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation ready _ _ _ childTruthRoot
      htruthAfterSubstitution hchildTruth).
Qed.

(** ------------------------------------------------------------------
    Exact [rawCoqRuleExIntroduction] slot of the public dispatcher. *)

Theorem
    raw_coqRestrictedPADirectStrongStepExistentialIntroductionCaseImplicationRoot :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectStrongStepExistentialIntroductionSemanticRoots
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
          (rawCoqRestrictedPAProofRuleCaseTemplate rawCoqRuleExIntroduction
            (liftTerm 8 (tVar 4)) (tVar 7) (liftTerm 8 (tVar 2))
            (tVar 6) (tVar 5) (tVar 4) (tVar 3)
            (tVar 2) (tVar 1) (tVar 0)))
        (rawDirectTemplateFormula inputs
          (rawCoqTemplateRenameN 8
            rawCoqRestrictedPADirectStrongStepRemainingTemplate)))
      root.
Proof.
  intros M hPA inputs tail hsemantic.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  set (baseContext :=
    coqRestrictedPADirectStrongStepExistentialIntroductionBaseContext tail).
  set (caseContext :=
    coqRestrictedPADirectStrongStepExistentialIntroductionCaseContext tail).
  set (admissibleContext :=
    coqRestrictedPADirectStrongStepExistentialIntroductionAdmissibleContext
      tail).
  set (readyContext :=
    coqRestrictedPADirectStrongStepExistentialIntroductionReadyContext tail).
  unfold
    RawCoqRestrictedPADirectStrongStepExistentialIntroductionSemanticRoots
    in hsemantic.
  cbn zeta in hsemantic.
  destruct hsemantic as [hchildLaw htruthLaw].
  destruct
    (raw_codedPALocalProofOf_coqRestrictedPADirectExistentialIntroductionConclusionAt
      M hPA translation tail hchildLaw htruthLaw)
    as [conclusionRoot hconclusion].

  set (readyCode := rawTemplateContextCode translation readyContext).
  set (admissibleCode :=
    rawTemplateContextCode translation admissibleContext).
  set (caseCode := rawTemplateContextCode translation caseContext).
  set (baseCode := rawTemplateContextCode translation baseContext).

  set (contextImpRoot := rawProofImpIRoot M admissibleCode
    (rawTemplateFormula translation
      coqRestrictedPADirectExistentialIntroductionOuterContextTruthTemplate)
    (rawTemplateFormula translation
      coqRestrictedPADirectExistentialIntroductionOuterConclusionTruthTemplate)
    conclusionRoot).
  assert (hcontextImp : RawCodedPALocalProofOf M admissibleCode
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectExistentialIntroductionOuterContextTruthTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectExistentialIntroductionOuterConclusionTruthTemplate))
    contextImpRoot).
  {
    unfold contextImpRoot.
    apply (raw_codedPALocalProofOf_impI M hPA admissibleCode
      (rawTemplateFormula translation
        coqRestrictedPADirectExistentialIntroductionOuterContextTruthTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectExistentialIntroductionOuterConclusionTruthTemplate)
      conclusionRoot).
    change (RawCodedPALocalProofOf M readyCode
      (rawTemplateFormula translation
        coqRestrictedPADirectExistentialIntroductionOuterConclusionTruthTemplate)
      conclusionRoot).
    change (RawCodedPALocalProofOf M
      (rawTemplateContextCode translation readyContext)
      (rawTemplateFormula translation
        coqRestrictedPADirectExistentialIntroductionOuterConclusionTruthTemplate)
      conclusionRoot).
    unfold readyContext.
    exact hconclusion.
  }

  set (admissibleImpRoot := rawProofImpIRoot M caseCode
    (rawTemplateFormula translation
      coqRestrictedPADirectExistentialIntroductionDeepAdmissibleTemplate)
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectExistentialIntroductionOuterContextTruthTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectExistentialIntroductionOuterConclusionTruthTemplate))
    contextImpRoot).
  assert (hadmissibleImp : RawCodedPALocalProofOf M caseCode
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectExistentialIntroductionDeepAdmissibleTemplate)
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          coqRestrictedPADirectExistentialIntroductionOuterContextTruthTemplate)
        (rawTemplateFormula translation
          coqRestrictedPADirectExistentialIntroductionOuterConclusionTruthTemplate)))
    admissibleImpRoot).
  {
    unfold admissibleImpRoot.
    apply (raw_codedPALocalProofOf_impI M hPA caseCode
      (rawTemplateFormula translation
        coqRestrictedPADirectExistentialIntroductionDeepAdmissibleTemplate)
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          coqRestrictedPADirectExistentialIntroductionOuterContextTruthTemplate)
        (rawTemplateFormula translation
          coqRestrictedPADirectExistentialIntroductionOuterConclusionTruthTemplate))
      contextImpRoot).
    exact hcontextImp.
  }

  set (caseImpRoot := rawProofImpIRoot M baseCode
    (rawTemplateFormula translation
      coqRestrictedPADirectExistentialIntroductionCaseTemplate)
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectExistentialIntroductionDeepAdmissibleTemplate)
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          coqRestrictedPADirectExistentialIntroductionOuterContextTruthTemplate)
        (rawTemplateFormula translation
          coqRestrictedPADirectExistentialIntroductionOuterConclusionTruthTemplate)))
    admissibleImpRoot).
  exists caseImpRoot.
  rewrite coqRestrictedPADirectExistentialIntroduction_remaining_shape.
  change (RawCodedPALocalProofOf M baseCode
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectExistentialIntroductionCaseTemplate)
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          coqRestrictedPADirectExistentialIntroductionDeepAdmissibleTemplate)
        (rawFormulaImpCode M
          (rawTemplateFormula translation
            coqRestrictedPADirectExistentialIntroductionOuterContextTruthTemplate)
          (rawTemplateFormula translation
            coqRestrictedPADirectExistentialIntroductionOuterConclusionTruthTemplate))))
    caseImpRoot).
  unfold caseImpRoot.
  apply (raw_codedPALocalProofOf_impI M hPA baseCode
    (rawTemplateFormula translation
      coqRestrictedPADirectExistentialIntroductionCaseTemplate)
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectExistentialIntroductionDeepAdmissibleTemplate)
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          coqRestrictedPADirectExistentialIntroductionOuterContextTruthTemplate)
        (rawTemplateFormula translation
          coqRestrictedPADirectExistentialIntroductionOuterConclusionTruthTemplate)))
    admissibleImpRoot).
  exact hadmissibleImp.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialIntroductionCase.
