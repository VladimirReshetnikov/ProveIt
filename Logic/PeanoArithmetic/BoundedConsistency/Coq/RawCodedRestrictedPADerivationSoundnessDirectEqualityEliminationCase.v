(**
  The exact equality-elimination branch of the direct strong step.

  At the eight endpoint witnesses the constructor exposes source and target
  terms [a] and [b], a one-variable motive [c], its equality formula [t],
  and two recursive children.  The equality child proves [a = b]; the motive
  child proves the source instance [c[a]].  The branch conclusion is the
  target instance [c[b]].

  This module projects every literal constructor field, specializes the
  inherited strong prefix to both displayed endpoints, transports context
  truth to their common witness context, and constructs the complete
  equality/substitution truth proof spine.  Only operation-level semantic
  resources remain open: honest recursive-child interfaces and the dynamic
  equality-substitution truth law.  In particular, no residual assumes this
  branch, its requested conclusion, or the direct strong step.
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
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationCase.

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
    Literal constructor fields at endpoint-witness depth eight.

    The dispatcher's argument order is

      code, context, conclusion, a, b, c, t, child1, child2, child3.

    After opening its eight existential witnesses these become respectively

      lift 8 root, #7, lift 8 conclusion, #6, #5, #4, #3, #2, #1, #0.

    Thus [#2] is the equality child with conclusion [#3], while [#1] is
    the motive child with source-instance conclusion [#0].  Naming these
    positions avoids silently swapping the two recursive hypotheses.
*)

Definition coqRestrictedPADirectEqualityEliminationWitnessContextTerm
    : TemplateTerm := ttVar 7.

Definition coqRestrictedPADirectEqualityEliminationSourceTerm
    : TemplateTerm := ttVar 6.

Definition coqRestrictedPADirectEqualityEliminationTargetTerm
    : TemplateTerm := ttVar 5.

Definition coqRestrictedPADirectEqualityEliminationMotiveFormulaTerm
    : TemplateTerm := ttVar 4.

Definition coqRestrictedPADirectEqualityEliminationEqualityFormulaTerm
    : TemplateTerm := ttVar 3.

Definition coqRestrictedPADirectEqualityEliminationEqualityChildTerm
    : TemplateTerm := ttVar 2.

Definition coqRestrictedPADirectEqualityEliminationMotiveChildTerm
    : TemplateTerm := ttVar 1.

Definition coqRestrictedPADirectEqualityEliminationSourceInstanceTerm
    : TemplateTerm := ttVar 0.

Definition coqRestrictedPADirectEqualityEliminationAssignmentCodeTerm
    : TemplateTerm := ttVar 9.

Definition coqRestrictedPADirectEqualityEliminationAssignmentStepTerm
    : TemplateTerm := ttVar 8.

Definition coqRestrictedPADirectEqualityEliminationCodeEqualityTemplate
    : TemplateFormula :=
  embedPAFormula
    (pEq (liftTerm 8 (tVar 4))
      (proofEqElimCodeTerm (tVar 7) (tVar 6) (tVar 5) (tVar 4)
        (tVar 2) (tVar 1))).

(** [substitute b c = conclusion]: the target instance is the branch's
    outer conclusion, whose code lives outside all eight witnesses. *)
Definition coqRestrictedPADirectEqualityEliminationTargetSubstitutionTemplate
    : TemplateFormula :=
  embedPAFormula
    (codedFormulaSingleSubstitutionTermAt
      (tVar 5) (tVar 4) (liftTerm 8 (tVar 2))).

Definition coqRestrictedPADirectEqualityEliminationEqualityFormulaCodeTemplate
    : TemplateFormula :=
  embedPAFormula
    (formulaEqCodeTermAt (tVar 3) (tVar 6) (tVar 5)).

Definition coqRestrictedPADirectEqualityEliminationEqualityChildEndpointTemplate
    : TemplateFormula :=
  embedPAFormula
    (proofEndpointTermAt (tVar 2) (tVar 7) (tVar 3)).

(** [substitute a c = child3]: [#0] is a formula code, not a proof code;
    it is the displayed conclusion of the motive child [#1]. *)
Definition coqRestrictedPADirectEqualityEliminationSourceSubstitutionTemplate
    : TemplateFormula :=
  embedPAFormula
    (codedFormulaSingleSubstitutionTermAt
      (tVar 6) (tVar 4) (tVar 0)).

Definition coqRestrictedPADirectEqualityEliminationMotiveChildEndpointTemplate
    : TemplateFormula :=
  embedPAFormula
    (proofEndpointTermAt (tVar 1) (tVar 7) (tVar 0)).

Definition coqRestrictedPADirectEqualityEliminationTerminalTruthTemplate
    : TemplateFormula := embedPAFormula (pEq tZero tZero).

Definition
    coqRestrictedPADirectEqualityEliminationMotiveChildEndpointSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectEqualityEliminationMotiveChildEndpointTemplate
    coqRestrictedPADirectEqualityEliminationTerminalTruthTemplate.

Definition
    coqRestrictedPADirectEqualityEliminationSourceSubstitutionSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectEqualityEliminationSourceSubstitutionTemplate
    coqRestrictedPADirectEqualityEliminationMotiveChildEndpointSuffixTemplate.

Definition
    coqRestrictedPADirectEqualityEliminationEqualityChildEndpointSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectEqualityEliminationEqualityChildEndpointTemplate
    coqRestrictedPADirectEqualityEliminationSourceSubstitutionSuffixTemplate.

Definition
    coqRestrictedPADirectEqualityEliminationEqualityFormulaCodeSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectEqualityEliminationEqualityFormulaCodeTemplate
    coqRestrictedPADirectEqualityEliminationEqualityChildEndpointSuffixTemplate.

Definition
    coqRestrictedPADirectEqualityEliminationTargetSubstitutionSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectEqualityEliminationTargetSubstitutionTemplate
    coqRestrictedPADirectEqualityEliminationEqualityFormulaCodeSuffixTemplate.

Definition coqRestrictedPADirectEqualityEliminationCaseTemplate
    : TemplateFormula :=
  rawCoqRestrictedPAProofRuleCaseTemplate rawCoqRuleEqualityElimination
    (liftTerm 8 (tVar 4)) (tVar 7) (liftTerm 8 (tVar 2))
    (tVar 6) (tVar 5) (tVar 4) (tVar 3)
    (tVar 2) (tVar 1) (tVar 0).

Lemma coqRestrictedPADirectEqualityElimination_case_shape :
  coqRestrictedPADirectEqualityEliminationCaseTemplate =
  tfAnd coqRestrictedPADirectEqualityEliminationCodeEqualityTemplate
    coqRestrictedPADirectEqualityEliminationTargetSubstitutionSuffixTemplate.
Proof. reflexivity. Qed.

(** ------------------------------------------------------------------
    The two exact instances of the inherited strong-prefix predicate.

    Conjunction introduction already compiled the generic four-binder
    specialization (context, conclusion, assignment code, assignment step).
    Reusing it here makes the conclusion transport explicit merely by
    choosing [#3] for the equality child and [#0] for the motive child.
*)

Definition coqRestrictedPADirectEqualityEliminationEqualityChildBelowTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildBelowTemplate
    coqRestrictedPADirectEqualityEliminationEqualityChildTerm.

Definition coqRestrictedPADirectEqualityEliminationMotiveChildBelowTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildBelowTemplate
    coqRestrictedPADirectEqualityEliminationMotiveChildTerm.

Definition
    coqRestrictedPADirectEqualityEliminationEqualityChildRestrictedTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildRestrictedTemplate
    coqRestrictedPADirectEqualityEliminationEqualityChildTerm
    coqRestrictedPADirectEqualityEliminationWitnessContextTerm
    coqRestrictedPADirectEqualityEliminationEqualityFormulaTerm.

Definition
    coqRestrictedPADirectEqualityEliminationMotiveChildRestrictedTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildRestrictedTemplate
    coqRestrictedPADirectEqualityEliminationMotiveChildTerm
    coqRestrictedPADirectEqualityEliminationWitnessContextTerm
    coqRestrictedPADirectEqualityEliminationSourceInstanceTerm.

Definition
    coqRestrictedPADirectEqualityEliminationEqualityChildRuleValidTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildEndpointTemplate
    coqRestrictedPADirectEqualityEliminationEqualityChildTerm
    coqRestrictedPADirectEqualityEliminationWitnessContextTerm
    coqRestrictedPADirectEqualityEliminationEqualityFormulaTerm.

Definition
    coqRestrictedPADirectEqualityEliminationMotiveChildRuleValidTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildEndpointTemplate
    coqRestrictedPADirectEqualityEliminationMotiveChildTerm
    coqRestrictedPADirectEqualityEliminationWitnessContextTerm
    coqRestrictedPADirectEqualityEliminationSourceInstanceTerm.

Definition
    coqRestrictedPADirectEqualityEliminationEqualityChildAdmissibleTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildAdmissibleTemplate
    coqRestrictedPADirectEqualityEliminationEqualityChildTerm
    coqRestrictedPADirectEqualityEliminationWitnessContextTerm
    coqRestrictedPADirectEqualityEliminationEqualityFormulaTerm.

Definition
    coqRestrictedPADirectEqualityEliminationMotiveChildAdmissibleTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildAdmissibleTemplate
    coqRestrictedPADirectEqualityEliminationMotiveChildTerm
    coqRestrictedPADirectEqualityEliminationWitnessContextTerm
    coqRestrictedPADirectEqualityEliminationSourceInstanceTerm.

Definition
    coqRestrictedPADirectEqualityEliminationEqualityChildContextTruthTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildContextTruthTemplate
    coqRestrictedPADirectEqualityEliminationEqualityChildTerm
    coqRestrictedPADirectEqualityEliminationWitnessContextTerm
    coqRestrictedPADirectEqualityEliminationEqualityFormulaTerm.

Definition
    coqRestrictedPADirectEqualityEliminationMotiveChildContextTruthTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildContextTruthTemplate
    coqRestrictedPADirectEqualityEliminationMotiveChildTerm
    coqRestrictedPADirectEqualityEliminationWitnessContextTerm
    coqRestrictedPADirectEqualityEliminationSourceInstanceTerm.

Definition coqRestrictedPADirectEqualityEliminationEqualityChildTruthTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildTruthTemplate
    coqRestrictedPADirectEqualityEliminationEqualityChildTerm
    coqRestrictedPADirectEqualityEliminationWitnessContextTerm
    coqRestrictedPADirectEqualityEliminationEqualityFormulaTerm.

Definition coqRestrictedPADirectEqualityEliminationMotiveChildTruthTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildTruthTemplate
    coqRestrictedPADirectEqualityEliminationMotiveChildTerm
    coqRestrictedPADirectEqualityEliminationWitnessContextTerm
    coqRestrictedPADirectEqualityEliminationSourceInstanceTerm.

Definition coqRestrictedPADirectEqualityEliminationOuterContextTruthTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionOuterContextTruthTemplate.

Definition coqRestrictedPADirectEqualityEliminationOuterConclusionTruthTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionOuterConclusionTruthTemplate.

Definition coqRestrictedPADirectEqualityEliminationDeepRestrictedTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionDeepRestrictedTemplate.

Definition coqRestrictedPADirectEqualityEliminationDeepAdmissibleTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionDeepAdmissibleTemplate.

Definition coqRestrictedPADirectEqualityEliminationDeepStrongPrefixTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionDeepStrongPrefixTemplate.

Lemma
    coqRestrictedPADirectEqualityElimination_equality_context_truth_agreement :
  coqRestrictedPADirectEqualityEliminationEqualityChildContextTruthTemplate =
  coqRestrictedPADirectAssumptionWitnessContextTruthTemplate.
Proof. reflexivity. Qed.

Lemma
    coqRestrictedPADirectEqualityElimination_motive_context_truth_agreement :
  coqRestrictedPADirectEqualityEliminationMotiveChildContextTruthTemplate =
  coqRestrictedPADirectAssumptionWitnessContextTruthTemplate.
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectEqualityElimination_remaining_shape :
  rawCoqTemplateRenameN 8
    rawCoqRestrictedPADirectStrongStepRemainingTemplate =
  tfImp coqRestrictedPADirectEqualityEliminationDeepAdmissibleTemplate
    (tfImp coqRestrictedPADirectEqualityEliminationOuterContextTruthTemplate
      coqRestrictedPADirectEqualityEliminationOuterConclusionTruthTemplate).
Proof. reflexivity. Qed.

(** ------------------------------------------------------------------
    Exact arbitrary-tail shell contexts and inherited assumptions. *)

Definition coqRestrictedPADirectStrongStepEqualityEliminationBaseContext
    (tail : TemplateContext) : TemplateContext :=
  rawCoqRestrictedPADirectEndpointWitnessBodyTemplate ::
    rawCoqRestrictedPADirectEndpointDeepTail
      (rawCoqRestrictedPADirectStrongStepEndpointTail tail).

Definition coqRestrictedPADirectStrongStepEqualityEliminationCaseContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectEqualityEliminationCaseTemplate ::
    coqRestrictedPADirectStrongStepEqualityEliminationBaseContext tail.

Definition coqRestrictedPADirectStrongStepEqualityEliminationAdmissibleContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectEqualityEliminationDeepAdmissibleTemplate ::
    coqRestrictedPADirectStrongStepEqualityEliminationCaseContext tail.

Definition coqRestrictedPADirectStrongStepEqualityEliminationReadyContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectEqualityEliminationOuterContextTruthTemplate ::
    coqRestrictedPADirectStrongStepEqualityEliminationAdmissibleContext tail.

Arguments coqRestrictedPADirectStrongStepEqualityEliminationBaseContext
  tail : clear implicits.
Arguments coqRestrictedPADirectStrongStepEqualityEliminationCaseContext
  tail : clear implicits.
Arguments coqRestrictedPADirectStrongStepEqualityEliminationAdmissibleContext
  tail : clear implicits.
Arguments coqRestrictedPADirectStrongStepEqualityEliminationReadyContext
  tail : clear implicits.

Lemma coqRestrictedPADirectEqualityElimination_ready_endpoint_in : forall tail,
  In rawCoqRestrictedPADirectEndpointWitnessBodyTemplate
    (coqRestrictedPADirectStrongStepEqualityEliminationReadyContext tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectStrongStepEqualityEliminationReadyContext,
    coqRestrictedPADirectStrongStepEqualityEliminationAdmissibleContext,
    coqRestrictedPADirectStrongStepEqualityEliminationCaseContext,
    coqRestrictedPADirectStrongStepEqualityEliminationBaseContext.
  do 3 right. left. reflexivity.
Qed.

Lemma coqRestrictedPADirectEqualityElimination_ready_case_in : forall tail,
  In coqRestrictedPADirectEqualityEliminationCaseTemplate
    (coqRestrictedPADirectStrongStepEqualityEliminationReadyContext tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectStrongStepEqualityEliminationReadyContext,
    coqRestrictedPADirectStrongStepEqualityEliminationAdmissibleContext,
    coqRestrictedPADirectStrongStepEqualityEliminationCaseContext.
  right. right. left. reflexivity.
Qed.

Lemma coqRestrictedPADirectEqualityElimination_ready_admissible_in :
    forall tail,
  In coqRestrictedPADirectEqualityEliminationDeepAdmissibleTemplate
    (coqRestrictedPADirectStrongStepEqualityEliminationReadyContext tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectStrongStepEqualityEliminationReadyContext,
    coqRestrictedPADirectStrongStepEqualityEliminationAdmissibleContext.
  right. left. reflexivity.
Qed.

Lemma coqRestrictedPADirectEqualityElimination_ready_context_truth_in :
    forall tail,
  In coqRestrictedPADirectEqualityEliminationOuterContextTruthTemplate
    (coqRestrictedPADirectStrongStepEqualityEliminationReadyContext tail).
Proof. intro tail. left. reflexivity. Qed.

Lemma coqRestrictedPADirectEqualityElimination_ready_restricted_in :
    forall tail,
  In coqRestrictedPADirectEqualityEliminationDeepRestrictedTemplate
    (coqRestrictedPADirectStrongStepEqualityEliminationReadyContext tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectStrongStepEqualityEliminationReadyContext,
    coqRestrictedPADirectStrongStepEqualityEliminationAdmissibleContext,
    coqRestrictedPADirectStrongStepEqualityEliminationCaseContext,
    coqRestrictedPADirectStrongStepEqualityEliminationBaseContext.
  do 3 right.
  rewrite <- raw_coqRestrictedPADirectEndpointDeepContext_shape.
  unfold coqRestrictedPADirectEqualityEliminationDeepRestrictedTemplate,
    coqRestrictedPADirectAndIntroductionDeepRestrictedTemplate.
  apply raw_coqTemplateNestedExContext_inherited.
  unfold rawCoqRestrictedPADirectStrongStepEndpointTail.
  left. reflexivity.
Qed.

Lemma coqRestrictedPADirectEqualityElimination_ready_prefix_in : forall tail,
  In coqRestrictedPADirectEqualityEliminationDeepStrongPrefixTemplate
    (coqRestrictedPADirectStrongStepEqualityEliminationReadyContext tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectStrongStepEqualityEliminationReadyContext,
    coqRestrictedPADirectStrongStepEqualityEliminationAdmissibleContext,
    coqRestrictedPADirectStrongStepEqualityEliminationCaseContext,
    coqRestrictedPADirectStrongStepEqualityEliminationBaseContext.
  do 3 right.
  rewrite <- raw_coqRestrictedPADirectEndpointDeepContext_shape.
  unfold coqRestrictedPADirectEqualityEliminationDeepStrongPrefixTemplate,
    coqRestrictedPADirectAndIntroductionDeepStrongPrefixTemplate.
  apply raw_coqTemplateNestedExContext_inherited.
  unfold rawCoqRestrictedPADirectStrongStepEndpointTail.
  right.
  unfold rawCoqRestrictedPADirectStrongStepFourBinderContext.
  apply coqRestrictedPADirectAndIntroduction_contextShiftN_head.
Qed.

(** ------------------------------------------------------------------
    Context-generic finite projections of all six constructor fields.

    [proofRuleConjunction] is right associated and ends in [0 = 0].  Each
    [SuffixRootAt] therefore peels one right branch, while the following
    field root takes its left branch.  Keeping the suffixes named makes the
    source/target substitutions and the two endpoints independently
    auditable.
*)

Definition coqRestrictedPADirectEqualityEliminationCaseRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAss context coqRestrictedPADirectEqualityEliminationCaseTemplate.

Definition coqRestrictedPADirectEqualityEliminationCodeEqualityRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectEqualityEliminationCodeEqualityTemplate
    coqRestrictedPADirectEqualityEliminationTargetSubstitutionSuffixTemplate
    (coqRestrictedPADirectEqualityEliminationCaseRootAt context).

Definition
    coqRestrictedPADirectEqualityEliminationTargetSubstitutionSuffixRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE2 context
    coqRestrictedPADirectEqualityEliminationCodeEqualityTemplate
    coqRestrictedPADirectEqualityEliminationTargetSubstitutionSuffixTemplate
    (coqRestrictedPADirectEqualityEliminationCaseRootAt context).

Definition coqRestrictedPADirectEqualityEliminationTargetSubstitutionRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectEqualityEliminationTargetSubstitutionTemplate
    coqRestrictedPADirectEqualityEliminationEqualityFormulaCodeSuffixTemplate
    (coqRestrictedPADirectEqualityEliminationTargetSubstitutionSuffixRootAt
      context).

Definition
    coqRestrictedPADirectEqualityEliminationEqualityFormulaCodeSuffixRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE2 context
    coqRestrictedPADirectEqualityEliminationTargetSubstitutionTemplate
    coqRestrictedPADirectEqualityEliminationEqualityFormulaCodeSuffixTemplate
    (coqRestrictedPADirectEqualityEliminationTargetSubstitutionSuffixRootAt
      context).

Definition
    coqRestrictedPADirectEqualityEliminationEqualityFormulaCodeRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectEqualityEliminationEqualityFormulaCodeTemplate
    coqRestrictedPADirectEqualityEliminationEqualityChildEndpointSuffixTemplate
    (coqRestrictedPADirectEqualityEliminationEqualityFormulaCodeSuffixRootAt
      context).

Definition
    coqRestrictedPADirectEqualityEliminationEqualityChildEndpointSuffixRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE2 context
    coqRestrictedPADirectEqualityEliminationEqualityFormulaCodeTemplate
    coqRestrictedPADirectEqualityEliminationEqualityChildEndpointSuffixTemplate
    (coqRestrictedPADirectEqualityEliminationEqualityFormulaCodeSuffixRootAt
      context).

Definition
    coqRestrictedPADirectEqualityEliminationEqualityChildEndpointRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectEqualityEliminationEqualityChildEndpointTemplate
    coqRestrictedPADirectEqualityEliminationSourceSubstitutionSuffixTemplate
    (coqRestrictedPADirectEqualityEliminationEqualityChildEndpointSuffixRootAt
      context).

Definition
    coqRestrictedPADirectEqualityEliminationSourceSubstitutionSuffixRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE2 context
    coqRestrictedPADirectEqualityEliminationEqualityChildEndpointTemplate
    coqRestrictedPADirectEqualityEliminationSourceSubstitutionSuffixTemplate
    (coqRestrictedPADirectEqualityEliminationEqualityChildEndpointSuffixRootAt
      context).

Definition coqRestrictedPADirectEqualityEliminationSourceSubstitutionRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectEqualityEliminationSourceSubstitutionTemplate
    coqRestrictedPADirectEqualityEliminationMotiveChildEndpointSuffixTemplate
    (coqRestrictedPADirectEqualityEliminationSourceSubstitutionSuffixRootAt
      context).

Definition
    coqRestrictedPADirectEqualityEliminationMotiveChildEndpointSuffixRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE2 context
    coqRestrictedPADirectEqualityEliminationSourceSubstitutionTemplate
    coqRestrictedPADirectEqualityEliminationMotiveChildEndpointSuffixTemplate
    (coqRestrictedPADirectEqualityEliminationSourceSubstitutionSuffixRootAt
      context).

Definition coqRestrictedPADirectEqualityEliminationMotiveChildEndpointRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectEqualityEliminationMotiveChildEndpointTemplate
    coqRestrictedPADirectEqualityEliminationTerminalTruthTemplate
    (coqRestrictedPADirectEqualityEliminationMotiveChildEndpointSuffixRootAt
      context).

Lemma coqRestrictedPADirectEqualityEliminationCaseRootAt_valid : forall
    context,
  In coqRestrictedPADirectEqualityEliminationCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectEqualityEliminationCaseTemplate
    (coqRestrictedPADirectEqualityEliminationCaseRootAt context).
Proof. intros context hin. apply templateRawDerives_assumption. exact hin. Qed.

Lemma coqRestrictedPADirectEqualityEliminationCodeEqualityRootAt_valid :
    forall context,
  In coqRestrictedPADirectEqualityEliminationCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectEqualityEliminationCodeEqualityTemplate
    (coqRestrictedPADirectEqualityEliminationCodeEqualityRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectEqualityEliminationCodeEqualityRootAt.
  apply coqRestrictedPADirect_templateRawDerives_andE1.
  rewrite <- coqRestrictedPADirectEqualityElimination_case_shape.
  apply coqRestrictedPADirectEqualityEliminationCaseRootAt_valid.
  exact hin.
Qed.

Lemma
    coqRestrictedPADirectEqualityEliminationTargetSubstitutionSuffixRootAt_valid :
    forall context,
  In coqRestrictedPADirectEqualityEliminationCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectEqualityEliminationTargetSubstitutionSuffixTemplate
    (coqRestrictedPADirectEqualityEliminationTargetSubstitutionSuffixRootAt
      context).
Proof.
  intros context hin.
  unfold
    coqRestrictedPADirectEqualityEliminationTargetSubstitutionSuffixRootAt.
  apply coqRestrictedPADirect_templateRawDerives_andE2.
  rewrite <- coqRestrictedPADirectEqualityElimination_case_shape.
  apply coqRestrictedPADirectEqualityEliminationCaseRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectEqualityEliminationTargetSubstitutionRootAt_valid :
    forall context,
  In coqRestrictedPADirectEqualityEliminationCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectEqualityEliminationTargetSubstitutionTemplate
    (coqRestrictedPADirectEqualityEliminationTargetSubstitutionRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectEqualityEliminationTargetSubstitutionRootAt.
  apply coqRestrictedPADirect_templateRawDerives_andE1.
  apply
    coqRestrictedPADirectEqualityEliminationTargetSubstitutionSuffixRootAt_valid.
  exact hin.
Qed.

Lemma
    coqRestrictedPADirectEqualityEliminationEqualityFormulaCodeSuffixRootAt_valid :
    forall context,
  In coqRestrictedPADirectEqualityEliminationCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectEqualityEliminationEqualityFormulaCodeSuffixTemplate
    (coqRestrictedPADirectEqualityEliminationEqualityFormulaCodeSuffixRootAt
      context).
Proof.
  intros context hin.
  unfold
    coqRestrictedPADirectEqualityEliminationEqualityFormulaCodeSuffixRootAt.
  apply coqRestrictedPADirect_templateRawDerives_andE2.
  apply
    coqRestrictedPADirectEqualityEliminationTargetSubstitutionSuffixRootAt_valid.
  exact hin.
Qed.

Lemma
    coqRestrictedPADirectEqualityEliminationEqualityFormulaCodeRootAt_valid :
    forall context,
  In coqRestrictedPADirectEqualityEliminationCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectEqualityEliminationEqualityFormulaCodeTemplate
    (coqRestrictedPADirectEqualityEliminationEqualityFormulaCodeRootAt
      context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectEqualityEliminationEqualityFormulaCodeRootAt.
  apply coqRestrictedPADirect_templateRawDerives_andE1.
  apply
    coqRestrictedPADirectEqualityEliminationEqualityFormulaCodeSuffixRootAt_valid.
  exact hin.
Qed.

Lemma
    coqRestrictedPADirectEqualityEliminationEqualityChildEndpointSuffixRootAt_valid :
    forall context,
  In coqRestrictedPADirectEqualityEliminationCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectEqualityEliminationEqualityChildEndpointSuffixTemplate
    (coqRestrictedPADirectEqualityEliminationEqualityChildEndpointSuffixRootAt
      context).
Proof.
  intros context hin.
  unfold
    coqRestrictedPADirectEqualityEliminationEqualityChildEndpointSuffixRootAt.
  apply coqRestrictedPADirect_templateRawDerives_andE2.
  apply
    coqRestrictedPADirectEqualityEliminationEqualityFormulaCodeSuffixRootAt_valid.
  exact hin.
Qed.

Lemma
    coqRestrictedPADirectEqualityEliminationEqualityChildEndpointRootAt_valid :
    forall context,
  In coqRestrictedPADirectEqualityEliminationCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectEqualityEliminationEqualityChildEndpointTemplate
    (coqRestrictedPADirectEqualityEliminationEqualityChildEndpointRootAt
      context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectEqualityEliminationEqualityChildEndpointRootAt.
  apply coqRestrictedPADirect_templateRawDerives_andE1.
  apply
    coqRestrictedPADirectEqualityEliminationEqualityChildEndpointSuffixRootAt_valid.
  exact hin.
Qed.

Lemma
    coqRestrictedPADirectEqualityEliminationSourceSubstitutionSuffixRootAt_valid :
    forall context,
  In coqRestrictedPADirectEqualityEliminationCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectEqualityEliminationSourceSubstitutionSuffixTemplate
    (coqRestrictedPADirectEqualityEliminationSourceSubstitutionSuffixRootAt
      context).
Proof.
  intros context hin.
  unfold
    coqRestrictedPADirectEqualityEliminationSourceSubstitutionSuffixRootAt.
  apply coqRestrictedPADirect_templateRawDerives_andE2.
  apply
    coqRestrictedPADirectEqualityEliminationEqualityChildEndpointSuffixRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectEqualityEliminationSourceSubstitutionRootAt_valid :
    forall context,
  In coqRestrictedPADirectEqualityEliminationCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectEqualityEliminationSourceSubstitutionTemplate
    (coqRestrictedPADirectEqualityEliminationSourceSubstitutionRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectEqualityEliminationSourceSubstitutionRootAt.
  apply coqRestrictedPADirect_templateRawDerives_andE1.
  apply
    coqRestrictedPADirectEqualityEliminationSourceSubstitutionSuffixRootAt_valid.
  exact hin.
Qed.

Lemma
    coqRestrictedPADirectEqualityEliminationMotiveChildEndpointSuffixRootAt_valid :
    forall context,
  In coqRestrictedPADirectEqualityEliminationCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectEqualityEliminationMotiveChildEndpointSuffixTemplate
    (coqRestrictedPADirectEqualityEliminationMotiveChildEndpointSuffixRootAt
      context).
Proof.
  intros context hin.
  unfold
    coqRestrictedPADirectEqualityEliminationMotiveChildEndpointSuffixRootAt.
  apply coqRestrictedPADirect_templateRawDerives_andE2.
  apply
    coqRestrictedPADirectEqualityEliminationSourceSubstitutionSuffixRootAt_valid.
  exact hin.
Qed.

Lemma
    coqRestrictedPADirectEqualityEliminationMotiveChildEndpointRootAt_valid :
    forall context,
  In coqRestrictedPADirectEqualityEliminationCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectEqualityEliminationMotiveChildEndpointTemplate
    (coqRestrictedPADirectEqualityEliminationMotiveChildEndpointRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectEqualityEliminationMotiveChildEndpointRootAt.
  apply coqRestrictedPADirect_templateRawDerives_andE1.
  apply
    coqRestrictedPADirectEqualityEliminationMotiveChildEndpointSuffixRootAt_valid.
  exact hin.
Qed.

(** ------------------------------------------------------------------
    Sharp semantic operation interfaces.

    Recursive descent is split by child.  The equality child operation sees
    only its equality-code and endpoint fields; the motive child operation
    sees only the source-substitution and its endpoint.  The target
    substitution is deliberately absent from both descent laws: it belongs
    solely to the final semantic transport from [c[a]] to [c[b]].
*)

Definition
    coqRestrictedPADirectEqualityEliminationEqualityChildInterfaceResultTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildInterfaceResultTemplate
    coqRestrictedPADirectEqualityEliminationEqualityChildTerm
    coqRestrictedPADirectEqualityEliminationWitnessContextTerm
    coqRestrictedPADirectEqualityEliminationEqualityFormulaTerm.

Definition
    coqRestrictedPADirectEqualityEliminationMotiveChildInterfaceResultTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildInterfaceResultTemplate
    coqRestrictedPADirectEqualityEliminationMotiveChildTerm
    coqRestrictedPADirectEqualityEliminationWitnessContextTerm
    coqRestrictedPADirectEqualityEliminationSourceInstanceTerm.

Definition coqRestrictedPADirectEqualityEliminationChildInterfaceLawTemplate
    (operationFact displayedEndpoint result : TemplateFormula)
    : TemplateFormula :=
  tfImp coqRestrictedPADirectEqualityEliminationDeepRestrictedTemplate
    (tfImp coqRestrictedPADirectEqualityEliminationCodeEqualityTemplate
      (tfImp operationFact
        (tfImp displayedEndpoint
          (tfImp coqRestrictedPADirectEqualityEliminationDeepAdmissibleTemplate
            result)))).

Definition
    coqRestrictedPADirectEqualityEliminationEqualityChildInterfaceLawTemplate
    : TemplateFormula :=
  coqRestrictedPADirectEqualityEliminationChildInterfaceLawTemplate
    coqRestrictedPADirectEqualityEliminationEqualityFormulaCodeTemplate
    coqRestrictedPADirectEqualityEliminationEqualityChildEndpointTemplate
    coqRestrictedPADirectEqualityEliminationEqualityChildInterfaceResultTemplate.

Definition
    coqRestrictedPADirectEqualityEliminationMotiveChildInterfaceLawTemplate
    : TemplateFormula :=
  coqRestrictedPADirectEqualityEliminationChildInterfaceLawTemplate
    coqRestrictedPADirectEqualityEliminationSourceSubstitutionTemplate
    coqRestrictedPADirectEqualityEliminationMotiveChildEndpointTemplate
    coqRestrictedPADirectEqualityEliminationMotiveChildInterfaceResultTemplate.

Definition coqRestrictedPADirectEqualityEliminationDynamicTruthLawTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectEqualityEliminationTargetSubstitutionTemplate
    (tfImp
      coqRestrictedPADirectEqualityEliminationEqualityFormulaCodeTemplate
      (tfImp coqRestrictedPADirectEqualityEliminationSourceSubstitutionTemplate
        (tfImp
          coqRestrictedPADirectEqualityEliminationEqualityChildTruthTemplate
          (tfImp
            coqRestrictedPADirectEqualityEliminationMotiveChildTruthTemplate
            coqRestrictedPADirectEqualityEliminationOuterConclusionTruthTemplate)))).

Definition RawCoqRestrictedPADirectEqualityEliminationChildInterfaceRootsAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (context : TemplateContext) : Prop :=
  (exists equalityRoot : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation context)
      (rawTemplateFormula translation
        coqRestrictedPADirectEqualityEliminationEqualityChildInterfaceLawTemplate)
      equalityRoot) /\
  (exists motiveRoot : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation context)
      (rawTemplateFormula translation
        coqRestrictedPADirectEqualityEliminationMotiveChildInterfaceLawTemplate)
      motiveRoot).

Arguments RawCoqRestrictedPADirectEqualityEliminationChildInterfaceRootsAt
  M translation context : clear implicits.

Definition RawCoqRestrictedPADirectEqualityEliminationDynamicTruthLawRootAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (context : TemplateContext) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation context)
      (rawTemplateFormula translation
        coqRestrictedPADirectEqualityEliminationDynamicTruthLawTemplate)
      root.

Arguments RawCoqRestrictedPADirectEqualityEliminationDynamicTruthLawRootAt
  M translation context : clear implicits.

Definition RawCoqRestrictedPADirectStrongStepEqualityEliminationSemanticRoots
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop :=
  let translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs in
  let ready :=
    coqRestrictedPADirectStrongStepEqualityEliminationReadyContext tail in
  RawCoqRestrictedPADirectEqualityEliminationChildInterfaceRootsAt
      M translation ready /\
  RawCoqRestrictedPADirectEqualityEliminationDynamicTruthLawRootAt
      M translation ready.

Arguments RawCoqRestrictedPADirectStrongStepEqualityEliminationSemanticRoots
  M hPA inputs tail : clear implicits.

(** Apply either recursive-child law to precisely its operation fact and
    displayed endpoint.  This is structural modus ponens only; the law root
    itself remains the honest semantic boundary. *)
Theorem
    raw_codedPALocalProofOf_coqRestrictedPADirectEqualityEliminationChildInterface :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (translation : RawCodedTemplateTranslation M) context
    operationFact displayedEndpoint result lawRoot restrictedRoot
    codeEqualityRoot operationFactRoot displayedEndpointRoot admissibleRoot,
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation context)
    (rawTemplateFormula translation
      (coqRestrictedPADirectEqualityEliminationChildInterfaceLawTemplate
        operationFact displayedEndpoint result)) lawRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation context)
    (rawTemplateFormula translation
      coqRestrictedPADirectEqualityEliminationDeepRestrictedTemplate)
    restrictedRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation context)
    (rawTemplateFormula translation
      coqRestrictedPADirectEqualityEliminationCodeEqualityTemplate)
    codeEqualityRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation context)
    (rawTemplateFormula translation operationFact) operationFactRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation context)
    (rawTemplateFormula translation displayedEndpoint) displayedEndpointRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation context)
    (rawTemplateFormula translation
      coqRestrictedPADirectEqualityEliminationDeepAdmissibleTemplate)
    admissibleRoot ->
  exists resultRoot : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation context)
      (rawTemplateFormula translation result) resultRoot.
Proof.
  intros M hPA translation context operationFact displayedEndpoint result
    lawRoot restrictedRoot codeEqualityRoot operationFactRoot
    displayedEndpointRoot admissibleRoot hlaw hrestricted hcodeEquality
    hoperationFact hdisplayedEndpoint hadmissible.
  unfold coqRestrictedPADirectEqualityEliminationChildInterfaceLawTemplate
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
      M hPA translation context _ _ _ operationFactRoot
      h2 hoperationFact) as h3.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation context _ _ _ displayedEndpointRoot
      h3 hdisplayedEndpoint) as h4.
  eexists.
  exact
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation context _ _ _ admissibleRoot h4 hadmissible).
Qed.

(** ------------------------------------------------------------------
    Constructor-local conclusion in the fully introduced ready context. *)

Theorem
    raw_codedPALocalProofOf_coqRestrictedPADirectEqualityEliminationConclusionAt :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (translation : RawCodedTemplateTranslation M) tail,
  RawCoqRestrictedPADirectEqualityEliminationChildInterfaceRootsAt
    M translation
    (coqRestrictedPADirectStrongStepEqualityEliminationReadyContext tail) ->
  RawCoqRestrictedPADirectEqualityEliminationDynamicTruthLawRootAt
    M translation
    (coqRestrictedPADirectStrongStepEqualityEliminationReadyContext tail) ->
  exists conclusionRoot : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation
        (coqRestrictedPADirectStrongStepEqualityEliminationReadyContext tail))
      (rawTemplateFormula translation
        coqRestrictedPADirectEqualityEliminationOuterConclusionTruthTemplate)
      conclusionRoot.
Proof.
  intros M hPA translation tail
    [[equalityLawRoot hequalityLaw] [motiveLawRoot hmotiveLaw]]
    [truthLawRoot htruthLaw].
  set (ready :=
    coqRestrictedPADirectStrongStepEqualityEliminationReadyContext tail).
  set (readyCode := rawTemplateContextCode translation ready).
  assert (hcase :
    In coqRestrictedPADirectEqualityEliminationCaseTemplate ready).
  {
    unfold ready.
    apply coqRestrictedPADirectEqualityElimination_ready_case_in.
  }

  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectEqualityEliminationCodeEqualityRootAt ready)
    (proj1
      (coqRestrictedPADirectEqualityEliminationCodeEqualityRootAt_valid
        ready hcase))) as hcodeEquality.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectEqualityEliminationTargetSubstitutionRootAt ready)
    (proj1
      (coqRestrictedPADirectEqualityEliminationTargetSubstitutionRootAt_valid
        ready hcase))) as htargetSubstitution.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectEqualityEliminationEqualityFormulaCodeRootAt ready)
    (proj1
      (coqRestrictedPADirectEqualityEliminationEqualityFormulaCodeRootAt_valid
        ready hcase))) as hequalityFormulaCode.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectEqualityEliminationEqualityChildEndpointRootAt
      ready)
    (proj1
      (coqRestrictedPADirectEqualityEliminationEqualityChildEndpointRootAt_valid
        ready hcase))) as hequalityDisplayedEndpoint.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectEqualityEliminationSourceSubstitutionRootAt ready)
    (proj1
      (coqRestrictedPADirectEqualityEliminationSourceSubstitutionRootAt_valid
        ready hcase))) as hsourceSubstitution.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectEqualityEliminationMotiveChildEndpointRootAt ready)
    (proj1
      (coqRestrictedPADirectEqualityEliminationMotiveChildEndpointRootAt_valid
        ready hcase))) as hmotiveDisplayedEndpoint.

  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAssumption
      M hPA translation ready
      coqRestrictedPADirectEqualityEliminationDeepRestrictedTemplate
      (coqRestrictedPADirectEqualityElimination_ready_restricted_in tail))
    as hrestricted.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAssumption
      M hPA translation ready
      coqRestrictedPADirectEqualityEliminationDeepAdmissibleTemplate
      (coqRestrictedPADirectEqualityElimination_ready_admissible_in tail))
    as hadmissible.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAssumption
      M hPA translation ready
      coqRestrictedPADirectEqualityEliminationDeepStrongPrefixTemplate
      (coqRestrictedPADirectEqualityElimination_ready_prefix_in tail))
    as hprefix.

  (** Both children retain the parent endpoint context [#7].  The same
      equality-transported context-truth root is consequently valid for both;
      only their conclusion arguments differ in the strong-prefix opening. *)
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt ready)
    (proj1
      (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt_valid
        ready
        (coqRestrictedPADirectEqualityElimination_ready_endpoint_in tail)
        (coqRestrictedPADirectEqualityElimination_ready_context_truth_in
          tail)))) as hwitnessContextTruth.

  (** Normalize compiled finite roots at the local context boundary.  The
      [lazymatch] captures each concrete proof code, avoiding accidental
      unfolding of the large endpoint disjunction. *)
  lazymatch type of hcodeEquality with
  | RawCodedPALocalProofOf _ _ _ ?root =>
      change (RawCodedPALocalProofOf M readyCode
        (rawTemplateFormula translation
          coqRestrictedPADirectEqualityEliminationCodeEqualityTemplate)
        root) in hcodeEquality
  end.
  lazymatch type of htargetSubstitution with
  | RawCodedPALocalProofOf _ _ _ ?root =>
      change (RawCodedPALocalProofOf M readyCode
        (rawTemplateFormula translation
          coqRestrictedPADirectEqualityEliminationTargetSubstitutionTemplate)
        root) in htargetSubstitution
  end.
  lazymatch type of hequalityFormulaCode with
  | RawCodedPALocalProofOf _ _ _ ?root =>
      change (RawCodedPALocalProofOf M readyCode
        (rawTemplateFormula translation
          coqRestrictedPADirectEqualityEliminationEqualityFormulaCodeTemplate)
        root) in hequalityFormulaCode
  end.
  lazymatch type of hequalityDisplayedEndpoint with
  | RawCodedPALocalProofOf _ _ _ ?root =>
      change (RawCodedPALocalProofOf M readyCode
        (rawTemplateFormula translation
          coqRestrictedPADirectEqualityEliminationEqualityChildEndpointTemplate)
        root) in hequalityDisplayedEndpoint
  end.
  lazymatch type of hsourceSubstitution with
  | RawCodedPALocalProofOf _ _ _ ?root =>
      change (RawCodedPALocalProofOf M readyCode
        (rawTemplateFormula translation
          coqRestrictedPADirectEqualityEliminationSourceSubstitutionTemplate)
        root) in hsourceSubstitution
  end.
  lazymatch type of hmotiveDisplayedEndpoint with
  | RawCodedPALocalProofOf _ _ _ ?root =>
      change (RawCodedPALocalProofOf M readyCode
        (rawTemplateFormula translation
          coqRestrictedPADirectEqualityEliminationMotiveChildEndpointTemplate)
        root) in hmotiveDisplayedEndpoint
  end.
  lazymatch type of hrestricted with
  | RawCodedPALocalProofOf _ _ _ ?root =>
      change (RawCodedPALocalProofOf M readyCode
        (rawTemplateFormula translation
          coqRestrictedPADirectEqualityEliminationDeepRestrictedTemplate)
        root) in hrestricted
  end.
  lazymatch type of hadmissible with
  | RawCodedPALocalProofOf _ _ _ ?root =>
      change (RawCodedPALocalProofOf M readyCode
        (rawTemplateFormula translation
          coqRestrictedPADirectEqualityEliminationDeepAdmissibleTemplate)
        root) in hadmissible
  end.
  lazymatch type of hprefix with
  | RawCodedPALocalProofOf _ _ _ ?root =>
      change (RawCodedPALocalProofOf M readyCode
        (rawTemplateFormula translation
          coqRestrictedPADirectEqualityEliminationDeepStrongPrefixTemplate)
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
    (raw_codedPALocalProofOf_coqRestrictedPADirectEqualityEliminationChildInterface
      M hPA translation ready
      coqRestrictedPADirectEqualityEliminationEqualityFormulaCodeTemplate
      coqRestrictedPADirectEqualityEliminationEqualityChildEndpointTemplate
      coqRestrictedPADirectEqualityEliminationEqualityChildInterfaceResultTemplate
      equalityLawRoot _ _ _ _ _
      hequalityLaw hrestricted hcodeEquality hequalityFormulaCode
      hequalityDisplayedEndpoint hadmissible)
    as [equalityInterfaceRoot hequalityInterface].
  destruct
    (raw_codedPALocalProofOf_coqRestrictedPADirectEqualityEliminationChildInterface
      M hPA translation ready
      coqRestrictedPADirectEqualityEliminationSourceSubstitutionTemplate
      coqRestrictedPADirectEqualityEliminationMotiveChildEndpointTemplate
      coqRestrictedPADirectEqualityEliminationMotiveChildInterfaceResultTemplate
      motiveLawRoot _ _ _ _ _
      hmotiveLaw hrestricted hcodeEquality hsourceSubstitution
      hmotiveDisplayedEndpoint hadmissible)
    as [motiveInterfaceRoot hmotiveInterface].

  assert (hequalityContextTruth : RawCodedPALocalProofOf M readyCode
    (rawTemplateFormula translation
      coqRestrictedPADirectEqualityEliminationEqualityChildContextTruthTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt ready))).
  {
    rewrite
      coqRestrictedPADirectEqualityElimination_equality_context_truth_agreement.
    exact hwitnessContextTruth.
  }
  assert (hmotiveContextTruth : RawCodedPALocalProofOf M readyCode
    (rawTemplateFormula translation
      coqRestrictedPADirectEqualityEliminationMotiveChildContextTruthTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt ready))).
  {
    rewrite
      coqRestrictedPADirectEqualityElimination_motive_context_truth_agreement.
    exact hwitnessContextTruth.
  }

  (** The generic recursive application opens the predicate's conclusion
      binder at [#3] and [#0] respectively.  These two explicit calls are the
      conclusion transports promised by the constructor endpoints. *)
  destruct
    (raw_codedPALocalProofOf_coqRestrictedPADirectAndIntroductionChildTruth
      M hPA translation ready
      coqRestrictedPADirectEqualityEliminationEqualityChildTerm
      coqRestrictedPADirectEqualityEliminationWitnessContextTerm
      coqRestrictedPADirectEqualityEliminationEqualityFormulaTerm
      equalityInterfaceRoot _ _
      hequalityInterface hprefix hequalityContextTruth)
    as [equalityTruthRoot hequalityTruth].
  destruct
    (raw_codedPALocalProofOf_coqRestrictedPADirectAndIntroductionChildTruth
      M hPA translation ready
      coqRestrictedPADirectEqualityEliminationMotiveChildTerm
      coqRestrictedPADirectEqualityEliminationWitnessContextTerm
      coqRestrictedPADirectEqualityEliminationSourceInstanceTerm
      motiveInterfaceRoot _ _
      hmotiveInterface hprefix hmotiveContextTruth)
    as [motiveTruthRoot hmotiveTruth].

  unfold coqRestrictedPADirectEqualityEliminationDynamicTruthLawTemplate
    in htruthLaw.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation ready _ _ truthLawRoot _
      htruthLaw htargetSubstitution) as htruthAfterTargetSubstitution.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation ready _ _ _ _
      htruthAfterTargetSubstitution hequalityFormulaCode)
    as htruthAfterEqualityFormula.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation ready _ _ _ _
      htruthAfterEqualityFormula hsourceSubstitution)
    as htruthAfterSourceSubstitution.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation ready _ _ _ equalityTruthRoot
      htruthAfterSourceSubstitution hequalityTruth)
    as htruthAfterEqualityChild.
  eexists.
  exact
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation ready _ _ _ motiveTruthRoot
      htruthAfterEqualityChild hmotiveTruth).
Qed.

(** ------------------------------------------------------------------
    Exact [rawCoqRuleEqualityElimination] slot of the public dispatcher. *)

Theorem
    raw_coqRestrictedPADirectStrongStepEqualityEliminationCaseImplicationRoot :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectStrongStepEqualityEliminationSemanticRoots
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
            rawCoqRuleEqualityElimination
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
    coqRestrictedPADirectStrongStepEqualityEliminationBaseContext tail).
  set (caseContext :=
    coqRestrictedPADirectStrongStepEqualityEliminationCaseContext tail).
  set (admissibleContext :=
    coqRestrictedPADirectStrongStepEqualityEliminationAdmissibleContext tail).
  set (readyContext :=
    coqRestrictedPADirectStrongStepEqualityEliminationReadyContext tail).
  unfold RawCoqRestrictedPADirectStrongStepEqualityEliminationSemanticRoots
    in hsemantic.
  cbn zeta in hsemantic.
  destruct hsemantic as [hchildInterfaces htruthLaw].
  destruct
    (raw_codedPALocalProofOf_coqRestrictedPADirectEqualityEliminationConclusionAt
      M hPA translation tail hchildInterfaces htruthLaw)
    as [conclusionRoot hconclusion].

  set (readyCode := rawTemplateContextCode translation readyContext).
  set (admissibleCode :=
    rawTemplateContextCode translation admissibleContext).
  set (caseCode := rawTemplateContextCode translation caseContext).
  set (baseCode := rawTemplateContextCode translation baseContext).

  set (contextImpRoot := rawProofImpIRoot M admissibleCode
    (rawTemplateFormula translation
      coqRestrictedPADirectEqualityEliminationOuterContextTruthTemplate)
    (rawTemplateFormula translation
      coqRestrictedPADirectEqualityEliminationOuterConclusionTruthTemplate)
    conclusionRoot).
  assert (hcontextImp : RawCodedPALocalProofOf M admissibleCode
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectEqualityEliminationOuterContextTruthTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectEqualityEliminationOuterConclusionTruthTemplate))
    contextImpRoot).
  {
    unfold contextImpRoot.
    apply (raw_codedPALocalProofOf_impI M hPA admissibleCode
      (rawTemplateFormula translation
        coqRestrictedPADirectEqualityEliminationOuterContextTruthTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectEqualityEliminationOuterConclusionTruthTemplate)
      conclusionRoot).
    change (RawCodedPALocalProofOf M readyCode
      (rawTemplateFormula translation
        coqRestrictedPADirectEqualityEliminationOuterConclusionTruthTemplate)
      conclusionRoot).
    change (RawCodedPALocalProofOf M
      (rawTemplateContextCode translation readyContext)
      (rawTemplateFormula translation
        coqRestrictedPADirectEqualityEliminationOuterConclusionTruthTemplate)
      conclusionRoot).
    unfold readyContext.
    exact hconclusion.
  }

  set (admissibleImpRoot := rawProofImpIRoot M caseCode
    (rawTemplateFormula translation
      coqRestrictedPADirectEqualityEliminationDeepAdmissibleTemplate)
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectEqualityEliminationOuterContextTruthTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectEqualityEliminationOuterConclusionTruthTemplate))
    contextImpRoot).
  assert (hadmissibleImp : RawCodedPALocalProofOf M caseCode
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectEqualityEliminationDeepAdmissibleTemplate)
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          coqRestrictedPADirectEqualityEliminationOuterContextTruthTemplate)
        (rawTemplateFormula translation
          coqRestrictedPADirectEqualityEliminationOuterConclusionTruthTemplate)))
    admissibleImpRoot).
  {
    unfold admissibleImpRoot.
    apply (raw_codedPALocalProofOf_impI M hPA caseCode
      (rawTemplateFormula translation
        coqRestrictedPADirectEqualityEliminationDeepAdmissibleTemplate)
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          coqRestrictedPADirectEqualityEliminationOuterContextTruthTemplate)
        (rawTemplateFormula translation
          coqRestrictedPADirectEqualityEliminationOuterConclusionTruthTemplate))
      contextImpRoot).
    exact hcontextImp.
  }

  set (caseImpRoot := rawProofImpIRoot M baseCode
    (rawTemplateFormula translation
      coqRestrictedPADirectEqualityEliminationCaseTemplate)
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectEqualityEliminationDeepAdmissibleTemplate)
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          coqRestrictedPADirectEqualityEliminationOuterContextTruthTemplate)
        (rawTemplateFormula translation
          coqRestrictedPADirectEqualityEliminationOuterConclusionTruthTemplate)))
    admissibleImpRoot).
  exists caseImpRoot.
  rewrite coqRestrictedPADirectEqualityElimination_remaining_shape.
  change (RawCodedPALocalProofOf M baseCode
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectEqualityEliminationCaseTemplate)
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          coqRestrictedPADirectEqualityEliminationDeepAdmissibleTemplate)
        (rawFormulaImpCode M
          (rawTemplateFormula translation
            coqRestrictedPADirectEqualityEliminationOuterContextTruthTemplate)
          (rawTemplateFormula translation
            coqRestrictedPADirectEqualityEliminationOuterConclusionTruthTemplate))))
    caseImpRoot).
  unfold caseImpRoot.
  apply (raw_codedPALocalProofOf_impI M hPA baseCode
    (rawTemplateFormula translation
      coqRestrictedPADirectEqualityEliminationCaseTemplate)
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectEqualityEliminationDeepAdmissibleTemplate)
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          coqRestrictedPADirectEqualityEliminationOuterContextTruthTemplate)
        (rawTemplateFormula translation
          coqRestrictedPADirectEqualityEliminationOuterConclusionTruthTemplate)))
    admissibleImpRoot).
  exact hadmissibleImp.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationCase.
