(**
  The exact conjunction-introduction branch of the direct strong step.

  The branch has two genuine recursive children.  This file keeps the
  proof-theoretic work visible:

  - all four fields of the right-associated constructor case are projected;
  - the inherited strong-prefix hypothesis is specialized to each child;
  - the four endpoint binders of the child soundness predicate are
    instantiated in their source order;
  - the child restrictedness, endpoint, admissibility, and context-truth
    premises are supplied one by one; and
  - the final [case -> admissible -> context truth -> conclusion truth]
    implication is introduced in exactly the order required by the public
    strong-step shell.

  Two genuinely semantic interfaces remain explicit.  For each child a
  recursive-child operation supplies descent, restrictedness, and inherited
  admissibility from the displayed constructor data.  A dynamic conjunction
  truth operation combines the two child truth certificates.  Neither
  residual is a constructor-branch root, a strong-step root, or an assumed
  proof of the requested conclusion.
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
  RawCodedProofAllEConstructor
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofConjunction
  RawCodedPALocalProofPropositionalRules
  RawCodedPALocalProofUniversalElimination
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateDirectStructuralTranslation
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixInductionShell
  RawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier
  RawCodedRestrictedPADerivationSoundnessDirectStrongStepShell
  RawCodedRestrictedPADerivationSoundnessDirectAssumptionCase.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase.

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
Import PABoundedRawCodedProofAllEConstructor.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofConjunction.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedPALocalProofUniversalElimination.
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

(** ------------------------------------------------------------------
    Literal endpoint witnesses at depth eight. *)

Definition coqRestrictedPADirectAndIntroductionParentRootTerm
    : TemplateTerm := embedPATerm (liftTerm 8 (tVar 4)).

Definition coqRestrictedPADirectAndIntroductionWitnessContextTerm
    : TemplateTerm := ttVar 7.

Definition coqRestrictedPADirectAndIntroductionOuterConclusionTerm
    : TemplateTerm := embedPATerm (liftTerm 8 (tVar 2)).

Definition coqRestrictedPADirectAndIntroductionLeftFormulaTerm
    : TemplateTerm := ttVar 6.

Definition coqRestrictedPADirectAndIntroductionRightFormulaTerm
    : TemplateTerm := ttVar 5.

Definition coqRestrictedPADirectAndIntroductionLeftChildTerm
    : TemplateTerm := ttVar 2.

Definition coqRestrictedPADirectAndIntroductionRightChildTerm
    : TemplateTerm := ttVar 1.

Definition coqRestrictedPADirectAndIntroductionAssignmentCodeTerm
    : TemplateTerm := ttVar 9.

Definition coqRestrictedPADirectAndIntroductionAssignmentStepTerm
    : TemplateTerm := ttVar 8.

Definition coqRestrictedPADirectAndIntroductionCodeEqualityTemplate
    : TemplateFormula :=
  embedPAFormula
    (pEq (liftTerm 8 (tVar 4))
      (proofAndICodeTerm (tVar 7) (tVar 6) (tVar 5)
        (tVar 2) (tVar 1))).

Definition coqRestrictedPADirectAndIntroductionFormulaAndTemplate
    : TemplateFormula :=
  embedPAFormula
    (formulaAndCodeTermAt (liftTerm 8 (tVar 2))
      (tVar 6) (tVar 5)).

Definition coqRestrictedPADirectAndIntroductionLeftEndpointTemplate
    : TemplateFormula :=
  embedPAFormula
    (proofEndpointTermAt (tVar 2) (tVar 7) (tVar 6)).

Definition coqRestrictedPADirectAndIntroductionRightEndpointTemplate
    : TemplateFormula :=
  embedPAFormula
    (proofEndpointTermAt (tVar 1) (tVar 7) (tVar 5)).

Definition coqRestrictedPADirectAndIntroductionTerminalTruthTemplate
    : TemplateFormula := embedPAFormula (pEq tZero tZero).

Definition coqRestrictedPADirectAndIntroductionRightEndpointSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectAndIntroductionRightEndpointTemplate
    coqRestrictedPADirectAndIntroductionTerminalTruthTemplate.

Definition coqRestrictedPADirectAndIntroductionLeftEndpointSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectAndIntroductionLeftEndpointTemplate
    coqRestrictedPADirectAndIntroductionRightEndpointSuffixTemplate.

Definition coqRestrictedPADirectAndIntroductionFormulaAndSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectAndIntroductionFormulaAndTemplate
    coqRestrictedPADirectAndIntroductionLeftEndpointSuffixTemplate.

Definition coqRestrictedPADirectAndIntroductionCaseTemplate
    : TemplateFormula :=
  rawCoqRestrictedPAProofRuleCaseTemplate rawCoqRuleAndIntroduction
    (liftTerm 8 (tVar 4)) (tVar 7) (liftTerm 8 (tVar 2))
    (tVar 6) (tVar 5) (tVar 4) (tVar 3)
    (tVar 2) (tVar 1) (tVar 0).

Lemma coqRestrictedPADirectAndIntroduction_case_shape :
  coqRestrictedPADirectAndIntroductionCaseTemplate =
  tfAnd coqRestrictedPADirectAndIntroductionCodeEqualityTemplate
    coqRestrictedPADirectAndIntroductionFormulaAndSuffixTemplate.
Proof. reflexivity. Qed.

(** ------------------------------------------------------------------
    The inherited strong-prefix formula and its two exact instances.

    Formula destructors are used only to name successive universal and
    implication bodies.  Shape lemmas below verify by computation that the
    names reduce to the intended soundness premises.  This avoids manually
    duplicating the delicate binder-renaming calculation. *)

Definition coqRestrictedPADirectTemplateAllBody
    (formula : TemplateFormula) : TemplateFormula :=
  match formula with
  | tfAll body => body
  | _ => tfBot
  end.

Definition coqRestrictedPADirectTemplateImpAntecedent
    (formula : TemplateFormula) : TemplateFormula :=
  match formula with
  | tfImp antecedent _ => antecedent
  | _ => tfBot
  end.

Definition coqRestrictedPADirectTemplateImpConsequent
    (formula : TemplateFormula) : TemplateFormula :=
  match formula with
  | tfImp _ consequent => consequent
  | _ => tfBot
  end.

Definition coqRestrictedPADirectAndIntroductionDeepStrongPrefixTemplate
    : TemplateFormula :=
  rawCoqTemplateRenameN 8
    (rawCoqTemplateRenameN 4
      coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate).

Definition coqRestrictedPADirectAndIntroductionDeepStrongPrefixBodyTemplate
    : TemplateFormula :=
  coqRestrictedPADirectTemplateAllBody
    coqRestrictedPADirectAndIntroductionDeepStrongPrefixTemplate.

Definition coqRestrictedPADirectAndIntroductionChildGuardedTemplate
    (child : TemplateTerm) : TemplateFormula :=
  templateFormulaOpen child
    coqRestrictedPADirectAndIntroductionDeepStrongPrefixBodyTemplate.

Definition coqRestrictedPADirectAndIntroductionChildBelowTemplate
    (child : TemplateTerm) : TemplateFormula :=
  coqRestrictedPADirectTemplateImpAntecedent
    (coqRestrictedPADirectAndIntroductionChildGuardedTemplate child).

Definition coqRestrictedPADirectAndIntroductionChildPredicateTemplate
    (child : TemplateTerm) : TemplateFormula :=
  coqRestrictedPADirectTemplateImpConsequent
    (coqRestrictedPADirectAndIntroductionChildGuardedTemplate child).

Definition coqRestrictedPADirectAndIntroductionChildAfterContextTemplate
    (child context : TemplateTerm) : TemplateFormula :=
  templateFormulaOpen context
    (coqRestrictedPADirectTemplateAllBody
      (coqRestrictedPADirectAndIntroductionChildPredicateTemplate child)).

Definition coqRestrictedPADirectAndIntroductionChildAfterConclusionTemplate
    (child context conclusion : TemplateTerm) : TemplateFormula :=
  templateFormulaOpen conclusion
    (coqRestrictedPADirectTemplateAllBody
      (coqRestrictedPADirectAndIntroductionChildAfterContextTemplate
        child context)).

Definition coqRestrictedPADirectAndIntroductionChildAfterAssignmentCodeTemplate
    (child context conclusion assignmentCode : TemplateTerm)
    : TemplateFormula :=
  templateFormulaOpen assignmentCode
    (coqRestrictedPADirectTemplateAllBody
      (coqRestrictedPADirectAndIntroductionChildAfterConclusionTemplate
        child context conclusion)).

Definition coqRestrictedPADirectAndIntroductionChildReadyTemplate
    (child context conclusion assignmentCode assignmentStep : TemplateTerm)
    : TemplateFormula :=
  templateFormulaOpen assignmentStep
    (coqRestrictedPADirectTemplateAllBody
      (coqRestrictedPADirectAndIntroductionChildAfterAssignmentCodeTemplate
        child context conclusion assignmentCode)).

Definition coqRestrictedPADirectAndIntroductionChildRestrictedTemplate
    (child context conclusion : TemplateTerm) : TemplateFormula :=
  coqRestrictedPADirectTemplateImpAntecedent
    (coqRestrictedPADirectAndIntroductionChildReadyTemplate
      child context conclusion
      coqRestrictedPADirectAndIntroductionAssignmentCodeTerm
      coqRestrictedPADirectAndIntroductionAssignmentStepTerm).

Definition coqRestrictedPADirectAndIntroductionChildAfterRestrictedTemplate
    (child context conclusion : TemplateTerm) : TemplateFormula :=
  coqRestrictedPADirectTemplateImpConsequent
    (coqRestrictedPADirectAndIntroductionChildReadyTemplate
      child context conclusion
      coqRestrictedPADirectAndIntroductionAssignmentCodeTerm
      coqRestrictedPADirectAndIntroductionAssignmentStepTerm).

Definition coqRestrictedPADirectAndIntroductionChildEndpointTemplate
    (child context conclusion : TemplateTerm) : TemplateFormula :=
  coqRestrictedPADirectTemplateImpAntecedent
    (coqRestrictedPADirectAndIntroductionChildAfterRestrictedTemplate
      child context conclusion).

Definition coqRestrictedPADirectAndIntroductionChildAfterEndpointTemplate
    (child context conclusion : TemplateTerm) : TemplateFormula :=
  coqRestrictedPADirectTemplateImpConsequent
    (coqRestrictedPADirectAndIntroductionChildAfterRestrictedTemplate
      child context conclusion).

Definition coqRestrictedPADirectAndIntroductionChildAdmissibleTemplate
    (child context conclusion : TemplateTerm) : TemplateFormula :=
  coqRestrictedPADirectTemplateImpAntecedent
    (coqRestrictedPADirectAndIntroductionChildAfterEndpointTemplate
      child context conclusion).

Definition coqRestrictedPADirectAndIntroductionChildAfterAdmissibleTemplate
    (child context conclusion : TemplateTerm) : TemplateFormula :=
  coqRestrictedPADirectTemplateImpConsequent
    (coqRestrictedPADirectAndIntroductionChildAfterEndpointTemplate
      child context conclusion).

Definition coqRestrictedPADirectAndIntroductionChildContextTruthTemplate
    (child context conclusion : TemplateTerm) : TemplateFormula :=
  coqRestrictedPADirectTemplateImpAntecedent
    (coqRestrictedPADirectAndIntroductionChildAfterAdmissibleTemplate
      child context conclusion).

Definition coqRestrictedPADirectAndIntroductionChildTruthTemplate
    (child context conclusion : TemplateTerm) : TemplateFormula :=
  coqRestrictedPADirectTemplateImpConsequent
    (coqRestrictedPADirectAndIntroductionChildAfterAdmissibleTemplate
      child context conclusion).

Definition coqRestrictedPADirectAndIntroductionLeftBelowTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildBelowTemplate
    coqRestrictedPADirectAndIntroductionLeftChildTerm.

Definition coqRestrictedPADirectAndIntroductionRightBelowTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildBelowTemplate
    coqRestrictedPADirectAndIntroductionRightChildTerm.

Definition coqRestrictedPADirectAndIntroductionLeftRestrictedTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildRestrictedTemplate
    coqRestrictedPADirectAndIntroductionLeftChildTerm
    coqRestrictedPADirectAndIntroductionWitnessContextTerm
    coqRestrictedPADirectAndIntroductionLeftFormulaTerm.

Definition coqRestrictedPADirectAndIntroductionRightRestrictedTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildRestrictedTemplate
    coqRestrictedPADirectAndIntroductionRightChildTerm
    coqRestrictedPADirectAndIntroductionWitnessContextTerm
    coqRestrictedPADirectAndIntroductionRightFormulaTerm.

Definition coqRestrictedPADirectAndIntroductionLeftAdmissibleTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildAdmissibleTemplate
    coqRestrictedPADirectAndIntroductionLeftChildTerm
    coqRestrictedPADirectAndIntroductionWitnessContextTerm
    coqRestrictedPADirectAndIntroductionLeftFormulaTerm.

Definition coqRestrictedPADirectAndIntroductionRightAdmissibleTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildAdmissibleTemplate
    coqRestrictedPADirectAndIntroductionRightChildTerm
    coqRestrictedPADirectAndIntroductionWitnessContextTerm
    coqRestrictedPADirectAndIntroductionRightFormulaTerm.

Definition coqRestrictedPADirectAndIntroductionLeftPredicateEndpointTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildEndpointTemplate
    coqRestrictedPADirectAndIntroductionLeftChildTerm
    coqRestrictedPADirectAndIntroductionWitnessContextTerm
    coqRestrictedPADirectAndIntroductionLeftFormulaTerm.

Definition coqRestrictedPADirectAndIntroductionRightPredicateEndpointTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildEndpointTemplate
    coqRestrictedPADirectAndIntroductionRightChildTerm
    coqRestrictedPADirectAndIntroductionWitnessContextTerm
    coqRestrictedPADirectAndIntroductionRightFormulaTerm.

Definition coqRestrictedPADirectAndIntroductionLeftPredicateContextTruthTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildContextTruthTemplate
    coqRestrictedPADirectAndIntroductionLeftChildTerm
    coqRestrictedPADirectAndIntroductionWitnessContextTerm
    coqRestrictedPADirectAndIntroductionLeftFormulaTerm.

Definition coqRestrictedPADirectAndIntroductionRightPredicateContextTruthTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildContextTruthTemplate
    coqRestrictedPADirectAndIntroductionRightChildTerm
    coqRestrictedPADirectAndIntroductionWitnessContextTerm
    coqRestrictedPADirectAndIntroductionRightFormulaTerm.

Definition coqRestrictedPADirectAndIntroductionWitnessContextTruthTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAssumptionWitnessContextTruthTemplate.

Definition coqRestrictedPADirectAndIntroductionLeftTruthTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildTruthTemplate
    coqRestrictedPADirectAndIntroductionLeftChildTerm
    coqRestrictedPADirectAndIntroductionWitnessContextTerm
    coqRestrictedPADirectAndIntroductionLeftFormulaTerm.

Definition coqRestrictedPADirectAndIntroductionRightTruthTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildTruthTemplate
    coqRestrictedPADirectAndIntroductionRightChildTerm
    coqRestrictedPADirectAndIntroductionWitnessContextTerm
    coqRestrictedPADirectAndIntroductionRightFormulaTerm.

Lemma coqRestrictedPADirectAndIntroduction_deep_prefix_shape :
  coqRestrictedPADirectAndIntroductionDeepStrongPrefixTemplate =
  tfAll coqRestrictedPADirectAndIntroductionDeepStrongPrefixBodyTemplate.
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectAndIntroduction_left_guarded_shape :
  coqRestrictedPADirectAndIntroductionChildGuardedTemplate
    coqRestrictedPADirectAndIntroductionLeftChildTerm =
  tfImp coqRestrictedPADirectAndIntroductionLeftBelowTemplate
    (coqRestrictedPADirectAndIntroductionChildPredicateTemplate
      coqRestrictedPADirectAndIntroductionLeftChildTerm).
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectAndIntroduction_right_guarded_shape :
  coqRestrictedPADirectAndIntroductionChildGuardedTemplate
    coqRestrictedPADirectAndIntroductionRightChildTerm =
  tfImp coqRestrictedPADirectAndIntroductionRightBelowTemplate
    (coqRestrictedPADirectAndIntroductionChildPredicateTemplate
      coqRestrictedPADirectAndIntroductionRightChildTerm).
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectAndIntroduction_left_ready_shape :
  coqRestrictedPADirectAndIntroductionChildReadyTemplate
    coqRestrictedPADirectAndIntroductionLeftChildTerm
    coqRestrictedPADirectAndIntroductionWitnessContextTerm
    coqRestrictedPADirectAndIntroductionLeftFormulaTerm
    coqRestrictedPADirectAndIntroductionAssignmentCodeTerm
  coqRestrictedPADirectAndIntroductionAssignmentStepTerm =
  tfImp coqRestrictedPADirectAndIntroductionLeftRestrictedTemplate
    (tfImp
      coqRestrictedPADirectAndIntroductionLeftPredicateEndpointTemplate
      (tfImp coqRestrictedPADirectAndIntroductionLeftAdmissibleTemplate
        (tfImp
          coqRestrictedPADirectAndIntroductionLeftPredicateContextTruthTemplate
          coqRestrictedPADirectAndIntroductionLeftTruthTemplate))).
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectAndIntroduction_right_ready_shape :
  coqRestrictedPADirectAndIntroductionChildReadyTemplate
    coqRestrictedPADirectAndIntroductionRightChildTerm
    coqRestrictedPADirectAndIntroductionWitnessContextTerm
    coqRestrictedPADirectAndIntroductionRightFormulaTerm
    coqRestrictedPADirectAndIntroductionAssignmentCodeTerm
  coqRestrictedPADirectAndIntroductionAssignmentStepTerm =
  tfImp coqRestrictedPADirectAndIntroductionRightRestrictedTemplate
    (tfImp
      coqRestrictedPADirectAndIntroductionRightPredicateEndpointTemplate
      (tfImp coqRestrictedPADirectAndIntroductionRightAdmissibleTemplate
        (tfImp
          coqRestrictedPADirectAndIntroductionRightPredicateContextTruthTemplate
          coqRestrictedPADirectAndIntroductionRightTruthTemplate))).
Proof. reflexivity. Qed.

(** The context-truth premise obtained from each opened child predicate is
    literally the transported witness-context truth application.  Child
    *rule validity*, by contrast, is intentionally kept distinct from the
    weaker endpoint field displayed by the parent constructor; the semantic
    recursive-child interface below is responsible for that upgrade. *)
Lemma coqRestrictedPADirectAndIntroduction_left_context_truth_agreement :
  coqRestrictedPADirectAndIntroductionLeftPredicateContextTruthTemplate =
  coqRestrictedPADirectAndIntroductionWitnessContextTruthTemplate.
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectAndIntroduction_right_context_truth_agreement :
  coqRestrictedPADirectAndIntroductionRightPredicateContextTruthTemplate =
  coqRestrictedPADirectAndIntroductionWitnessContextTruthTemplate.
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectAndIntroduction_left_below_shape :
  coqRestrictedPADirectAndIntroductionLeftBelowTemplate =
  embedPAFormula
    (Formula.ltTermAt (tVar 2) (liftTerm 8 (tVar 4))).
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectAndIntroduction_right_below_shape :
  coqRestrictedPADirectAndIntroductionRightBelowTemplate =
  embedPAFormula
    (Formula.ltTermAt (tVar 1) (liftTerm 8 (tVar 4))).
Proof. reflexivity. Qed.

(** ------------------------------------------------------------------
    Exact arbitrary-tail shell contexts. *)

Definition coqRestrictedPADirectAndIntroductionDeepRestrictedTemplate
    : TemplateFormula :=
  rawCoqTemplateRenameN 8
    coqRestrictedPADerivationSoundnessRestrictedProofTemplate.

Definition coqRestrictedPADirectAndIntroductionDeepAdmissibleTemplate
    : TemplateFormula :=
  rawCoqTemplateRenameN 8
    coqRestrictedPADerivationSoundnessAdmissibleTemplate.

Definition coqRestrictedPADirectAndIntroductionOuterContextTruthTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAssumptionOuterContextTruthTemplate.

Definition coqRestrictedPADirectAndIntroductionOuterConclusionTruthTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate.

Lemma coqRestrictedPADirectAndIntroduction_remaining_shape :
  rawCoqTemplateRenameN 8
    rawCoqRestrictedPADirectStrongStepRemainingTemplate =
  tfImp coqRestrictedPADirectAndIntroductionDeepAdmissibleTemplate
    (tfImp
      coqRestrictedPADirectAndIntroductionOuterContextTruthTemplate
      coqRestrictedPADirectAndIntroductionOuterConclusionTruthTemplate).
Proof. reflexivity. Qed.

Definition coqRestrictedPADirectStrongStepAndIntroductionBaseContext
    (tail : TemplateContext) : TemplateContext :=
  rawCoqRestrictedPADirectEndpointWitnessBodyTemplate ::
    rawCoqRestrictedPADirectEndpointDeepTail
      (rawCoqRestrictedPADirectStrongStepEndpointTail tail).

Definition coqRestrictedPADirectStrongStepAndIntroductionCaseContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectAndIntroductionCaseTemplate ::
    coqRestrictedPADirectStrongStepAndIntroductionBaseContext tail.

Definition coqRestrictedPADirectStrongStepAndIntroductionAdmissibleContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectAndIntroductionDeepAdmissibleTemplate ::
    coqRestrictedPADirectStrongStepAndIntroductionCaseContext tail.

Definition coqRestrictedPADirectStrongStepAndIntroductionReadyContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectAndIntroductionOuterContextTruthTemplate ::
    coqRestrictedPADirectStrongStepAndIntroductionAdmissibleContext tail.

Arguments coqRestrictedPADirectStrongStepAndIntroductionBaseContext
  tail : clear implicits.
Arguments coqRestrictedPADirectStrongStepAndIntroductionCaseContext
  tail : clear implicits.
Arguments coqRestrictedPADirectStrongStepAndIntroductionAdmissibleContext
  tail : clear implicits.
Arguments coqRestrictedPADirectStrongStepAndIntroductionReadyContext
  tail : clear implicits.

(** Shifting a context repeatedly shifts its former head by the same number
    of renamings.  This is the precise reason the strong-prefix formula
    available below the four endpoint universals is [renameN 4 K]. *)
Lemma coqRestrictedPADirectAndIntroduction_contextShiftN_head : forall
    count head tail,
  In (rawCoqTemplateRenameN count head)
    (rawCoqTemplateContextShiftN count (head :: tail)).
Proof.
  induction count as [|remaining ih]; intros head tail.
  - cbn [rawCoqTemplateRenameN rawCoqTemplateContextShiftN].
    left. reflexivity.
  - cbn [rawCoqTemplateRenameN rawCoqTemplateContextShiftN].
    apply ih.
Qed.

Lemma coqRestrictedPADirectAndIntroduction_ready_endpoint_in : forall tail,
  In rawCoqRestrictedPADirectEndpointWitnessBodyTemplate
    (coqRestrictedPADirectStrongStepAndIntroductionReadyContext tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectStrongStepAndIntroductionReadyContext,
    coqRestrictedPADirectStrongStepAndIntroductionAdmissibleContext,
    coqRestrictedPADirectStrongStepAndIntroductionCaseContext,
    coqRestrictedPADirectStrongStepAndIntroductionBaseContext.
  do 3 right. left. reflexivity.
Qed.

Lemma coqRestrictedPADirectAndIntroduction_ready_case_in : forall tail,
  In coqRestrictedPADirectAndIntroductionCaseTemplate
    (coqRestrictedPADirectStrongStepAndIntroductionReadyContext tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectStrongStepAndIntroductionReadyContext,
    coqRestrictedPADirectStrongStepAndIntroductionAdmissibleContext,
    coqRestrictedPADirectStrongStepAndIntroductionCaseContext.
  right. right. left. reflexivity.
Qed.

Lemma coqRestrictedPADirectAndIntroduction_ready_admissible_in : forall tail,
  In coqRestrictedPADirectAndIntroductionDeepAdmissibleTemplate
    (coqRestrictedPADirectStrongStepAndIntroductionReadyContext tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectStrongStepAndIntroductionReadyContext,
    coqRestrictedPADirectStrongStepAndIntroductionAdmissibleContext.
  right. left. reflexivity.
Qed.

Lemma coqRestrictedPADirectAndIntroduction_ready_context_truth_in :
    forall tail,
  In coqRestrictedPADirectAndIntroductionOuterContextTruthTemplate
    (coqRestrictedPADirectStrongStepAndIntroductionReadyContext tail).
Proof. intro tail. left. reflexivity. Qed.

Lemma coqRestrictedPADirectAndIntroduction_ready_restricted_in : forall tail,
  In coqRestrictedPADirectAndIntroductionDeepRestrictedTemplate
    (coqRestrictedPADirectStrongStepAndIntroductionReadyContext tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectStrongStepAndIntroductionReadyContext,
    coqRestrictedPADirectStrongStepAndIntroductionAdmissibleContext,
    coqRestrictedPADirectStrongStepAndIntroductionCaseContext,
    coqRestrictedPADirectStrongStepAndIntroductionBaseContext.
  do 3 right.
  rewrite <- raw_coqRestrictedPADirectEndpointDeepContext_shape.
  unfold coqRestrictedPADirectAndIntroductionDeepRestrictedTemplate.
  apply raw_coqTemplateNestedExContext_inherited.
  unfold rawCoqRestrictedPADirectStrongStepEndpointTail.
  left. reflexivity.
Qed.

Lemma coqRestrictedPADirectAndIntroduction_ready_prefix_in : forall tail,
  In coqRestrictedPADirectAndIntroductionDeepStrongPrefixTemplate
    (coqRestrictedPADirectStrongStepAndIntroductionReadyContext tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectStrongStepAndIntroductionReadyContext,
    coqRestrictedPADirectStrongStepAndIntroductionAdmissibleContext,
    coqRestrictedPADirectStrongStepAndIntroductionCaseContext,
    coqRestrictedPADirectStrongStepAndIntroductionBaseContext.
  do 3 right.
  rewrite <- raw_coqRestrictedPADirectEndpointDeepContext_shape.
  unfold coqRestrictedPADirectAndIntroductionDeepStrongPrefixTemplate.
  apply raw_coqTemplateNestedExContext_inherited.
  unfold rawCoqRestrictedPADirectStrongStepEndpointTail.
  right.
  unfold rawCoqRestrictedPADirectStrongStepFourBinderContext.
  apply coqRestrictedPADirectAndIntroduction_contextShiftN_head.
Qed.

(** ------------------------------------------------------------------
    Context-generic finite projection roots for the constructor case. *)

Definition coqRestrictedPADirectAndIntroductionCaseRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAss context coqRestrictedPADirectAndIntroductionCaseTemplate.

Definition coqRestrictedPADirectAndIntroductionCodeEqualityRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectAndIntroductionCodeEqualityTemplate
    coqRestrictedPADirectAndIntroductionFormulaAndSuffixTemplate
    (coqRestrictedPADirectAndIntroductionCaseRootAt context).

Definition coqRestrictedPADirectAndIntroductionFormulaAndSuffixRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE2 context
    coqRestrictedPADirectAndIntroductionCodeEqualityTemplate
    coqRestrictedPADirectAndIntroductionFormulaAndSuffixTemplate
    (coqRestrictedPADirectAndIntroductionCaseRootAt context).

Definition coqRestrictedPADirectAndIntroductionFormulaAndRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectAndIntroductionFormulaAndTemplate
    coqRestrictedPADirectAndIntroductionLeftEndpointSuffixTemplate
    (coqRestrictedPADirectAndIntroductionFormulaAndSuffixRootAt context).

Definition coqRestrictedPADirectAndIntroductionLeftEndpointSuffixRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE2 context
    coqRestrictedPADirectAndIntroductionFormulaAndTemplate
    coqRestrictedPADirectAndIntroductionLeftEndpointSuffixTemplate
    (coqRestrictedPADirectAndIntroductionFormulaAndSuffixRootAt context).

Definition coqRestrictedPADirectAndIntroductionLeftEndpointRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectAndIntroductionLeftEndpointTemplate
    coqRestrictedPADirectAndIntroductionRightEndpointSuffixTemplate
    (coqRestrictedPADirectAndIntroductionLeftEndpointSuffixRootAt context).

Definition coqRestrictedPADirectAndIntroductionRightEndpointSuffixRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE2 context
    coqRestrictedPADirectAndIntroductionLeftEndpointTemplate
    coqRestrictedPADirectAndIntroductionRightEndpointSuffixTemplate
    (coqRestrictedPADirectAndIntroductionLeftEndpointSuffixRootAt context).

Definition coqRestrictedPADirectAndIntroductionRightEndpointRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectAndIntroductionRightEndpointTemplate
    coqRestrictedPADirectAndIntroductionTerminalTruthTemplate
    (coqRestrictedPADirectAndIntroductionRightEndpointSuffixRootAt context).

Lemma coqRestrictedPADirectAndIntroductionCaseRootAt_valid : forall
    context,
  In coqRestrictedPADirectAndIntroductionCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectAndIntroductionCaseTemplate
    (coqRestrictedPADirectAndIntroductionCaseRootAt context).
Proof. intros context hin. apply templateRawDerives_assumption. exact hin. Qed.

Lemma coqRestrictedPADirectAndIntroductionCodeEqualityRootAt_valid : forall
    context,
  In coqRestrictedPADirectAndIntroductionCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectAndIntroductionCodeEqualityTemplate
    (coqRestrictedPADirectAndIntroductionCodeEqualityRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectAndIntroductionCodeEqualityRootAt.
  apply coqRestrictedPADirect_templateRawDerives_andE1.
  rewrite <- coqRestrictedPADirectAndIntroduction_case_shape.
  apply coqRestrictedPADirectAndIntroductionCaseRootAt_valid. exact hin.
Qed.

Lemma coqRestrictedPADirectAndIntroductionFormulaAndSuffixRootAt_valid :
    forall context,
  In coqRestrictedPADirectAndIntroductionCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectAndIntroductionFormulaAndSuffixTemplate
    (coqRestrictedPADirectAndIntroductionFormulaAndSuffixRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectAndIntroductionFormulaAndSuffixRootAt.
  apply coqRestrictedPADirect_templateRawDerives_andE2.
  rewrite <- coqRestrictedPADirectAndIntroduction_case_shape.
  apply coqRestrictedPADirectAndIntroductionCaseRootAt_valid. exact hin.
Qed.

Lemma coqRestrictedPADirectAndIntroductionFormulaAndRootAt_valid : forall
    context,
  In coqRestrictedPADirectAndIntroductionCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectAndIntroductionFormulaAndTemplate
    (coqRestrictedPADirectAndIntroductionFormulaAndRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectAndIntroductionFormulaAndRootAt.
  apply coqRestrictedPADirect_templateRawDerives_andE1.
  apply coqRestrictedPADirectAndIntroductionFormulaAndSuffixRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectAndIntroductionLeftEndpointSuffixRootAt_valid :
    forall context,
  In coqRestrictedPADirectAndIntroductionCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectAndIntroductionLeftEndpointSuffixTemplate
    (coqRestrictedPADirectAndIntroductionLeftEndpointSuffixRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectAndIntroductionLeftEndpointSuffixRootAt.
  apply coqRestrictedPADirect_templateRawDerives_andE2.
  apply coqRestrictedPADirectAndIntroductionFormulaAndSuffixRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectAndIntroductionLeftEndpointRootAt_valid : forall
    context,
  In coqRestrictedPADirectAndIntroductionCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectAndIntroductionLeftEndpointTemplate
    (coqRestrictedPADirectAndIntroductionLeftEndpointRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectAndIntroductionLeftEndpointRootAt.
  apply coqRestrictedPADirect_templateRawDerives_andE1.
  apply coqRestrictedPADirectAndIntroductionLeftEndpointSuffixRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectAndIntroductionRightEndpointSuffixRootAt_valid :
    forall context,
  In coqRestrictedPADirectAndIntroductionCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectAndIntroductionRightEndpointSuffixTemplate
    (coqRestrictedPADirectAndIntroductionRightEndpointSuffixRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectAndIntroductionRightEndpointSuffixRootAt.
  apply coqRestrictedPADirect_templateRawDerives_andE2.
  apply coqRestrictedPADirectAndIntroductionLeftEndpointSuffixRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectAndIntroductionRightEndpointRootAt_valid : forall
    context,
  In coqRestrictedPADirectAndIntroductionCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectAndIntroductionRightEndpointTemplate
    (coqRestrictedPADirectAndIntroductionRightEndpointRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectAndIntroductionRightEndpointRootAt.
  apply coqRestrictedPADirect_templateRawDerives_andE1.
  apply coqRestrictedPADirectAndIntroductionRightEndpointSuffixRootAt_valid.
  exact hin.
Qed.

(** ------------------------------------------------------------------
    Sharp semantic operation interfaces. *)

Definition coqRestrictedPADirectAndIntroductionChildInterfaceResultTemplate
    (child context conclusion : TemplateTerm) : TemplateFormula :=
  tfAnd
    (coqRestrictedPADirectAndIntroductionChildBelowTemplate child)
    (tfAnd
      (coqRestrictedPADirectAndIntroductionChildRestrictedTemplate
        child context conclusion)
      (tfAnd
        (coqRestrictedPADirectAndIntroductionChildEndpointTemplate
          child context conclusion)
        (coqRestrictedPADirectAndIntroductionChildAdmissibleTemplate
          child context conclusion))).

Definition coqRestrictedPADirectAndIntroductionChildInterfaceLawTemplate
    (child context conclusion : TemplateTerm)
    (displayedEndpoint : TemplateFormula) : TemplateFormula :=
  tfImp coqRestrictedPADirectAndIntroductionDeepRestrictedTemplate
    (tfImp coqRestrictedPADirectAndIntroductionCodeEqualityTemplate
      (tfImp coqRestrictedPADirectAndIntroductionFormulaAndTemplate
        (tfImp displayedEndpoint
          (tfImp coqRestrictedPADirectAndIntroductionDeepAdmissibleTemplate
            (coqRestrictedPADirectAndIntroductionChildInterfaceResultTemplate
              child context conclusion))))).

Definition coqRestrictedPADirectAndIntroductionLeftChildInterfaceLawTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildInterfaceLawTemplate
    coqRestrictedPADirectAndIntroductionLeftChildTerm
    coqRestrictedPADirectAndIntroductionWitnessContextTerm
    coqRestrictedPADirectAndIntroductionLeftFormulaTerm
    coqRestrictedPADirectAndIntroductionLeftEndpointTemplate.

Definition coqRestrictedPADirectAndIntroductionRightChildInterfaceLawTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildInterfaceLawTemplate
    coqRestrictedPADirectAndIntroductionRightChildTerm
    coqRestrictedPADirectAndIntroductionWitnessContextTerm
    coqRestrictedPADirectAndIntroductionRightFormulaTerm
    coqRestrictedPADirectAndIntroductionRightEndpointTemplate.

Definition coqRestrictedPADirectAndIntroductionTruthLawTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectAndIntroductionFormulaAndTemplate
    (tfImp coqRestrictedPADirectAndIntroductionLeftTruthTemplate
      (tfImp coqRestrictedPADirectAndIntroductionRightTruthTemplate
        coqRestrictedPADirectAndIntroductionOuterConclusionTruthTemplate)).

Definition RawCoqRestrictedPADirectAndIntroductionChildInterfaceRootsAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (context : TemplateContext) : Prop :=
  (exists leftRoot : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation context)
      (rawTemplateFormula translation
        coqRestrictedPADirectAndIntroductionLeftChildInterfaceLawTemplate)
      leftRoot) /\
  (exists rightRoot : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation context)
      (rawTemplateFormula translation
        coqRestrictedPADirectAndIntroductionRightChildInterfaceLawTemplate)
      rightRoot).

Arguments RawCoqRestrictedPADirectAndIntroductionChildInterfaceRootsAt
  M translation context : clear implicits.

Definition RawCoqRestrictedPADirectAndIntroductionTruthLawRootAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (context : TemplateContext) : Prop :=
  exists truthRoot : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation context)
      (rawTemplateFormula translation
        coqRestrictedPADirectAndIntroductionTruthLawTemplate)
      truthRoot.

Arguments RawCoqRestrictedPADirectAndIntroductionTruthLawRootAt
  M translation context : clear implicits.

Definition RawCoqRestrictedPADirectStrongStepAndIntroductionSemanticRoots
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop :=
  let translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs in
  let ready :=
    coqRestrictedPADirectStrongStepAndIntroductionReadyContext tail in
  RawCoqRestrictedPADirectAndIntroductionChildInterfaceRootsAt
      M translation ready /\
  RawCoqRestrictedPADirectAndIntroductionTruthLawRootAt
      M translation ready.

Arguments
  RawCoqRestrictedPADirectStrongStepAndIntroductionSemanticRoots
  M hPA inputs tail : clear implicits.

(** ------------------------------------------------------------------
    Reusable local-proof combinators.

    The generic template compiler handles closed finite trees.  The two
    lemmas below are the corresponding open-root operations: they compose a
    caller-provided implication or universal proof without pretending that
    such a semantic root is a finite template proof. *)

Lemma raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    context antecedent consequent implicationRoot antecedentRoot,
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation context)
    (rawTemplateFormula translation (tfImp antecedent consequent))
    implicationRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation context)
    (rawTemplateFormula translation antecedent)
    antecedentRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation context)
    (rawTemplateFormula translation consequent)
    (rawProofImpERoot M
      (rawTemplateContextCode translation context)
      (rawTemplateFormula translation antecedent)
      (rawTemplateFormula translation consequent)
      implicationRoot antecedentRoot).
Proof.
  intros M hPA translation context antecedent consequent
    implicationRoot antecedentRoot himp hantecedent.
  rewrite rawTemplateFormula_imp in himp.
  exact (raw_codedPALocalProofOf_impE M hPA
    (rawTemplateContextCode translation context)
    (rawTemplateFormula translation antecedent)
    (rawTemplateFormula translation consequent)
    implicationRoot antecedentRoot himp hantecedent).
Qed.

Lemma raw_codedPALocalProofOf_coqRestrictedPADirect_templateAllE : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    context body replacement child,
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation context)
    (rawTemplateFormula translation (tfAll body)) child ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation context)
    (rawTemplateFormula translation
      (templateFormulaOpen replacement body))
    (rawProofAllERoot M
      (rawTemplateContextCode translation context)
      (rawTemplateFormula translation body)
      (rawTemplateTerm translation replacement)
      child).
Proof.
  intros M hPA translation context body replacement child hchild.
  rewrite rawTemplateFormula_all in hchild.
  apply (raw_codedPALocalProofOf_allE M hPA
    (rawTemplateContextCode translation context)
    (rawTemplateFormula translation body)
    (rawTemplateTerm translation replacement)
    (rawTemplateFormula translation
      (templateFormulaOpen replacement body)) child).
  - exact hchild.
  - exact (rawTemplateFormula_open translation body replacement).
Qed.

Lemma raw_codedPALocalProofOf_coqRestrictedPADirect_templateAssumption :
    forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M) context formula,
  In formula context ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation context)
    (rawTemplateFormula translation formula)
    (rawTemplateProofCode translation (trpAss context formula)).
Proof.
  intros M hPA translation context formula hin.
  apply (raw_templateProof_localProof M hPA translation
    (trpAss context formula)).
  exact (proj1 (templateRawDerives_assumption context formula hin)).
Qed.

(** Generic shape facts used by both child instances. *)
Lemma coqRestrictedPADirectAndIntroduction_child_guarded_shape : forall child,
  coqRestrictedPADirectAndIntroductionChildGuardedTemplate child =
  tfImp (coqRestrictedPADirectAndIntroductionChildBelowTemplate child)
    (coqRestrictedPADirectAndIntroductionChildPredicateTemplate child).
Proof. intro child. reflexivity. Qed.

Lemma coqRestrictedPADirectAndIntroduction_child_predicate_all_shape :
    forall child,
  coqRestrictedPADirectAndIntroductionChildPredicateTemplate child =
  tfAll (coqRestrictedPADirectTemplateAllBody
    (coqRestrictedPADirectAndIntroductionChildPredicateTemplate child)).
Proof. intro child. reflexivity. Qed.

Lemma coqRestrictedPADirectAndIntroduction_child_after_context_all_shape :
    forall child context,
  coqRestrictedPADirectAndIntroductionChildAfterContextTemplate
      child context =
  tfAll (coqRestrictedPADirectTemplateAllBody
    (coqRestrictedPADirectAndIntroductionChildAfterContextTemplate
      child context)).
Proof. intros child context. reflexivity. Qed.

Lemma coqRestrictedPADirectAndIntroduction_child_after_conclusion_all_shape :
    forall child context conclusion,
  coqRestrictedPADirectAndIntroductionChildAfterConclusionTemplate
      child context conclusion =
  tfAll (coqRestrictedPADirectTemplateAllBody
    (coqRestrictedPADirectAndIntroductionChildAfterConclusionTemplate
      child context conclusion)).
Proof. intros child context conclusion. reflexivity. Qed.

Lemma
    coqRestrictedPADirectAndIntroduction_child_after_assignment_all_shape :
    forall child context conclusion assignmentCode,
  coqRestrictedPADirectAndIntroductionChildAfterAssignmentCodeTemplate
      child context conclusion assignmentCode =
  tfAll (coqRestrictedPADirectTemplateAllBody
    (coqRestrictedPADirectAndIntroductionChildAfterAssignmentCodeTemplate
      child context conclusion assignmentCode)).
Proof. intros child context conclusion assignmentCode. reflexivity. Qed.

Lemma coqRestrictedPADirectAndIntroduction_child_ready_shape : forall
    child context conclusion,
  coqRestrictedPADirectAndIntroductionChildReadyTemplate
      child context conclusion
      coqRestrictedPADirectAndIntroductionAssignmentCodeTerm
      coqRestrictedPADirectAndIntroductionAssignmentStepTerm =
  tfImp
    (coqRestrictedPADirectAndIntroductionChildRestrictedTemplate
      child context conclusion)
    (tfImp
      (coqRestrictedPADirectAndIntroductionChildEndpointTemplate
        child context conclusion)
      (tfImp
        (coqRestrictedPADirectAndIntroductionChildAdmissibleTemplate
          child context conclusion)
        (tfImp
          (coqRestrictedPADirectAndIntroductionChildContextTruthTemplate
            child context conclusion)
          (coqRestrictedPADirectAndIntroductionChildTruthTemplate
            child context conclusion)))).
Proof. intros child context conclusion. reflexivity. Qed.

(** Apply a recursive-child operation to the five facts which its semantic
    implementation is allowed to inspect. *)
Theorem
    raw_codedPALocalProofOf_coqRestrictedPADirectAndIntroductionChildInterface :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (translation : RawCodedTemplateTranslation M)
    localContext child witnessContext childConclusion displayedEndpoint
    lawRoot restrictedRoot codeEqualityRoot formulaAndRoot
    displayedEndpointRoot admissibleRoot,
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation localContext)
    (rawTemplateFormula translation
      (coqRestrictedPADirectAndIntroductionChildInterfaceLawTemplate
        child witnessContext childConclusion displayedEndpoint)) lawRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation localContext)
    (rawTemplateFormula translation
      coqRestrictedPADirectAndIntroductionDeepRestrictedTemplate)
    restrictedRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation localContext)
    (rawTemplateFormula translation
      coqRestrictedPADirectAndIntroductionCodeEqualityTemplate)
    codeEqualityRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation localContext)
    (rawTemplateFormula translation
      coqRestrictedPADirectAndIntroductionFormulaAndTemplate)
    formulaAndRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation localContext)
    (rawTemplateFormula translation displayedEndpoint)
    displayedEndpointRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation localContext)
    (rawTemplateFormula translation
      coqRestrictedPADirectAndIntroductionDeepAdmissibleTemplate)
    admissibleRoot ->
  exists resultRoot : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation localContext)
      (rawTemplateFormula translation
        (coqRestrictedPADirectAndIntroductionChildInterfaceResultTemplate
          child witnessContext childConclusion)) resultRoot.
Proof.
  intros M hPA translation localContext child witnessContext
    childConclusion displayedEndpoint lawRoot restrictedRoot
    codeEqualityRoot formulaAndRoot displayedEndpointRoot admissibleRoot
    hlaw hrestricted hcodeEquality hformulaAnd hdisplayedEndpoint
    hadmissible.
  unfold coqRestrictedPADirectAndIntroductionChildInterfaceLawTemplate
    in hlaw.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation localContext _ _ lawRoot restrictedRoot
      hlaw hrestricted) as h1.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation localContext _ _ _ codeEqualityRoot
      h1 hcodeEquality) as h2.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation localContext _ _ _ formulaAndRoot
      h2 hformulaAnd) as h3.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation localContext _ _ _ displayedEndpointRoot
      h3 hdisplayedEndpoint) as h4.
  eexists.
  exact
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation localContext _ _ _ admissibleRoot
      h4 hadmissible).
Qed.

(** Project the result of the semantic child operation and feed all four
    facts into the exact strong-prefix instance. *)
Theorem
    raw_codedPALocalProofOf_coqRestrictedPADirectAndIntroductionChildTruth :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (translation : RawCodedTemplateTranslation M)
    localContext child witnessContext childConclusion
    interfaceRoot prefixRoot contextTruthRoot,
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation localContext)
    (rawTemplateFormula translation
      (coqRestrictedPADirectAndIntroductionChildInterfaceResultTemplate
        child witnessContext childConclusion)) interfaceRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation localContext)
    (rawTemplateFormula translation
      coqRestrictedPADirectAndIntroductionDeepStrongPrefixTemplate)
    prefixRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation localContext)
    (rawTemplateFormula translation
      (coqRestrictedPADirectAndIntroductionChildContextTruthTemplate
        child witnessContext childConclusion)) contextTruthRoot ->
  exists truthRoot : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation localContext)
      (rawTemplateFormula translation
        (coqRestrictedPADirectAndIntroductionChildTruthTemplate
          child witnessContext childConclusion)) truthRoot.
Proof.
  intros M hPA translation localContext child witnessContext
    childConclusion interfaceRoot prefixRoot contextTruthRoot
    hinterface hprefix hcontextTruth.
  set (contextCode := rawTemplateContextCode translation localContext).
  set (below := coqRestrictedPADirectAndIntroductionChildBelowTemplate child).
  set (restricted :=
    coqRestrictedPADirectAndIntroductionChildRestrictedTemplate
      child witnessContext childConclusion).
  set (childEndpoint :=
    coqRestrictedPADirectAndIntroductionChildEndpointTemplate
      child witnessContext childConclusion).
  set (childAdmissible :=
    coqRestrictedPADirectAndIntroductionChildAdmissibleTemplate
      child witnessContext childConclusion).
  set (lastPair := tfAnd childEndpoint childAdmissible).
  set (rest := tfAnd restricted lastPair).

  unfold
    coqRestrictedPADirectAndIntroductionChildInterfaceResultTemplate
    in hinterface.
  rewrite rawTemplateFormula_and in hinterface.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA _ _ _
    interfaceRoot hinterface)
    as hbelow.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA _ _ _
    interfaceRoot hinterface)
    as hrest.
  rewrite rawTemplateFormula_and in hrest.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA _ _ _ _ hrest)
    as hrestricted.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA _ _ _ _ hrest)
    as hlastPair.
  rewrite rawTemplateFormula_and in hlastPair.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA _ _ _ _ hlastPair)
    as hchildEndpoint.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA _ _ _ _ hlastPair)
    as hchildAdmissible.

  rewrite coqRestrictedPADirectAndIntroduction_deep_prefix_shape in hprefix.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAllE
      M hPA translation localContext
      coqRestrictedPADirectAndIntroductionDeepStrongPrefixBodyTemplate
      child prefixRoot hprefix) as hguarded.
  lazymatch type of hguarded with
  | RawCodedPALocalProofOf _ _ _ ?guardedRoot =>
      change (RawCodedPALocalProofOf M contextCode
        (rawTemplateFormula translation
          (coqRestrictedPADirectAndIntroductionChildGuardedTemplate child))
        guardedRoot) in hguarded
  end.
  rewrite coqRestrictedPADirectAndIntroduction_child_guarded_shape
    in hguarded.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation localContext _ _ _ _ hguarded hbelow)
    as hpredicate.

  rewrite
    coqRestrictedPADirectAndIntroduction_child_predicate_all_shape
    in hpredicate.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAllE
      M hPA translation localContext _ witnessContext _ hpredicate)
    as hafterContext.
  lazymatch type of hafterContext with
  | RawCodedPALocalProofOf _ _ _ ?afterContextRoot =>
      change (RawCodedPALocalProofOf M contextCode
        (rawTemplateFormula translation
          (coqRestrictedPADirectAndIntroductionChildAfterContextTemplate
            child witnessContext)) afterContextRoot) in hafterContext
  end.
  rewrite
    coqRestrictedPADirectAndIntroduction_child_after_context_all_shape
    in hafterContext.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAllE
      M hPA translation localContext _ childConclusion _ hafterContext)
    as hafterConclusion.
  lazymatch type of hafterConclusion with
  | RawCodedPALocalProofOf _ _ _ ?afterConclusionRoot =>
      change (RawCodedPALocalProofOf M contextCode
        (rawTemplateFormula translation
          (coqRestrictedPADirectAndIntroductionChildAfterConclusionTemplate
            child witnessContext childConclusion)) afterConclusionRoot)
        in hafterConclusion
  end.
  rewrite
    coqRestrictedPADirectAndIntroduction_child_after_conclusion_all_shape
    in hafterConclusion.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAllE
      M hPA translation localContext _
      coqRestrictedPADirectAndIntroductionAssignmentCodeTerm _
      hafterConclusion) as hafterAssignmentCode.
  lazymatch type of hafterAssignmentCode with
  | RawCodedPALocalProofOf _ _ _ ?afterAssignmentCodeRoot =>
      change (RawCodedPALocalProofOf M contextCode
        (rawTemplateFormula translation
          (coqRestrictedPADirectAndIntroductionChildAfterAssignmentCodeTemplate
            child witnessContext childConclusion
            coqRestrictedPADirectAndIntroductionAssignmentCodeTerm))
        afterAssignmentCodeRoot) in hafterAssignmentCode
  end.
  rewrite
    coqRestrictedPADirectAndIntroduction_child_after_assignment_all_shape
    in hafterAssignmentCode.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAllE
      M hPA translation localContext _
      coqRestrictedPADirectAndIntroductionAssignmentStepTerm _
      hafterAssignmentCode) as hready.
  lazymatch type of hready with
  | RawCodedPALocalProofOf _ _ _ ?readyRoot =>
      change (RawCodedPALocalProofOf M contextCode
        (rawTemplateFormula translation
          (coqRestrictedPADirectAndIntroductionChildReadyTemplate
            child witnessContext childConclusion
            coqRestrictedPADirectAndIntroductionAssignmentCodeTerm
            coqRestrictedPADirectAndIntroductionAssignmentStepTerm))
        readyRoot) in hready
  end.
  rewrite coqRestrictedPADirectAndIntroduction_child_ready_shape in hready.

  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation localContext _ _ _ _ hready hrestricted)
    as hafterRestricted.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation localContext _ _ _ _
      hafterRestricted hchildEndpoint) as hafterEndpoint.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation localContext _ _ _ _
      hafterEndpoint hchildAdmissible) as hafterAdmissible.
  eexists.
  exact
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation localContext _ _ _ contextTruthRoot
      hafterAdmissible hcontextTruth).
Qed.

(** ------------------------------------------------------------------
    Constructor-local conclusion in the fully introduced shell context. *)

Theorem
    raw_codedPALocalProofOf_coqRestrictedPADirectAndIntroductionConclusionAt :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (translation : RawCodedTemplateTranslation M) tail,
  RawCoqRestrictedPADirectAndIntroductionChildInterfaceRootsAt M translation
    (coqRestrictedPADirectStrongStepAndIntroductionReadyContext tail) ->
  RawCoqRestrictedPADirectAndIntroductionTruthLawRootAt M translation
    (coqRestrictedPADirectStrongStepAndIntroductionReadyContext tail) ->
  exists conclusionRoot : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation
        (coqRestrictedPADirectStrongStepAndIntroductionReadyContext tail))
      (rawTemplateFormula translation
        coqRestrictedPADirectAndIntroductionOuterConclusionTruthTemplate)
      conclusionRoot.
Proof.
  intros M hPA translation tail
    [[leftLawRoot hleftLaw] [rightLawRoot hrightLaw]]
    [truthLawRoot htruthLaw].
  set (ready :=
    coqRestrictedPADirectStrongStepAndIntroductionReadyContext tail).
  set (readyCode := rawTemplateContextCode translation ready).
  assert (hcase :
    In coqRestrictedPADirectAndIntroductionCaseTemplate ready).
  {
    unfold ready.
    apply coqRestrictedPADirectAndIntroduction_ready_case_in.
  }

  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectAndIntroductionCodeEqualityRootAt ready)
    (proj1
      (coqRestrictedPADirectAndIntroductionCodeEqualityRootAt_valid
        ready hcase))) as hcodeEquality.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectAndIntroductionFormulaAndRootAt ready)
    (proj1
      (coqRestrictedPADirectAndIntroductionFormulaAndRootAt_valid
        ready hcase))) as hformulaAnd.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectAndIntroductionLeftEndpointRootAt ready)
    (proj1
      (coqRestrictedPADirectAndIntroductionLeftEndpointRootAt_valid
        ready hcase))) as hleftDisplayedEndpoint.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectAndIntroductionRightEndpointRootAt ready)
    (proj1
      (coqRestrictedPADirectAndIntroductionRightEndpointRootAt_valid
        ready hcase))) as hrightDisplayedEndpoint.

  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAssumption
      M hPA translation ready
      coqRestrictedPADirectAndIntroductionDeepRestrictedTemplate
      (coqRestrictedPADirectAndIntroduction_ready_restricted_in tail))
    as hrestricted.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAssumption
      M hPA translation ready
      coqRestrictedPADirectAndIntroductionDeepAdmissibleTemplate
      (coqRestrictedPADirectAndIntroduction_ready_admissible_in tail))
    as hadmissible.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAssumption
      M hPA translation ready
      coqRestrictedPADirectAndIntroductionDeepStrongPrefixTemplate
      (coqRestrictedPADirectAndIntroduction_ready_prefix_in tail))
    as hprefix.

  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt ready)
    (proj1
      (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt_valid
        ready
        (coqRestrictedPADirectAndIntroduction_ready_endpoint_in tail)
        (coqRestrictedPADirectAndIntroduction_ready_context_truth_in tail))))
    as hwitnessContextTruth.

  lazymatch type of hcodeEquality with
  | RawCodedPALocalProofOf _ _ _ ?root =>
      change (RawCodedPALocalProofOf M readyCode
        (rawTemplateFormula translation
          coqRestrictedPADirectAndIntroductionCodeEqualityTemplate) root)
        in hcodeEquality
  end.
  lazymatch type of hformulaAnd with
  | RawCodedPALocalProofOf _ _ _ ?root =>
      change (RawCodedPALocalProofOf M readyCode
        (rawTemplateFormula translation
          coqRestrictedPADirectAndIntroductionFormulaAndTemplate) root)
        in hformulaAnd
  end.
  lazymatch type of hleftDisplayedEndpoint with
  | RawCodedPALocalProofOf _ _ _ ?root =>
      change (RawCodedPALocalProofOf M readyCode
        (rawTemplateFormula translation
          coqRestrictedPADirectAndIntroductionLeftEndpointTemplate) root)
        in hleftDisplayedEndpoint
  end.
  lazymatch type of hrightDisplayedEndpoint with
  | RawCodedPALocalProofOf _ _ _ ?root =>
      change (RawCodedPALocalProofOf M readyCode
        (rawTemplateFormula translation
          coqRestrictedPADirectAndIntroductionRightEndpointTemplate) root)
        in hrightDisplayedEndpoint
  end.
  lazymatch type of hrestricted with
  | RawCodedPALocalProofOf _ _ _ ?root =>
      change (RawCodedPALocalProofOf M readyCode
        (rawTemplateFormula translation
          coqRestrictedPADirectAndIntroductionDeepRestrictedTemplate) root)
        in hrestricted
  end.
  lazymatch type of hadmissible with
  | RawCodedPALocalProofOf _ _ _ ?root =>
      change (RawCodedPALocalProofOf M readyCode
        (rawTemplateFormula translation
          coqRestrictedPADirectAndIntroductionDeepAdmissibleTemplate) root)
        in hadmissible
  end.
  lazymatch type of hprefix with
  | RawCodedPALocalProofOf _ _ _ ?root =>
      change (RawCodedPALocalProofOf M readyCode
        (rawTemplateFormula translation
          coqRestrictedPADirectAndIntroductionDeepStrongPrefixTemplate) root)
        in hprefix
  end.
  lazymatch type of hwitnessContextTruth with
  | RawCodedPALocalProofOf _ _ _ ?root =>
      change (RawCodedPALocalProofOf M readyCode
        (rawTemplateFormula translation
          coqRestrictedPADirectAndIntroductionWitnessContextTruthTemplate)
        root) in hwitnessContextTruth
  end.

  destruct
    (raw_codedPALocalProofOf_coqRestrictedPADirectAndIntroductionChildInterface
      M hPA translation ready
      coqRestrictedPADirectAndIntroductionLeftChildTerm
      coqRestrictedPADirectAndIntroductionWitnessContextTerm
      coqRestrictedPADirectAndIntroductionLeftFormulaTerm
      coqRestrictedPADirectAndIntroductionLeftEndpointTemplate
      leftLawRoot _ _ _ _ _
      hleftLaw hrestricted hcodeEquality hformulaAnd
      hleftDisplayedEndpoint hadmissible)
    as [leftInterfaceRoot hleftInterface].
  destruct
    (raw_codedPALocalProofOf_coqRestrictedPADirectAndIntroductionChildInterface
      M hPA translation ready
      coqRestrictedPADirectAndIntroductionRightChildTerm
      coqRestrictedPADirectAndIntroductionWitnessContextTerm
      coqRestrictedPADirectAndIntroductionRightFormulaTerm
      coqRestrictedPADirectAndIntroductionRightEndpointTemplate
      rightLawRoot _ _ _ _ _
      hrightLaw hrestricted hcodeEquality hformulaAnd
      hrightDisplayedEndpoint hadmissible)
    as [rightInterfaceRoot hrightInterface].

  assert (hleftContextTruth : RawCodedPALocalProofOf M readyCode
    (rawTemplateFormula translation
      coqRestrictedPADirectAndIntroductionLeftPredicateContextTruthTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt ready))).
  {
    rewrite
      coqRestrictedPADirectAndIntroduction_left_context_truth_agreement.
    exact hwitnessContextTruth.
  }
  assert (hrightContextTruth : RawCodedPALocalProofOf M readyCode
    (rawTemplateFormula translation
      coqRestrictedPADirectAndIntroductionRightPredicateContextTruthTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt ready))).
  {
    rewrite
      coqRestrictedPADirectAndIntroduction_right_context_truth_agreement.
    exact hwitnessContextTruth.
  }

  destruct
    (raw_codedPALocalProofOf_coqRestrictedPADirectAndIntroductionChildTruth
      M hPA translation ready
      coqRestrictedPADirectAndIntroductionLeftChildTerm
      coqRestrictedPADirectAndIntroductionWitnessContextTerm
      coqRestrictedPADirectAndIntroductionLeftFormulaTerm
      leftInterfaceRoot _ _
      hleftInterface hprefix hleftContextTruth)
    as [leftTruthRoot hleftTruth].
  destruct
    (raw_codedPALocalProofOf_coqRestrictedPADirectAndIntroductionChildTruth
      M hPA translation ready
      coqRestrictedPADirectAndIntroductionRightChildTerm
      coqRestrictedPADirectAndIntroductionWitnessContextTerm
      coqRestrictedPADirectAndIntroductionRightFormulaTerm
      rightInterfaceRoot _ _
      hrightInterface hprefix hrightContextTruth)
    as [rightTruthRoot hrightTruth].

  unfold coqRestrictedPADirectAndIntroductionTruthLawTemplate in htruthLaw.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation ready _ _ truthLawRoot _
      htruthLaw hformulaAnd) as htruthAfterFormulaAnd.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation ready _ _ _ leftTruthRoot
      htruthAfterFormulaAnd hleftTruth) as htruthAfterLeft.
  eexists.
  exact
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation ready _ _ _ rightTruthRoot
      htruthAfterLeft hrightTruth).
Qed.

(** ------------------------------------------------------------------
    Exact [rawCoqRuleAndIntroduction] slot of the public dispatcher. *)

Theorem
    raw_coqRestrictedPADirectStrongStepAndIntroductionCaseImplicationRoot :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectStrongStepAndIntroductionSemanticRoots
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
            rawCoqRuleAndIntroduction
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
    coqRestrictedPADirectStrongStepAndIntroductionBaseContext tail).
  set (caseContext :=
    coqRestrictedPADirectStrongStepAndIntroductionCaseContext tail).
  set (admissibleContext :=
    coqRestrictedPADirectStrongStepAndIntroductionAdmissibleContext tail).
  set (readyContext :=
    coqRestrictedPADirectStrongStepAndIntroductionReadyContext tail).
  unfold RawCoqRestrictedPADirectStrongStepAndIntroductionSemanticRoots
    in hsemantic.
  cbn zeta in hsemantic.
  destruct hsemantic as [hchildInterfaces htruthLaw].
  destruct
    (raw_codedPALocalProofOf_coqRestrictedPADirectAndIntroductionConclusionAt
      M hPA translation tail hchildInterfaces htruthLaw)
    as [conclusionRoot hconclusion].

  set (readyCode := rawTemplateContextCode translation readyContext).
  set (admissibleCode :=
    rawTemplateContextCode translation admissibleContext).
  set (caseCode := rawTemplateContextCode translation caseContext).
  set (baseCode := rawTemplateContextCode translation baseContext).

  set (contextImpRoot := rawProofImpIRoot M admissibleCode
    (rawTemplateFormula translation
      coqRestrictedPADirectAndIntroductionOuterContextTruthTemplate)
    (rawTemplateFormula translation
      coqRestrictedPADirectAndIntroductionOuterConclusionTruthTemplate)
    conclusionRoot).
  assert (hcontextImp : RawCodedPALocalProofOf M admissibleCode
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectAndIntroductionOuterContextTruthTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectAndIntroductionOuterConclusionTruthTemplate))
    contextImpRoot).
  {
    unfold contextImpRoot.
    apply (raw_codedPALocalProofOf_impI M hPA admissibleCode
      (rawTemplateFormula translation
        coqRestrictedPADirectAndIntroductionOuterContextTruthTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectAndIntroductionOuterConclusionTruthTemplate)
      conclusionRoot).
    change (RawCodedPALocalProofOf M readyCode
      (rawTemplateFormula translation
        coqRestrictedPADirectAndIntroductionOuterConclusionTruthTemplate)
      conclusionRoot).
    change (RawCodedPALocalProofOf M
      (rawTemplateContextCode translation readyContext)
      (rawTemplateFormula translation
        coqRestrictedPADirectAndIntroductionOuterConclusionTruthTemplate)
      conclusionRoot).
    unfold readyContext.
    exact hconclusion.
  }

  set (admissibleImpRoot := rawProofImpIRoot M caseCode
    (rawTemplateFormula translation
      coqRestrictedPADirectAndIntroductionDeepAdmissibleTemplate)
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectAndIntroductionOuterContextTruthTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectAndIntroductionOuterConclusionTruthTemplate))
    contextImpRoot).
  assert (hadmissibleImp : RawCodedPALocalProofOf M caseCode
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectAndIntroductionDeepAdmissibleTemplate)
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          coqRestrictedPADirectAndIntroductionOuterContextTruthTemplate)
        (rawTemplateFormula translation
          coqRestrictedPADirectAndIntroductionOuterConclusionTruthTemplate)))
    admissibleImpRoot).
  {
    unfold admissibleImpRoot.
    apply (raw_codedPALocalProofOf_impI M hPA caseCode
      (rawTemplateFormula translation
        coqRestrictedPADirectAndIntroductionDeepAdmissibleTemplate)
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          coqRestrictedPADirectAndIntroductionOuterContextTruthTemplate)
        (rawTemplateFormula translation
          coqRestrictedPADirectAndIntroductionOuterConclusionTruthTemplate))
      contextImpRoot).
    exact hcontextImp.
  }

  set (caseImpRoot := rawProofImpIRoot M baseCode
    (rawTemplateFormula translation
      coqRestrictedPADirectAndIntroductionCaseTemplate)
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectAndIntroductionDeepAdmissibleTemplate)
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          coqRestrictedPADirectAndIntroductionOuterContextTruthTemplate)
        (rawTemplateFormula translation
          coqRestrictedPADirectAndIntroductionOuterConclusionTruthTemplate)))
    admissibleImpRoot).
  exists caseImpRoot.
  rewrite coqRestrictedPADirectAndIntroduction_remaining_shape.
  change (RawCodedPALocalProofOf M baseCode
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectAndIntroductionCaseTemplate)
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          coqRestrictedPADirectAndIntroductionDeepAdmissibleTemplate)
        (rawFormulaImpCode M
          (rawTemplateFormula translation
            coqRestrictedPADirectAndIntroductionOuterContextTruthTemplate)
          (rawTemplateFormula translation
            coqRestrictedPADirectAndIntroductionOuterConclusionTruthTemplate))))
    caseImpRoot).
  unfold caseImpRoot.
  apply (raw_codedPALocalProofOf_impI M hPA baseCode
    (rawTemplateFormula translation
      coqRestrictedPADirectAndIntroductionCaseTemplate)
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectAndIntroductionDeepAdmissibleTemplate)
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          coqRestrictedPADirectAndIntroductionOuterContextTruthTemplate)
        (rawTemplateFormula translation
          coqRestrictedPADirectAndIntroductionOuterConclusionTruthTemplate)))
    admissibleImpRoot).
  exact hadmissibleImp.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase.
