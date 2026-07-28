(**
  The genuine existential-elimination constructor case for the direct
  derivation-soundness strong step.

  At the eight-witness endpoint depth the dispatcher exposes

    outerConclusion = result,
    existentialFormula = Ex(body),
    endpoint(existentialChild, witnessContext, existentialFormula),
    shiftContext(witnessContext, shiftedContext),
    shiftFormula(result, shiftedResult),
    endpoint(bodyChild, body :: shiftedContext, shiftedResult).

  Every constructor field is projected below.  The endpoint-witness equality
  transports outer context truth to [witnessContext].  Four deliberately
  sharp semantic roots retain exactly the eigenvariable-sensitive boundary:

  - the first recursive child yields truth of the existential formula;
  - context shifting plus a body witness yields truth of the binder context;
  - the second recursive child yields truth of the shifted result in that
    binder context;
  - the dynamic existential law combines those resources and transports the
    shifted result back to the unshifted result.

  The checked spine applies those roots in order and transports truth of
  [result] along [outerConclusion = result].  It assumes no desired branch,
  desired conclusion, or strong-step theorem.
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
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationCase.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
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

Definition coqRestrictedPADirectExistentialEliminationCodeEqualityTemplate
    : TemplateFormula :=
  embedPAFormula
    (pEq (liftTerm 8 (tVar 4))
      (proofExECodeTerm (tVar 7) (tVar 6) (tVar 5)
        (tVar 2) (tVar 1))).

Definition coqRestrictedPADirectExistentialEliminationResultFormulaTerm
    : TemplateTerm := ttVar 5.

Definition coqRestrictedPADirectExistentialEliminationConclusionEqualityTemplate
    : TemplateFormula :=
  tfEq coqRestrictedPADirectAssumptionOuterConclusionTerm
    coqRestrictedPADirectExistentialEliminationResultFormulaTerm.

Definition coqRestrictedPADirectExistentialEliminationFormulaCodeTemplate
    : TemplateFormula :=
  embedPAFormula (formulaExCodeTermAt (tVar 0) (tVar 6)).

Definition
    coqRestrictedPADirectExistentialEliminationExistentialEndpointTemplate
    : TemplateFormula :=
  embedPAFormula
    (proofEndpointTermAt (tVar 2) (tVar 7) (tVar 0)).

Definition coqRestrictedPADirectExistentialEliminationContextShiftTemplate
    : TemplateFormula :=
  embedPAFormula (contextShiftTermAt (tVar 7) (tVar 4)).

Definition coqRestrictedPADirectExistentialEliminationConclusionShiftTemplate
    : TemplateFormula :=
  embedPAFormula
    (codedFormulaShiftTermAt tZero (Term.numeral 1)
      (tVar 5) (tVar 3)).

Definition coqRestrictedPADirectExistentialEliminationBodyEndpointTemplate
    : TemplateFormula :=
  embedPAFormula
    (proofEndpointTermAt (tVar 1)
      (nodeTerm (tVar 6) (tVar 4)) (tVar 3)).

Definition coqRestrictedPADirectExistentialEliminationTerminalTruthTemplate
    : TemplateFormula := embedPAFormula (pEq tZero tZero).

Definition coqRestrictedPADirectExistentialEliminationBodyEndpointSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectExistentialEliminationBodyEndpointTemplate
    coqRestrictedPADirectExistentialEliminationTerminalTruthTemplate.

Definition coqRestrictedPADirectExistentialEliminationConclusionShiftSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectExistentialEliminationConclusionShiftTemplate
    coqRestrictedPADirectExistentialEliminationBodyEndpointSuffixTemplate.

Definition coqRestrictedPADirectExistentialEliminationContextShiftSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectExistentialEliminationContextShiftTemplate
    coqRestrictedPADirectExistentialEliminationConclusionShiftSuffixTemplate.

Definition
    coqRestrictedPADirectExistentialEliminationExistentialEndpointSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectExistentialEliminationExistentialEndpointTemplate
    coqRestrictedPADirectExistentialEliminationContextShiftSuffixTemplate.

Definition coqRestrictedPADirectExistentialEliminationFormulaSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectExistentialEliminationFormulaCodeTemplate
    coqRestrictedPADirectExistentialEliminationExistentialEndpointSuffixTemplate.

Definition coqRestrictedPADirectExistentialEliminationConclusionSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectExistentialEliminationConclusionEqualityTemplate
    coqRestrictedPADirectExistentialEliminationFormulaSuffixTemplate.

Definition coqRestrictedPADirectExistentialEliminationCaseTemplate
    : TemplateFormula :=
  rawCoqRestrictedPAProofRuleCaseTemplate rawCoqRuleExElimination
    (liftTerm 8 (tVar 4)) (tVar 7) (liftTerm 8 (tVar 2))
    (tVar 6) (tVar 5) (tVar 4) (tVar 3)
    (tVar 2) (tVar 1) (tVar 0).

Lemma coqRestrictedPADirectExistentialElimination_case_shape :
  coqRestrictedPADirectExistentialEliminationCaseTemplate =
  tfAnd coqRestrictedPADirectExistentialEliminationCodeEqualityTemplate
    coqRestrictedPADirectExistentialEliminationConclusionSuffixTemplate.
Proof. reflexivity. Qed.

(** ------------------------------------------------------------------
    Truth leaves and the exact eigenvariable-sensitive residual. *)

Definition coqRestrictedPADirectExistentialEliminationExistentialTruthTemplate
    : TemplateFormula :=
  tfOpaque coqRestrictedPAConclusionTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     ttVar 0; ttVar 9; ttVar 8].

Definition coqRestrictedPADirectExistentialEliminationBodyTruthTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAssumptionWitnessFormulaTruthTemplate.

Definition coqRestrictedPADirectExistentialEliminationBinderContextTerm
    : TemplateTerm :=
  embedPATerm (nodeTerm (tVar 6) (tVar 4)).

Definition
    coqRestrictedPADirectExistentialEliminationBinderContextTruthTemplate
    : TemplateFormula :=
  tfOpaque coqRestrictedPAContextTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     coqRestrictedPADirectExistentialEliminationBinderContextTerm;
     ttVar 9; ttVar 8].

Definition coqRestrictedPADirectExistentialEliminationShiftedResultTruthTemplate
    : TemplateFormula :=
  tfOpaque coqRestrictedPAConclusionTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     ttVar 3; ttVar 9; ttVar 8].

Definition coqRestrictedPADirectExistentialEliminationResultTruthTemplate
    : TemplateFormula :=
  tfOpaque coqRestrictedPAConclusionTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     coqRestrictedPADirectExistentialEliminationResultFormulaTerm;
     ttVar 9; ttVar 8].

Lemma coqRestrictedPADirectExistentialElimination_result_truth_shape :
  coqRestrictedPADirectExistentialEliminationResultTruthTemplate =
  tfOpaque coqRestrictedPAConclusionTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     ttVar 5; ttVar 9; ttVar 8].
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectExistentialElimination_conclusion_motive_result :
  templateFormulaOpen
    coqRestrictedPADirectExistentialEliminationResultFormulaTerm
    coqRestrictedPADirectAssumptionConclusionTruthMotive =
  coqRestrictedPADirectExistentialEliminationResultTruthTemplate.
Proof. reflexivity. Qed.

Definition
    coqRestrictedPADirectExistentialEliminationExistentialChildLawTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectExistentialEliminationExistentialEndpointTemplate
    (tfImp coqRestrictedPADirectAssumptionWitnessContextTruthTemplate
      coqRestrictedPADirectExistentialEliminationExistentialTruthTemplate).

Definition
    coqRestrictedPADirectExistentialEliminationBinderContextTruthLawTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectExistentialEliminationContextShiftTemplate
    (tfImp coqRestrictedPADirectAssumptionWitnessContextTruthTemplate
      (tfImp coqRestrictedPADirectExistentialEliminationBodyTruthTemplate
        coqRestrictedPADirectExistentialEliminationBinderContextTruthTemplate)).

Definition coqRestrictedPADirectExistentialEliminationBodyChildLawTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectExistentialEliminationBodyEndpointTemplate
    (tfImp
      coqRestrictedPADirectExistentialEliminationBinderContextTruthTemplate
      coqRestrictedPADirectExistentialEliminationShiftedResultTruthTemplate).

Definition coqRestrictedPADirectExistentialEliminationDynamicTruthLawTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectExistentialEliminationFormulaCodeTemplate
    (tfImp coqRestrictedPADirectExistentialEliminationConclusionShiftTemplate
      (tfImp
        coqRestrictedPADirectExistentialEliminationExistentialTruthTemplate
        (tfImp
          (tfImp coqRestrictedPADirectExistentialEliminationBodyTruthTemplate
            coqRestrictedPADirectExistentialEliminationBinderContextTruthTemplate)
          (tfImp
            (tfImp
              coqRestrictedPADirectExistentialEliminationBinderContextTruthTemplate
              coqRestrictedPADirectExistentialEliminationShiftedResultTruthTemplate)
            coqRestrictedPADirectExistentialEliminationResultTruthTemplate)))).

Lemma rawTemplateFormula_existentialEliminationExistentialChildLaw_view : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  rawTemplateFormula translation
    coqRestrictedPADirectExistentialEliminationExistentialChildLawTemplate =
  rawFormulaImpCode M
    (rawTemplateFormula translation
      coqRestrictedPADirectExistentialEliminationExistentialEndpointTemplate)
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionWitnessContextTruthTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectExistentialEliminationExistentialTruthTemplate)).
Proof.
  intros M translation.
  unfold
    coqRestrictedPADirectExistentialEliminationExistentialChildLawTemplate.
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectExistentialEliminationExistentialEndpointTemplate
    (tfImp coqRestrictedPADirectAssumptionWitnessContextTruthTemplate
      coqRestrictedPADirectExistentialEliminationExistentialTruthTemplate)).
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectAssumptionWitnessContextTruthTemplate
    coqRestrictedPADirectExistentialEliminationExistentialTruthTemplate).
  reflexivity.
Qed.

Lemma rawTemplateFormula_existentialEliminationBinderContextTruthLaw_view :
    forall (M : RawPAModel)
      (translation : RawCodedTemplateTranslation M),
  rawTemplateFormula translation
    coqRestrictedPADirectExistentialEliminationBinderContextTruthLawTemplate =
  rawFormulaImpCode M
    (rawTemplateFormula translation
      coqRestrictedPADirectExistentialEliminationContextShiftTemplate)
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionWitnessContextTruthTemplate)
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          coqRestrictedPADirectExistentialEliminationBodyTruthTemplate)
        (rawTemplateFormula translation
          coqRestrictedPADirectExistentialEliminationBinderContextTruthTemplate))).
Proof.
  intros M translation.
  unfold
    coqRestrictedPADirectExistentialEliminationBinderContextTruthLawTemplate.
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectExistentialEliminationContextShiftTemplate
    (tfImp coqRestrictedPADirectAssumptionWitnessContextTruthTemplate
      (tfImp coqRestrictedPADirectExistentialEliminationBodyTruthTemplate
        coqRestrictedPADirectExistentialEliminationBinderContextTruthTemplate))).
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectAssumptionWitnessContextTruthTemplate
    (tfImp coqRestrictedPADirectExistentialEliminationBodyTruthTemplate
      coqRestrictedPADirectExistentialEliminationBinderContextTruthTemplate)).
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectExistentialEliminationBodyTruthTemplate
    coqRestrictedPADirectExistentialEliminationBinderContextTruthTemplate).
  reflexivity.
Qed.

Lemma rawTemplateFormula_existentialEliminationBodyChildLaw_view : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  rawTemplateFormula translation
    coqRestrictedPADirectExistentialEliminationBodyChildLawTemplate =
  rawFormulaImpCode M
    (rawTemplateFormula translation
      coqRestrictedPADirectExistentialEliminationBodyEndpointTemplate)
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectExistentialEliminationBinderContextTruthTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectExistentialEliminationShiftedResultTruthTemplate)).
Proof.
  intros M translation.
  unfold coqRestrictedPADirectExistentialEliminationBodyChildLawTemplate.
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectExistentialEliminationBodyEndpointTemplate
    (tfImp
      coqRestrictedPADirectExistentialEliminationBinderContextTruthTemplate
      coqRestrictedPADirectExistentialEliminationShiftedResultTruthTemplate)).
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectExistentialEliminationBinderContextTruthTemplate
    coqRestrictedPADirectExistentialEliminationShiftedResultTruthTemplate).
  reflexivity.
Qed.

Lemma rawTemplateFormula_existentialEliminationDynamicTruthLaw_view : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  rawTemplateFormula translation
    coqRestrictedPADirectExistentialEliminationDynamicTruthLawTemplate =
  rawFormulaImpCode M
    (rawTemplateFormula translation
      coqRestrictedPADirectExistentialEliminationFormulaCodeTemplate)
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectExistentialEliminationConclusionShiftTemplate)
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          coqRestrictedPADirectExistentialEliminationExistentialTruthTemplate)
        (rawFormulaImpCode M
          (rawFormulaImpCode M
            (rawTemplateFormula translation
              coqRestrictedPADirectExistentialEliminationBodyTruthTemplate)
            (rawTemplateFormula translation
              coqRestrictedPADirectExistentialEliminationBinderContextTruthTemplate))
          (rawFormulaImpCode M
            (rawFormulaImpCode M
              (rawTemplateFormula translation
                coqRestrictedPADirectExistentialEliminationBinderContextTruthTemplate)
              (rawTemplateFormula translation
                coqRestrictedPADirectExistentialEliminationShiftedResultTruthTemplate))
            (rawTemplateFormula translation
              coqRestrictedPADirectExistentialEliminationResultTruthTemplate))))).
Proof.
  intros M translation.
  unfold coqRestrictedPADirectExistentialEliminationDynamicTruthLawTemplate.
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectExistentialEliminationFormulaCodeTemplate
    (tfImp coqRestrictedPADirectExistentialEliminationConclusionShiftTemplate
      (tfImp
        coqRestrictedPADirectExistentialEliminationExistentialTruthTemplate
        (tfImp
          (tfImp coqRestrictedPADirectExistentialEliminationBodyTruthTemplate
            coqRestrictedPADirectExistentialEliminationBinderContextTruthTemplate)
          (tfImp
            (tfImp
              coqRestrictedPADirectExistentialEliminationBinderContextTruthTemplate
              coqRestrictedPADirectExistentialEliminationShiftedResultTruthTemplate)
            coqRestrictedPADirectExistentialEliminationResultTruthTemplate))))).
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectExistentialEliminationConclusionShiftTemplate
    (tfImp
      coqRestrictedPADirectExistentialEliminationExistentialTruthTemplate
      (tfImp
        (tfImp coqRestrictedPADirectExistentialEliminationBodyTruthTemplate
          coqRestrictedPADirectExistentialEliminationBinderContextTruthTemplate)
        (tfImp
          (tfImp
            coqRestrictedPADirectExistentialEliminationBinderContextTruthTemplate
            coqRestrictedPADirectExistentialEliminationShiftedResultTruthTemplate)
          coqRestrictedPADirectExistentialEliminationResultTruthTemplate)))).
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectExistentialEliminationExistentialTruthTemplate
    (tfImp
      (tfImp coqRestrictedPADirectExistentialEliminationBodyTruthTemplate
        coqRestrictedPADirectExistentialEliminationBinderContextTruthTemplate)
      (tfImp
        (tfImp
          coqRestrictedPADirectExistentialEliminationBinderContextTruthTemplate
          coqRestrictedPADirectExistentialEliminationShiftedResultTruthTemplate)
        coqRestrictedPADirectExistentialEliminationResultTruthTemplate))).
  rewrite (rawTemplateFormula_imp translation
    (tfImp coqRestrictedPADirectExistentialEliminationBodyTruthTemplate
      coqRestrictedPADirectExistentialEliminationBinderContextTruthTemplate)
    (tfImp
      (tfImp
        coqRestrictedPADirectExistentialEliminationBinderContextTruthTemplate
        coqRestrictedPADirectExistentialEliminationShiftedResultTruthTemplate)
      coqRestrictedPADirectExistentialEliminationResultTruthTemplate)).
  rewrite (rawTemplateFormula_imp translation
    (tfImp
      coqRestrictedPADirectExistentialEliminationBinderContextTruthTemplate
      coqRestrictedPADirectExistentialEliminationShiftedResultTruthTemplate)
    coqRestrictedPADirectExistentialEliminationResultTruthTemplate).
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectExistentialEliminationBodyTruthTemplate
    coqRestrictedPADirectExistentialEliminationBinderContextTruthTemplate).
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectExistentialEliminationBinderContextTruthTemplate
    coqRestrictedPADirectExistentialEliminationShiftedResultTruthTemplate).
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    Exact shell contexts and residual root package. *)

Definition
    coqRestrictedPADirectStrongStepExistentialEliminationDeepEndpointContext
    (tail : TemplateContext) : TemplateContext :=
  rawCoqRestrictedPADirectEndpointWitnessBodyTemplate ::
    rawCoqRestrictedPADirectEndpointDeepTail
      (rawCoqRestrictedPADirectStrongStepEndpointTail tail).

Definition coqRestrictedPADirectStrongStepExistentialEliminationCaseContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectExistentialEliminationCaseTemplate ::
    coqRestrictedPADirectStrongStepExistentialEliminationDeepEndpointContext
      tail.

Definition
    coqRestrictedPADirectStrongStepExistentialEliminationAdmissibleContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectAssumptionDeepAdmissibleTemplate ::
    coqRestrictedPADirectStrongStepExistentialEliminationCaseContext tail.

Definition coqRestrictedPADirectStrongStepExistentialEliminationReadyContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectAssumptionOuterContextTruthTemplate ::
    coqRestrictedPADirectStrongStepExistentialEliminationAdmissibleContext tail.

Arguments
  coqRestrictedPADirectStrongStepExistentialEliminationDeepEndpointContext
  tail : clear implicits.
Arguments coqRestrictedPADirectStrongStepExistentialEliminationCaseContext
  tail : clear implicits.
Arguments
  coqRestrictedPADirectStrongStepExistentialEliminationAdmissibleContext
  tail : clear implicits.
Arguments coqRestrictedPADirectStrongStepExistentialEliminationReadyContext
  tail : clear implicits.

Definition RawCoqRestrictedPADirectExistentialEliminationSemanticRoots
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop :=
  let translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs in
  let readyContext :=
    coqRestrictedPADirectStrongStepExistentialEliminationReadyContext tail in
  (exists existentialChildRoot : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation readyContext)
      (rawTemplateFormula translation
        coqRestrictedPADirectExistentialEliminationExistentialChildLawTemplate)
      existentialChildRoot) /\
  (exists binderContextRoot : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation readyContext)
      (rawTemplateFormula translation
        coqRestrictedPADirectExistentialEliminationBinderContextTruthLawTemplate)
      binderContextRoot) /\
  (exists bodyChildRoot : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation readyContext)
      (rawTemplateFormula translation
        coqRestrictedPADirectExistentialEliminationBodyChildLawTemplate)
      bodyChildRoot) /\
  (exists dynamicTruthRoot : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation readyContext)
      (rawTemplateFormula translation
        coqRestrictedPADirectExistentialEliminationDynamicTruthLawTemplate)
      dynamicTruthRoot).

Arguments RawCoqRestrictedPADirectExistentialEliminationSemanticRoots
  M hPA inputs tail : clear implicits.

(** ------------------------------------------------------------------
    Parameterized finite branch projections. *)

Definition coqRestrictedPADirectExistentialEliminationCaseRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAss context coqRestrictedPADirectExistentialEliminationCaseTemplate.

Definition coqRestrictedPADirectExistentialEliminationCodeEqualityRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectExistentialEliminationCodeEqualityTemplate
    coqRestrictedPADirectExistentialEliminationConclusionSuffixTemplate
    (coqRestrictedPADirectExistentialEliminationCaseRootAt context).

Definition coqRestrictedPADirectExistentialEliminationConclusionSuffixRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE2 context
    coqRestrictedPADirectExistentialEliminationCodeEqualityTemplate
    coqRestrictedPADirectExistentialEliminationConclusionSuffixTemplate
    (coqRestrictedPADirectExistentialEliminationCaseRootAt context).

Definition coqRestrictedPADirectExistentialEliminationConclusionEqualityRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectExistentialEliminationConclusionEqualityTemplate
    coqRestrictedPADirectExistentialEliminationFormulaSuffixTemplate
    (coqRestrictedPADirectExistentialEliminationConclusionSuffixRootAt context).

Definition coqRestrictedPADirectExistentialEliminationFormulaSuffixRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE2 context
    coqRestrictedPADirectExistentialEliminationConclusionEqualityTemplate
    coqRestrictedPADirectExistentialEliminationFormulaSuffixTemplate
    (coqRestrictedPADirectExistentialEliminationConclusionSuffixRootAt context).

Definition coqRestrictedPADirectExistentialEliminationFormulaCodeRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectExistentialEliminationFormulaCodeTemplate
    coqRestrictedPADirectExistentialEliminationExistentialEndpointSuffixTemplate
    (coqRestrictedPADirectExistentialEliminationFormulaSuffixRootAt context).

Definition
    coqRestrictedPADirectExistentialEliminationExistentialEndpointSuffixRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE2 context
    coqRestrictedPADirectExistentialEliminationFormulaCodeTemplate
    coqRestrictedPADirectExistentialEliminationExistentialEndpointSuffixTemplate
    (coqRestrictedPADirectExistentialEliminationFormulaSuffixRootAt context).

Definition
    coqRestrictedPADirectExistentialEliminationExistentialEndpointRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectExistentialEliminationExistentialEndpointTemplate
    coqRestrictedPADirectExistentialEliminationContextShiftSuffixTemplate
    (coqRestrictedPADirectExistentialEliminationExistentialEndpointSuffixRootAt
      context).

Definition coqRestrictedPADirectExistentialEliminationContextShiftSuffixRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE2 context
    coqRestrictedPADirectExistentialEliminationExistentialEndpointTemplate
    coqRestrictedPADirectExistentialEliminationContextShiftSuffixTemplate
    (coqRestrictedPADirectExistentialEliminationExistentialEndpointSuffixRootAt
      context).

Definition coqRestrictedPADirectExistentialEliminationContextShiftRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectExistentialEliminationContextShiftTemplate
    coqRestrictedPADirectExistentialEliminationConclusionShiftSuffixTemplate
    (coqRestrictedPADirectExistentialEliminationContextShiftSuffixRootAt
      context).

Definition
    coqRestrictedPADirectExistentialEliminationConclusionShiftSuffixRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE2 context
    coqRestrictedPADirectExistentialEliminationContextShiftTemplate
    coqRestrictedPADirectExistentialEliminationConclusionShiftSuffixTemplate
    (coqRestrictedPADirectExistentialEliminationContextShiftSuffixRootAt
      context).

Definition coqRestrictedPADirectExistentialEliminationConclusionShiftRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectExistentialEliminationConclusionShiftTemplate
    coqRestrictedPADirectExistentialEliminationBodyEndpointSuffixTemplate
    (coqRestrictedPADirectExistentialEliminationConclusionShiftSuffixRootAt
      context).

Definition coqRestrictedPADirectExistentialEliminationBodyEndpointSuffixRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE2 context
    coqRestrictedPADirectExistentialEliminationConclusionShiftTemplate
    coqRestrictedPADirectExistentialEliminationBodyEndpointSuffixTemplate
    (coqRestrictedPADirectExistentialEliminationConclusionShiftSuffixRootAt
      context).

Definition coqRestrictedPADirectExistentialEliminationBodyEndpointRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectExistentialEliminationBodyEndpointTemplate
    coqRestrictedPADirectExistentialEliminationTerminalTruthTemplate
    (coqRestrictedPADirectExistentialEliminationBodyEndpointSuffixRootAt
      context).

Definition coqRestrictedPADirectExistentialEliminationTerminalTruthRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE2 context
    coqRestrictedPADirectExistentialEliminationBodyEndpointTemplate
    coqRestrictedPADirectExistentialEliminationTerminalTruthTemplate
    (coqRestrictedPADirectExistentialEliminationBodyEndpointSuffixRootAt
      context).

Lemma coqRestrictedPADirectExistentialEliminationCaseRootAt_valid :
    forall context,
  In coqRestrictedPADirectExistentialEliminationCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectExistentialEliminationCaseTemplate
    (coqRestrictedPADirectExistentialEliminationCaseRootAt context).
Proof.
  intros context hin. apply templateRawDerives_assumption. exact hin.
Qed.

Lemma coqRestrictedPADirectExistentialEliminationCodeEqualityRootAt_valid :
    forall context,
  In coqRestrictedPADirectExistentialEliminationCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectExistentialEliminationCodeEqualityTemplate
    (coqRestrictedPADirectExistentialEliminationCodeEqualityRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectExistentialEliminationCodeEqualityRootAt.
  apply templateAndLeftFrom_derives.
  rewrite <- coqRestrictedPADirectExistentialElimination_case_shape.
  apply coqRestrictedPADirectExistentialEliminationCaseRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectExistentialEliminationConclusionSuffixRootAt_valid :
    forall context,
  In coqRestrictedPADirectExistentialEliminationCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectExistentialEliminationConclusionSuffixTemplate
    (coqRestrictedPADirectExistentialEliminationConclusionSuffixRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectExistentialEliminationConclusionSuffixRootAt.
  apply templateAndRightFrom_derives.
  rewrite <- coqRestrictedPADirectExistentialElimination_case_shape.
  apply coqRestrictedPADirectExistentialEliminationCaseRootAt_valid.
  exact hin.
Qed.

Lemma
    coqRestrictedPADirectExistentialEliminationConclusionEqualityRootAt_valid :
    forall context,
  In coqRestrictedPADirectExistentialEliminationCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectExistentialEliminationConclusionEqualityTemplate
    (coqRestrictedPADirectExistentialEliminationConclusionEqualityRootAt
      context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectExistentialEliminationConclusionEqualityRootAt.
  apply templateAndLeftFrom_derives.
  apply
    coqRestrictedPADirectExistentialEliminationConclusionSuffixRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectExistentialEliminationFormulaSuffixRootAt_valid :
    forall context,
  In coqRestrictedPADirectExistentialEliminationCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectExistentialEliminationFormulaSuffixTemplate
    (coqRestrictedPADirectExistentialEliminationFormulaSuffixRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectExistentialEliminationFormulaSuffixRootAt.
  apply templateAndRightFrom_derives.
  apply
    coqRestrictedPADirectExistentialEliminationConclusionSuffixRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectExistentialEliminationFormulaCodeRootAt_valid :
    forall context,
  In coqRestrictedPADirectExistentialEliminationCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectExistentialEliminationFormulaCodeTemplate
    (coqRestrictedPADirectExistentialEliminationFormulaCodeRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectExistentialEliminationFormulaCodeRootAt.
  apply templateAndLeftFrom_derives.
  apply coqRestrictedPADirectExistentialEliminationFormulaSuffixRootAt_valid.
  exact hin.
Qed.

Lemma
    coqRestrictedPADirectExistentialEliminationExistentialEndpointSuffixRootAt_valid :
    forall context,
  In coqRestrictedPADirectExistentialEliminationCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectExistentialEliminationExistentialEndpointSuffixTemplate
    (coqRestrictedPADirectExistentialEliminationExistentialEndpointSuffixRootAt
      context).
Proof.
  intros context hin.
  unfold
    coqRestrictedPADirectExistentialEliminationExistentialEndpointSuffixRootAt.
  apply templateAndRightFrom_derives.
  apply coqRestrictedPADirectExistentialEliminationFormulaSuffixRootAt_valid.
  exact hin.
Qed.

Lemma
    coqRestrictedPADirectExistentialEliminationExistentialEndpointRootAt_valid :
    forall context,
  In coqRestrictedPADirectExistentialEliminationCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectExistentialEliminationExistentialEndpointTemplate
    (coqRestrictedPADirectExistentialEliminationExistentialEndpointRootAt
      context).
Proof.
  intros context hin.
  unfold
    coqRestrictedPADirectExistentialEliminationExistentialEndpointRootAt.
  apply templateAndLeftFrom_derives.
  apply
    coqRestrictedPADirectExistentialEliminationExistentialEndpointSuffixRootAt_valid.
  exact hin.
Qed.

Lemma
    coqRestrictedPADirectExistentialEliminationContextShiftSuffixRootAt_valid :
    forall context,
  In coqRestrictedPADirectExistentialEliminationCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectExistentialEliminationContextShiftSuffixTemplate
    (coqRestrictedPADirectExistentialEliminationContextShiftSuffixRootAt
      context).
Proof.
  intros context hin.
  unfold
    coqRestrictedPADirectExistentialEliminationContextShiftSuffixRootAt.
  apply templateAndRightFrom_derives.
  apply
    coqRestrictedPADirectExistentialEliminationExistentialEndpointSuffixRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectExistentialEliminationContextShiftRootAt_valid :
    forall context,
  In coqRestrictedPADirectExistentialEliminationCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectExistentialEliminationContextShiftTemplate
    (coqRestrictedPADirectExistentialEliminationContextShiftRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectExistentialEliminationContextShiftRootAt.
  apply templateAndLeftFrom_derives.
  apply
    coqRestrictedPADirectExistentialEliminationContextShiftSuffixRootAt_valid.
  exact hin.
Qed.

Lemma
    coqRestrictedPADirectExistentialEliminationConclusionShiftSuffixRootAt_valid :
    forall context,
  In coqRestrictedPADirectExistentialEliminationCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectExistentialEliminationConclusionShiftSuffixTemplate
    (coqRestrictedPADirectExistentialEliminationConclusionShiftSuffixRootAt
      context).
Proof.
  intros context hin.
  unfold
    coqRestrictedPADirectExistentialEliminationConclusionShiftSuffixRootAt.
  apply templateAndRightFrom_derives.
  apply
    coqRestrictedPADirectExistentialEliminationContextShiftSuffixRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectExistentialEliminationConclusionShiftRootAt_valid :
    forall context,
  In coqRestrictedPADirectExistentialEliminationCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectExistentialEliminationConclusionShiftTemplate
    (coqRestrictedPADirectExistentialEliminationConclusionShiftRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectExistentialEliminationConclusionShiftRootAt.
  apply templateAndLeftFrom_derives.
  apply
    coqRestrictedPADirectExistentialEliminationConclusionShiftSuffixRootAt_valid.
  exact hin.
Qed.

Lemma
    coqRestrictedPADirectExistentialEliminationBodyEndpointSuffixRootAt_valid :
    forall context,
  In coqRestrictedPADirectExistentialEliminationCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectExistentialEliminationBodyEndpointSuffixTemplate
    (coqRestrictedPADirectExistentialEliminationBodyEndpointSuffixRootAt
      context).
Proof.
  intros context hin.
  unfold
    coqRestrictedPADirectExistentialEliminationBodyEndpointSuffixRootAt.
  apply templateAndRightFrom_derives.
  apply
    coqRestrictedPADirectExistentialEliminationConclusionShiftSuffixRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectExistentialEliminationBodyEndpointRootAt_valid :
    forall context,
  In coqRestrictedPADirectExistentialEliminationCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectExistentialEliminationBodyEndpointTemplate
    (coqRestrictedPADirectExistentialEliminationBodyEndpointRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectExistentialEliminationBodyEndpointRootAt.
  apply templateAndLeftFrom_derives.
  apply
    coqRestrictedPADirectExistentialEliminationBodyEndpointSuffixRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectExistentialEliminationTerminalTruthRootAt_valid :
    forall context,
  In coqRestrictedPADirectExistentialEliminationCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectExistentialEliminationTerminalTruthTemplate
    (coqRestrictedPADirectExistentialEliminationTerminalTruthRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectExistentialEliminationTerminalTruthRootAt.
  apply templateAndRightFrom_derives.
  apply
    coqRestrictedPADirectExistentialEliminationBodyEndpointSuffixRootAt_valid.
  exact hin.
Qed.

(** ------------------------------------------------------------------
    A fully compiled truth transport along [outerConclusion = result]. *)

Definition coqRestrictedPADirectExistentialEliminationTransportChildContext
    (context : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectExistentialEliminationResultTruthTemplate :: context.

Definition coqRestrictedPADirectExistentialEliminationConclusionSymmetryRootAt
    (context : TemplateContext) : TemplateRawProof :=
  coqRestrictedPADirectEqSymmetryRoot context
    coqRestrictedPADirectAssumptionOuterConclusionTerm
    coqRestrictedPADirectExistentialEliminationResultFormulaTerm
    (coqRestrictedPADirectExistentialEliminationConclusionEqualityRootAt
      context).

Definition coqRestrictedPADirectExistentialEliminationResultTruthRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAss context coqRestrictedPADirectExistentialEliminationResultTruthTemplate.

Definition coqRestrictedPADirectExistentialEliminationOuterTruthChildRootAt
    (context : TemplateContext) : TemplateRawProof :=
  let childContext :=
    coqRestrictedPADirectExistentialEliminationTransportChildContext context in
  trpEqElim childContext
    coqRestrictedPADirectExistentialEliminationResultFormulaTerm
    coqRestrictedPADirectAssumptionOuterConclusionTerm
    coqRestrictedPADirectAssumptionConclusionTruthMotive
    (coqRestrictedPADirectExistentialEliminationConclusionSymmetryRootAt
      childContext)
    (coqRestrictedPADirectExistentialEliminationResultTruthRootAt childContext).

Definition coqRestrictedPADirectExistentialEliminationConclusionTransportRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpImpI context
    coqRestrictedPADirectExistentialEliminationResultTruthTemplate
    coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate
    (coqRestrictedPADirectExistentialEliminationOuterTruthChildRootAt context).

Lemma coqRestrictedPADirectExistentialEliminationConclusionSymmetryRootAt_valid :
  forall context,
  In coqRestrictedPADirectExistentialEliminationCaseTemplate context ->
  TemplateRawDerives context
    (tfEq coqRestrictedPADirectExistentialEliminationResultFormulaTerm
      coqRestrictedPADirectAssumptionOuterConclusionTerm)
    (coqRestrictedPADirectExistentialEliminationConclusionSymmetryRootAt
      context).
Proof.
  intros context hin.
  apply coqRestrictedPADirectEqSymmetryRoot_valid.
  apply coqRestrictedPADirectExistentialEliminationConclusionEqualityRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectExistentialEliminationConclusionTransportRootAt_valid :
  forall context,
  In coqRestrictedPADirectExistentialEliminationCaseTemplate context ->
  TemplateRawDerives context
    (tfImp coqRestrictedPADirectExistentialEliminationResultTruthTemplate
      coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate)
    (coqRestrictedPADirectExistentialEliminationConclusionTransportRootAt
      context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectExistentialEliminationConclusionTransportRootAt,
    coqRestrictedPADirectExistentialEliminationOuterTruthChildRootAt.
  cbn zeta.
  apply coqRestrictedPADirect_templateRawDerives_impI.
  rewrite <- coqRestrictedPADirectAssumption_conclusion_motive_outer.
  apply coqRestrictedPADirect_templateRawDerives_eqElim.
  - apply
      coqRestrictedPADirectExistentialEliminationConclusionSymmetryRootAt_valid.
    right. exact hin.
  - rewrite
      coqRestrictedPADirectExistentialElimination_conclusion_motive_result.
    apply templateRawDerives_assumption. left. reflexivity.
Qed.

(** ------------------------------------------------------------------
    Compile the semantic roots and checked existential-elimination spine. *)

Theorem
    raw_codedPALocalProofOf_coqRestrictedPADirectExistentialEliminationConclusion
    : forall (M : RawPAModel) (hPA : RawPASatisfies M)
      (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectExistentialEliminationSemanticRoots
    M hPA inputs tail ->
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectStrongStepExistentialEliminationReadyContext
          tail))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate)
      root.
Proof.
  intros M hPA inputs tail hsemanticRoots.
  unfold RawCoqRestrictedPADirectExistentialEliminationSemanticRoots
    in hsemanticRoots.
  cbn zeta in hsemanticRoots.
  destruct hsemanticRoots as
    ((existentialChildRoot & hexistentialChildLaw) &
     (binderContextRoot & hbinderContextLaw) &
     (bodyChildRoot & hbodyChildLaw) &
     (dynamicTruthRoot & hdynamicTruthLaw)).

  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  set (readyContext :=
    coqRestrictedPADirectStrongStepExistentialEliminationReadyContext tail).
  set (readyContextCode :=
    rawTemplateContextCode translation readyContext).

  assert (hcase :
    In coqRestrictedPADirectExistentialEliminationCaseTemplate readyContext).
  {
    unfold readyContext,
      coqRestrictedPADirectStrongStepExistentialEliminationReadyContext,
      coqRestrictedPADirectStrongStepExistentialEliminationAdmissibleContext,
      coqRestrictedPADirectStrongStepExistentialEliminationCaseContext.
    right. right. left. reflexivity.
  }
  assert (hendpointBody :
    In rawCoqRestrictedPADirectEndpointWitnessBodyTemplate readyContext).
  {
    unfold readyContext,
      coqRestrictedPADirectStrongStepExistentialEliminationReadyContext,
      coqRestrictedPADirectStrongStepExistentialEliminationAdmissibleContext,
      coqRestrictedPADirectStrongStepExistentialEliminationCaseContext,
      coqRestrictedPADirectStrongStepExistentialEliminationDeepEndpointContext.
    do 3 right. left. reflexivity.
  }
  assert (houterContextTruth :
    In coqRestrictedPADirectAssumptionOuterContextTruthTemplate readyContext).
  {
    unfold readyContext,
      coqRestrictedPADirectStrongStepExistentialEliminationReadyContext.
    left. reflexivity.
  }

  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectExistentialEliminationFormulaCodeRootAt readyContext)
    (proj1
      (coqRestrictedPADirectExistentialEliminationFormulaCodeRootAt_valid
        readyContext hcase))) as hformulaCode.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectExistentialEliminationExistentialEndpointRootAt
      readyContext)
    (proj1
      (coqRestrictedPADirectExistentialEliminationExistentialEndpointRootAt_valid
        readyContext hcase))) as hexistentialEndpoint.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectExistentialEliminationContextShiftRootAt readyContext)
    (proj1
      (coqRestrictedPADirectExistentialEliminationContextShiftRootAt_valid
        readyContext hcase))) as hcontextShift.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectExistentialEliminationConclusionShiftRootAt
      readyContext)
    (proj1
      (coqRestrictedPADirectExistentialEliminationConclusionShiftRootAt_valid
        readyContext hcase))) as hconclusionShift.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectExistentialEliminationBodyEndpointRootAt readyContext)
    (proj1
      (coqRestrictedPADirectExistentialEliminationBodyEndpointRootAt_valid
        readyContext hcase))) as hbodyEndpoint.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt readyContext)
    (proj1
      (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt_valid
        readyContext hendpointBody houterContextTruth)))
    as hwitnessContextTruth.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectExistentialEliminationConclusionTransportRootAt
      readyContext)
    (proj1
      (coqRestrictedPADirectExistentialEliminationConclusionTransportRootAt_valid
        readyContext hcase))) as htransport.

  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectExistentialEliminationFormulaCodeTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectExistentialEliminationFormulaCodeRootAt
        readyContext))) in hformulaCode.
  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectExistentialEliminationExistentialEndpointTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectExistentialEliminationExistentialEndpointRootAt
        readyContext))) in hexistentialEndpoint.
  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectExistentialEliminationContextShiftTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectExistentialEliminationContextShiftRootAt
        readyContext))) in hcontextShift.
  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectExistentialEliminationConclusionShiftTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectExistentialEliminationConclusionShiftRootAt
        readyContext))) in hconclusionShift.
  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectExistentialEliminationBodyEndpointTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectExistentialEliminationBodyEndpointRootAt
        readyContext))) in hbodyEndpoint.
  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectAssumptionWitnessContextTruthTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt
        readyContext))) in hwitnessContextTruth.
  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      (tfImp coqRestrictedPADirectExistentialEliminationResultTruthTemplate
        coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate))
    (rawTemplateProofCode translation
      (coqRestrictedPADirectExistentialEliminationConclusionTransportRootAt
        readyContext))) in htransport.
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectExistentialEliminationResultTruthTemplate
    coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate)
    in htransport.

  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectExistentialEliminationExistentialChildLawTemplate)
    existentialChildRoot) in hexistentialChildLaw.
  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectExistentialEliminationBinderContextTruthLawTemplate)
    binderContextRoot) in hbinderContextLaw.
  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectExistentialEliminationBodyChildLawTemplate)
    bodyChildRoot) in hbodyChildLaw.
  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectExistentialEliminationDynamicTruthLawTemplate)
    dynamicTruthRoot) in hdynamicTruthLaw.
  rewrite
    rawTemplateFormula_existentialEliminationExistentialChildLaw_view
    in hexistentialChildLaw.
  rewrite rawTemplateFormula_existentialEliminationBinderContextTruthLaw_view
    in hbinderContextLaw.
  rewrite rawTemplateFormula_existentialEliminationBodyChildLaw_view
    in hbodyChildLaw.
  rewrite rawTemplateFormula_existentialEliminationDynamicTruthLaw_view
    in hdynamicTruthLaw.

  set (existentialEndpointCode := rawTemplateFormula translation
    coqRestrictedPADirectExistentialEliminationExistentialEndpointTemplate).
  set (bodyEndpointCode := rawTemplateFormula translation
    coqRestrictedPADirectExistentialEliminationBodyEndpointTemplate).
  set (contextShiftCode := rawTemplateFormula translation
    coqRestrictedPADirectExistentialEliminationContextShiftTemplate).
  set (conclusionShiftCode := rawTemplateFormula translation
    coqRestrictedPADirectExistentialEliminationConclusionShiftTemplate).
  set (witnessContextTruthCode := rawTemplateFormula translation
    coqRestrictedPADirectAssumptionWitnessContextTruthTemplate).
  set (existentialTruthCode := rawTemplateFormula translation
    coqRestrictedPADirectExistentialEliminationExistentialTruthTemplate).
  set (bodyTruthCode := rawTemplateFormula translation
    coqRestrictedPADirectExistentialEliminationBodyTruthTemplate).
  set (binderContextTruthCode := rawTemplateFormula translation
    coqRestrictedPADirectExistentialEliminationBinderContextTruthTemplate).
  set (shiftedResultTruthCode := rawTemplateFormula translation
    coqRestrictedPADirectExistentialEliminationShiftedResultTruthTemplate).
  set (formulaCodeRelation := rawTemplateFormula translation
    coqRestrictedPADirectExistentialEliminationFormulaCodeTemplate).
  set (resultTruthCode := rawTemplateFormula translation
    coqRestrictedPADirectExistentialEliminationResultTruthTemplate).
  set (outerConclusionTruthCode := rawTemplateFormula translation
    coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate).
  set (bodyToBinderCode :=
    rawFormulaImpCode M bodyTruthCode binderContextTruthCode).
  set (binderToShiftedResultCode :=
    rawFormulaImpCode M binderContextTruthCode shiftedResultTruthCode).

  (** First recursive child: truth of the existential formula. *)
  set (existentialAfterEndpointRoot := rawProofImpERoot M readyContextCode
    existentialEndpointCode
    (rawFormulaImpCode M witnessContextTruthCode existentialTruthCode)
    existentialChildRoot
    (rawTemplateProofCode translation
      (coqRestrictedPADirectExistentialEliminationExistentialEndpointRootAt
        readyContext))).
  assert (hexistentialAfterEndpoint : RawCodedPALocalProofOf M
    readyContextCode
    (rawFormulaImpCode M witnessContextTruthCode existentialTruthCode)
    existentialAfterEndpointRoot).
  {
    unfold existentialAfterEndpointRoot.
    apply (raw_codedPALocalProofOf_impE M hPA readyContextCode
      existentialEndpointCode
      (rawFormulaImpCode M witnessContextTruthCode existentialTruthCode)
      existentialChildRoot
      (rawTemplateProofCode translation
        (coqRestrictedPADirectExistentialEliminationExistentialEndpointRootAt
          readyContext))).
    - exact hexistentialChildLaw.
    - unfold existentialEndpointCode. exact hexistentialEndpoint.
  }

  set (existentialTruthRoot := rawProofImpERoot M readyContextCode
    witnessContextTruthCode existentialTruthCode existentialAfterEndpointRoot
    (rawTemplateProofCode translation
      (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt
        readyContext))).
  assert (hexistentialTruth : RawCodedPALocalProofOf M readyContextCode
    existentialTruthCode existentialTruthRoot).
  {
    unfold existentialTruthRoot.
    apply (raw_codedPALocalProofOf_impE M hPA readyContextCode
      witnessContextTruthCode existentialTruthCode
      existentialAfterEndpointRoot
      (rawTemplateProofCode translation
        (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt
          readyContext))).
    - exact hexistentialAfterEndpoint.
    - unfold witnessContextTruthCode. exact hwitnessContextTruth.
  }

  (** Shift the ambient context and expose the body-to-binder-context map. *)
  set (binderAfterShiftRoot := rawProofImpERoot M readyContextCode
    contextShiftCode
    (rawFormulaImpCode M witnessContextTruthCode bodyToBinderCode)
    binderContextRoot
    (rawTemplateProofCode translation
      (coqRestrictedPADirectExistentialEliminationContextShiftRootAt
        readyContext))).
  assert (hbinderAfterShift : RawCodedPALocalProofOf M readyContextCode
    (rawFormulaImpCode M witnessContextTruthCode bodyToBinderCode)
    binderAfterShiftRoot).
  {
    unfold binderAfterShiftRoot, bodyToBinderCode.
    apply (raw_codedPALocalProofOf_impE M hPA readyContextCode
      contextShiftCode
      (rawFormulaImpCode M witnessContextTruthCode
        (rawFormulaImpCode M bodyTruthCode binderContextTruthCode))
      binderContextRoot
      (rawTemplateProofCode translation
        (coqRestrictedPADirectExistentialEliminationContextShiftRootAt
          readyContext))).
    - exact hbinderContextLaw.
    - unfold contextShiftCode. exact hcontextShift.
  }

  set (bodyToBinderRoot := rawProofImpERoot M readyContextCode
    witnessContextTruthCode bodyToBinderCode binderAfterShiftRoot
    (rawTemplateProofCode translation
      (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt
        readyContext))).
  assert (hbodyToBinder : RawCodedPALocalProofOf M readyContextCode
    bodyToBinderCode bodyToBinderRoot).
  {
    unfold bodyToBinderRoot.
    apply (raw_codedPALocalProofOf_impE M hPA readyContextCode
      witnessContextTruthCode bodyToBinderCode binderAfterShiftRoot
      (rawTemplateProofCode translation
        (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt
          readyContext))).
    - exact hbinderAfterShift.
    - unfold witnessContextTruthCode. exact hwitnessContextTruth.
  }

  (** Second recursive child: binder-context truth yields shifted result. *)
  set (bodyAfterEndpointRoot := rawProofImpERoot M readyContextCode
    bodyEndpointCode binderToShiftedResultCode bodyChildRoot
    (rawTemplateProofCode translation
      (coqRestrictedPADirectExistentialEliminationBodyEndpointRootAt
        readyContext))).
  assert (hbodyAfterEndpoint : RawCodedPALocalProofOf M readyContextCode
    binderToShiftedResultCode bodyAfterEndpointRoot).
  {
    unfold bodyAfterEndpointRoot, binderToShiftedResultCode.
    apply (raw_codedPALocalProofOf_impE M hPA readyContextCode
      bodyEndpointCode
      (rawFormulaImpCode M binderContextTruthCode shiftedResultTruthCode)
      bodyChildRoot
      (rawTemplateProofCode translation
        (coqRestrictedPADirectExistentialEliminationBodyEndpointRootAt
          readyContext))).
    - exact hbodyChildLaw.
    - unfold bodyEndpointCode. exact hbodyEndpoint.
  }

  (** Checked dynamic Ex-elimination spine. *)
  set (dynamicAfterFormulaRoot := rawProofImpERoot M readyContextCode
    formulaCodeRelation
    (rawFormulaImpCode M conclusionShiftCode
      (rawFormulaImpCode M existentialTruthCode
        (rawFormulaImpCode M bodyToBinderCode
          (rawFormulaImpCode M binderToShiftedResultCode resultTruthCode))))
    dynamicTruthRoot
    (rawTemplateProofCode translation
      (coqRestrictedPADirectExistentialEliminationFormulaCodeRootAt
        readyContext))).
  assert (hdynamicAfterFormula : RawCodedPALocalProofOf M readyContextCode
    (rawFormulaImpCode M conclusionShiftCode
      (rawFormulaImpCode M existentialTruthCode
        (rawFormulaImpCode M bodyToBinderCode
          (rawFormulaImpCode M binderToShiftedResultCode resultTruthCode))))
    dynamicAfterFormulaRoot).
  {
    unfold dynamicAfterFormulaRoot, bodyToBinderCode,
      binderToShiftedResultCode.
    apply (raw_codedPALocalProofOf_impE M hPA readyContextCode
      formulaCodeRelation
      (rawFormulaImpCode M conclusionShiftCode
        (rawFormulaImpCode M existentialTruthCode
          (rawFormulaImpCode M
            (rawFormulaImpCode M bodyTruthCode binderContextTruthCode)
            (rawFormulaImpCode M
              (rawFormulaImpCode M
                binderContextTruthCode shiftedResultTruthCode)
              resultTruthCode))))
      dynamicTruthRoot
      (rawTemplateProofCode translation
        (coqRestrictedPADirectExistentialEliminationFormulaCodeRootAt
          readyContext))).
    - exact hdynamicTruthLaw.
    - unfold formulaCodeRelation. exact hformulaCode.
  }

  set (dynamicAfterShiftRoot := rawProofImpERoot M readyContextCode
    conclusionShiftCode
    (rawFormulaImpCode M existentialTruthCode
      (rawFormulaImpCode M bodyToBinderCode
        (rawFormulaImpCode M binderToShiftedResultCode resultTruthCode)))
    dynamicAfterFormulaRoot
    (rawTemplateProofCode translation
      (coqRestrictedPADirectExistentialEliminationConclusionShiftRootAt
        readyContext))).
  assert (hdynamicAfterShift : RawCodedPALocalProofOf M readyContextCode
    (rawFormulaImpCode M existentialTruthCode
      (rawFormulaImpCode M bodyToBinderCode
        (rawFormulaImpCode M binderToShiftedResultCode resultTruthCode)))
    dynamicAfterShiftRoot).
  {
    unfold dynamicAfterShiftRoot.
    apply (raw_codedPALocalProofOf_impE M hPA readyContextCode
      conclusionShiftCode
      (rawFormulaImpCode M existentialTruthCode
        (rawFormulaImpCode M bodyToBinderCode
          (rawFormulaImpCode M binderToShiftedResultCode resultTruthCode)))
      dynamicAfterFormulaRoot
      (rawTemplateProofCode translation
        (coqRestrictedPADirectExistentialEliminationConclusionShiftRootAt
          readyContext))).
    - exact hdynamicAfterFormula.
    - unfold conclusionShiftCode. exact hconclusionShift.
  }

  set (dynamicAfterExistentialRoot := rawProofImpERoot M readyContextCode
    existentialTruthCode
    (rawFormulaImpCode M bodyToBinderCode
      (rawFormulaImpCode M binderToShiftedResultCode resultTruthCode))
    dynamicAfterShiftRoot existentialTruthRoot).
  assert (hdynamicAfterExistential : RawCodedPALocalProofOf M
    readyContextCode
    (rawFormulaImpCode M bodyToBinderCode
      (rawFormulaImpCode M binderToShiftedResultCode resultTruthCode))
    dynamicAfterExistentialRoot).
  {
    unfold dynamicAfterExistentialRoot.
    apply (raw_codedPALocalProofOf_impE M hPA readyContextCode
      existentialTruthCode
      (rawFormulaImpCode M bodyToBinderCode
        (rawFormulaImpCode M binderToShiftedResultCode resultTruthCode))
      dynamicAfterShiftRoot existentialTruthRoot).
    - exact hdynamicAfterShift.
    - exact hexistentialTruth.
  }

  set (dynamicAfterBinderRoot := rawProofImpERoot M readyContextCode
    bodyToBinderCode
    (rawFormulaImpCode M binderToShiftedResultCode resultTruthCode)
    dynamicAfterExistentialRoot bodyToBinderRoot).
  assert (hdynamicAfterBinder : RawCodedPALocalProofOf M readyContextCode
    (rawFormulaImpCode M binderToShiftedResultCode resultTruthCode)
    dynamicAfterBinderRoot).
  {
    unfold dynamicAfterBinderRoot.
    apply (raw_codedPALocalProofOf_impE M hPA readyContextCode
      bodyToBinderCode
      (rawFormulaImpCode M binderToShiftedResultCode resultTruthCode)
      dynamicAfterExistentialRoot bodyToBinderRoot).
    - exact hdynamicAfterExistential.
    - exact hbodyToBinder.
  }

  set (resultTruthRoot := rawProofImpERoot M readyContextCode
    binderToShiftedResultCode resultTruthCode dynamicAfterBinderRoot
    bodyAfterEndpointRoot).
  assert (hresultTruth : RawCodedPALocalProofOf M readyContextCode
    resultTruthCode resultTruthRoot).
  {
    unfold resultTruthRoot.
    apply (raw_codedPALocalProofOf_impE M hPA readyContextCode
      binderToShiftedResultCode resultTruthCode dynamicAfterBinderRoot
      bodyAfterEndpointRoot).
    - exact hdynamicAfterBinder.
    - exact hbodyAfterEndpoint.
  }

  exists (rawProofImpERoot M readyContextCode resultTruthCode
    outerConclusionTruthCode
    (rawTemplateProofCode translation
      (coqRestrictedPADirectExistentialEliminationConclusionTransportRootAt
        readyContext))
    resultTruthRoot).
  apply (raw_codedPALocalProofOf_impE M hPA readyContextCode
    resultTruthCode outerConclusionTruthCode
    (rawTemplateProofCode translation
      (coqRestrictedPADirectExistentialEliminationConclusionTransportRootAt
        readyContext))
    resultTruthRoot).
  - exact htransport.
  - exact hresultTruth.
Qed.

(** ------------------------------------------------------------------
    Exact public slot of the seventeen-case strong-step family. *)

Theorem raw_coqRestrictedPADirectStrongStepExistentialEliminationCaseRoot :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectExistentialEliminationSemanticRoots
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
            rawCoqRuleExElimination
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
    coqRestrictedPADirectStrongStepExistentialEliminationDeepEndpointContext
      tail).
  set (caseContext :=
    coqRestrictedPADirectStrongStepExistentialEliminationCaseContext tail).
  set (admissibleContext :=
    coqRestrictedPADirectStrongStepExistentialEliminationAdmissibleContext tail).
  set (readyContext :=
    coqRestrictedPADirectStrongStepExistentialEliminationReadyContext tail).
  destruct
    (raw_codedPALocalProofOf_coqRestrictedPADirectExistentialEliminationConclusion
      M hPA inputs tail hsemanticRoots) as
    [conclusionRoot hconclusion].

  set (baseContextCode := rawTemplateContextCode translation baseContext).
  set (caseContextCode := rawTemplateContextCode translation caseContext).
  set (admissibleContextCode :=
    rawTemplateContextCode translation admissibleContext).
  set (readyContextCode := rawTemplateContextCode translation readyContext).
  set (caseCode := rawTemplateFormula translation
    coqRestrictedPADirectExistentialEliminationCaseTemplate).
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
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationCase.
