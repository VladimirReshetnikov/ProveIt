(**
  The genuine disjunction-elimination constructor case for the direct
  derivation-soundness strong step.

  At the eight-witness endpoint depth the dispatcher exposes

    outerConclusion = result,
    disjunctionCode = Or(left, right),
    endpoint(disjunctionChild, witnessContext, disjunctionCode),
    endpoint(leftChild, left :: witnessContext, result),
    endpoint(rightChild, right :: witnessContext, result).

  Every displayed field is projected below.  The endpoint witness equality
  transports outer context truth to [witnessContext].  Four deliberately
  sharp semantic roots then expose the actual recursion/Tarski boundary:

  - the disjunction child yields truth of the displayed disjunction;
  - each case child yields [left -> result] or [right -> result], including
    the genuinely dynamic context extension by its assumed disjunct; and
  - the disjunction Tarski law combines those three child results.

  The proof applies those roots in the checked Or-elimination order and
  transports truth of [result] back along [outerConclusion = result].  No
  desired branch, desired conclusion, strong-step root, or equality
  transport is assumed.  Literal projections, equality symmetry/elimination,
  modus ponens, and exact shell implication introductions are compiled as
  model-coded PA proofs.
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
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationCase.

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

Definition coqRestrictedPADirectOrEliminationCodeEqualityTemplate
    : TemplateFormula :=
  embedPAFormula
    (pEq (liftTerm 8 (tVar 4))
      (proofOrECodeTerm (tVar 7) (tVar 6) (tVar 5) (tVar 4)
        (tVar 2) (tVar 1) (tVar 0))).

(** The common conclusion of the two case children occupies witness slot
    four.  It is distinct from the outer conclusion, which was present before
    opening the eight endpoint witnesses. *)
Definition coqRestrictedPADirectOrEliminationResultFormulaTerm
    : TemplateTerm := ttVar 4.

Definition coqRestrictedPADirectOrEliminationConclusionEqualityTemplate
    : TemplateFormula :=
  tfEq coqRestrictedPADirectAssumptionOuterConclusionTerm
    coqRestrictedPADirectOrEliminationResultFormulaTerm.

Definition coqRestrictedPADirectOrEliminationFormulaCodeTemplate
    : TemplateFormula :=
  embedPAFormula
    (formulaOrCodeTermAt (tVar 3) (tVar 6) (tVar 5)).

Definition coqRestrictedPADirectOrEliminationDisjunctionEndpointTemplate
    : TemplateFormula :=
  embedPAFormula
    (proofEndpointTermAt (tVar 2) (tVar 7) (tVar 3)).

Definition coqRestrictedPADirectOrEliminationLeftEndpointTemplate
    : TemplateFormula :=
  embedPAFormula
    (proofEndpointTermAt (tVar 1)
      (nodeTerm (tVar 6) (tVar 7)) (tVar 4)).

Definition coqRestrictedPADirectOrEliminationRightEndpointTemplate
    : TemplateFormula :=
  embedPAFormula
    (proofEndpointTermAt (tVar 0)
      (nodeTerm (tVar 5) (tVar 7)) (tVar 4)).

Definition coqRestrictedPADirectOrEliminationTerminalTruthTemplate
    : TemplateFormula :=
  embedPAFormula (pEq tZero tZero).

Definition coqRestrictedPADirectOrEliminationRightEndpointSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectOrEliminationRightEndpointTemplate
    coqRestrictedPADirectOrEliminationTerminalTruthTemplate.

Definition coqRestrictedPADirectOrEliminationLeftEndpointSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectOrEliminationLeftEndpointTemplate
    coqRestrictedPADirectOrEliminationRightEndpointSuffixTemplate.

Definition
    coqRestrictedPADirectOrEliminationDisjunctionEndpointSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectOrEliminationDisjunctionEndpointTemplate
    coqRestrictedPADirectOrEliminationLeftEndpointSuffixTemplate.

Definition coqRestrictedPADirectOrEliminationFormulaSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectOrEliminationFormulaCodeTemplate
    coqRestrictedPADirectOrEliminationDisjunctionEndpointSuffixTemplate.

Definition coqRestrictedPADirectOrEliminationConclusionSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectOrEliminationConclusionEqualityTemplate
    coqRestrictedPADirectOrEliminationFormulaSuffixTemplate.

Definition coqRestrictedPADirectOrEliminationCaseTemplate
    : TemplateFormula :=
  rawCoqRestrictedPAProofRuleCaseTemplate rawCoqRuleOrElimination
    (liftTerm 8 (tVar 4)) (tVar 7) (liftTerm 8 (tVar 2))
    (tVar 6) (tVar 5) (tVar 4) (tVar 3)
    (tVar 2) (tVar 1) (tVar 0).

Lemma coqRestrictedPADirectOrElimination_case_shape :
  coqRestrictedPADirectOrEliminationCaseTemplate =
  tfAnd coqRestrictedPADirectOrEliminationCodeEqualityTemplate
    coqRestrictedPADirectOrEliminationConclusionSuffixTemplate.
Proof. reflexivity. Qed.

(** ------------------------------------------------------------------
    Truth leaves and the exact semantic residual. *)

Definition coqRestrictedPADirectOrEliminationDisjunctionTruthTemplate
    : TemplateFormula :=
  tfOpaque coqRestrictedPAConclusionTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     ttVar 3; ttVar 9; ttVar 8].

Definition coqRestrictedPADirectOrEliminationLeftTruthTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAssumptionWitnessFormulaTruthTemplate.

Definition coqRestrictedPADirectOrEliminationRightTruthTemplate
    : TemplateFormula :=
  tfOpaque coqRestrictedPAConclusionTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     ttVar 5; ttVar 9; ttVar 8].

Definition coqRestrictedPADirectOrEliminationResultTruthTemplate
    : TemplateFormula :=
  tfOpaque coqRestrictedPAConclusionTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     coqRestrictedPADirectOrEliminationResultFormulaTerm;
     ttVar 9; ttVar 8].

Lemma coqRestrictedPADirectOrElimination_result_truth_shape :
  coqRestrictedPADirectOrEliminationResultTruthTemplate =
  tfOpaque coqRestrictedPAConclusionTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     ttVar 4; ttVar 9; ttVar 8].
Proof. reflexivity. Qed.

(** Equality elimination opens its motive at the case-result term. *)
Lemma coqRestrictedPADirectOrElimination_conclusion_motive_result :
  templateFormulaOpen
    coqRestrictedPADirectOrEliminationResultFormulaTerm
    coqRestrictedPADirectAssumptionConclusionTruthMotive =
  coqRestrictedPADirectOrEliminationResultTruthTemplate.
Proof. reflexivity. Qed.

(** The main child remains in [witnessContext]. *)
Definition coqRestrictedPADirectOrEliminationDisjunctionChildLawTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectOrEliminationDisjunctionEndpointTemplate
    (tfImp coqRestrictedPADirectAssumptionWitnessContextTruthTemplate
      coqRestrictedPADirectOrEliminationDisjunctionTruthTemplate).

(** Each case child is recursively sound in a context extended by the
    corresponding disjunct.  Exposing the result as an implication is the
    exact object-level form of discharging that additional assumption. *)
Definition coqRestrictedPADirectOrEliminationLeftChildLawTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectOrEliminationLeftEndpointTemplate
    (tfImp coqRestrictedPADirectAssumptionWitnessContextTruthTemplate
      (tfImp coqRestrictedPADirectOrEliminationLeftTruthTemplate
        coqRestrictedPADirectOrEliminationResultTruthTemplate)).

Definition coqRestrictedPADirectOrEliminationRightChildLawTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectOrEliminationRightEndpointTemplate
    (tfImp coqRestrictedPADirectAssumptionWitnessContextTruthTemplate
      (tfImp coqRestrictedPADirectOrEliminationRightTruthTemplate
        coqRestrictedPADirectOrEliminationResultTruthTemplate)).

Definition coqRestrictedPADirectOrEliminationDynamicTruthLawTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectOrEliminationFormulaCodeTemplate
    (tfImp coqRestrictedPADirectOrEliminationDisjunctionTruthTemplate
      (tfImp
        (tfImp coqRestrictedPADirectOrEliminationLeftTruthTemplate
          coqRestrictedPADirectOrEliminationResultTruthTemplate)
        (tfImp
          (tfImp coqRestrictedPADirectOrEliminationRightTruthTemplate
            coqRestrictedPADirectOrEliminationResultTruthTemplate)
          coqRestrictedPADirectOrEliminationResultTruthTemplate))).

Lemma rawTemplateFormula_orEliminationDisjunctionChildLaw_view : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  rawTemplateFormula translation
    coqRestrictedPADirectOrEliminationDisjunctionChildLawTemplate =
  rawFormulaImpCode M
    (rawTemplateFormula translation
      coqRestrictedPADirectOrEliminationDisjunctionEndpointTemplate)
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionWitnessContextTruthTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectOrEliminationDisjunctionTruthTemplate)).
Proof.
  intros M translation.
  unfold coqRestrictedPADirectOrEliminationDisjunctionChildLawTemplate.
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectOrEliminationDisjunctionEndpointTemplate
    (tfImp coqRestrictedPADirectAssumptionWitnessContextTruthTemplate
      coqRestrictedPADirectOrEliminationDisjunctionTruthTemplate)).
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectAssumptionWitnessContextTruthTemplate
    coqRestrictedPADirectOrEliminationDisjunctionTruthTemplate).
  reflexivity.
Qed.

(** A single view lemma serves both case-child laws. *)
Lemma rawTemplateFormula_orEliminationCaseChildLaw_view : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    endpointTruth disjunctTruth,
  rawTemplateFormula translation
    (tfImp endpointTruth
      (tfImp coqRestrictedPADirectAssumptionWitnessContextTruthTemplate
        (tfImp disjunctTruth
          coqRestrictedPADirectOrEliminationResultTruthTemplate))) =
  rawFormulaImpCode M (rawTemplateFormula translation endpointTruth)
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionWitnessContextTruthTemplate)
      (rawFormulaImpCode M
        (rawTemplateFormula translation disjunctTruth)
        (rawTemplateFormula translation
          coqRestrictedPADirectOrEliminationResultTruthTemplate))).
Proof.
  intros M translation endpointTruth disjunctTruth.
  rewrite (rawTemplateFormula_imp translation endpointTruth
    (tfImp coqRestrictedPADirectAssumptionWitnessContextTruthTemplate
      (tfImp disjunctTruth
        coqRestrictedPADirectOrEliminationResultTruthTemplate))).
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectAssumptionWitnessContextTruthTemplate
    (tfImp disjunctTruth
      coqRestrictedPADirectOrEliminationResultTruthTemplate)).
  rewrite (rawTemplateFormula_imp translation disjunctTruth
    coqRestrictedPADirectOrEliminationResultTruthTemplate).
  reflexivity.
Qed.

Lemma rawTemplateFormula_orEliminationDynamicTruthLaw_view : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  rawTemplateFormula translation
    coqRestrictedPADirectOrEliminationDynamicTruthLawTemplate =
  rawFormulaImpCode M
    (rawTemplateFormula translation
      coqRestrictedPADirectOrEliminationFormulaCodeTemplate)
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectOrEliminationDisjunctionTruthTemplate)
      (rawFormulaImpCode M
        (rawFormulaImpCode M
          (rawTemplateFormula translation
            coqRestrictedPADirectOrEliminationLeftTruthTemplate)
          (rawTemplateFormula translation
            coqRestrictedPADirectOrEliminationResultTruthTemplate))
        (rawFormulaImpCode M
          (rawFormulaImpCode M
            (rawTemplateFormula translation
              coqRestrictedPADirectOrEliminationRightTruthTemplate)
            (rawTemplateFormula translation
              coqRestrictedPADirectOrEliminationResultTruthTemplate))
          (rawTemplateFormula translation
            coqRestrictedPADirectOrEliminationResultTruthTemplate)))).
Proof.
  intros M translation.
  unfold coqRestrictedPADirectOrEliminationDynamicTruthLawTemplate.
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectOrEliminationFormulaCodeTemplate
    (tfImp coqRestrictedPADirectOrEliminationDisjunctionTruthTemplate
      (tfImp
        (tfImp coqRestrictedPADirectOrEliminationLeftTruthTemplate
          coqRestrictedPADirectOrEliminationResultTruthTemplate)
        (tfImp
          (tfImp coqRestrictedPADirectOrEliminationRightTruthTemplate
            coqRestrictedPADirectOrEliminationResultTruthTemplate)
          coqRestrictedPADirectOrEliminationResultTruthTemplate)))).
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectOrEliminationDisjunctionTruthTemplate
    (tfImp
      (tfImp coqRestrictedPADirectOrEliminationLeftTruthTemplate
        coqRestrictedPADirectOrEliminationResultTruthTemplate)
      (tfImp
        (tfImp coqRestrictedPADirectOrEliminationRightTruthTemplate
          coqRestrictedPADirectOrEliminationResultTruthTemplate)
        coqRestrictedPADirectOrEliminationResultTruthTemplate))).
  rewrite (rawTemplateFormula_imp translation
    (tfImp coqRestrictedPADirectOrEliminationLeftTruthTemplate
      coqRestrictedPADirectOrEliminationResultTruthTemplate)
    (tfImp
      (tfImp coqRestrictedPADirectOrEliminationRightTruthTemplate
        coqRestrictedPADirectOrEliminationResultTruthTemplate)
      coqRestrictedPADirectOrEliminationResultTruthTemplate)).
  rewrite (rawTemplateFormula_imp translation
    (tfImp coqRestrictedPADirectOrEliminationRightTruthTemplate
      coqRestrictedPADirectOrEliminationResultTruthTemplate)
    coqRestrictedPADirectOrEliminationResultTruthTemplate).
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectOrEliminationLeftTruthTemplate
    coqRestrictedPADirectOrEliminationResultTruthTemplate).
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectOrEliminationRightTruthTemplate
    coqRestrictedPADirectOrEliminationResultTruthTemplate).
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    Exact shell contexts and residual root interfaces. *)

Definition
    coqRestrictedPADirectStrongStepOrEliminationDeepEndpointContext
    (tail : TemplateContext) : TemplateContext :=
  rawCoqRestrictedPADirectEndpointWitnessBodyTemplate ::
    rawCoqRestrictedPADirectEndpointDeepTail
      (rawCoqRestrictedPADirectStrongStepEndpointTail tail).

Definition coqRestrictedPADirectStrongStepOrEliminationCaseContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectOrEliminationCaseTemplate ::
    coqRestrictedPADirectStrongStepOrEliminationDeepEndpointContext
      tail.

Definition
    coqRestrictedPADirectStrongStepOrEliminationAdmissibleContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectAssumptionDeepAdmissibleTemplate ::
    coqRestrictedPADirectStrongStepOrEliminationCaseContext tail.

Definition coqRestrictedPADirectStrongStepOrEliminationReadyContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectAssumptionOuterContextTruthTemplate ::
    coqRestrictedPADirectStrongStepOrEliminationAdmissibleContext tail.

Arguments
  coqRestrictedPADirectStrongStepOrEliminationDeepEndpointContext
  tail : clear implicits.
Arguments coqRestrictedPADirectStrongStepOrEliminationCaseContext
  tail : clear implicits.
Arguments
  coqRestrictedPADirectStrongStepOrEliminationAdmissibleContext
  tail : clear implicits.
Arguments coqRestrictedPADirectStrongStepOrEliminationReadyContext
  tail : clear implicits.

Definition RawCoqRestrictedPADirectOrEliminationSemanticRoots
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop :=
  (exists disjunctionChildRoot : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectStrongStepOrEliminationReadyContext tail))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectOrEliminationDisjunctionChildLawTemplate)
      disjunctionChildRoot) /\
  (exists leftChildRoot : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectStrongStepOrEliminationReadyContext tail))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectOrEliminationLeftChildLawTemplate)
      leftChildRoot) /\
  (exists rightChildRoot : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectStrongStepOrEliminationReadyContext tail))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectOrEliminationRightChildLawTemplate)
      rightChildRoot) /\
  (exists dynamicTruthRoot : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectStrongStepOrEliminationReadyContext tail))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectOrEliminationDynamicTruthLawTemplate)
      dynamicTruthRoot).

Arguments RawCoqRestrictedPADirectOrEliminationSemanticRoots
  M hPA inputs tail : clear implicits.

(** ------------------------------------------------------------------
    Parameterized finite branch projections. *)

Definition coqRestrictedPADirectOrEliminationCaseRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAss context coqRestrictedPADirectOrEliminationCaseTemplate.

Definition coqRestrictedPADirectOrEliminationCodeEqualityRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectOrEliminationCodeEqualityTemplate
    coqRestrictedPADirectOrEliminationConclusionSuffixTemplate
    (coqRestrictedPADirectOrEliminationCaseRootAt context).

Definition coqRestrictedPADirectOrEliminationConclusionSuffixRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE2 context
    coqRestrictedPADirectOrEliminationCodeEqualityTemplate
    coqRestrictedPADirectOrEliminationConclusionSuffixTemplate
    (coqRestrictedPADirectOrEliminationCaseRootAt context).

Definition coqRestrictedPADirectOrEliminationConclusionEqualityRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectOrEliminationConclusionEqualityTemplate
    coqRestrictedPADirectOrEliminationFormulaSuffixTemplate
    (coqRestrictedPADirectOrEliminationConclusionSuffixRootAt context).

Definition coqRestrictedPADirectOrEliminationFormulaSuffixRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE2 context
    coqRestrictedPADirectOrEliminationConclusionEqualityTemplate
    coqRestrictedPADirectOrEliminationFormulaSuffixTemplate
    (coqRestrictedPADirectOrEliminationConclusionSuffixRootAt context).

Definition coqRestrictedPADirectOrEliminationFormulaCodeRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectOrEliminationFormulaCodeTemplate
    coqRestrictedPADirectOrEliminationDisjunctionEndpointSuffixTemplate
    (coqRestrictedPADirectOrEliminationFormulaSuffixRootAt context).

Definition
    coqRestrictedPADirectOrEliminationDisjunctionEndpointSuffixRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE2 context
    coqRestrictedPADirectOrEliminationFormulaCodeTemplate
    coqRestrictedPADirectOrEliminationDisjunctionEndpointSuffixTemplate
    (coqRestrictedPADirectOrEliminationFormulaSuffixRootAt context).

Definition coqRestrictedPADirectOrEliminationDisjunctionEndpointRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectOrEliminationDisjunctionEndpointTemplate
    coqRestrictedPADirectOrEliminationLeftEndpointSuffixTemplate
    (coqRestrictedPADirectOrEliminationDisjunctionEndpointSuffixRootAt
      context).

Definition coqRestrictedPADirectOrEliminationLeftEndpointSuffixRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE2 context
    coqRestrictedPADirectOrEliminationDisjunctionEndpointTemplate
    coqRestrictedPADirectOrEliminationLeftEndpointSuffixTemplate
    (coqRestrictedPADirectOrEliminationDisjunctionEndpointSuffixRootAt
      context).

Definition coqRestrictedPADirectOrEliminationLeftEndpointRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectOrEliminationLeftEndpointTemplate
    coqRestrictedPADirectOrEliminationRightEndpointSuffixTemplate
    (coqRestrictedPADirectOrEliminationLeftEndpointSuffixRootAt context).

Definition coqRestrictedPADirectOrEliminationRightEndpointSuffixRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE2 context
    coqRestrictedPADirectOrEliminationLeftEndpointTemplate
    coqRestrictedPADirectOrEliminationRightEndpointSuffixTemplate
    (coqRestrictedPADirectOrEliminationLeftEndpointSuffixRootAt context).

Definition coqRestrictedPADirectOrEliminationRightEndpointRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectOrEliminationRightEndpointTemplate
    coqRestrictedPADirectOrEliminationTerminalTruthTemplate
    (coqRestrictedPADirectOrEliminationRightEndpointSuffixRootAt context).

Lemma coqRestrictedPADirectOrEliminationCaseRootAt_valid :
  forall context,
  In coqRestrictedPADirectOrEliminationCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectOrEliminationCaseTemplate
    (coqRestrictedPADirectOrEliminationCaseRootAt context).
Proof.
  intros context hin. apply templateRawDerives_assumption. exact hin.
Qed.

Lemma coqRestrictedPADirectOrEliminationCodeEqualityRootAt_valid :
  forall context,
  In coqRestrictedPADirectOrEliminationCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectOrEliminationCodeEqualityTemplate
    (coqRestrictedPADirectOrEliminationCodeEqualityRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectOrEliminationCodeEqualityRootAt.
  apply templateAndLeftFrom_derives.
  rewrite <- coqRestrictedPADirectOrElimination_case_shape.
  apply coqRestrictedPADirectOrEliminationCaseRootAt_valid. exact hin.
Qed.

Lemma coqRestrictedPADirectOrEliminationConclusionSuffixRootAt_valid :
  forall context,
  In coqRestrictedPADirectOrEliminationCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectOrEliminationConclusionSuffixTemplate
    (coqRestrictedPADirectOrEliminationConclusionSuffixRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectOrEliminationConclusionSuffixRootAt.
  apply templateAndRightFrom_derives.
  rewrite <- coqRestrictedPADirectOrElimination_case_shape.
  apply coqRestrictedPADirectOrEliminationCaseRootAt_valid. exact hin.
Qed.

Lemma coqRestrictedPADirectOrEliminationConclusionEqualityRootAt_valid :
  forall context,
  In coqRestrictedPADirectOrEliminationCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectOrEliminationConclusionEqualityTemplate
    (coqRestrictedPADirectOrEliminationConclusionEqualityRootAt
      context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectOrEliminationConclusionEqualityRootAt.
  apply templateAndLeftFrom_derives.
  apply coqRestrictedPADirectOrEliminationConclusionSuffixRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectOrEliminationFormulaSuffixRootAt_valid :
  forall context,
  In coqRestrictedPADirectOrEliminationCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectOrEliminationFormulaSuffixTemplate
    (coqRestrictedPADirectOrEliminationFormulaSuffixRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectOrEliminationFormulaSuffixRootAt.
  apply templateAndRightFrom_derives.
  apply coqRestrictedPADirectOrEliminationConclusionSuffixRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectOrEliminationFormulaCodeRootAt_valid :
  forall context,
  In coqRestrictedPADirectOrEliminationCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectOrEliminationFormulaCodeTemplate
    (coqRestrictedPADirectOrEliminationFormulaCodeRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectOrEliminationFormulaCodeRootAt.
  apply templateAndLeftFrom_derives.
  apply coqRestrictedPADirectOrEliminationFormulaSuffixRootAt_valid.
  exact hin.
Qed.

Lemma
    coqRestrictedPADirectOrEliminationDisjunctionEndpointSuffixRootAt_valid :
  forall context,
  In coqRestrictedPADirectOrEliminationCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectOrEliminationDisjunctionEndpointSuffixTemplate
    (coqRestrictedPADirectOrEliminationDisjunctionEndpointSuffixRootAt
      context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectOrEliminationDisjunctionEndpointSuffixRootAt.
  apply templateAndRightFrom_derives.
  apply coqRestrictedPADirectOrEliminationFormulaSuffixRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectOrEliminationDisjunctionEndpointRootAt_valid :
  forall context,
  In coqRestrictedPADirectOrEliminationCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectOrEliminationDisjunctionEndpointTemplate
    (coqRestrictedPADirectOrEliminationDisjunctionEndpointRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectOrEliminationDisjunctionEndpointRootAt.
  apply templateAndLeftFrom_derives.
  apply
    coqRestrictedPADirectOrEliminationDisjunctionEndpointSuffixRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectOrEliminationLeftEndpointSuffixRootAt_valid :
  forall context,
  In coqRestrictedPADirectOrEliminationCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectOrEliminationLeftEndpointSuffixTemplate
    (coqRestrictedPADirectOrEliminationLeftEndpointSuffixRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectOrEliminationLeftEndpointSuffixRootAt.
  apply templateAndRightFrom_derives.
  apply
    coqRestrictedPADirectOrEliminationDisjunctionEndpointSuffixRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectOrEliminationLeftEndpointRootAt_valid :
  forall context,
  In coqRestrictedPADirectOrEliminationCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectOrEliminationLeftEndpointTemplate
    (coqRestrictedPADirectOrEliminationLeftEndpointRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectOrEliminationLeftEndpointRootAt.
  apply templateAndLeftFrom_derives.
  apply coqRestrictedPADirectOrEliminationLeftEndpointSuffixRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectOrEliminationRightEndpointSuffixRootAt_valid :
  forall context,
  In coqRestrictedPADirectOrEliminationCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectOrEliminationRightEndpointSuffixTemplate
    (coqRestrictedPADirectOrEliminationRightEndpointSuffixRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectOrEliminationRightEndpointSuffixRootAt.
  apply templateAndRightFrom_derives.
  apply coqRestrictedPADirectOrEliminationLeftEndpointSuffixRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectOrEliminationRightEndpointRootAt_valid :
  forall context,
  In coqRestrictedPADirectOrEliminationCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectOrEliminationRightEndpointTemplate
    (coqRestrictedPADirectOrEliminationRightEndpointRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectOrEliminationRightEndpointRootAt.
  apply templateAndLeftFrom_derives.
  apply coqRestrictedPADirectOrEliminationRightEndpointSuffixRootAt_valid.
  exact hin.
Qed.

(** ------------------------------------------------------------------
    A fully compiled truth transport along [outerConclusion = result]. *)

Definition coqRestrictedPADirectOrEliminationTransportChildContext
    (context : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectOrEliminationResultTruthTemplate :: context.

Definition coqRestrictedPADirectOrEliminationConclusionSymmetryRootAt
    (context : TemplateContext) : TemplateRawProof :=
  coqRestrictedPADirectEqSymmetryRoot context
    coqRestrictedPADirectAssumptionOuterConclusionTerm
    coqRestrictedPADirectOrEliminationResultFormulaTerm
    (coqRestrictedPADirectOrEliminationConclusionEqualityRootAt
      context).

Definition coqRestrictedPADirectOrEliminationResultTruthRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAss context coqRestrictedPADirectOrEliminationResultTruthTemplate.

Definition coqRestrictedPADirectOrEliminationOuterTruthChildRootAt
    (context : TemplateContext) : TemplateRawProof :=
  let childContext :=
    coqRestrictedPADirectOrEliminationTransportChildContext context in
  trpEqElim childContext
    coqRestrictedPADirectOrEliminationResultFormulaTerm
    coqRestrictedPADirectAssumptionOuterConclusionTerm
    coqRestrictedPADirectAssumptionConclusionTruthMotive
    (coqRestrictedPADirectOrEliminationConclusionSymmetryRootAt
      childContext)
    (coqRestrictedPADirectOrEliminationResultTruthRootAt childContext).

Definition coqRestrictedPADirectOrEliminationConclusionTransportRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpImpI context
    coqRestrictedPADirectOrEliminationResultTruthTemplate
    coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate
    (coqRestrictedPADirectOrEliminationOuterTruthChildRootAt context).

Lemma coqRestrictedPADirectOrEliminationConclusionSymmetryRootAt_valid :
  forall context,
  In coqRestrictedPADirectOrEliminationCaseTemplate context ->
  TemplateRawDerives context
    (tfEq coqRestrictedPADirectOrEliminationResultFormulaTerm
      coqRestrictedPADirectAssumptionOuterConclusionTerm)
    (coqRestrictedPADirectOrEliminationConclusionSymmetryRootAt
      context).
Proof.
  intros context hin.
  apply coqRestrictedPADirectEqSymmetryRoot_valid.
  apply coqRestrictedPADirectOrEliminationConclusionEqualityRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectOrEliminationConclusionTransportRootAt_valid :
  forall context,
  In coqRestrictedPADirectOrEliminationCaseTemplate context ->
  TemplateRawDerives context
    (tfImp coqRestrictedPADirectOrEliminationResultTruthTemplate
      coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate)
    (coqRestrictedPADirectOrEliminationConclusionTransportRootAt
      context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectOrEliminationConclusionTransportRootAt,
    coqRestrictedPADirectOrEliminationOuterTruthChildRootAt.
  cbn zeta.
  apply coqRestrictedPADirect_templateRawDerives_impI.
  rewrite <- coqRestrictedPADirectAssumption_conclusion_motive_outer.
  apply coqRestrictedPADirect_templateRawDerives_eqElim.
  - apply
      coqRestrictedPADirectOrEliminationConclusionSymmetryRootAt_valid.
    right. exact hin.
  - rewrite
      coqRestrictedPADirectOrElimination_conclusion_motive_result.
    apply templateRawDerives_assumption. left. reflexivity.
Qed.

(** ------------------------------------------------------------------
    Compile the semantic residual and the checked Or-elimination spine. *)

  Theorem
    raw_codedPALocalProofOf_coqRestrictedPADirectOrEliminationConclusion
    : forall (M : RawPAModel) (hPA : RawPASatisfies M)
      (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectOrEliminationSemanticRoots
    M hPA inputs tail ->
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectStrongStepOrEliminationReadyContext tail))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate)
      root.
Proof.
  intros M hPA inputs tail
    ((disjunctionChildLawRoot & hdisjunctionChildLaw) &
     (leftChildLawRoot & hleftChildLaw) &
     (rightChildLawRoot & hrightChildLaw) &
     (dynamicTruthLawRoot & hdynamicTruthLaw)).
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  set (readyContext :=
    coqRestrictedPADirectStrongStepOrEliminationReadyContext tail).
  set (readyContextCode :=
    rawTemplateContextCode translation readyContext).

  assert (hcase :
    In coqRestrictedPADirectOrEliminationCaseTemplate readyContext).
  {
    unfold readyContext,
      coqRestrictedPADirectStrongStepOrEliminationReadyContext,
      coqRestrictedPADirectStrongStepOrEliminationAdmissibleContext,
      coqRestrictedPADirectStrongStepOrEliminationCaseContext.
    right. right. left. reflexivity.
  }
  assert (hendpointBody :
    In rawCoqRestrictedPADirectEndpointWitnessBodyTemplate readyContext).
  {
    unfold readyContext,
      coqRestrictedPADirectStrongStepOrEliminationReadyContext,
      coqRestrictedPADirectStrongStepOrEliminationAdmissibleContext,
      coqRestrictedPADirectStrongStepOrEliminationCaseContext,
      coqRestrictedPADirectStrongStepOrEliminationDeepEndpointContext.
    do 3 right. left. reflexivity.
  }
  assert (houterContextTruth :
    In coqRestrictedPADirectAssumptionOuterContextTruthTemplate
      readyContext).
  {
    unfold readyContext,
      coqRestrictedPADirectStrongStepOrEliminationReadyContext.
    left. reflexivity.
  }

  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectOrEliminationFormulaCodeRootAt readyContext)
    (proj1
      (coqRestrictedPADirectOrEliminationFormulaCodeRootAt_valid
        readyContext hcase))) as hformulaCode.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectOrEliminationDisjunctionEndpointRootAt
      readyContext)
    (proj1
      (coqRestrictedPADirectOrEliminationDisjunctionEndpointRootAt_valid
        readyContext hcase))) as hdisjunctionEndpoint.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectOrEliminationLeftEndpointRootAt readyContext)
    (proj1
      (coqRestrictedPADirectOrEliminationLeftEndpointRootAt_valid
        readyContext hcase))) as hleftEndpoint.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectOrEliminationRightEndpointRootAt readyContext)
    (proj1
      (coqRestrictedPADirectOrEliminationRightEndpointRootAt_valid
        readyContext hcase))) as hrightEndpoint.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt readyContext)
    (proj1
      (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt_valid
        readyContext hendpointBody houterContextTruth)))
    as hwitnessContextTruth.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectOrEliminationConclusionTransportRootAt
      readyContext)
    (proj1
      (coqRestrictedPADirectOrEliminationConclusionTransportRootAt_valid
        readyContext hcase))) as htransport.

  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectOrEliminationFormulaCodeTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectOrEliminationFormulaCodeRootAt
        readyContext))) in hformulaCode.
  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectOrEliminationDisjunctionEndpointTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectOrEliminationDisjunctionEndpointRootAt
        readyContext))) in hdisjunctionEndpoint.
  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectOrEliminationLeftEndpointTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectOrEliminationLeftEndpointRootAt
        readyContext))) in hleftEndpoint.
  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectOrEliminationRightEndpointTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectOrEliminationRightEndpointRootAt
        readyContext))) in hrightEndpoint.
  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectAssumptionWitnessContextTruthTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt
        readyContext))) in hwitnessContextTruth.
  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      (tfImp coqRestrictedPADirectOrEliminationResultTruthTemplate
        coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate))
    (rawTemplateProofCode translation
      (coqRestrictedPADirectOrEliminationConclusionTransportRootAt
        readyContext))) in htransport.
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectOrEliminationResultTruthTemplate
    coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate)
    in htransport.

  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectOrEliminationDisjunctionChildLawTemplate)
    disjunctionChildLawRoot) in hdisjunctionChildLaw.
  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectOrEliminationLeftChildLawTemplate)
    leftChildLawRoot) in hleftChildLaw.
  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectOrEliminationRightChildLawTemplate)
    rightChildLawRoot) in hrightChildLaw.
  change (RawCodedPALocalProofOf M readyContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectOrEliminationDynamicTruthLawTemplate)
    dynamicTruthLawRoot) in hdynamicTruthLaw.
  rewrite rawTemplateFormula_orEliminationDisjunctionChildLaw_view
    in hdisjunctionChildLaw.
  unfold coqRestrictedPADirectOrEliminationLeftChildLawTemplate
    in hleftChildLaw.
  rewrite rawTemplateFormula_orEliminationCaseChildLaw_view
    in hleftChildLaw.
  unfold coqRestrictedPADirectOrEliminationRightChildLawTemplate
    in hrightChildLaw.
  rewrite rawTemplateFormula_orEliminationCaseChildLaw_view
    in hrightChildLaw.
  rewrite rawTemplateFormula_orEliminationDynamicTruthLaw_view
    in hdynamicTruthLaw.

  set (disjunctionEndpointCode := rawTemplateFormula translation
    coqRestrictedPADirectOrEliminationDisjunctionEndpointTemplate).
  set (leftEndpointCode := rawTemplateFormula translation
    coqRestrictedPADirectOrEliminationLeftEndpointTemplate).
  set (rightEndpointCode := rawTemplateFormula translation
    coqRestrictedPADirectOrEliminationRightEndpointTemplate).
  set (witnessContextTruthCode := rawTemplateFormula translation
    coqRestrictedPADirectAssumptionWitnessContextTruthTemplate).
  set (disjunctionTruthCode := rawTemplateFormula translation
    coqRestrictedPADirectOrEliminationDisjunctionTruthTemplate).
  set (leftTruthCode := rawTemplateFormula translation
    coqRestrictedPADirectOrEliminationLeftTruthTemplate).
  set (rightTruthCode := rawTemplateFormula translation
    coqRestrictedPADirectOrEliminationRightTruthTemplate).
  set (formulaCodeRelation := rawTemplateFormula translation
    coqRestrictedPADirectOrEliminationFormulaCodeTemplate).
  set (resultTruthCode := rawTemplateFormula translation
    coqRestrictedPADirectOrEliminationResultTruthTemplate).
  set (outerConclusionTruthCode := rawTemplateFormula translation
    coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate).
  set (leftToResultCode :=
    rawFormulaImpCode M leftTruthCode resultTruthCode).
  set (rightToResultCode :=
    rawFormulaImpCode M rightTruthCode resultTruthCode).

  (** First child: obtain truth of the displayed disjunction. *)
  set (disjunctionAfterEndpointRoot := rawProofImpERoot M readyContextCode
    disjunctionEndpointCode
    (rawFormulaImpCode M witnessContextTruthCode disjunctionTruthCode)
    disjunctionChildLawRoot
    (rawTemplateProofCode translation
      (coqRestrictedPADirectOrEliminationDisjunctionEndpointRootAt
        readyContext))).
  assert (hdisjunctionAfterEndpoint : RawCodedPALocalProofOf M
    readyContextCode
    (rawFormulaImpCode M witnessContextTruthCode disjunctionTruthCode)
    disjunctionAfterEndpointRoot).
  {
    unfold disjunctionAfterEndpointRoot.
    apply (raw_codedPALocalProofOf_impE M hPA readyContextCode
      disjunctionEndpointCode
      (rawFormulaImpCode M witnessContextTruthCode disjunctionTruthCode)
      disjunctionChildLawRoot
      (rawTemplateProofCode translation
        (coqRestrictedPADirectOrEliminationDisjunctionEndpointRootAt
          readyContext))).
    - exact hdisjunctionChildLaw.
    - unfold disjunctionEndpointCode. exact hdisjunctionEndpoint.
  }

  set (disjunctionTruthRoot := rawProofImpERoot M readyContextCode
    witnessContextTruthCode disjunctionTruthCode
    disjunctionAfterEndpointRoot
    (rawTemplateProofCode translation
      (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt
        readyContext))).
  assert (hdisjunctionTruth : RawCodedPALocalProofOf M readyContextCode
    disjunctionTruthCode disjunctionTruthRoot).
  {
    unfold disjunctionTruthRoot.
    apply (raw_codedPALocalProofOf_impE M hPA readyContextCode
      witnessContextTruthCode disjunctionTruthCode
      disjunctionAfterEndpointRoot
      (rawTemplateProofCode translation
        (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt
          readyContext))).
    - exact hdisjunctionAfterEndpoint.
    - unfold witnessContextTruthCode. exact hwitnessContextTruth.
  }

  (** Left case child: discharge its additional left-disjunct context entry. *)
  set (leftAfterEndpointRoot := rawProofImpERoot M readyContextCode
    leftEndpointCode
    (rawFormulaImpCode M witnessContextTruthCode leftToResultCode)
    leftChildLawRoot
    (rawTemplateProofCode translation
      (coqRestrictedPADirectOrEliminationLeftEndpointRootAt readyContext))).
  assert (hleftAfterEndpoint : RawCodedPALocalProofOf M readyContextCode
    (rawFormulaImpCode M witnessContextTruthCode leftToResultCode)
    leftAfterEndpointRoot).
  {
    unfold leftAfterEndpointRoot, leftToResultCode.
    apply (raw_codedPALocalProofOf_impE M hPA readyContextCode
      leftEndpointCode
      (rawFormulaImpCode M witnessContextTruthCode
        (rawFormulaImpCode M leftTruthCode resultTruthCode))
      leftChildLawRoot
      (rawTemplateProofCode translation
        (coqRestrictedPADirectOrEliminationLeftEndpointRootAt
          readyContext))).
    - exact hleftChildLaw.
    - unfold leftEndpointCode. exact hleftEndpoint.
  }

  set (leftToResultRoot := rawProofImpERoot M readyContextCode
    witnessContextTruthCode leftToResultCode leftAfterEndpointRoot
    (rawTemplateProofCode translation
      (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt
        readyContext))).
  assert (hleftToResult : RawCodedPALocalProofOf M readyContextCode
    leftToResultCode leftToResultRoot).
  {
    unfold leftToResultRoot.
    apply (raw_codedPALocalProofOf_impE M hPA readyContextCode
      witnessContextTruthCode leftToResultCode leftAfterEndpointRoot
      (rawTemplateProofCode translation
        (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt
          readyContext))).
    - exact hleftAfterEndpoint.
    - unfold witnessContextTruthCode. exact hwitnessContextTruth.
  }

  (** Right case child, symmetrically. *)
  set (rightAfterEndpointRoot := rawProofImpERoot M readyContextCode
    rightEndpointCode
    (rawFormulaImpCode M witnessContextTruthCode rightToResultCode)
    rightChildLawRoot
    (rawTemplateProofCode translation
      (coqRestrictedPADirectOrEliminationRightEndpointRootAt readyContext))).
  assert (hrightAfterEndpoint : RawCodedPALocalProofOf M readyContextCode
    (rawFormulaImpCode M witnessContextTruthCode rightToResultCode)
    rightAfterEndpointRoot).
  {
    unfold rightAfterEndpointRoot, rightToResultCode.
    apply (raw_codedPALocalProofOf_impE M hPA readyContextCode
      rightEndpointCode
      (rawFormulaImpCode M witnessContextTruthCode
        (rawFormulaImpCode M rightTruthCode resultTruthCode))
      rightChildLawRoot
      (rawTemplateProofCode translation
        (coqRestrictedPADirectOrEliminationRightEndpointRootAt
          readyContext))).
    - exact hrightChildLaw.
    - unfold rightEndpointCode. exact hrightEndpoint.
  }

  set (rightToResultRoot := rawProofImpERoot M readyContextCode
    witnessContextTruthCode rightToResultCode rightAfterEndpointRoot
    (rawTemplateProofCode translation
      (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt
        readyContext))).
  assert (hrightToResult : RawCodedPALocalProofOf M readyContextCode
    rightToResultCode rightToResultRoot).
  {
    unfold rightToResultRoot.
    apply (raw_codedPALocalProofOf_impE M hPA readyContextCode
      witnessContextTruthCode rightToResultCode rightAfterEndpointRoot
      (rawTemplateProofCode translation
        (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt
          readyContext))).
    - exact hrightAfterEndpoint.
    - unfold witnessContextTruthCode. exact hwitnessContextTruth.
  }

  (** Checked Tarski Or-elimination spine. *)
  set (dynamicAfterFormulaRoot := rawProofImpERoot M readyContextCode
    formulaCodeRelation
    (rawFormulaImpCode M disjunctionTruthCode
      (rawFormulaImpCode M leftToResultCode
        (rawFormulaImpCode M rightToResultCode resultTruthCode)))
    dynamicTruthLawRoot
    (rawTemplateProofCode translation
      (coqRestrictedPADirectOrEliminationFormulaCodeRootAt
        readyContext))).
  assert (hdynamicAfterFormula : RawCodedPALocalProofOf M readyContextCode
    (rawFormulaImpCode M disjunctionTruthCode
      (rawFormulaImpCode M leftToResultCode
        (rawFormulaImpCode M rightToResultCode resultTruthCode)))
    dynamicAfterFormulaRoot).
  {
    unfold dynamicAfterFormulaRoot.
    apply (raw_codedPALocalProofOf_impE M hPA readyContextCode
      formulaCodeRelation
      (rawFormulaImpCode M disjunctionTruthCode
        (rawFormulaImpCode M leftToResultCode
          (rawFormulaImpCode M rightToResultCode resultTruthCode)))
      dynamicTruthLawRoot
      (rawTemplateProofCode translation
        (coqRestrictedPADirectOrEliminationFormulaCodeRootAt
          readyContext))).
    - exact hdynamicTruthLaw.
    - unfold formulaCodeRelation. exact hformulaCode.
  }

  set (dynamicAfterDisjunctionRoot := rawProofImpERoot M readyContextCode
    disjunctionTruthCode
    (rawFormulaImpCode M leftToResultCode
      (rawFormulaImpCode M rightToResultCode resultTruthCode))
    dynamicAfterFormulaRoot disjunctionTruthRoot).
  assert (hdynamicAfterDisjunction : RawCodedPALocalProofOf M
    readyContextCode
    (rawFormulaImpCode M leftToResultCode
      (rawFormulaImpCode M rightToResultCode resultTruthCode))
    dynamicAfterDisjunctionRoot).
  {
    unfold dynamicAfterDisjunctionRoot.
    apply (raw_codedPALocalProofOf_impE M hPA readyContextCode
      disjunctionTruthCode
      (rawFormulaImpCode M leftToResultCode
        (rawFormulaImpCode M rightToResultCode resultTruthCode))
      dynamicAfterFormulaRoot disjunctionTruthRoot).
    - exact hdynamicAfterFormula.
    - exact hdisjunctionTruth.
  }

  set (dynamicAfterLeftRoot := rawProofImpERoot M readyContextCode
    leftToResultCode
    (rawFormulaImpCode M rightToResultCode resultTruthCode)
    dynamicAfterDisjunctionRoot leftToResultRoot).
  assert (hdynamicAfterLeft : RawCodedPALocalProofOf M readyContextCode
    (rawFormulaImpCode M rightToResultCode resultTruthCode)
    dynamicAfterLeftRoot).
  {
    unfold dynamicAfterLeftRoot.
    apply (raw_codedPALocalProofOf_impE M hPA readyContextCode
      leftToResultCode
      (rawFormulaImpCode M rightToResultCode resultTruthCode)
      dynamicAfterDisjunctionRoot leftToResultRoot).
    - exact hdynamicAfterDisjunction.
    - exact hleftToResult.
  }

  set (resultTruthRoot := rawProofImpERoot M readyContextCode
    rightToResultCode resultTruthCode dynamicAfterLeftRoot
    rightToResultRoot).
  assert (hresultTruth : RawCodedPALocalProofOf M readyContextCode
    resultTruthCode resultTruthRoot).
  {
    unfold resultTruthRoot.
    apply (raw_codedPALocalProofOf_impE M hPA readyContextCode
      rightToResultCode resultTruthCode dynamicAfterLeftRoot
      rightToResultRoot).
    - exact hdynamicAfterLeft.
    - exact hrightToResult.
  }

  exists (rawProofImpERoot M readyContextCode resultTruthCode
    outerConclusionTruthCode
    (rawTemplateProofCode translation
      (coqRestrictedPADirectOrEliminationConclusionTransportRootAt
        readyContext))
    resultTruthRoot).
  apply (raw_codedPALocalProofOf_impE M hPA readyContextCode
    resultTruthCode outerConclusionTruthCode
    (rawTemplateProofCode translation
      (coqRestrictedPADirectOrEliminationConclusionTransportRootAt
        readyContext))
    resultTruthRoot).
  - exact htransport.
  - exact hresultTruth.
Qed.

(** ------------------------------------------------------------------
    Exact public slot of the seventeen-case strong-step family. *)

Theorem raw_coqRestrictedPADirectStrongStepOrEliminationCaseRoot :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectOrEliminationSemanticRoots
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
            rawCoqRuleOrElimination
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
    coqRestrictedPADirectStrongStepOrEliminationDeepEndpointContext
      tail).
  set (caseContext :=
    coqRestrictedPADirectStrongStepOrEliminationCaseContext tail).
  set (admissibleContext :=
    coqRestrictedPADirectStrongStepOrEliminationAdmissibleContext tail).
  set (readyContext :=
    coqRestrictedPADirectStrongStepOrEliminationReadyContext tail).
  destruct
    (raw_codedPALocalProofOf_coqRestrictedPADirectOrEliminationConclusion
      M hPA inputs tail hsemanticRoots) as
    [conclusionRoot hconclusion].

  set (baseContextCode := rawTemplateContextCode translation baseContext).
  set (caseContextCode := rawTemplateContextCode translation caseContext).
  set (admissibleContextCode :=
    rawTemplateContextCode translation admissibleContext).
  set (readyContextCode := rawTemplateContextCode translation readyContext).
  set (caseCode := rawTemplateFormula translation
    coqRestrictedPADirectOrEliminationCaseTemplate).
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
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationCase.
