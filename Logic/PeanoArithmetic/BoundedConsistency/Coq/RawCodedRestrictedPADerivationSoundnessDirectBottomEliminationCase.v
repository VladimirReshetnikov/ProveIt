(**
  The genuine bottom-elimination constructor case for the direct strong step.

  Unlike excluded middle, Bot-E has one recursive proof child.  The endpoint
  branch supplies a child whose conclusion is the coded bottom formula.  The
  inherited strong prefix [K(d)] and restricted-root premise must therefore
  be used to obtain a contradiction from truth of the endpoint context.

  This file performs all finite proof plumbing around that recursive step:

  - it projects the Bot-E code equation, bottom-code equation, and child
    endpoint from the literal rule conjunction;
  - it projects [K(d)] and restricted proof from their exact eight-witness
    contexts;
  - it projects the endpoint's context equality and uses two honest equality
    eliminations to transport outer context truth to the witness context;
  - it turns the resulting object-level bottom into arbitrary conclusion
    truth by the genuine Bot-E proof constructor; and
  - it discharges the unused conclusion-admissibility premise and the rule
    case itself.

  The only residual is the exact recursive-child contradiction law.  Given
  [K(d)], restrictedness of [d], the Bot-E constructor data, and truth of the
  child context, it derives object-level bottom.  It mentions neither the
  desired branch implication nor conclusion truth.  Implementing this law
  requires the still-missing object-level compilers for proof-code descent,
  restricted-proof descent, recursive [K] instantiation, and bottom-truth
  refutation.
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
  RawCodedTemplateDirectStructuralTranslation
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixInductionShell
  RawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier
  RawCodedRestrictedPADerivationSoundnessDirectStrongStepShell.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectBottomEliminationCase.

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
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixInductionShell.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectStrongStepShell.

(** ------------------------------------------------------------------
    Generic inherited-context bookkeeping. *)

(** A formula shifted through [count] successive eigenvariable contexts is
    still literally present.  This proof deliberately follows one list
    constructor at a time; simplifying the eventual concrete context would
    normalize the enormous eight-times-renamed soundness suffix. *)
Lemma raw_coqRestrictedPADirectBottom_contextShiftN_inherited : forall
    count context formula,
  In formula context ->
  In (rawCoqTemplateRenameN count formula)
    (rawCoqTemplateContextShiftN count context).
Proof.
  induction count as [|remaining ih];
    intros context formula hin.
  - exact hin.
  - cbn [rawCoqTemplateContextShiftN rawCoqTemplateRenameN].
    apply ih.
    unfold templateContextShift, templateContextRename.
    apply in_map. exact hin.
Qed.

(** The analogous fact for the eight nested existential eliminations. *)
Lemma raw_coqRestrictedPADirectBottom_nestedExContext_inherited : forall
    count body tail formula,
  In formula tail ->
  In (rawCoqTemplateRenameN count formula)
    (rawCoqTemplateNestedExContext count body tail).
Proof.
  induction count as [|remaining ih];
    intros body tail formula hin.
  - right. exact hin.
  - cbn [rawCoqTemplateNestedExContext rawCoqTemplateRenameN].
    apply ih.
    unfold templateContextShift, templateContextRename.
    apply in_map. right. exact hin.
Qed.

(** ------------------------------------------------------------------
    Exact contexts and inherited strong-step premises. *)

Definition coqRestrictedPADirectBottomDeepContext
    (tail : TemplateContext) : TemplateContext :=
  rawCoqRestrictedPADirectEndpointDeepContext
    (rawCoqRestrictedPADirectStrongStepEndpointTail tail).

Definition coqRestrictedPADirectBottomCaseTemplate : TemplateFormula :=
  rawCoqRestrictedPAProofRuleCaseTemplate rawCoqRuleBottomElimination
    (liftTerm 8 (tVar 4)) (tVar 7) (liftTerm 8 (tVar 2))
    (tVar 6) (tVar 5) (tVar 4) (tVar 3)
    (tVar 2) (tVar 1) (tVar 0).

Definition coqRestrictedPADirectBottomCaseContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectBottomCaseTemplate ::
    coqRestrictedPADirectBottomDeepContext tail.

(** [K(d)] has already crossed the four endpoint binders before the endpoint
    implication is introduced, and then crosses all eight rule witnesses. *)
Definition coqRestrictedPADirectBottomStrongPrefixTemplate
    : TemplateFormula :=
  rawCoqTemplateRenameN 8
    (rawCoqTemplateRenameN 4
      coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate).

Definition coqRestrictedPADirectBottomRestrictedProofTemplate
    : TemplateFormula :=
  rawCoqTemplateRenameN 8
    coqRestrictedPADerivationSoundnessRestrictedProofTemplate.

Lemma coqRestrictedPADirectBottom_strongPrefix_in_four_binders : forall tail,
  In
    (rawCoqTemplateRenameN 4
      coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate)
    (rawCoqRestrictedPADirectStrongStepFourBinderContext tail).
Proof.
  intro tail.
  unfold rawCoqRestrictedPADirectStrongStepFourBinderContext.
  apply raw_coqRestrictedPADirectBottom_contextShiftN_inherited.
  left. reflexivity.
Qed.

Lemma coqRestrictedPADirectBottom_strongPrefix_in_endpoint_tail : forall tail,
  In
    (rawCoqTemplateRenameN 4
      coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate)
    (rawCoqRestrictedPADirectStrongStepEndpointTail tail).
Proof.
  intro tail.
  unfold rawCoqRestrictedPADirectStrongStepEndpointTail.
  right.
  exact (coqRestrictedPADirectBottom_strongPrefix_in_four_binders tail).
Qed.

Lemma coqRestrictedPADirectBottom_restricted_in_endpoint_tail : forall tail,
  In coqRestrictedPADerivationSoundnessRestrictedProofTemplate
    (rawCoqRestrictedPADirectStrongStepEndpointTail tail).
Proof.
  intro tail. unfold rawCoqRestrictedPADirectStrongStepEndpointTail.
  left. reflexivity.
Qed.

Lemma coqRestrictedPADirectBottom_strongPrefix_in_case_context : forall tail,
  In coqRestrictedPADirectBottomStrongPrefixTemplate
    (coqRestrictedPADirectBottomCaseContext tail).
Proof.
  intro tail. right.
  unfold coqRestrictedPADirectBottomDeepContext,
    coqRestrictedPADirectBottomStrongPrefixTemplate.
  apply raw_coqRestrictedPADirectBottom_nestedExContext_inherited.
  exact (coqRestrictedPADirectBottom_strongPrefix_in_endpoint_tail tail).
Qed.

Lemma coqRestrictedPADirectBottom_restricted_in_case_context : forall tail,
  In coqRestrictedPADirectBottomRestrictedProofTemplate
    (coqRestrictedPADirectBottomCaseContext tail).
Proof.
  intro tail. right.
  unfold coqRestrictedPADirectBottomDeepContext,
    coqRestrictedPADirectBottomRestrictedProofTemplate.
  apply raw_coqRestrictedPADirectBottom_nestedExContext_inherited.
  exact (coqRestrictedPADirectBottom_restricted_in_endpoint_tail tail).
Qed.

(** ------------------------------------------------------------------
    Literal Bot-E rule fields. *)

Definition coqRestrictedPADirectBottomCodeEqualityTemplate
    : TemplateFormula :=
  embedPAFormula
    (pEq (liftTerm 8 (tVar 4))
      (proofBotECodeTerm (tVar 7) (tVar 6) (tVar 2))).

Definition coqRestrictedPADirectBottomConclusionEqualityTemplate
    : TemplateFormula :=
  embedPAFormula (pEq (liftTerm 8 (tVar 2)) (tVar 6)).

Definition coqRestrictedPADirectBottomFormulaCodeTemplate
    : TemplateFormula :=
  embedPAFormula (formulaBotCodeTermAt (tVar 5)).

Definition coqRestrictedPADirectBottomChildEndpointTemplate
    : TemplateFormula :=
  embedPAFormula (proofEndpointTermAt (tVar 2) (tVar 7) (tVar 5)).

Definition coqRestrictedPADirectBottomTerminalTemplate
    : TemplateFormula :=
  embedPAFormula (pEq tZero tZero).

Definition coqRestrictedPADirectBottomEndpointSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectBottomChildEndpointTemplate
    coqRestrictedPADirectBottomTerminalTemplate.

Definition coqRestrictedPADirectBottomFormulaSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectBottomFormulaCodeTemplate
    coqRestrictedPADirectBottomEndpointSuffixTemplate.

Definition coqRestrictedPADirectBottomConclusionSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectBottomConclusionEqualityTemplate
    coqRestrictedPADirectBottomFormulaSuffixTemplate.

Lemma coqRestrictedPADirectBottom_case_shape :
  coqRestrictedPADirectBottomCaseTemplate =
  tfAnd coqRestrictedPADirectBottomCodeEqualityTemplate
    coqRestrictedPADirectBottomConclusionSuffixTemplate.
Proof. reflexivity. Qed.

(** ------------------------------------------------------------------
    Endpoint context equality and the two truth applications. *)

Definition coqRestrictedPADirectBottomWitnessContextTerm : TemplateTerm :=
  ttVar 7.

Definition coqRestrictedPADirectBottomOuterContextTerm : TemplateTerm :=
  embedPATerm (liftTerm 8 (tVar 3)).

Definition coqRestrictedPADirectBottomContextEqualityTemplate
    : TemplateFormula :=
  tfEq coqRestrictedPADirectBottomWitnessContextTerm
    coqRestrictedPADirectBottomOuterContextTerm.

Lemma coqRestrictedPADirectBottom_endpoint_equality_shape :
  rawCoqRestrictedPADirectEndpointWitnessEqualityTemplate =
  coqRestrictedPADirectBottomContextEqualityTemplate.
Proof. reflexivity. Qed.

Definition coqRestrictedPADirectBottomOuterContextTruthTemplate
    : TemplateFormula :=
  rawCoqTemplateRenameN 8
    coqRestrictedPADerivationSoundnessContextTruthTemplate.

Definition coqRestrictedPADirectBottomWitnessContextTruthTemplate
    : TemplateFormula :=
  tfOpaque coqRestrictedPAContextTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     coqRestrictedPADirectBottomWitnessContextTerm;
     ttVar 9; ttVar 8].

Lemma coqRestrictedPADirectBottom_outer_context_truth_shape :
  coqRestrictedPADirectBottomOuterContextTruthTemplate =
  tfOpaque coqRestrictedPAContextTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     coqRestrictedPADirectBottomOuterContextTerm;
     ttVar 9; ttVar 8].
Proof. reflexivity. Qed.

Definition coqRestrictedPADirectBottomAdmissibleTemplate
    : TemplateFormula :=
  rawCoqTemplateRenameN 8
    coqRestrictedPADerivationSoundnessAdmissibleTemplate.

Definition coqRestrictedPADirectBottomConclusionTruthTemplate
    : TemplateFormula :=
  rawCoqTemplateRenameN 8
    coqRestrictedPADerivationSoundnessConclusionTruthTemplate.

Definition coqRestrictedPADirectBottomRemainingTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectBottomAdmissibleTemplate
    (tfImp coqRestrictedPADirectBottomOuterContextTruthTemplate
      coqRestrictedPADirectBottomConclusionTruthTemplate).

Lemma coqRestrictedPADirectBottom_remaining_shape :
  coqRestrictedPADirectBottomRemainingTemplate =
  rawCoqTemplateRenameN 8
    rawCoqRestrictedPADirectStrongStepRemainingTemplate.
Proof. reflexivity. Qed.

(** ------------------------------------------------------------------
    The exact recursive semantic residual. *)

Definition coqRestrictedPADirectBottomAfterStrongPrefixTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectBottomRestrictedProofTemplate
    (tfImp coqRestrictedPADirectBottomCodeEqualityTemplate
      (tfImp coqRestrictedPADirectBottomFormulaCodeTemplate
        (tfImp coqRestrictedPADirectBottomChildEndpointTemplate
          (tfImp coqRestrictedPADirectBottomWitnessContextTruthTemplate
            tfBot)))).

Definition coqRestrictedPADirectBottomAfterRestrictedTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectBottomCodeEqualityTemplate
    (tfImp coqRestrictedPADirectBottomFormulaCodeTemplate
      (tfImp coqRestrictedPADirectBottomChildEndpointTemplate
        (tfImp coqRestrictedPADirectBottomWitnessContextTruthTemplate
          tfBot))).

Definition coqRestrictedPADirectBottomAfterCodeTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectBottomFormulaCodeTemplate
    (tfImp coqRestrictedPADirectBottomChildEndpointTemplate
      (tfImp coqRestrictedPADirectBottomWitnessContextTruthTemplate tfBot)).

Definition coqRestrictedPADirectBottomAfterFormulaTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectBottomChildEndpointTemplate
    (tfImp coqRestrictedPADirectBottomWitnessContextTruthTemplate tfBot).

Definition coqRestrictedPADirectBottomAfterEndpointTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectBottomWitnessContextTruthTemplate tfBot.

Definition coqRestrictedPADirectBottomRecursiveContradictionLawTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectBottomStrongPrefixTemplate
    coqRestrictedPADirectBottomAfterStrongPrefixTemplate.

Definition RawCoqRestrictedPADirectBottomRecursiveContradictionLawRoot
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (tail : TemplateContext) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation
        (coqRestrictedPADirectBottomCaseContext tail))
      (rawTemplateFormula translation
        coqRestrictedPADirectBottomRecursiveContradictionLawTemplate)
      root.

Arguments RawCoqRestrictedPADirectBottomRecursiveContradictionLawRoot
  M translation tail : clear implicits.

(** ------------------------------------------------------------------
    Declarative finite-proof helpers. *)

Lemma coqRestrictedPADirectBottom_templateRawDerives_andE1 : forall
    context left right child,
  TemplateRawDerives context (tfAnd left right) child ->
  TemplateRawDerives context left
    (trpAndE1 context left right child).
Proof.
  intros context left right child
    [hvalid [hcontext hconclusion]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; try assumption; reflexivity.
Qed.

Lemma coqRestrictedPADirectBottom_templateRawDerives_andE2 : forall
    context left right child,
  TemplateRawDerives context (tfAnd left right) child ->
  TemplateRawDerives context right
    (trpAndE2 context left right child).
Proof.
  intros context left right child
    [hvalid [hcontext hconclusion]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; try assumption; reflexivity.
Qed.

Lemma coqRestrictedPADirectBottom_templateRawDerives_impI : forall
    context antecedent consequent child,
  TemplateRawDerives (antecedent :: context) consequent child ->
  TemplateRawDerives context (tfImp antecedent consequent)
    (trpImpI context antecedent consequent child).
Proof.
  intros context antecedent consequent child
    [hvalid [hcontext hconclusion]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; try assumption; reflexivity.
Qed.

Lemma coqRestrictedPADirectBottom_templateRawDerives_impE : forall
    context antecedent consequent implicationChild antecedentChild,
  TemplateRawDerives context (tfImp antecedent consequent)
    implicationChild ->
  TemplateRawDerives context antecedent antecedentChild ->
  TemplateRawDerives context consequent
    (trpImpE context antecedent consequent
      implicationChild antecedentChild).
Proof.
  intros context antecedent consequent implicationChild antecedentChild
    [himpValid [himpContext himpConclusion]]
    [hargValid [hargContext hargConclusion]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; try assumption; reflexivity.
Qed.

Lemma coqRestrictedPADirectBottom_templateRawDerives_botE : forall
    context conclusion child,
  TemplateRawDerives context tfBot child ->
  TemplateRawDerives context conclusion
    (trpBotE context conclusion child).
Proof.
  intros context conclusion child
    [hvalid [hcontext hconclusion]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; try assumption; reflexivity.
Qed.

Lemma coqRestrictedPADirectBottom_templateRawDerives_eqElim : forall
    context source target motive equalityChild motiveChild,
  TemplateRawDerives context (tfEq source target) equalityChild ->
  TemplateRawDerives context
    (templateFormulaOpen source motive) motiveChild ->
  TemplateRawDerives context
    (templateFormulaOpen target motive)
    (trpEqElim context source target motive equalityChild motiveChild).
Proof.
  intros context source target motive equalityChild motiveChild
    [heqValid [heqContext heqConclusion]]
    [hmotiveValid [hmotiveContext hmotiveConclusion]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; try assumption; reflexivity.
Qed.

(** ------------------------------------------------------------------
    Literal projections. *)

Definition coqRestrictedPADirectBottomCaseRoot tail : TemplateRawProof :=
  trpAss (coqRestrictedPADirectBottomCaseContext tail)
    coqRestrictedPADirectBottomCaseTemplate.

Definition coqRestrictedPADirectBottomCodeRoot tail : TemplateRawProof :=
  trpAndE1 (coqRestrictedPADirectBottomCaseContext tail)
    coqRestrictedPADirectBottomCodeEqualityTemplate
    coqRestrictedPADirectBottomConclusionSuffixTemplate
    (coqRestrictedPADirectBottomCaseRoot tail).

Definition coqRestrictedPADirectBottomConclusionSuffixRoot tail
    : TemplateRawProof :=
  trpAndE2 (coqRestrictedPADirectBottomCaseContext tail)
    coqRestrictedPADirectBottomCodeEqualityTemplate
    coqRestrictedPADirectBottomConclusionSuffixTemplate
    (coqRestrictedPADirectBottomCaseRoot tail).

Definition coqRestrictedPADirectBottomFormulaSuffixRoot tail
    : TemplateRawProof :=
  trpAndE2 (coqRestrictedPADirectBottomCaseContext tail)
    coqRestrictedPADirectBottomConclusionEqualityTemplate
    coqRestrictedPADirectBottomFormulaSuffixTemplate
    (coqRestrictedPADirectBottomConclusionSuffixRoot tail).

Definition coqRestrictedPADirectBottomFormulaRoot tail : TemplateRawProof :=
  trpAndE1 (coqRestrictedPADirectBottomCaseContext tail)
    coqRestrictedPADirectBottomFormulaCodeTemplate
    coqRestrictedPADirectBottomEndpointSuffixTemplate
    (coqRestrictedPADirectBottomFormulaSuffixRoot tail).

Definition coqRestrictedPADirectBottomEndpointSuffixRoot tail
    : TemplateRawProof :=
  trpAndE2 (coqRestrictedPADirectBottomCaseContext tail)
    coqRestrictedPADirectBottomFormulaCodeTemplate
    coqRestrictedPADirectBottomEndpointSuffixTemplate
    (coqRestrictedPADirectBottomFormulaSuffixRoot tail).

Definition coqRestrictedPADirectBottomEndpointRoot tail : TemplateRawProof :=
  trpAndE1 (coqRestrictedPADirectBottomCaseContext tail)
    coqRestrictedPADirectBottomChildEndpointTemplate
    coqRestrictedPADirectBottomTerminalTemplate
    (coqRestrictedPADirectBottomEndpointSuffixRoot tail).

Definition coqRestrictedPADirectBottomStrongPrefixRoot tail
    : TemplateRawProof :=
  trpAss (coqRestrictedPADirectBottomCaseContext tail)
    coqRestrictedPADirectBottomStrongPrefixTemplate.

Definition coqRestrictedPADirectBottomRestrictedRoot tail
    : TemplateRawProof :=
  trpAss (coqRestrictedPADirectBottomCaseContext tail)
    coqRestrictedPADirectBottomRestrictedProofTemplate.

Lemma coqRestrictedPADirectBottomCaseRoot_valid : forall tail,
  TemplateRawDerives (coqRestrictedPADirectBottomCaseContext tail)
    coqRestrictedPADirectBottomCaseTemplate
    (coqRestrictedPADirectBottomCaseRoot tail).
Proof. intro tail. apply templateRawDerives_assumption. left. reflexivity. Qed.

Lemma coqRestrictedPADirectBottomCodeRoot_valid : forall tail,
  TemplateRawDerives (coqRestrictedPADirectBottomCaseContext tail)
    coqRestrictedPADirectBottomCodeEqualityTemplate
    (coqRestrictedPADirectBottomCodeRoot tail).
Proof.
  intro tail. unfold coqRestrictedPADirectBottomCodeRoot.
  apply coqRestrictedPADirectBottom_templateRawDerives_andE1.
  rewrite <- coqRestrictedPADirectBottom_case_shape.
  exact (coqRestrictedPADirectBottomCaseRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectBottomConclusionSuffixRoot_valid : forall tail,
  TemplateRawDerives (coqRestrictedPADirectBottomCaseContext tail)
    coqRestrictedPADirectBottomConclusionSuffixTemplate
    (coqRestrictedPADirectBottomConclusionSuffixRoot tail).
Proof.
  intro tail. unfold coqRestrictedPADirectBottomConclusionSuffixRoot.
  apply coqRestrictedPADirectBottom_templateRawDerives_andE2.
  rewrite <- coqRestrictedPADirectBottom_case_shape.
  exact (coqRestrictedPADirectBottomCaseRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectBottomFormulaSuffixRoot_valid : forall tail,
  TemplateRawDerives (coqRestrictedPADirectBottomCaseContext tail)
    coqRestrictedPADirectBottomFormulaSuffixTemplate
    (coqRestrictedPADirectBottomFormulaSuffixRoot tail).
Proof.
  intro tail. unfold coqRestrictedPADirectBottomFormulaSuffixRoot.
  apply coqRestrictedPADirectBottom_templateRawDerives_andE2.
  exact (coqRestrictedPADirectBottomConclusionSuffixRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectBottomFormulaRoot_valid : forall tail,
  TemplateRawDerives (coqRestrictedPADirectBottomCaseContext tail)
    coqRestrictedPADirectBottomFormulaCodeTemplate
    (coqRestrictedPADirectBottomFormulaRoot tail).
Proof.
  intro tail. unfold coqRestrictedPADirectBottomFormulaRoot.
  apply coqRestrictedPADirectBottom_templateRawDerives_andE1.
  exact (coqRestrictedPADirectBottomFormulaSuffixRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectBottomEndpointSuffixRoot_valid : forall tail,
  TemplateRawDerives (coqRestrictedPADirectBottomCaseContext tail)
    coqRestrictedPADirectBottomEndpointSuffixTemplate
    (coqRestrictedPADirectBottomEndpointSuffixRoot tail).
Proof.
  intro tail. unfold coqRestrictedPADirectBottomEndpointSuffixRoot.
  apply coqRestrictedPADirectBottom_templateRawDerives_andE2.
  exact (coqRestrictedPADirectBottomFormulaSuffixRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectBottomEndpointRoot_valid : forall tail,
  TemplateRawDerives (coqRestrictedPADirectBottomCaseContext tail)
    coqRestrictedPADirectBottomChildEndpointTemplate
    (coqRestrictedPADirectBottomEndpointRoot tail).
Proof.
  intro tail. unfold coqRestrictedPADirectBottomEndpointRoot.
  apply coqRestrictedPADirectBottom_templateRawDerives_andE1.
  exact (coqRestrictedPADirectBottomEndpointSuffixRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectBottomStrongPrefixRoot_valid : forall tail,
  TemplateRawDerives (coqRestrictedPADirectBottomCaseContext tail)
    coqRestrictedPADirectBottomStrongPrefixTemplate
    (coqRestrictedPADirectBottomStrongPrefixRoot tail).
Proof.
  intro tail. apply templateRawDerives_assumption.
  exact (coqRestrictedPADirectBottom_strongPrefix_in_case_context tail).
Qed.

Lemma coqRestrictedPADirectBottomRestrictedRoot_valid : forall tail,
  TemplateRawDerives (coqRestrictedPADirectBottomCaseContext tail)
    coqRestrictedPADirectBottomRestrictedProofTemplate
    (coqRestrictedPADirectBottomRestrictedRoot tail).
Proof.
  intro tail. apply templateRawDerives_assumption.
  exact (coqRestrictedPADirectBottom_restricted_in_case_context tail).
Qed.

(** ------------------------------------------------------------------
    Context-truth transport across the endpoint equality. *)

Definition coqRestrictedPADirectBottomTransportContext tail
    : TemplateContext :=
  coqRestrictedPADirectBottomOuterContextTruthTemplate ::
    coqRestrictedPADirectBottomCaseContext tail.

Definition coqRestrictedPADirectBottomEndpointBodyTransportRoot tail
    : TemplateRawProof :=
  trpAss (coqRestrictedPADirectBottomTransportContext tail)
    rawCoqRestrictedPADirectEndpointWitnessBodyTemplate.

Definition coqRestrictedPADirectBottomContextEqualityTransportRoot tail
    : TemplateRawProof :=
  trpAndE1 (coqRestrictedPADirectBottomTransportContext tail)
    coqRestrictedPADirectBottomContextEqualityTemplate
    (rawCoqTemplateRuleDisjunction
      rawCoqRestrictedPADirectEndpointRuleCaseTemplates)
    (coqRestrictedPADirectBottomEndpointBodyTransportRoot tail).

Definition coqRestrictedPADirectBottomEqSymmetryMotive
    (fixed : TemplateTerm) : TemplateFormula :=
  tfEq (ttVar 0) (templateTermRename S fixed).

Definition coqRestrictedPADirectBottomContextSymmetryRoot tail
    : TemplateRawProof :=
  trpEqElim (coqRestrictedPADirectBottomTransportContext tail)
    coqRestrictedPADirectBottomWitnessContextTerm
    coqRestrictedPADirectBottomOuterContextTerm
    (coqRestrictedPADirectBottomEqSymmetryMotive
      coqRestrictedPADirectBottomWitnessContextTerm)
    (coqRestrictedPADirectBottomContextEqualityTransportRoot tail)
    (trpEqRefl (coqRestrictedPADirectBottomTransportContext tail)
      coqRestrictedPADirectBottomWitnessContextTerm).

Definition coqRestrictedPADirectBottomContextTruthMotive
    : TemplateFormula :=
  tfOpaque coqRestrictedPAContextTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     ttVar 0; ttVar 10; ttVar 9].

Definition coqRestrictedPADirectBottomOuterContextTruthRoot tail
    : TemplateRawProof :=
  trpAss (coqRestrictedPADirectBottomTransportContext tail)
    coqRestrictedPADirectBottomOuterContextTruthTemplate.

Definition coqRestrictedPADirectBottomWitnessContextTruthRoot tail
    : TemplateRawProof :=
  trpEqElim (coqRestrictedPADirectBottomTransportContext tail)
    coqRestrictedPADirectBottomOuterContextTerm
    coqRestrictedPADirectBottomWitnessContextTerm
    coqRestrictedPADirectBottomContextTruthMotive
    (coqRestrictedPADirectBottomContextSymmetryRoot tail)
    (coqRestrictedPADirectBottomOuterContextTruthRoot tail).

Definition coqRestrictedPADirectBottomContextTruthTransportRoot tail
    : TemplateRawProof :=
  trpImpI (coqRestrictedPADirectBottomCaseContext tail)
    coqRestrictedPADirectBottomOuterContextTruthTemplate
    coqRestrictedPADirectBottomWitnessContextTruthTemplate
    (coqRestrictedPADirectBottomWitnessContextTruthRoot tail).

Lemma coqRestrictedPADirectBottomEqSymmetryMotive_open : forall fixed input,
  templateFormulaOpen input
    (coqRestrictedPADirectBottomEqSymmetryMotive fixed) =
  tfEq input fixed.
Proof.
  intros fixed input.
  unfold coqRestrictedPADirectBottomEqSymmetryMotive,
    templateFormulaOpen.
  cbn. f_equal.
  induction fixed; cbn; f_equal; assumption || reflexivity.
Qed.

Lemma coqRestrictedPADirectBottom_context_motive_outer :
  templateFormulaOpen coqRestrictedPADirectBottomOuterContextTerm
    coqRestrictedPADirectBottomContextTruthMotive =
  coqRestrictedPADirectBottomOuterContextTruthTemplate.
Proof.
  rewrite coqRestrictedPADirectBottom_outer_context_truth_shape.
  reflexivity.
Qed.

Lemma coqRestrictedPADirectBottom_context_motive_witness :
  templateFormulaOpen coqRestrictedPADirectBottomWitnessContextTerm
    coqRestrictedPADirectBottomContextTruthMotive =
  coqRestrictedPADirectBottomWitnessContextTruthTemplate.
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectBottomEndpointBodyTransportRoot_valid :
    forall tail,
  TemplateRawDerives (coqRestrictedPADirectBottomTransportContext tail)
    rawCoqRestrictedPADirectEndpointWitnessBodyTemplate
    (coqRestrictedPADirectBottomEndpointBodyTransportRoot tail).
Proof.
  intro tail. apply templateRawDerives_assumption.
  unfold coqRestrictedPADirectBottomTransportContext,
    coqRestrictedPADirectBottomCaseContext.
  right. right.
  unfold coqRestrictedPADirectBottomDeepContext.
  rewrite raw_coqRestrictedPADirectEndpointDeepContext_shape.
  left. reflexivity.
Qed.

Lemma coqRestrictedPADirectBottomContextEqualityTransportRoot_valid :
    forall tail,
  TemplateRawDerives (coqRestrictedPADirectBottomTransportContext tail)
    coqRestrictedPADirectBottomContextEqualityTemplate
    (coqRestrictedPADirectBottomContextEqualityTransportRoot tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectBottomContextEqualityTransportRoot.
  apply coqRestrictedPADirectBottom_templateRawDerives_andE1.
  rewrite <- coqRestrictedPADirectBottom_endpoint_equality_shape.
  exact (coqRestrictedPADirectBottomEndpointBodyTransportRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectBottomContextSymmetryRoot_valid : forall tail,
  TemplateRawDerives (coqRestrictedPADirectBottomTransportContext tail)
    (tfEq coqRestrictedPADirectBottomOuterContextTerm
      coqRestrictedPADirectBottomWitnessContextTerm)
    (coqRestrictedPADirectBottomContextSymmetryRoot tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectBottomContextSymmetryRoot.
  rewrite <- coqRestrictedPADirectBottomEqSymmetryMotive_open.
  apply coqRestrictedPADirectBottom_templateRawDerives_eqElim.
  - exact (coqRestrictedPADirectBottomContextEqualityTransportRoot_valid tail).
  - rewrite coqRestrictedPADirectBottomEqSymmetryMotive_open.
    apply templateRawDerives_eqRefl.
Qed.

Lemma coqRestrictedPADirectBottomOuterContextTruthRoot_valid : forall tail,
  TemplateRawDerives (coqRestrictedPADirectBottomTransportContext tail)
    coqRestrictedPADirectBottomOuterContextTruthTemplate
    (coqRestrictedPADirectBottomOuterContextTruthRoot tail).
Proof. intro tail. apply templateRawDerives_assumption. left. reflexivity. Qed.

Lemma coqRestrictedPADirectBottomWitnessContextTruthRoot_valid : forall tail,
  TemplateRawDerives (coqRestrictedPADirectBottomTransportContext tail)
    coqRestrictedPADirectBottomWitnessContextTruthTemplate
    (coqRestrictedPADirectBottomWitnessContextTruthRoot tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectBottomWitnessContextTruthRoot.
  rewrite <- coqRestrictedPADirectBottom_context_motive_witness.
  apply coqRestrictedPADirectBottom_templateRawDerives_eqElim.
  - exact (coqRestrictedPADirectBottomContextSymmetryRoot_valid tail).
  - rewrite coqRestrictedPADirectBottom_context_motive_outer.
    exact (coqRestrictedPADirectBottomOuterContextTruthRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectBottomContextTruthTransportRoot_valid : forall tail,
  TemplateRawDerives (coqRestrictedPADirectBottomCaseContext tail)
    (tfImp coqRestrictedPADirectBottomOuterContextTruthTemplate
      coqRestrictedPADirectBottomWitnessContextTruthTemplate)
    (coqRestrictedPADirectBottomContextTruthTransportRoot tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectBottomContextTruthTransportRoot.
  apply coqRestrictedPADirectBottom_templateRawDerives_impI.
  exact (coqRestrictedPADirectBottomWitnessContextTruthRoot_valid tail).
Qed.

(** ------------------------------------------------------------------
    Finite completion from child contradiction to the required suffix. *)

Definition coqRestrictedPADirectBottomCompletionContext0 tail
    : TemplateContext :=
  coqRestrictedPADirectBottomAfterEndpointTemplate ::
    coqRestrictedPADirectBottomCaseContext tail.

Definition coqRestrictedPADirectBottomCompletionContext1 tail
    : TemplateContext :=
  tfImp coqRestrictedPADirectBottomOuterContextTruthTemplate
      coqRestrictedPADirectBottomWitnessContextTruthTemplate ::
    coqRestrictedPADirectBottomCompletionContext0 tail.

Definition coqRestrictedPADirectBottomCompletionContext2 tail
    : TemplateContext :=
  coqRestrictedPADirectBottomAdmissibleTemplate ::
    coqRestrictedPADirectBottomCompletionContext1 tail.

Definition coqRestrictedPADirectBottomCompletionContext3 tail
    : TemplateContext :=
  coqRestrictedPADirectBottomOuterContextTruthTemplate ::
    coqRestrictedPADirectBottomCompletionContext2 tail.

Definition coqRestrictedPADirectBottomCompletionBottomLawRoot tail
    : TemplateRawProof :=
  trpAss (coqRestrictedPADirectBottomCompletionContext3 tail)
    coqRestrictedPADirectBottomAfterEndpointTemplate.

Definition coqRestrictedPADirectBottomCompletionTransportRoot tail
    : TemplateRawProof :=
  trpAss (coqRestrictedPADirectBottomCompletionContext3 tail)
    (tfImp coqRestrictedPADirectBottomOuterContextTruthTemplate
      coqRestrictedPADirectBottomWitnessContextTruthTemplate).

Definition coqRestrictedPADirectBottomCompletionOuterTruthRoot tail
    : TemplateRawProof :=
  trpAss (coqRestrictedPADirectBottomCompletionContext3 tail)
    coqRestrictedPADirectBottomOuterContextTruthTemplate.

Definition coqRestrictedPADirectBottomCompletionWitnessTruthRoot tail
    : TemplateRawProof :=
  trpImpE (coqRestrictedPADirectBottomCompletionContext3 tail)
    coqRestrictedPADirectBottomOuterContextTruthTemplate
    coqRestrictedPADirectBottomWitnessContextTruthTemplate
    (coqRestrictedPADirectBottomCompletionTransportRoot tail)
    (coqRestrictedPADirectBottomCompletionOuterTruthRoot tail).

Definition coqRestrictedPADirectBottomCompletionBottomRoot tail
    : TemplateRawProof :=
  trpImpE (coqRestrictedPADirectBottomCompletionContext3 tail)
    coqRestrictedPADirectBottomWitnessContextTruthTemplate tfBot
    (coqRestrictedPADirectBottomCompletionBottomLawRoot tail)
    (coqRestrictedPADirectBottomCompletionWitnessTruthRoot tail).

Definition coqRestrictedPADirectBottomCompletionConclusionRoot tail
    : TemplateRawProof :=
  trpBotE (coqRestrictedPADirectBottomCompletionContext3 tail)
    coqRestrictedPADirectBottomConclusionTruthTemplate
    (coqRestrictedPADirectBottomCompletionBottomRoot tail).

Definition coqRestrictedPADirectBottomCompletionOuterImpRoot tail
    : TemplateRawProof :=
  trpImpI (coqRestrictedPADirectBottomCompletionContext2 tail)
    coqRestrictedPADirectBottomOuterContextTruthTemplate
    coqRestrictedPADirectBottomConclusionTruthTemplate
    (coqRestrictedPADirectBottomCompletionConclusionRoot tail).

Definition coqRestrictedPADirectBottomCompletionAdmissibleImpRoot tail
    : TemplateRawProof :=
  trpImpI (coqRestrictedPADirectBottomCompletionContext1 tail)
    coqRestrictedPADirectBottomAdmissibleTemplate
    (tfImp coqRestrictedPADirectBottomOuterContextTruthTemplate
      coqRestrictedPADirectBottomConclusionTruthTemplate)
    (coqRestrictedPADirectBottomCompletionOuterImpRoot tail).

Definition coqRestrictedPADirectBottomCompletionTransportImpRoot tail
    : TemplateRawProof :=
  trpImpI (coqRestrictedPADirectBottomCompletionContext0 tail)
    (tfImp coqRestrictedPADirectBottomOuterContextTruthTemplate
      coqRestrictedPADirectBottomWitnessContextTruthTemplate)
    coqRestrictedPADirectBottomRemainingTemplate
    (coqRestrictedPADirectBottomCompletionAdmissibleImpRoot tail).

Definition coqRestrictedPADirectBottomCompletionRoot tail
    : TemplateRawProof :=
  trpImpI (coqRestrictedPADirectBottomCaseContext tail)
    coqRestrictedPADirectBottomAfterEndpointTemplate
    (tfImp
      (tfImp coqRestrictedPADirectBottomOuterContextTruthTemplate
        coqRestrictedPADirectBottomWitnessContextTruthTemplate)
      coqRestrictedPADirectBottomRemainingTemplate)
    (coqRestrictedPADirectBottomCompletionTransportImpRoot tail).

Lemma coqRestrictedPADirectBottomCompletionBottomLawRoot_valid : forall tail,
  TemplateRawDerives (coqRestrictedPADirectBottomCompletionContext3 tail)
    coqRestrictedPADirectBottomAfterEndpointTemplate
    (coqRestrictedPADirectBottomCompletionBottomLawRoot tail).
Proof.
  intro tail. apply templateRawDerives_assumption.
  unfold coqRestrictedPADirectBottomCompletionContext3,
    coqRestrictedPADirectBottomCompletionContext2,
    coqRestrictedPADirectBottomCompletionContext1,
    coqRestrictedPADirectBottomCompletionContext0.
  right. right. right. left. reflexivity.
Qed.

Lemma coqRestrictedPADirectBottomCompletionTransportRoot_valid : forall tail,
  TemplateRawDerives (coqRestrictedPADirectBottomCompletionContext3 tail)
    (tfImp coqRestrictedPADirectBottomOuterContextTruthTemplate
      coqRestrictedPADirectBottomWitnessContextTruthTemplate)
    (coqRestrictedPADirectBottomCompletionTransportRoot tail).
Proof.
  intro tail. apply templateRawDerives_assumption.
  unfold coqRestrictedPADirectBottomCompletionContext3,
    coqRestrictedPADirectBottomCompletionContext2,
    coqRestrictedPADirectBottomCompletionContext1.
  right. right. left. reflexivity.
Qed.

Lemma coqRestrictedPADirectBottomCompletionOuterTruthRoot_valid : forall tail,
  TemplateRawDerives (coqRestrictedPADirectBottomCompletionContext3 tail)
    coqRestrictedPADirectBottomOuterContextTruthTemplate
    (coqRestrictedPADirectBottomCompletionOuterTruthRoot tail).
Proof. intro tail. apply templateRawDerives_assumption. left. reflexivity. Qed.

Lemma coqRestrictedPADirectBottomCompletionWitnessTruthRoot_valid : forall tail,
  TemplateRawDerives (coqRestrictedPADirectBottomCompletionContext3 tail)
    coqRestrictedPADirectBottomWitnessContextTruthTemplate
    (coqRestrictedPADirectBottomCompletionWitnessTruthRoot tail).
Proof.
  intro tail. unfold coqRestrictedPADirectBottomCompletionWitnessTruthRoot.
  apply coqRestrictedPADirectBottom_templateRawDerives_impE.
  - exact (coqRestrictedPADirectBottomCompletionTransportRoot_valid tail).
  - exact (coqRestrictedPADirectBottomCompletionOuterTruthRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectBottomCompletionBottomRoot_valid : forall tail,
  TemplateRawDerives (coqRestrictedPADirectBottomCompletionContext3 tail)
    tfBot (coqRestrictedPADirectBottomCompletionBottomRoot tail).
Proof.
  intro tail. unfold coqRestrictedPADirectBottomCompletionBottomRoot.
  apply coqRestrictedPADirectBottom_templateRawDerives_impE.
  - exact (coqRestrictedPADirectBottomCompletionBottomLawRoot_valid tail).
  - exact (coqRestrictedPADirectBottomCompletionWitnessTruthRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectBottomCompletionConclusionRoot_valid : forall tail,
  TemplateRawDerives (coqRestrictedPADirectBottomCompletionContext3 tail)
    coqRestrictedPADirectBottomConclusionTruthTemplate
    (coqRestrictedPADirectBottomCompletionConclusionRoot tail).
Proof.
  intro tail. unfold coqRestrictedPADirectBottomCompletionConclusionRoot.
  apply coqRestrictedPADirectBottom_templateRawDerives_botE.
  exact (coqRestrictedPADirectBottomCompletionBottomRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectBottomCompletionOuterImpRoot_valid : forall tail,
  TemplateRawDerives (coqRestrictedPADirectBottomCompletionContext2 tail)
    (tfImp coqRestrictedPADirectBottomOuterContextTruthTemplate
      coqRestrictedPADirectBottomConclusionTruthTemplate)
    (coqRestrictedPADirectBottomCompletionOuterImpRoot tail).
Proof.
  intro tail. unfold coqRestrictedPADirectBottomCompletionOuterImpRoot.
  apply coqRestrictedPADirectBottom_templateRawDerives_impI.
  exact (coqRestrictedPADirectBottomCompletionConclusionRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectBottomCompletionAdmissibleImpRoot_valid :
    forall tail,
  TemplateRawDerives (coqRestrictedPADirectBottomCompletionContext1 tail)
    coqRestrictedPADirectBottomRemainingTemplate
    (coqRestrictedPADirectBottomCompletionAdmissibleImpRoot tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectBottomCompletionAdmissibleImpRoot,
    coqRestrictedPADirectBottomRemainingTemplate.
  apply coqRestrictedPADirectBottom_templateRawDerives_impI.
  exact (coqRestrictedPADirectBottomCompletionOuterImpRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectBottomCompletionTransportImpRoot_valid :
    forall tail,
  TemplateRawDerives (coqRestrictedPADirectBottomCompletionContext0 tail)
    (tfImp
      (tfImp coqRestrictedPADirectBottomOuterContextTruthTemplate
        coqRestrictedPADirectBottomWitnessContextTruthTemplate)
      coqRestrictedPADirectBottomRemainingTemplate)
    (coqRestrictedPADirectBottomCompletionTransportImpRoot tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectBottomCompletionTransportImpRoot.
  apply coqRestrictedPADirectBottom_templateRawDerives_impI.
  exact (coqRestrictedPADirectBottomCompletionAdmissibleImpRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectBottomCompletionRoot_valid : forall tail,
  TemplateRawDerives (coqRestrictedPADirectBottomCaseContext tail)
    (tfImp coqRestrictedPADirectBottomAfterEndpointTemplate
      (tfImp
        (tfImp coqRestrictedPADirectBottomOuterContextTruthTemplate
          coqRestrictedPADirectBottomWitnessContextTruthTemplate)
        coqRestrictedPADirectBottomRemainingTemplate))
    (coqRestrictedPADirectBottomCompletionRoot tail).
Proof.
  intro tail. unfold coqRestrictedPADirectBottomCompletionRoot.
  apply coqRestrictedPADirectBottom_templateRawDerives_impI.
  exact (coqRestrictedPADirectBottomCompletionTransportImpRoot_valid tail).
Qed.

(** ------------------------------------------------------------------
    Raw compilation and exact dispatcher slot. *)

Theorem raw_codedPALocalProofOf_coqRestrictedPADirectBottomEliminationCase :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  let translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs in
  RawCoqRestrictedPADirectBottomRecursiveContradictionLawRoot
    M translation tail ->
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation
        (coqRestrictedPADirectBottomDeepContext tail))
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          coqRestrictedPADirectBottomCaseTemplate)
        (rawTemplateFormula translation
          coqRestrictedPADirectBottomRemainingTemplate))
      root.
Proof.
  intros M hPA inputs tail. cbn zeta.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  intros (lawRoot & hlaw).
  set (caseContextCode := rawTemplateContextCode translation
    (coqRestrictedPADirectBottomCaseContext tail)).

  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectBottomStrongPrefixRoot tail)
    (proj1 (coqRestrictedPADirectBottomStrongPrefixRoot_valid tail)))
    as hstrongPrefix.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectBottomRestrictedRoot tail)
    (proj1 (coqRestrictedPADirectBottomRestrictedRoot_valid tail)))
    as hrestricted.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectBottomCodeRoot tail)
    (proj1 (coqRestrictedPADirectBottomCodeRoot_valid tail))) as hcode.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectBottomFormulaRoot tail)
    (proj1 (coqRestrictedPADirectBottomFormulaRoot_valid tail))) as hformula.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectBottomEndpointRoot tail)
    (proj1 (coqRestrictedPADirectBottomEndpointRoot_valid tail))) as hendpoint.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectBottomContextTruthTransportRoot tail)
    (proj1
      (coqRestrictedPADirectBottomContextTruthTransportRoot_valid tail)))
    as htransport.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectBottomCompletionRoot tail)
    (proj1 (coqRestrictedPADirectBottomCompletionRoot_valid tail)))
    as hcompletion.

  change (RawCodedPALocalProofOf M caseContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectBottomStrongPrefixTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectBottomStrongPrefixRoot tail))) in hstrongPrefix.
  change (RawCodedPALocalProofOf M caseContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectBottomRestrictedProofTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectBottomRestrictedRoot tail))) in hrestricted.
  change (RawCodedPALocalProofOf M caseContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectBottomCodeEqualityTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectBottomCodeRoot tail))) in hcode.
  change (RawCodedPALocalProofOf M caseContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectBottomFormulaCodeTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectBottomFormulaRoot tail))) in hformula.
  change (RawCodedPALocalProofOf M caseContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectBottomChildEndpointTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectBottomEndpointRoot tail))) in hendpoint.

  assert (hlaw0 : RawCodedPALocalProofOf M caseContextCode
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectBottomStrongPrefixTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectBottomAfterStrongPrefixTemplate)) lawRoot).
  { rewrite <- rawTemplateFormula_imp. exact hlaw. }
  set (root1 := rawProofImpERoot M caseContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectBottomStrongPrefixTemplate)
    (rawTemplateFormula translation
      coqRestrictedPADirectBottomAfterStrongPrefixTemplate)
    lawRoot
    (rawTemplateProofCode translation
      (coqRestrictedPADirectBottomStrongPrefixRoot tail))).
  assert (h1 : RawCodedPALocalProofOf M caseContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectBottomAfterStrongPrefixTemplate) root1).
  {
    unfold root1.
    exact (raw_codedPALocalProofOf_impE M hPA caseContextCode
      (rawTemplateFormula translation
        coqRestrictedPADirectBottomStrongPrefixTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectBottomAfterStrongPrefixTemplate)
      lawRoot
      (rawTemplateProofCode translation
        (coqRestrictedPADirectBottomStrongPrefixRoot tail))
      hlaw0 hstrongPrefix).
  }

  assert (h1' : RawCodedPALocalProofOf M caseContextCode
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectBottomRestrictedProofTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectBottomAfterRestrictedTemplate)) root1).
  { rewrite <- rawTemplateFormula_imp. exact h1. }
  set (root2 := rawProofImpERoot M caseContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectBottomRestrictedProofTemplate)
    (rawTemplateFormula translation
      coqRestrictedPADirectBottomAfterRestrictedTemplate)
    root1
    (rawTemplateProofCode translation
      (coqRestrictedPADirectBottomRestrictedRoot tail))).
  assert (h2 : RawCodedPALocalProofOf M caseContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectBottomAfterRestrictedTemplate) root2).
  {
    unfold root2.
    exact (raw_codedPALocalProofOf_impE M hPA caseContextCode
      (rawTemplateFormula translation
        coqRestrictedPADirectBottomRestrictedProofTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectBottomAfterRestrictedTemplate)
      root1
      (rawTemplateProofCode translation
        (coqRestrictedPADirectBottomRestrictedRoot tail))
      h1' hrestricted).
  }

  assert (h2' : RawCodedPALocalProofOf M caseContextCode
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectBottomCodeEqualityTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectBottomAfterCodeTemplate)) root2).
  { rewrite <- rawTemplateFormula_imp. exact h2. }
  set (root3 := rawProofImpERoot M caseContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectBottomCodeEqualityTemplate)
    (rawTemplateFormula translation
      coqRestrictedPADirectBottomAfterCodeTemplate)
    root2
    (rawTemplateProofCode translation
      (coqRestrictedPADirectBottomCodeRoot tail))).
  assert (h3 : RawCodedPALocalProofOf M caseContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectBottomAfterCodeTemplate) root3).
  {
    unfold root3.
    exact (raw_codedPALocalProofOf_impE M hPA caseContextCode
      (rawTemplateFormula translation
        coqRestrictedPADirectBottomCodeEqualityTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectBottomAfterCodeTemplate)
      root2
      (rawTemplateProofCode translation
        (coqRestrictedPADirectBottomCodeRoot tail)) h2' hcode).
  }

  assert (h3' : RawCodedPALocalProofOf M caseContextCode
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectBottomFormulaCodeTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectBottomAfterFormulaTemplate)) root3).
  { rewrite <- rawTemplateFormula_imp. exact h3. }
  set (root4 := rawProofImpERoot M caseContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectBottomFormulaCodeTemplate)
    (rawTemplateFormula translation
      coqRestrictedPADirectBottomAfterFormulaTemplate)
    root3
    (rawTemplateProofCode translation
      (coqRestrictedPADirectBottomFormulaRoot tail))).
  assert (h4 : RawCodedPALocalProofOf M caseContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectBottomAfterFormulaTemplate) root4).
  {
    unfold root4.
    exact (raw_codedPALocalProofOf_impE M hPA caseContextCode
      (rawTemplateFormula translation
        coqRestrictedPADirectBottomFormulaCodeTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectBottomAfterFormulaTemplate)
      root3
      (rawTemplateProofCode translation
        (coqRestrictedPADirectBottomFormulaRoot tail)) h3' hformula).
  }

  assert (h4' : RawCodedPALocalProofOf M caseContextCode
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectBottomChildEndpointTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectBottomAfterEndpointTemplate)) root4).
  { rewrite <- rawTemplateFormula_imp. exact h4. }
  set (bottomLawRoot := rawProofImpERoot M caseContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectBottomChildEndpointTemplate)
    (rawTemplateFormula translation
      coqRestrictedPADirectBottomAfterEndpointTemplate)
    root4
    (rawTemplateProofCode translation
      (coqRestrictedPADirectBottomEndpointRoot tail))).
  assert (hbottomLaw : RawCodedPALocalProofOf M caseContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectBottomAfterEndpointTemplate) bottomLawRoot).
  {
    unfold bottomLawRoot.
    exact (raw_codedPALocalProofOf_impE M hPA caseContextCode
      (rawTemplateFormula translation
        coqRestrictedPADirectBottomChildEndpointTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectBottomAfterEndpointTemplate)
      root4
      (rawTemplateProofCode translation
        (coqRestrictedPADirectBottomEndpointRoot tail)) h4' hendpoint).
  }

  assert (hcompletion0 : RawCodedPALocalProofOf M caseContextCode
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectBottomAfterEndpointTemplate)
      (rawTemplateFormula translation
        (tfImp
          (tfImp coqRestrictedPADirectBottomOuterContextTruthTemplate
            coqRestrictedPADirectBottomWitnessContextTruthTemplate)
          coqRestrictedPADirectBottomRemainingTemplate)))
    (rawTemplateProofCode translation
      (coqRestrictedPADirectBottomCompletionRoot tail))).
  { rewrite <- rawTemplateFormula_imp. exact hcompletion. }
  set (completion1Root := rawProofImpERoot M caseContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectBottomAfterEndpointTemplate)
    (rawTemplateFormula translation
      (tfImp
        (tfImp coqRestrictedPADirectBottomOuterContextTruthTemplate
          coqRestrictedPADirectBottomWitnessContextTruthTemplate)
        coqRestrictedPADirectBottomRemainingTemplate))
    (rawTemplateProofCode translation
      (coqRestrictedPADirectBottomCompletionRoot tail)) bottomLawRoot).
  assert (hcompletion1 : RawCodedPALocalProofOf M caseContextCode
    (rawTemplateFormula translation
      (tfImp
        (tfImp coqRestrictedPADirectBottomOuterContextTruthTemplate
          coqRestrictedPADirectBottomWitnessContextTruthTemplate)
        coqRestrictedPADirectBottomRemainingTemplate)) completion1Root).
  {
    unfold completion1Root.
    exact (raw_codedPALocalProofOf_impE M hPA caseContextCode
      (rawTemplateFormula translation
        coqRestrictedPADirectBottomAfterEndpointTemplate)
      (rawTemplateFormula translation
        (tfImp
          (tfImp coqRestrictedPADirectBottomOuterContextTruthTemplate
            coqRestrictedPADirectBottomWitnessContextTruthTemplate)
          coqRestrictedPADirectBottomRemainingTemplate))
      (rawTemplateProofCode translation
        (coqRestrictedPADirectBottomCompletionRoot tail)) bottomLawRoot
      hcompletion0 hbottomLaw).
  }
  assert (hcompletion1' : RawCodedPALocalProofOf M caseContextCode
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        (tfImp coqRestrictedPADirectBottomOuterContextTruthTemplate
          coqRestrictedPADirectBottomWitnessContextTruthTemplate))
      (rawTemplateFormula translation
        coqRestrictedPADirectBottomRemainingTemplate)) completion1Root).
  { rewrite <- rawTemplateFormula_imp. exact hcompletion1. }

  change (RawCodedPALocalProofOf M caseContextCode
    (rawTemplateFormula translation
      (tfImp coqRestrictedPADirectBottomOuterContextTruthTemplate
        coqRestrictedPADirectBottomWitnessContextTruthTemplate))
    (rawTemplateProofCode translation
      (coqRestrictedPADirectBottomContextTruthTransportRoot tail)))
    in htransport.
  set (remainingRoot := rawProofImpERoot M caseContextCode
    (rawTemplateFormula translation
      (tfImp coqRestrictedPADirectBottomOuterContextTruthTemplate
        coqRestrictedPADirectBottomWitnessContextTruthTemplate))
    (rawTemplateFormula translation
      coqRestrictedPADirectBottomRemainingTemplate)
    completion1Root
    (rawTemplateProofCode translation
      (coqRestrictedPADirectBottomContextTruthTransportRoot tail))).
  assert (hremaining : RawCodedPALocalProofOf M caseContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectBottomRemainingTemplate) remainingRoot).
  {
    unfold remainingRoot.
    exact (raw_codedPALocalProofOf_impE M hPA caseContextCode
      (rawTemplateFormula translation
        (tfImp coqRestrictedPADirectBottomOuterContextTruthTemplate
          coqRestrictedPADirectBottomWitnessContextTruthTemplate))
      (rawTemplateFormula translation
        coqRestrictedPADirectBottomRemainingTemplate)
      completion1Root
      (rawTemplateProofCode translation
        (coqRestrictedPADirectBottomContextTruthTransportRoot tail))
      hcompletion1' htransport).
  }

  exists (rawProofImpIRoot M
    (rawTemplateContextCode translation
      (coqRestrictedPADirectBottomDeepContext tail))
    (rawTemplateFormula translation coqRestrictedPADirectBottomCaseTemplate)
    (rawTemplateFormula translation
      coqRestrictedPADirectBottomRemainingTemplate) remainingRoot).
  apply (raw_codedPALocalProofOf_impI M hPA
    (rawTemplateContextCode translation
      (coqRestrictedPADirectBottomDeepContext tail))
    (rawTemplateFormula translation coqRestrictedPADirectBottomCaseTemplate)
    (rawTemplateFormula translation
      coqRestrictedPADirectBottomRemainingTemplate) remainingRoot).
  change (RawCodedPALocalProofOf M caseContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectBottomRemainingTemplate) remainingRoot).
  exact hremaining.
Qed.

Corollary raw_coqRestrictedPADirectStrongStepBottomEliminationCaseRoot :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  let translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs in
  RawCoqRestrictedPADirectBottomRecursiveContradictionLawRoot
    M translation tail ->
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation
        (rawCoqRestrictedPADirectEndpointWitnessBodyTemplate ::
          rawCoqRestrictedPADirectEndpointDeepTail
            (rawCoqRestrictedPADirectStrongStepEndpointTail tail)))
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          (rawCoqRestrictedPAProofRuleCaseTemplate
            rawCoqRuleBottomElimination
            (liftTerm 8 (tVar 4)) (tVar 7) (liftTerm 8 (tVar 2))
            (tVar 6) (tVar 5) (tVar 4) (tVar 3)
            (tVar 2) (tVar 1) (tVar 0)))
        (rawTemplateFormula translation
          (rawCoqTemplateRenameN 8
            rawCoqRestrictedPADirectStrongStepRemainingTemplate))) root.
Proof.
  intros M hPA inputs tail. cbn zeta. intro hlaw.
  destruct
    (raw_codedPALocalProofOf_coqRestrictedPADirectBottomEliminationCase
      M hPA inputs tail hlaw) as [root hroot].
  exists root.
  unfold coqRestrictedPADirectBottomDeepContext in hroot.
  rewrite raw_coqRestrictedPADirectEndpointDeepContext_shape in hroot.
  rewrite <- coqRestrictedPADirectBottom_remaining_shape.
  exact hroot.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectBottomEliminationCase.
