(**
  The genuine implication-elimination case for the direct strong step.

  The rule has two recursive children: one proves a coded implication and
  one proves its antecedent.  This module compiles every finite operation
  surrounding those recursive uses.  In particular it projects both child
  endpoints, the implication-code equation, [K(d)], and restrictedness of
  the current root; transports context truth to the endpoint's witness
  context; and transports truth of the witness consequent back to the outer
  conclusion.

  The sole residual is the recursive dynamic modus-ponens law.  It consumes
  exactly the data needed to descend to both children and returns truth of
  the witness consequent.  It does not return outer conclusion truth and it
  contains neither the whole branch implication nor the strong step.
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
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectImpEliminationCase.

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
    Exact contexts and inherited premises. *)

Lemma raw_coqRestrictedPADirectImpE_contextShiftN_inherited : forall
    count context formula,
  In formula context ->
  In (rawCoqTemplateRenameN count formula)
    (rawCoqTemplateContextShiftN count context).
Proof.
  induction count as [|remaining ih];
    intros context formula hin.
  - exact hin.
  - cbn [rawCoqTemplateContextShiftN rawCoqTemplateRenameN].
    apply ih. unfold templateContextShift, templateContextRename.
    apply in_map. exact hin.
Qed.

Lemma raw_coqRestrictedPADirectImpE_nestedExContext_inherited : forall
    count body tail formula,
  In formula tail ->
  In (rawCoqTemplateRenameN count formula)
    (rawCoqTemplateNestedExContext count body tail).
Proof.
  induction count as [|remaining ih];
    intros body tail formula hin.
  - right. exact hin.
  - cbn [rawCoqTemplateNestedExContext rawCoqTemplateRenameN].
    apply ih. unfold templateContextShift, templateContextRename.
    apply in_map. right. exact hin.
Qed.

Definition coqRestrictedPADirectImpEDeepContext
    (tail : TemplateContext) : TemplateContext :=
  rawCoqRestrictedPADirectEndpointDeepContext
    (rawCoqRestrictedPADirectStrongStepEndpointTail tail).

Definition coqRestrictedPADirectImpECaseTemplate : TemplateFormula :=
  rawCoqRestrictedPAProofRuleCaseTemplate rawCoqRuleImpElimination
    (liftTerm 8 (tVar 4)) (tVar 7) (liftTerm 8 (tVar 2))
    (tVar 6) (tVar 5) (tVar 4) (tVar 3)
    (tVar 2) (tVar 1) (tVar 0).

Definition coqRestrictedPADirectImpECaseContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectImpECaseTemplate ::
    coqRestrictedPADirectImpEDeepContext tail.

Definition coqRestrictedPADirectImpEStrongPrefixTemplate : TemplateFormula :=
  rawCoqTemplateRenameN 8
    (rawCoqTemplateRenameN 4
      coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate).

Definition coqRestrictedPADirectImpERestrictedProofTemplate
    : TemplateFormula :=
  rawCoqTemplateRenameN 8
    coqRestrictedPADerivationSoundnessRestrictedProofTemplate.

Lemma coqRestrictedPADirectImpE_strongPrefix_in_endpoint_tail : forall tail,
  In
    (rawCoqTemplateRenameN 4
      coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate)
    (rawCoqRestrictedPADirectStrongStepEndpointTail tail).
Proof.
  intro tail. unfold rawCoqRestrictedPADirectStrongStepEndpointTail.
  right. unfold rawCoqRestrictedPADirectStrongStepFourBinderContext.
  apply raw_coqRestrictedPADirectImpE_contextShiftN_inherited.
  left. reflexivity.
Qed.

Lemma coqRestrictedPADirectImpE_restricted_in_endpoint_tail : forall tail,
  In coqRestrictedPADerivationSoundnessRestrictedProofTemplate
    (rawCoqRestrictedPADirectStrongStepEndpointTail tail).
Proof.
  intro tail. unfold rawCoqRestrictedPADirectStrongStepEndpointTail.
  left. reflexivity.
Qed.

Lemma coqRestrictedPADirectImpE_strongPrefix_in_case_context : forall tail,
  In coqRestrictedPADirectImpEStrongPrefixTemplate
    (coqRestrictedPADirectImpECaseContext tail).
Proof.
  intro tail. right.
  unfold coqRestrictedPADirectImpEDeepContext,
    coqRestrictedPADirectImpEStrongPrefixTemplate.
  apply raw_coqRestrictedPADirectImpE_nestedExContext_inherited.
  exact (coqRestrictedPADirectImpE_strongPrefix_in_endpoint_tail tail).
Qed.

Lemma coqRestrictedPADirectImpE_restricted_in_case_context : forall tail,
  In coqRestrictedPADirectImpERestrictedProofTemplate
    (coqRestrictedPADirectImpECaseContext tail).
Proof.
  intro tail. right.
  unfold coqRestrictedPADirectImpEDeepContext,
    coqRestrictedPADirectImpERestrictedProofTemplate.
  apply raw_coqRestrictedPADirectImpE_nestedExContext_inherited.
  exact (coqRestrictedPADirectImpE_restricted_in_endpoint_tail tail).
Qed.

(** ------------------------------------------------------------------
    Literal implication-elimination fields. *)

Definition coqRestrictedPADirectImpECodeEqualityTemplate : TemplateFormula :=
  embedPAFormula
    (pEq (liftTerm 8 (tVar 4))
      (proofImpECodeTerm (tVar 7) (tVar 6) (tVar 5)
        (tVar 2) (tVar 1))).

Definition coqRestrictedPADirectImpEConclusionEqualityTemplate
    : TemplateFormula :=
  embedPAFormula (pEq (liftTerm 8 (tVar 2)) (tVar 5)).

Definition coqRestrictedPADirectImpEFormulaCodeTemplate : TemplateFormula :=
  embedPAFormula
    (formulaImpCodeTermAt (tVar 4) (tVar 6) (tVar 5)).

Definition coqRestrictedPADirectImpEFirstEndpointTemplate : TemplateFormula :=
  embedPAFormula (proofEndpointTermAt (tVar 2) (tVar 7) (tVar 4)).

Definition coqRestrictedPADirectImpESecondEndpointTemplate
    : TemplateFormula :=
  embedPAFormula (proofEndpointTermAt (tVar 1) (tVar 7) (tVar 6)).

Definition coqRestrictedPADirectImpETerminalTemplate : TemplateFormula :=
  embedPAFormula (pEq tZero tZero).

Definition coqRestrictedPADirectImpESecondEndpointSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectImpESecondEndpointTemplate
    coqRestrictedPADirectImpETerminalTemplate.

Definition coqRestrictedPADirectImpEFirstEndpointSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectImpEFirstEndpointTemplate
    coqRestrictedPADirectImpESecondEndpointSuffixTemplate.

Definition coqRestrictedPADirectImpEFormulaSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectImpEFormulaCodeTemplate
    coqRestrictedPADirectImpEFirstEndpointSuffixTemplate.

Definition coqRestrictedPADirectImpEConclusionSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectImpEConclusionEqualityTemplate
    coqRestrictedPADirectImpEFormulaSuffixTemplate.

Lemma coqRestrictedPADirectImpE_case_shape :
  coqRestrictedPADirectImpECaseTemplate =
  tfAnd coqRestrictedPADirectImpECodeEqualityTemplate
    coqRestrictedPADirectImpEConclusionSuffixTemplate.
Proof. reflexivity. Qed.

(** ------------------------------------------------------------------
    Context, conclusion, admissibility, and truth formulas. *)

Definition coqRestrictedPADirectImpEWitnessContextTerm : TemplateTerm :=
  ttVar 7.

Definition coqRestrictedPADirectImpEOuterContextTerm : TemplateTerm :=
  embedPATerm (liftTerm 8 (tVar 3)).

Definition coqRestrictedPADirectImpEWitnessConclusionTerm : TemplateTerm :=
  ttVar 5.

Definition coqRestrictedPADirectImpEOuterConclusionTerm : TemplateTerm :=
  embedPATerm (liftTerm 8 (tVar 2)).

Definition coqRestrictedPADirectImpEContextEqualityTemplate
    : TemplateFormula :=
  tfEq coqRestrictedPADirectImpEWitnessContextTerm
    coqRestrictedPADirectImpEOuterContextTerm.

Lemma coqRestrictedPADirectImpE_endpoint_equality_shape :
  rawCoqRestrictedPADirectEndpointWitnessEqualityTemplate =
  coqRestrictedPADirectImpEContextEqualityTemplate.
Proof. reflexivity. Qed.

Definition coqRestrictedPADirectImpEAdmissibleTemplate : TemplateFormula :=
  rawCoqTemplateRenameN 8
    coqRestrictedPADerivationSoundnessAdmissibleTemplate.

Definition coqRestrictedPADirectImpEOuterContextTruthTemplate
    : TemplateFormula :=
  rawCoqTemplateRenameN 8
    coqRestrictedPADerivationSoundnessContextTruthTemplate.

Definition coqRestrictedPADirectImpEWitnessContextTruthTemplate
    : TemplateFormula :=
  tfOpaque coqRestrictedPAContextTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     coqRestrictedPADirectImpEWitnessContextTerm;
     ttVar 9; ttVar 8].

Definition coqRestrictedPADirectImpEOuterConclusionTruthTemplate
    : TemplateFormula :=
  rawCoqTemplateRenameN 8
    coqRestrictedPADerivationSoundnessConclusionTruthTemplate.

Definition coqRestrictedPADirectImpEWitnessConclusionTruthTemplate
    : TemplateFormula :=
  tfOpaque coqRestrictedPAConclusionTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     coqRestrictedPADirectImpEWitnessConclusionTerm;
     ttVar 9; ttVar 8].

Lemma coqRestrictedPADirectImpE_outer_context_truth_shape :
  coqRestrictedPADirectImpEOuterContextTruthTemplate =
  tfOpaque coqRestrictedPAContextTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     coqRestrictedPADirectImpEOuterContextTerm;
     ttVar 9; ttVar 8].
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectImpE_outer_conclusion_truth_shape :
  coqRestrictedPADirectImpEOuterConclusionTruthTemplate =
  tfOpaque coqRestrictedPAConclusionTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     coqRestrictedPADirectImpEOuterConclusionTerm;
     ttVar 9; ttVar 8].
Proof. reflexivity. Qed.

Definition coqRestrictedPADirectImpERemainingTemplate : TemplateFormula :=
  tfImp coqRestrictedPADirectImpEAdmissibleTemplate
    (tfImp coqRestrictedPADirectImpEOuterContextTruthTemplate
      coqRestrictedPADirectImpEOuterConclusionTruthTemplate).

Lemma coqRestrictedPADirectImpE_remaining_shape :
  coqRestrictedPADirectImpERemainingTemplate =
  rawCoqTemplateRenameN 8
    rawCoqRestrictedPADirectStrongStepRemainingTemplate.
Proof. reflexivity. Qed.

(** ------------------------------------------------------------------
    The exact recursive dynamic modus-ponens residual. *)

Definition coqRestrictedPADirectImpECoreTemplate : TemplateFormula :=
  tfImp coqRestrictedPADirectImpEAdmissibleTemplate
    (tfImp coqRestrictedPADirectImpEWitnessContextTruthTemplate
      coqRestrictedPADirectImpEWitnessConclusionTruthTemplate).

Definition coqRestrictedPADirectImpEAfterSecondEndpointTemplate
    : TemplateFormula := coqRestrictedPADirectImpECoreTemplate.

Definition coqRestrictedPADirectImpEAfterFirstEndpointTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectImpESecondEndpointTemplate
    coqRestrictedPADirectImpEAfterSecondEndpointTemplate.

Definition coqRestrictedPADirectImpEAfterFormulaTemplate : TemplateFormula :=
  tfImp coqRestrictedPADirectImpEFirstEndpointTemplate
    coqRestrictedPADirectImpEAfterFirstEndpointTemplate.

Definition coqRestrictedPADirectImpEAfterConclusionTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectImpEFormulaCodeTemplate
    coqRestrictedPADirectImpEAfterFormulaTemplate.

Definition coqRestrictedPADirectImpEAfterCodeTemplate : TemplateFormula :=
  tfImp coqRestrictedPADirectImpEConclusionEqualityTemplate
    coqRestrictedPADirectImpEAfterConclusionTemplate.

Definition coqRestrictedPADirectImpEAfterRestrictedTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectImpECodeEqualityTemplate
    coqRestrictedPADirectImpEAfterCodeTemplate.

Definition coqRestrictedPADirectImpEAfterStrongPrefixTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectImpERestrictedProofTemplate
    coqRestrictedPADirectImpEAfterRestrictedTemplate.

Definition coqRestrictedPADirectImpERecursiveModusPonensLawTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectImpEStrongPrefixTemplate
    coqRestrictedPADirectImpEAfterStrongPrefixTemplate.

Definition RawCoqRestrictedPADirectImpERecursiveModusPonensLawRoot
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (tail : TemplateContext) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation
        (coqRestrictedPADirectImpECaseContext tail))
      (rawTemplateFormula translation
        coqRestrictedPADirectImpERecursiveModusPonensLawTemplate)
      root.

Arguments RawCoqRestrictedPADirectImpERecursiveModusPonensLawRoot
  M translation tail : clear implicits.

(** ------------------------------------------------------------------
    Declarative finite-proof helpers. *)

Lemma coqRestrictedPADirectImpE_templateRawDerives_andE1 : forall
    context left right child,
  TemplateRawDerives context (tfAnd left right) child ->
  TemplateRawDerives context left
    (trpAndE1 context left right child).
Proof.
  intros context left right child [hv [hc hq]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; try assumption; reflexivity.
Qed.

Lemma coqRestrictedPADirectImpE_templateRawDerives_andE2 : forall
    context left right child,
  TemplateRawDerives context (tfAnd left right) child ->
  TemplateRawDerives context right
    (trpAndE2 context left right child).
Proof.
  intros context left right child [hv [hc hq]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; try assumption; reflexivity.
Qed.

Lemma coqRestrictedPADirectImpE_templateRawDerives_impI : forall
    context antecedent consequent child,
  TemplateRawDerives (antecedent :: context) consequent child ->
  TemplateRawDerives context (tfImp antecedent consequent)
    (trpImpI context antecedent consequent child).
Proof.
  intros context antecedent consequent child [hv [hc hq]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; try assumption; reflexivity.
Qed.

Lemma coqRestrictedPADirectImpE_templateRawDerives_impE : forall
    context antecedent consequent implicationChild antecedentChild,
  TemplateRawDerives context (tfImp antecedent consequent)
    implicationChild ->
  TemplateRawDerives context antecedent antecedentChild ->
  TemplateRawDerives context consequent
    (trpImpE context antecedent consequent
      implicationChild antecedentChild).
Proof.
  intros context antecedent consequent implicationChild antecedentChild
    [hi [hic hiq]] [ha [hac haq]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; try assumption; reflexivity.
Qed.

Lemma coqRestrictedPADirectImpE_templateRawDerives_eqElim : forall
    context source target motive equalityChild motiveChild,
  TemplateRawDerives context (tfEq source target) equalityChild ->
  TemplateRawDerives context
    (templateFormulaOpen source motive) motiveChild ->
  TemplateRawDerives context
    (templateFormulaOpen target motive)
    (trpEqElim context source target motive equalityChild motiveChild).
Proof.
  intros context source target motive equalityChild motiveChild
    [he [hec heq]] [hm [hmc hmq]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; try assumption; reflexivity.
Qed.

(** ------------------------------------------------------------------
    Rule-field and inherited-premise projections. *)

Definition coqRestrictedPADirectImpECaseRoot tail : TemplateRawProof :=
  trpAss (coqRestrictedPADirectImpECaseContext tail)
    coqRestrictedPADirectImpECaseTemplate.

Definition coqRestrictedPADirectImpECodeRoot tail : TemplateRawProof :=
  trpAndE1 (coqRestrictedPADirectImpECaseContext tail)
    coqRestrictedPADirectImpECodeEqualityTemplate
    coqRestrictedPADirectImpEConclusionSuffixTemplate
    (coqRestrictedPADirectImpECaseRoot tail).

Definition coqRestrictedPADirectImpEConclusionSuffixRoot tail
    : TemplateRawProof :=
  trpAndE2 (coqRestrictedPADirectImpECaseContext tail)
    coqRestrictedPADirectImpECodeEqualityTemplate
    coqRestrictedPADirectImpEConclusionSuffixTemplate
    (coqRestrictedPADirectImpECaseRoot tail).

Definition coqRestrictedPADirectImpEConclusionRoot tail : TemplateRawProof :=
  trpAndE1 (coqRestrictedPADirectImpECaseContext tail)
    coqRestrictedPADirectImpEConclusionEqualityTemplate
    coqRestrictedPADirectImpEFormulaSuffixTemplate
    (coqRestrictedPADirectImpEConclusionSuffixRoot tail).

Definition coqRestrictedPADirectImpEFormulaSuffixRoot tail
    : TemplateRawProof :=
  trpAndE2 (coqRestrictedPADirectImpECaseContext tail)
    coqRestrictedPADirectImpEConclusionEqualityTemplate
    coqRestrictedPADirectImpEFormulaSuffixTemplate
    (coqRestrictedPADirectImpEConclusionSuffixRoot tail).

Definition coqRestrictedPADirectImpEFormulaRoot tail : TemplateRawProof :=
  trpAndE1 (coqRestrictedPADirectImpECaseContext tail)
    coqRestrictedPADirectImpEFormulaCodeTemplate
    coqRestrictedPADirectImpEFirstEndpointSuffixTemplate
    (coqRestrictedPADirectImpEFormulaSuffixRoot tail).

Definition coqRestrictedPADirectImpEFirstEndpointSuffixRoot tail
    : TemplateRawProof :=
  trpAndE2 (coqRestrictedPADirectImpECaseContext tail)
    coqRestrictedPADirectImpEFormulaCodeTemplate
    coqRestrictedPADirectImpEFirstEndpointSuffixTemplate
    (coqRestrictedPADirectImpEFormulaSuffixRoot tail).

Definition coqRestrictedPADirectImpEFirstEndpointRoot tail
    : TemplateRawProof :=
  trpAndE1 (coqRestrictedPADirectImpECaseContext tail)
    coqRestrictedPADirectImpEFirstEndpointTemplate
    coqRestrictedPADirectImpESecondEndpointSuffixTemplate
    (coqRestrictedPADirectImpEFirstEndpointSuffixRoot tail).

Definition coqRestrictedPADirectImpESecondEndpointSuffixRoot tail
    : TemplateRawProof :=
  trpAndE2 (coqRestrictedPADirectImpECaseContext tail)
    coqRestrictedPADirectImpEFirstEndpointTemplate
    coqRestrictedPADirectImpESecondEndpointSuffixTemplate
    (coqRestrictedPADirectImpEFirstEndpointSuffixRoot tail).

Definition coqRestrictedPADirectImpESecondEndpointRoot tail
    : TemplateRawProof :=
  trpAndE1 (coqRestrictedPADirectImpECaseContext tail)
    coqRestrictedPADirectImpESecondEndpointTemplate
    coqRestrictedPADirectImpETerminalTemplate
    (coqRestrictedPADirectImpESecondEndpointSuffixRoot tail).

Definition coqRestrictedPADirectImpEStrongPrefixRoot tail : TemplateRawProof :=
  trpAss (coqRestrictedPADirectImpECaseContext tail)
    coqRestrictedPADirectImpEStrongPrefixTemplate.

Definition coqRestrictedPADirectImpERestrictedRoot tail : TemplateRawProof :=
  trpAss (coqRestrictedPADirectImpECaseContext tail)
    coqRestrictedPADirectImpERestrictedProofTemplate.

Lemma coqRestrictedPADirectImpECaseRoot_valid : forall tail,
  TemplateRawDerives (coqRestrictedPADirectImpECaseContext tail)
    coqRestrictedPADirectImpECaseTemplate
    (coqRestrictedPADirectImpECaseRoot tail).
Proof. intro tail. apply templateRawDerives_assumption. left. reflexivity. Qed.

Lemma coqRestrictedPADirectImpECodeRoot_valid : forall tail,
  TemplateRawDerives (coqRestrictedPADirectImpECaseContext tail)
    coqRestrictedPADirectImpECodeEqualityTemplate
    (coqRestrictedPADirectImpECodeRoot tail).
Proof.
  intro tail. unfold coqRestrictedPADirectImpECodeRoot.
  apply coqRestrictedPADirectImpE_templateRawDerives_andE1.
  rewrite <- coqRestrictedPADirectImpE_case_shape.
  exact (coqRestrictedPADirectImpECaseRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectImpEConclusionSuffixRoot_valid : forall tail,
  TemplateRawDerives (coqRestrictedPADirectImpECaseContext tail)
    coqRestrictedPADirectImpEConclusionSuffixTemplate
    (coqRestrictedPADirectImpEConclusionSuffixRoot tail).
Proof.
  intro tail. unfold coqRestrictedPADirectImpEConclusionSuffixRoot.
  apply coqRestrictedPADirectImpE_templateRawDerives_andE2.
  rewrite <- coqRestrictedPADirectImpE_case_shape.
  exact (coqRestrictedPADirectImpECaseRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectImpEConclusionRoot_valid : forall tail,
  TemplateRawDerives (coqRestrictedPADirectImpECaseContext tail)
    coqRestrictedPADirectImpEConclusionEqualityTemplate
    (coqRestrictedPADirectImpEConclusionRoot tail).
Proof.
  intro tail. unfold coqRestrictedPADirectImpEConclusionRoot.
  apply coqRestrictedPADirectImpE_templateRawDerives_andE1.
  exact (coqRestrictedPADirectImpEConclusionSuffixRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectImpEFormulaSuffixRoot_valid : forall tail,
  TemplateRawDerives (coqRestrictedPADirectImpECaseContext tail)
    coqRestrictedPADirectImpEFormulaSuffixTemplate
    (coqRestrictedPADirectImpEFormulaSuffixRoot tail).
Proof.
  intro tail. unfold coqRestrictedPADirectImpEFormulaSuffixRoot.
  apply coqRestrictedPADirectImpE_templateRawDerives_andE2.
  exact (coqRestrictedPADirectImpEConclusionSuffixRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectImpEFormulaRoot_valid : forall tail,
  TemplateRawDerives (coqRestrictedPADirectImpECaseContext tail)
    coqRestrictedPADirectImpEFormulaCodeTemplate
    (coqRestrictedPADirectImpEFormulaRoot tail).
Proof.
  intro tail. unfold coqRestrictedPADirectImpEFormulaRoot.
  apply coqRestrictedPADirectImpE_templateRawDerives_andE1.
  exact (coqRestrictedPADirectImpEFormulaSuffixRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectImpEFirstEndpointSuffixRoot_valid : forall tail,
  TemplateRawDerives (coqRestrictedPADirectImpECaseContext tail)
    coqRestrictedPADirectImpEFirstEndpointSuffixTemplate
    (coqRestrictedPADirectImpEFirstEndpointSuffixRoot tail).
Proof.
  intro tail. unfold coqRestrictedPADirectImpEFirstEndpointSuffixRoot.
  apply coqRestrictedPADirectImpE_templateRawDerives_andE2.
  exact (coqRestrictedPADirectImpEFormulaSuffixRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectImpEFirstEndpointRoot_valid : forall tail,
  TemplateRawDerives (coqRestrictedPADirectImpECaseContext tail)
    coqRestrictedPADirectImpEFirstEndpointTemplate
    (coqRestrictedPADirectImpEFirstEndpointRoot tail).
Proof.
  intro tail. unfold coqRestrictedPADirectImpEFirstEndpointRoot.
  apply coqRestrictedPADirectImpE_templateRawDerives_andE1.
  exact (coqRestrictedPADirectImpEFirstEndpointSuffixRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectImpESecondEndpointSuffixRoot_valid : forall tail,
  TemplateRawDerives (coqRestrictedPADirectImpECaseContext tail)
    coqRestrictedPADirectImpESecondEndpointSuffixTemplate
    (coqRestrictedPADirectImpESecondEndpointSuffixRoot tail).
Proof.
  intro tail. unfold coqRestrictedPADirectImpESecondEndpointSuffixRoot.
  apply coqRestrictedPADirectImpE_templateRawDerives_andE2.
  exact (coqRestrictedPADirectImpEFirstEndpointSuffixRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectImpESecondEndpointRoot_valid : forall tail,
  TemplateRawDerives (coqRestrictedPADirectImpECaseContext tail)
    coqRestrictedPADirectImpESecondEndpointTemplate
    (coqRestrictedPADirectImpESecondEndpointRoot tail).
Proof.
  intro tail. unfold coqRestrictedPADirectImpESecondEndpointRoot.
  apply coqRestrictedPADirectImpE_templateRawDerives_andE1.
  exact (coqRestrictedPADirectImpESecondEndpointSuffixRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectImpEStrongPrefixRoot_valid : forall tail,
  TemplateRawDerives (coqRestrictedPADirectImpECaseContext tail)
    coqRestrictedPADirectImpEStrongPrefixTemplate
    (coqRestrictedPADirectImpEStrongPrefixRoot tail).
Proof.
  intro tail. apply templateRawDerives_assumption.
  exact (coqRestrictedPADirectImpE_strongPrefix_in_case_context tail).
Qed.

Lemma coqRestrictedPADirectImpERestrictedRoot_valid : forall tail,
  TemplateRawDerives (coqRestrictedPADirectImpECaseContext tail)
    coqRestrictedPADirectImpERestrictedProofTemplate
    (coqRestrictedPADirectImpERestrictedRoot tail).
Proof.
  intro tail. apply templateRawDerives_assumption.
  exact (coqRestrictedPADirectImpE_restricted_in_case_context tail).
Qed.

(** ------------------------------------------------------------------
    Equality transport for context truth and conclusion truth. *)

Definition coqRestrictedPADirectImpEEqSymmetryMotive
    (fixed : TemplateTerm) : TemplateFormula :=
  tfEq (ttVar 0) (templateTermRename S fixed).

Lemma coqRestrictedPADirectImpEEqSymmetryMotive_open : forall fixed input,
  templateFormulaOpen input
    (coqRestrictedPADirectImpEEqSymmetryMotive fixed) =
  tfEq input fixed.
Proof.
  intros fixed input.
  unfold coqRestrictedPADirectImpEEqSymmetryMotive, templateFormulaOpen.
  cbn. f_equal.
  induction fixed; cbn; f_equal; assumption || reflexivity.
Qed.

Definition coqRestrictedPADirectImpEContextTruthMotive : TemplateFormula :=
  tfOpaque coqRestrictedPAContextTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     ttVar 0; ttVar 10; ttVar 9].

Definition coqRestrictedPADirectImpEConclusionTruthMotive
    : TemplateFormula :=
  tfOpaque coqRestrictedPAConclusionTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     ttVar 0; ttVar 10; ttVar 9].

Lemma coqRestrictedPADirectImpE_context_motive_outer :
  templateFormulaOpen coqRestrictedPADirectImpEOuterContextTerm
    coqRestrictedPADirectImpEContextTruthMotive =
  coqRestrictedPADirectImpEOuterContextTruthTemplate.
Proof. rewrite coqRestrictedPADirectImpE_outer_context_truth_shape. reflexivity. Qed.

Lemma coqRestrictedPADirectImpE_context_motive_witness :
  templateFormulaOpen coqRestrictedPADirectImpEWitnessContextTerm
    coqRestrictedPADirectImpEContextTruthMotive =
  coqRestrictedPADirectImpEWitnessContextTruthTemplate.
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectImpE_conclusion_motive_outer :
  templateFormulaOpen coqRestrictedPADirectImpEOuterConclusionTerm
    coqRestrictedPADirectImpEConclusionTruthMotive =
  coqRestrictedPADirectImpEOuterConclusionTruthTemplate.
Proof. rewrite coqRestrictedPADirectImpE_outer_conclusion_truth_shape. reflexivity. Qed.

Lemma coqRestrictedPADirectImpE_conclusion_motive_witness :
  templateFormulaOpen coqRestrictedPADirectImpEWitnessConclusionTerm
    coqRestrictedPADirectImpEConclusionTruthMotive =
  coqRestrictedPADirectImpEWitnessConclusionTruthTemplate.
Proof. reflexivity. Qed.

(** Context transport lives under an assumed outer-context truth atom. *)
Definition coqRestrictedPADirectImpEContextTransportContext tail
    : TemplateContext :=
  coqRestrictedPADirectImpEOuterContextTruthTemplate ::
    coqRestrictedPADirectImpECaseContext tail.

Definition coqRestrictedPADirectImpEEndpointBodyTransportRoot tail
    : TemplateRawProof :=
  trpAss (coqRestrictedPADirectImpEContextTransportContext tail)
    rawCoqRestrictedPADirectEndpointWitnessBodyTemplate.

Definition coqRestrictedPADirectImpEContextEqualityRoot tail
    : TemplateRawProof :=
  trpAndE1 (coqRestrictedPADirectImpEContextTransportContext tail)
    coqRestrictedPADirectImpEContextEqualityTemplate
    (rawCoqTemplateRuleDisjunction
      rawCoqRestrictedPADirectEndpointRuleCaseTemplates)
    (coqRestrictedPADirectImpEEndpointBodyTransportRoot tail).

Definition coqRestrictedPADirectImpEContextSymmetryRoot tail
    : TemplateRawProof :=
  trpEqElim (coqRestrictedPADirectImpEContextTransportContext tail)
    coqRestrictedPADirectImpEWitnessContextTerm
    coqRestrictedPADirectImpEOuterContextTerm
    (coqRestrictedPADirectImpEEqSymmetryMotive
      coqRestrictedPADirectImpEWitnessContextTerm)
    (coqRestrictedPADirectImpEContextEqualityRoot tail)
    (trpEqRefl (coqRestrictedPADirectImpEContextTransportContext tail)
      coqRestrictedPADirectImpEWitnessContextTerm).

Definition coqRestrictedPADirectImpEOuterContextTruthRoot tail
    : TemplateRawProof :=
  trpAss (coqRestrictedPADirectImpEContextTransportContext tail)
    coqRestrictedPADirectImpEOuterContextTruthTemplate.

Definition coqRestrictedPADirectImpEWitnessContextTruthRoot tail
    : TemplateRawProof :=
  trpEqElim (coqRestrictedPADirectImpEContextTransportContext tail)
    coqRestrictedPADirectImpEOuterContextTerm
    coqRestrictedPADirectImpEWitnessContextTerm
    coqRestrictedPADirectImpEContextTruthMotive
    (coqRestrictedPADirectImpEContextSymmetryRoot tail)
    (coqRestrictedPADirectImpEOuterContextTruthRoot tail).

Definition coqRestrictedPADirectImpEContextTransportRoot tail
    : TemplateRawProof :=
  trpImpI (coqRestrictedPADirectImpECaseContext tail)
    coqRestrictedPADirectImpEOuterContextTruthTemplate
    coqRestrictedPADirectImpEWitnessContextTruthTemplate
    (coqRestrictedPADirectImpEWitnessContextTruthRoot tail).

(** Conclusion transport lives under assumed witness-conclusion truth. *)
Definition coqRestrictedPADirectImpEConclusionTransportContext tail
    : TemplateContext :=
  coqRestrictedPADirectImpEWitnessConclusionTruthTemplate ::
    coqRestrictedPADirectImpECaseContext tail.

Definition coqRestrictedPADirectImpECaseTransportRoot tail
    : TemplateRawProof :=
  trpAss (coqRestrictedPADirectImpEConclusionTransportContext tail)
    coqRestrictedPADirectImpECaseTemplate.

Definition coqRestrictedPADirectImpEConclusionSuffixTransportRoot tail
    : TemplateRawProof :=
  trpAndE2 (coqRestrictedPADirectImpEConclusionTransportContext tail)
    coqRestrictedPADirectImpECodeEqualityTemplate
    coqRestrictedPADirectImpEConclusionSuffixTemplate
    (coqRestrictedPADirectImpECaseTransportRoot tail).

Definition coqRestrictedPADirectImpEConclusionEqualityTransportRoot tail
    : TemplateRawProof :=
  trpAndE1 (coqRestrictedPADirectImpEConclusionTransportContext tail)
    coqRestrictedPADirectImpEConclusionEqualityTemplate
    coqRestrictedPADirectImpEFormulaSuffixTemplate
    (coqRestrictedPADirectImpEConclusionSuffixTransportRoot tail).

Definition coqRestrictedPADirectImpEConclusionSymmetryRoot tail
    : TemplateRawProof :=
  trpEqElim (coqRestrictedPADirectImpEConclusionTransportContext tail)
    coqRestrictedPADirectImpEOuterConclusionTerm
    coqRestrictedPADirectImpEWitnessConclusionTerm
    (coqRestrictedPADirectImpEEqSymmetryMotive
      coqRestrictedPADirectImpEOuterConclusionTerm)
    (coqRestrictedPADirectImpEConclusionEqualityTransportRoot tail)
    (trpEqRefl (coqRestrictedPADirectImpEConclusionTransportContext tail)
      coqRestrictedPADirectImpEOuterConclusionTerm).

Definition coqRestrictedPADirectImpEWitnessConclusionTruthRoot tail
    : TemplateRawProof :=
  trpAss (coqRestrictedPADirectImpEConclusionTransportContext tail)
    coqRestrictedPADirectImpEWitnessConclusionTruthTemplate.

Definition coqRestrictedPADirectImpEOuterConclusionTruthRoot tail
    : TemplateRawProof :=
  trpEqElim (coqRestrictedPADirectImpEConclusionTransportContext tail)
    coqRestrictedPADirectImpEWitnessConclusionTerm
    coqRestrictedPADirectImpEOuterConclusionTerm
    coqRestrictedPADirectImpEConclusionTruthMotive
    (coqRestrictedPADirectImpEConclusionSymmetryRoot tail)
    (coqRestrictedPADirectImpEWitnessConclusionTruthRoot tail).

Definition coqRestrictedPADirectImpEConclusionTransportRoot tail
    : TemplateRawProof :=
  trpImpI (coqRestrictedPADirectImpECaseContext tail)
    coqRestrictedPADirectImpEWitnessConclusionTruthTemplate
    coqRestrictedPADirectImpEOuterConclusionTruthTemplate
    (coqRestrictedPADirectImpEOuterConclusionTruthRoot tail).

(** Validation is intentionally explicit at every temporary context. *)
Lemma coqRestrictedPADirectImpEEndpointBodyTransportRoot_valid : forall tail,
  TemplateRawDerives (coqRestrictedPADirectImpEContextTransportContext tail)
    rawCoqRestrictedPADirectEndpointWitnessBodyTemplate
    (coqRestrictedPADirectImpEEndpointBodyTransportRoot tail).
Proof.
  intro tail. apply templateRawDerives_assumption.
  unfold coqRestrictedPADirectImpEContextTransportContext,
    coqRestrictedPADirectImpECaseContext.
  right. right. unfold coqRestrictedPADirectImpEDeepContext.
  rewrite raw_coqRestrictedPADirectEndpointDeepContext_shape.
  left. reflexivity.
Qed.

Lemma coqRestrictedPADirectImpEContextEqualityRoot_valid : forall tail,
  TemplateRawDerives (coqRestrictedPADirectImpEContextTransportContext tail)
    coqRestrictedPADirectImpEContextEqualityTemplate
    (coqRestrictedPADirectImpEContextEqualityRoot tail).
Proof.
  intro tail. unfold coqRestrictedPADirectImpEContextEqualityRoot.
  apply coqRestrictedPADirectImpE_templateRawDerives_andE1.
  rewrite <- coqRestrictedPADirectImpE_endpoint_equality_shape.
  exact (coqRestrictedPADirectImpEEndpointBodyTransportRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectImpEContextSymmetryRoot_valid : forall tail,
  TemplateRawDerives (coqRestrictedPADirectImpEContextTransportContext tail)
    (tfEq coqRestrictedPADirectImpEOuterContextTerm
      coqRestrictedPADirectImpEWitnessContextTerm)
    (coqRestrictedPADirectImpEContextSymmetryRoot tail).
Proof.
  intro tail. unfold coqRestrictedPADirectImpEContextSymmetryRoot.
  rewrite <- coqRestrictedPADirectImpEEqSymmetryMotive_open.
  apply coqRestrictedPADirectImpE_templateRawDerives_eqElim.
  - exact (coqRestrictedPADirectImpEContextEqualityRoot_valid tail).
  - rewrite coqRestrictedPADirectImpEEqSymmetryMotive_open.
    apply templateRawDerives_eqRefl.
Qed.

Lemma coqRestrictedPADirectImpEOuterContextTruthRoot_valid : forall tail,
  TemplateRawDerives (coqRestrictedPADirectImpEContextTransportContext tail)
    coqRestrictedPADirectImpEOuterContextTruthTemplate
    (coqRestrictedPADirectImpEOuterContextTruthRoot tail).
Proof. intro tail. apply templateRawDerives_assumption. left. reflexivity. Qed.

Lemma coqRestrictedPADirectImpEWitnessContextTruthRoot_valid : forall tail,
  TemplateRawDerives (coqRestrictedPADirectImpEContextTransportContext tail)
    coqRestrictedPADirectImpEWitnessContextTruthTemplate
    (coqRestrictedPADirectImpEWitnessContextTruthRoot tail).
Proof.
  intro tail. unfold coqRestrictedPADirectImpEWitnessContextTruthRoot.
  rewrite <- coqRestrictedPADirectImpE_context_motive_witness.
  apply coqRestrictedPADirectImpE_templateRawDerives_eqElim.
  - exact (coqRestrictedPADirectImpEContextSymmetryRoot_valid tail).
  - rewrite coqRestrictedPADirectImpE_context_motive_outer.
    exact (coqRestrictedPADirectImpEOuterContextTruthRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectImpEContextTransportRoot_valid : forall tail,
  TemplateRawDerives (coqRestrictedPADirectImpECaseContext tail)
    (tfImp coqRestrictedPADirectImpEOuterContextTruthTemplate
      coqRestrictedPADirectImpEWitnessContextTruthTemplate)
    (coqRestrictedPADirectImpEContextTransportRoot tail).
Proof.
  intro tail. unfold coqRestrictedPADirectImpEContextTransportRoot.
  apply coqRestrictedPADirectImpE_templateRawDerives_impI.
  exact (coqRestrictedPADirectImpEWitnessContextTruthRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectImpECaseTransportRoot_valid : forall tail,
  TemplateRawDerives
    (coqRestrictedPADirectImpEConclusionTransportContext tail)
    coqRestrictedPADirectImpECaseTemplate
    (coqRestrictedPADirectImpECaseTransportRoot tail).
Proof.
  intro tail. apply templateRawDerives_assumption.
  unfold coqRestrictedPADirectImpEConclusionTransportContext.
  right. left. reflexivity.
Qed.

Lemma coqRestrictedPADirectImpEConclusionSuffixTransportRoot_valid :
    forall tail,
  TemplateRawDerives
    (coqRestrictedPADirectImpEConclusionTransportContext tail)
    coqRestrictedPADirectImpEConclusionSuffixTemplate
    (coqRestrictedPADirectImpEConclusionSuffixTransportRoot tail).
Proof.
  intro tail. unfold coqRestrictedPADirectImpEConclusionSuffixTransportRoot.
  apply coqRestrictedPADirectImpE_templateRawDerives_andE2.
  rewrite <- coqRestrictedPADirectImpE_case_shape.
  exact (coqRestrictedPADirectImpECaseTransportRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectImpEConclusionEqualityTransportRoot_valid :
    forall tail,
  TemplateRawDerives
    (coqRestrictedPADirectImpEConclusionTransportContext tail)
    coqRestrictedPADirectImpEConclusionEqualityTemplate
    (coqRestrictedPADirectImpEConclusionEqualityTransportRoot tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectImpEConclusionEqualityTransportRoot.
  apply coqRestrictedPADirectImpE_templateRawDerives_andE1.
  exact (coqRestrictedPADirectImpEConclusionSuffixTransportRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectImpEConclusionSymmetryRoot_valid : forall tail,
  TemplateRawDerives
    (coqRestrictedPADirectImpEConclusionTransportContext tail)
    (tfEq coqRestrictedPADirectImpEWitnessConclusionTerm
      coqRestrictedPADirectImpEOuterConclusionTerm)
    (coqRestrictedPADirectImpEConclusionSymmetryRoot tail).
Proof.
  intro tail. unfold coqRestrictedPADirectImpEConclusionSymmetryRoot.
  rewrite <- coqRestrictedPADirectImpEEqSymmetryMotive_open.
  apply coqRestrictedPADirectImpE_templateRawDerives_eqElim.
  - exact
      (coqRestrictedPADirectImpEConclusionEqualityTransportRoot_valid tail).
  - rewrite coqRestrictedPADirectImpEEqSymmetryMotive_open.
    apply templateRawDerives_eqRefl.
Qed.

Lemma coqRestrictedPADirectImpEWitnessConclusionTruthRoot_valid : forall tail,
  TemplateRawDerives
    (coqRestrictedPADirectImpEConclusionTransportContext tail)
    coqRestrictedPADirectImpEWitnessConclusionTruthTemplate
    (coqRestrictedPADirectImpEWitnessConclusionTruthRoot tail).
Proof. intro tail. apply templateRawDerives_assumption. left. reflexivity. Qed.

Lemma coqRestrictedPADirectImpEOuterConclusionTruthRoot_valid : forall tail,
  TemplateRawDerives
    (coqRestrictedPADirectImpEConclusionTransportContext tail)
    coqRestrictedPADirectImpEOuterConclusionTruthTemplate
    (coqRestrictedPADirectImpEOuterConclusionTruthRoot tail).
Proof.
  intro tail. unfold coqRestrictedPADirectImpEOuterConclusionTruthRoot.
  rewrite <- coqRestrictedPADirectImpE_conclusion_motive_outer.
  apply coqRestrictedPADirectImpE_templateRawDerives_eqElim.
  - exact (coqRestrictedPADirectImpEConclusionSymmetryRoot_valid tail).
  - rewrite coqRestrictedPADirectImpE_conclusion_motive_witness.
    exact (coqRestrictedPADirectImpEWitnessConclusionTruthRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectImpEConclusionTransportRoot_valid : forall tail,
  TemplateRawDerives (coqRestrictedPADirectImpECaseContext tail)
    (tfImp coqRestrictedPADirectImpEWitnessConclusionTruthTemplate
      coqRestrictedPADirectImpEOuterConclusionTruthTemplate)
    (coqRestrictedPADirectImpEConclusionTransportRoot tail).
Proof.
  intro tail. unfold coqRestrictedPADirectImpEConclusionTransportRoot.
  apply coqRestrictedPADirectImpE_templateRawDerives_impI.
  exact (coqRestrictedPADirectImpEOuterConclusionTruthRoot_valid tail).
Qed.

(** ------------------------------------------------------------------
    Completion tautology joining the recursive law and transports. *)

Definition coqRestrictedPADirectImpECompletionContext0 tail : TemplateContext :=
  coqRestrictedPADirectImpECoreTemplate ::
    coqRestrictedPADirectImpECaseContext tail.

Definition coqRestrictedPADirectImpECompletionContext1 tail : TemplateContext :=
  tfImp coqRestrictedPADirectImpEOuterContextTruthTemplate
      coqRestrictedPADirectImpEWitnessContextTruthTemplate ::
    coqRestrictedPADirectImpECompletionContext0 tail.

Definition coqRestrictedPADirectImpECompletionContext2 tail : TemplateContext :=
  tfImp coqRestrictedPADirectImpEWitnessConclusionTruthTemplate
      coqRestrictedPADirectImpEOuterConclusionTruthTemplate ::
    coqRestrictedPADirectImpECompletionContext1 tail.

Definition coqRestrictedPADirectImpECompletionContext3 tail : TemplateContext :=
  coqRestrictedPADirectImpEAdmissibleTemplate ::
    coqRestrictedPADirectImpECompletionContext2 tail.

Definition coqRestrictedPADirectImpECompletionContext4 tail : TemplateContext :=
  coqRestrictedPADirectImpEOuterContextTruthTemplate ::
    coqRestrictedPADirectImpECompletionContext3 tail.

Definition coqRestrictedPADirectImpECompletionCoreRoot tail : TemplateRawProof :=
  trpAss (coqRestrictedPADirectImpECompletionContext4 tail)
    coqRestrictedPADirectImpECoreTemplate.

Definition coqRestrictedPADirectImpECompletionAdmissibleRoot tail
    : TemplateRawProof :=
  trpAss (coqRestrictedPADirectImpECompletionContext4 tail)
    coqRestrictedPADirectImpEAdmissibleTemplate.

Definition coqRestrictedPADirectImpECompletionCoreAfterAdmissibleRoot tail
    : TemplateRawProof :=
  trpImpE (coqRestrictedPADirectImpECompletionContext4 tail)
    coqRestrictedPADirectImpEAdmissibleTemplate
    (tfImp coqRestrictedPADirectImpEWitnessContextTruthTemplate
      coqRestrictedPADirectImpEWitnessConclusionTruthTemplate)
    (coqRestrictedPADirectImpECompletionCoreRoot tail)
    (coqRestrictedPADirectImpECompletionAdmissibleRoot tail).

Definition coqRestrictedPADirectImpECompletionContextTransportRoot tail
    : TemplateRawProof :=
  trpAss (coqRestrictedPADirectImpECompletionContext4 tail)
    (tfImp coqRestrictedPADirectImpEOuterContextTruthTemplate
      coqRestrictedPADirectImpEWitnessContextTruthTemplate).

Definition coqRestrictedPADirectImpECompletionOuterContextTruthRoot tail
    : TemplateRawProof :=
  trpAss (coqRestrictedPADirectImpECompletionContext4 tail)
    coqRestrictedPADirectImpEOuterContextTruthTemplate.

Definition coqRestrictedPADirectImpECompletionWitnessContextTruthRoot tail
    : TemplateRawProof :=
  trpImpE (coqRestrictedPADirectImpECompletionContext4 tail)
    coqRestrictedPADirectImpEOuterContextTruthTemplate
    coqRestrictedPADirectImpEWitnessContextTruthTemplate
    (coqRestrictedPADirectImpECompletionContextTransportRoot tail)
    (coqRestrictedPADirectImpECompletionOuterContextTruthRoot tail).

Definition coqRestrictedPADirectImpECompletionWitnessConclusionTruthRoot tail
    : TemplateRawProof :=
  trpImpE (coqRestrictedPADirectImpECompletionContext4 tail)
    coqRestrictedPADirectImpEWitnessContextTruthTemplate
    coqRestrictedPADirectImpEWitnessConclusionTruthTemplate
    (coqRestrictedPADirectImpECompletionCoreAfterAdmissibleRoot tail)
    (coqRestrictedPADirectImpECompletionWitnessContextTruthRoot tail).

Definition coqRestrictedPADirectImpECompletionConclusionTransportRoot tail
    : TemplateRawProof :=
  trpAss (coqRestrictedPADirectImpECompletionContext4 tail)
    (tfImp coqRestrictedPADirectImpEWitnessConclusionTruthTemplate
      coqRestrictedPADirectImpEOuterConclusionTruthTemplate).

Definition coqRestrictedPADirectImpECompletionOuterConclusionTruthRoot tail
    : TemplateRawProof :=
  trpImpE (coqRestrictedPADirectImpECompletionContext4 tail)
    coqRestrictedPADirectImpEWitnessConclusionTruthTemplate
    coqRestrictedPADirectImpEOuterConclusionTruthTemplate
    (coqRestrictedPADirectImpECompletionConclusionTransportRoot tail)
    (coqRestrictedPADirectImpECompletionWitnessConclusionTruthRoot tail).

Definition coqRestrictedPADirectImpECompletionOuterImpRoot tail
    : TemplateRawProof :=
  trpImpI (coqRestrictedPADirectImpECompletionContext3 tail)
    coqRestrictedPADirectImpEOuterContextTruthTemplate
    coqRestrictedPADirectImpEOuterConclusionTruthTemplate
    (coqRestrictedPADirectImpECompletionOuterConclusionTruthRoot tail).

Definition coqRestrictedPADirectImpECompletionAdmissibleImpRoot tail
    : TemplateRawProof :=
  trpImpI (coqRestrictedPADirectImpECompletionContext2 tail)
    coqRestrictedPADirectImpEAdmissibleTemplate
    (tfImp coqRestrictedPADirectImpEOuterContextTruthTemplate
      coqRestrictedPADirectImpEOuterConclusionTruthTemplate)
    (coqRestrictedPADirectImpECompletionOuterImpRoot tail).

Definition coqRestrictedPADirectImpECompletionConclusionTransportImpRoot tail
    : TemplateRawProof :=
  trpImpI (coqRestrictedPADirectImpECompletionContext1 tail)
    (tfImp coqRestrictedPADirectImpEWitnessConclusionTruthTemplate
      coqRestrictedPADirectImpEOuterConclusionTruthTemplate)
    coqRestrictedPADirectImpERemainingTemplate
    (coqRestrictedPADirectImpECompletionAdmissibleImpRoot tail).

Definition coqRestrictedPADirectImpECompletionContextTransportImpRoot tail
    : TemplateRawProof :=
  trpImpI (coqRestrictedPADirectImpECompletionContext0 tail)
    (tfImp coqRestrictedPADirectImpEOuterContextTruthTemplate
      coqRestrictedPADirectImpEWitnessContextTruthTemplate)
    (tfImp
      (tfImp coqRestrictedPADirectImpEWitnessConclusionTruthTemplate
        coqRestrictedPADirectImpEOuterConclusionTruthTemplate)
      coqRestrictedPADirectImpERemainingTemplate)
    (coqRestrictedPADirectImpECompletionConclusionTransportImpRoot tail).

Definition coqRestrictedPADirectImpECompletionRoot tail : TemplateRawProof :=
  trpImpI (coqRestrictedPADirectImpECaseContext tail)
    coqRestrictedPADirectImpECoreTemplate
    (tfImp
      (tfImp coqRestrictedPADirectImpEOuterContextTruthTemplate
        coqRestrictedPADirectImpEWitnessContextTruthTemplate)
      (tfImp
        (tfImp coqRestrictedPADirectImpEWitnessConclusionTruthTemplate
          coqRestrictedPADirectImpEOuterConclusionTruthTemplate)
        coqRestrictedPADirectImpERemainingTemplate))
    (coqRestrictedPADirectImpECompletionContextTransportImpRoot tail).

(** The four membership proofs use fixed list steps only. *)
Lemma coqRestrictedPADirectImpECompletionCoreRoot_valid : forall tail,
  TemplateRawDerives (coqRestrictedPADirectImpECompletionContext4 tail)
    coqRestrictedPADirectImpECoreTemplate
    (coqRestrictedPADirectImpECompletionCoreRoot tail).
Proof.
  intro tail. apply templateRawDerives_assumption.
  unfold coqRestrictedPADirectImpECompletionContext4,
    coqRestrictedPADirectImpECompletionContext3,
    coqRestrictedPADirectImpECompletionContext2,
    coqRestrictedPADirectImpECompletionContext1,
    coqRestrictedPADirectImpECompletionContext0.
  right. right. right. right. left. reflexivity.
Qed.

Lemma coqRestrictedPADirectImpECompletionAdmissibleRoot_valid : forall tail,
  TemplateRawDerives (coqRestrictedPADirectImpECompletionContext4 tail)
    coqRestrictedPADirectImpEAdmissibleTemplate
    (coqRestrictedPADirectImpECompletionAdmissibleRoot tail).
Proof.
  intro tail. apply templateRawDerives_assumption.
  unfold coqRestrictedPADirectImpECompletionContext4,
    coqRestrictedPADirectImpECompletionContext3.
  right. left. reflexivity.
Qed.

Lemma coqRestrictedPADirectImpECompletionContextTransportRoot_valid :
    forall tail,
  TemplateRawDerives (coqRestrictedPADirectImpECompletionContext4 tail)
    (tfImp coqRestrictedPADirectImpEOuterContextTruthTemplate
      coqRestrictedPADirectImpEWitnessContextTruthTemplate)
    (coqRestrictedPADirectImpECompletionContextTransportRoot tail).
Proof.
  intro tail. apply templateRawDerives_assumption.
  unfold coqRestrictedPADirectImpECompletionContext4,
    coqRestrictedPADirectImpECompletionContext3,
    coqRestrictedPADirectImpECompletionContext2,
    coqRestrictedPADirectImpECompletionContext1.
  right. right. right. left. reflexivity.
Qed.

Lemma coqRestrictedPADirectImpECompletionOuterContextTruthRoot_valid :
    forall tail,
  TemplateRawDerives (coqRestrictedPADirectImpECompletionContext4 tail)
    coqRestrictedPADirectImpEOuterContextTruthTemplate
    (coqRestrictedPADirectImpECompletionOuterContextTruthRoot tail).
Proof. intro tail. apply templateRawDerives_assumption. left. reflexivity. Qed.

Lemma coqRestrictedPADirectImpECompletionConclusionTransportRoot_valid :
    forall tail,
  TemplateRawDerives (coqRestrictedPADirectImpECompletionContext4 tail)
    (tfImp coqRestrictedPADirectImpEWitnessConclusionTruthTemplate
      coqRestrictedPADirectImpEOuterConclusionTruthTemplate)
    (coqRestrictedPADirectImpECompletionConclusionTransportRoot tail).
Proof.
  intro tail. apply templateRawDerives_assumption.
  unfold coqRestrictedPADirectImpECompletionContext4,
    coqRestrictedPADirectImpECompletionContext3,
    coqRestrictedPADirectImpECompletionContext2.
  right. right. left. reflexivity.
Qed.

Lemma coqRestrictedPADirectImpECompletionCoreAfterAdmissibleRoot_valid :
    forall tail,
  TemplateRawDerives (coqRestrictedPADirectImpECompletionContext4 tail)
    (tfImp coqRestrictedPADirectImpEWitnessContextTruthTemplate
      coqRestrictedPADirectImpEWitnessConclusionTruthTemplate)
    (coqRestrictedPADirectImpECompletionCoreAfterAdmissibleRoot tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectImpECompletionCoreAfterAdmissibleRoot.
  apply coqRestrictedPADirectImpE_templateRawDerives_impE.
  - exact (coqRestrictedPADirectImpECompletionCoreRoot_valid tail).
  - exact (coqRestrictedPADirectImpECompletionAdmissibleRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectImpECompletionWitnessContextTruthRoot_valid :
    forall tail,
  TemplateRawDerives (coqRestrictedPADirectImpECompletionContext4 tail)
    coqRestrictedPADirectImpEWitnessContextTruthTemplate
    (coqRestrictedPADirectImpECompletionWitnessContextTruthRoot tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectImpECompletionWitnessContextTruthRoot.
  apply coqRestrictedPADirectImpE_templateRawDerives_impE.
  - exact (coqRestrictedPADirectImpECompletionContextTransportRoot_valid tail).
  - exact
      (coqRestrictedPADirectImpECompletionOuterContextTruthRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectImpECompletionWitnessConclusionTruthRoot_valid :
    forall tail,
  TemplateRawDerives (coqRestrictedPADirectImpECompletionContext4 tail)
    coqRestrictedPADirectImpEWitnessConclusionTruthTemplate
    (coqRestrictedPADirectImpECompletionWitnessConclusionTruthRoot tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectImpECompletionWitnessConclusionTruthRoot.
  apply coqRestrictedPADirectImpE_templateRawDerives_impE.
  - exact
      (coqRestrictedPADirectImpECompletionCoreAfterAdmissibleRoot_valid tail).
  - exact
      (coqRestrictedPADirectImpECompletionWitnessContextTruthRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectImpECompletionOuterConclusionTruthRoot_valid :
    forall tail,
  TemplateRawDerives (coqRestrictedPADirectImpECompletionContext4 tail)
    coqRestrictedPADirectImpEOuterConclusionTruthTemplate
    (coqRestrictedPADirectImpECompletionOuterConclusionTruthRoot tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectImpECompletionOuterConclusionTruthRoot.
  apply coqRestrictedPADirectImpE_templateRawDerives_impE.
  - exact
      (coqRestrictedPADirectImpECompletionConclusionTransportRoot_valid tail).
  - exact
      (coqRestrictedPADirectImpECompletionWitnessConclusionTruthRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectImpECompletionOuterImpRoot_valid : forall tail,
  TemplateRawDerives (coqRestrictedPADirectImpECompletionContext3 tail)
    (tfImp coqRestrictedPADirectImpEOuterContextTruthTemplate
      coqRestrictedPADirectImpEOuterConclusionTruthTemplate)
    (coqRestrictedPADirectImpECompletionOuterImpRoot tail).
Proof.
  intro tail. unfold coqRestrictedPADirectImpECompletionOuterImpRoot.
  apply coqRestrictedPADirectImpE_templateRawDerives_impI.
  exact (coqRestrictedPADirectImpECompletionOuterConclusionTruthRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectImpECompletionAdmissibleImpRoot_valid : forall tail,
  TemplateRawDerives (coqRestrictedPADirectImpECompletionContext2 tail)
    coqRestrictedPADirectImpERemainingTemplate
    (coqRestrictedPADirectImpECompletionAdmissibleImpRoot tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectImpECompletionAdmissibleImpRoot,
    coqRestrictedPADirectImpERemainingTemplate.
  apply coqRestrictedPADirectImpE_templateRawDerives_impI.
  exact (coqRestrictedPADirectImpECompletionOuterImpRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectImpECompletionConclusionTransportImpRoot_valid :
    forall tail,
  TemplateRawDerives (coqRestrictedPADirectImpECompletionContext1 tail)
    (tfImp
      (tfImp coqRestrictedPADirectImpEWitnessConclusionTruthTemplate
        coqRestrictedPADirectImpEOuterConclusionTruthTemplate)
      coqRestrictedPADirectImpERemainingTemplate)
    (coqRestrictedPADirectImpECompletionConclusionTransportImpRoot tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectImpECompletionConclusionTransportImpRoot.
  apply coqRestrictedPADirectImpE_templateRawDerives_impI.
  exact (coqRestrictedPADirectImpECompletionAdmissibleImpRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectImpECompletionContextTransportImpRoot_valid :
    forall tail,
  TemplateRawDerives (coqRestrictedPADirectImpECompletionContext0 tail)
    (tfImp
      (tfImp coqRestrictedPADirectImpEOuterContextTruthTemplate
        coqRestrictedPADirectImpEWitnessContextTruthTemplate)
      (tfImp
        (tfImp coqRestrictedPADirectImpEWitnessConclusionTruthTemplate
          coqRestrictedPADirectImpEOuterConclusionTruthTemplate)
        coqRestrictedPADirectImpERemainingTemplate))
    (coqRestrictedPADirectImpECompletionContextTransportImpRoot tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectImpECompletionContextTransportImpRoot.
  apply coqRestrictedPADirectImpE_templateRawDerives_impI.
  exact
    (coqRestrictedPADirectImpECompletionConclusionTransportImpRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectImpECompletionRoot_valid : forall tail,
  TemplateRawDerives (coqRestrictedPADirectImpECaseContext tail)
    (tfImp coqRestrictedPADirectImpECoreTemplate
      (tfImp
        (tfImp coqRestrictedPADirectImpEOuterContextTruthTemplate
          coqRestrictedPADirectImpEWitnessContextTruthTemplate)
        (tfImp
          (tfImp coqRestrictedPADirectImpEWitnessConclusionTruthTemplate
            coqRestrictedPADirectImpEOuterConclusionTruthTemplate)
          coqRestrictedPADirectImpERemainingTemplate)))
    (coqRestrictedPADirectImpECompletionRoot tail).
Proof.
  intro tail. unfold coqRestrictedPADirectImpECompletionRoot.
  apply coqRestrictedPADirectImpE_templateRawDerives_impI.
  exact (coqRestrictedPADirectImpECompletionContextTransportImpRoot_valid tail).
Qed.

(** ------------------------------------------------------------------
    Raw compilation. *)

Theorem raw_codedPALocalProofOf_coqRestrictedPADirectImpEliminationCase :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  let translation := rawDirectStructuralTemplateTranslation M hPA inputs in
  RawCoqRestrictedPADirectImpERecursiveModusPonensLawRoot
    M translation tail ->
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation
        (coqRestrictedPADirectImpEDeepContext tail))
      (rawFormulaImpCode M
        (rawTemplateFormula translation coqRestrictedPADirectImpECaseTemplate)
        (rawTemplateFormula translation
          coqRestrictedPADirectImpERemainingTemplate)) root.
Proof.
  intros M hPA inputs tail. cbn zeta.
  set (translation := rawDirectStructuralTemplateTranslation M hPA inputs).
  intros (lawRoot & hlaw).
  set (context := rawTemplateContextCode translation
    (coqRestrictedPADirectImpECaseContext tail)).

  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectImpEStrongPrefixRoot tail)
    (proj1 (coqRestrictedPADirectImpEStrongPrefixRoot_valid tail))) as hk.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectImpERestrictedRoot tail)
    (proj1 (coqRestrictedPADirectImpERestrictedRoot_valid tail))) as hr.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectImpECodeRoot tail)
    (proj1 (coqRestrictedPADirectImpECodeRoot_valid tail))) as hc.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectImpEConclusionRoot tail)
    (proj1 (coqRestrictedPADirectImpEConclusionRoot_valid tail))) as hq.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectImpEFormulaRoot tail)
    (proj1 (coqRestrictedPADirectImpEFormulaRoot_valid tail))) as hf.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectImpEFirstEndpointRoot tail)
    (proj1 (coqRestrictedPADirectImpEFirstEndpointRoot_valid tail))) as he1.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectImpESecondEndpointRoot tail)
    (proj1 (coqRestrictedPADirectImpESecondEndpointRoot_valid tail))) as he2.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectImpEContextTransportRoot tail)
    (proj1 (coqRestrictedPADirectImpEContextTransportRoot_valid tail)))
    as hct.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectImpEConclusionTransportRoot tail)
    (proj1 (coqRestrictedPADirectImpEConclusionTransportRoot_valid tail)))
    as hqt.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectImpECompletionRoot tail)
    (proj1 (coqRestrictedPADirectImpECompletionRoot_valid tail))) as hcomp.

  change (RawCodedPALocalProofOf M context
    (rawTemplateFormula translation coqRestrictedPADirectImpEStrongPrefixTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectImpEStrongPrefixRoot tail))) in hk.
  change (RawCodedPALocalProofOf M context
    (rawTemplateFormula translation coqRestrictedPADirectImpERestrictedProofTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectImpERestrictedRoot tail))) in hr.
  change (RawCodedPALocalProofOf M context
    (rawTemplateFormula translation coqRestrictedPADirectImpECodeEqualityTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectImpECodeRoot tail))) in hc.
  change (RawCodedPALocalProofOf M context
    (rawTemplateFormula translation
      coqRestrictedPADirectImpEConclusionEqualityTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectImpEConclusionRoot tail))) in hq.
  change (RawCodedPALocalProofOf M context
    (rawTemplateFormula translation coqRestrictedPADirectImpEFormulaCodeTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectImpEFormulaRoot tail))) in hf.
  change (RawCodedPALocalProofOf M context
    (rawTemplateFormula translation coqRestrictedPADirectImpEFirstEndpointTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectImpEFirstEndpointRoot tail))) in he1.
  change (RawCodedPALocalProofOf M context
    (rawTemplateFormula translation coqRestrictedPADirectImpESecondEndpointTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectImpESecondEndpointRoot tail))) in he2.

  (** Seven literal modus-ponens steps expose the semantic core. *)
  assert (hlaw0 : RawCodedPALocalProofOf M context
    (rawFormulaImpCode M
      (rawTemplateFormula translation coqRestrictedPADirectImpEStrongPrefixTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectImpEAfterStrongPrefixTemplate)) lawRoot).
  { rewrite <- rawTemplateFormula_imp. exact hlaw. }
  set (r1 := rawProofImpERoot M context
    (rawTemplateFormula translation coqRestrictedPADirectImpEStrongPrefixTemplate)
    (rawTemplateFormula translation coqRestrictedPADirectImpEAfterStrongPrefixTemplate)
    lawRoot (rawTemplateProofCode translation
      (coqRestrictedPADirectImpEStrongPrefixRoot tail))).
  assert (h1 : RawCodedPALocalProofOf M context
    (rawTemplateFormula translation coqRestrictedPADirectImpEAfterStrongPrefixTemplate) r1).
  { unfold r1. eapply raw_codedPALocalProofOf_impE; eauto. }

  assert (h1' : RawCodedPALocalProofOf M context
    (rawFormulaImpCode M
      (rawTemplateFormula translation coqRestrictedPADirectImpERestrictedProofTemplate)
      (rawTemplateFormula translation coqRestrictedPADirectImpEAfterRestrictedTemplate)) r1).
  { rewrite <- rawTemplateFormula_imp. exact h1. }
  set (r2 := rawProofImpERoot M context
    (rawTemplateFormula translation coqRestrictedPADirectImpERestrictedProofTemplate)
    (rawTemplateFormula translation coqRestrictedPADirectImpEAfterRestrictedTemplate)
    r1 (rawTemplateProofCode translation
      (coqRestrictedPADirectImpERestrictedRoot tail))).
  assert (h2 : RawCodedPALocalProofOf M context
    (rawTemplateFormula translation coqRestrictedPADirectImpEAfterRestrictedTemplate) r2).
  { unfold r2. eapply raw_codedPALocalProofOf_impE; eauto. }

  assert (h2' : RawCodedPALocalProofOf M context
    (rawFormulaImpCode M
      (rawTemplateFormula translation coqRestrictedPADirectImpECodeEqualityTemplate)
      (rawTemplateFormula translation coqRestrictedPADirectImpEAfterCodeTemplate)) r2).
  { rewrite <- rawTemplateFormula_imp. exact h2. }
  set (r3 := rawProofImpERoot M context
    (rawTemplateFormula translation coqRestrictedPADirectImpECodeEqualityTemplate)
    (rawTemplateFormula translation coqRestrictedPADirectImpEAfterCodeTemplate)
    r2 (rawTemplateProofCode translation (coqRestrictedPADirectImpECodeRoot tail))).
  assert (h3 : RawCodedPALocalProofOf M context
    (rawTemplateFormula translation coqRestrictedPADirectImpEAfterCodeTemplate) r3).
  { unfold r3. eapply raw_codedPALocalProofOf_impE; eauto. }

  assert (h3' : RawCodedPALocalProofOf M context
    (rawFormulaImpCode M
      (rawTemplateFormula translation coqRestrictedPADirectImpEConclusionEqualityTemplate)
      (rawTemplateFormula translation coqRestrictedPADirectImpEAfterConclusionTemplate)) r3).
  { rewrite <- rawTemplateFormula_imp. exact h3. }
  set (r4 := rawProofImpERoot M context
    (rawTemplateFormula translation coqRestrictedPADirectImpEConclusionEqualityTemplate)
    (rawTemplateFormula translation coqRestrictedPADirectImpEAfterConclusionTemplate)
    r3 (rawTemplateProofCode translation
      (coqRestrictedPADirectImpEConclusionRoot tail))).
  assert (h4 : RawCodedPALocalProofOf M context
    (rawTemplateFormula translation coqRestrictedPADirectImpEAfterConclusionTemplate) r4).
  { unfold r4. eapply raw_codedPALocalProofOf_impE; eauto. }

  assert (h4' : RawCodedPALocalProofOf M context
    (rawFormulaImpCode M
      (rawTemplateFormula translation coqRestrictedPADirectImpEFormulaCodeTemplate)
      (rawTemplateFormula translation coqRestrictedPADirectImpEAfterFormulaTemplate)) r4).
  { rewrite <- rawTemplateFormula_imp. exact h4. }
  set (r5 := rawProofImpERoot M context
    (rawTemplateFormula translation coqRestrictedPADirectImpEFormulaCodeTemplate)
    (rawTemplateFormula translation coqRestrictedPADirectImpEAfterFormulaTemplate)
    r4 (rawTemplateProofCode translation
      (coqRestrictedPADirectImpEFormulaRoot tail))).
  assert (h5 : RawCodedPALocalProofOf M context
    (rawTemplateFormula translation coqRestrictedPADirectImpEAfterFormulaTemplate) r5).
  { unfold r5. eapply raw_codedPALocalProofOf_impE; eauto. }

  assert (h5' : RawCodedPALocalProofOf M context
    (rawFormulaImpCode M
      (rawTemplateFormula translation coqRestrictedPADirectImpEFirstEndpointTemplate)
      (rawTemplateFormula translation coqRestrictedPADirectImpEAfterFirstEndpointTemplate)) r5).
  { rewrite <- rawTemplateFormula_imp. exact h5. }
  set (r6 := rawProofImpERoot M context
    (rawTemplateFormula translation coqRestrictedPADirectImpEFirstEndpointTemplate)
    (rawTemplateFormula translation coqRestrictedPADirectImpEAfterFirstEndpointTemplate)
    r5 (rawTemplateProofCode translation
      (coqRestrictedPADirectImpEFirstEndpointRoot tail))).
  assert (h6 : RawCodedPALocalProofOf M context
    (rawTemplateFormula translation coqRestrictedPADirectImpEAfterFirstEndpointTemplate) r6).
  { unfold r6. eapply raw_codedPALocalProofOf_impE; eauto. }

  assert (h6' : RawCodedPALocalProofOf M context
    (rawFormulaImpCode M
      (rawTemplateFormula translation coqRestrictedPADirectImpESecondEndpointTemplate)
      (rawTemplateFormula translation coqRestrictedPADirectImpECoreTemplate)) r6).
  { rewrite <- rawTemplateFormula_imp. exact h6. }
  set (coreRoot := rawProofImpERoot M context
    (rawTemplateFormula translation coqRestrictedPADirectImpESecondEndpointTemplate)
    (rawTemplateFormula translation coqRestrictedPADirectImpECoreTemplate)
    r6 (rawTemplateProofCode translation
      (coqRestrictedPADirectImpESecondEndpointRoot tail))).
  assert (hcore : RawCodedPALocalProofOf M context
    (rawTemplateFormula translation coqRestrictedPADirectImpECoreTemplate) coreRoot).
  { unfold coreRoot. eapply raw_codedPALocalProofOf_impE; eauto. }

  (** Apply the checked three-input completion tautology. *)
  assert (hcomp0 : RawCodedPALocalProofOf M context
    (rawFormulaImpCode M
      (rawTemplateFormula translation coqRestrictedPADirectImpECoreTemplate)
      (rawTemplateFormula translation
        (tfImp
          (tfImp coqRestrictedPADirectImpEOuterContextTruthTemplate
            coqRestrictedPADirectImpEWitnessContextTruthTemplate)
          (tfImp
            (tfImp coqRestrictedPADirectImpEWitnessConclusionTruthTemplate
              coqRestrictedPADirectImpEOuterConclusionTruthTemplate)
            coqRestrictedPADirectImpERemainingTemplate))))
    (rawTemplateProofCode translation
      (coqRestrictedPADirectImpECompletionRoot tail))).
  { rewrite <- rawTemplateFormula_imp. exact hcomp. }
  set (c1 := rawProofImpERoot M context
    (rawTemplateFormula translation coqRestrictedPADirectImpECoreTemplate)
    (rawTemplateFormula translation
      (tfImp
        (tfImp coqRestrictedPADirectImpEOuterContextTruthTemplate
          coqRestrictedPADirectImpEWitnessContextTruthTemplate)
        (tfImp
          (tfImp coqRestrictedPADirectImpEWitnessConclusionTruthTemplate
            coqRestrictedPADirectImpEOuterConclusionTruthTemplate)
          coqRestrictedPADirectImpERemainingTemplate)))
    (rawTemplateProofCode translation
      (coqRestrictedPADirectImpECompletionRoot tail)) coreRoot).
  assert (hc1 : RawCodedPALocalProofOf M context
    (rawTemplateFormula translation
      (tfImp
        (tfImp coqRestrictedPADirectImpEOuterContextTruthTemplate
          coqRestrictedPADirectImpEWitnessContextTruthTemplate)
        (tfImp
          (tfImp coqRestrictedPADirectImpEWitnessConclusionTruthTemplate
            coqRestrictedPADirectImpEOuterConclusionTruthTemplate)
          coqRestrictedPADirectImpERemainingTemplate))) c1).
  {
    unfold c1.
    exact (raw_codedPALocalProofOf_impE M hPA context
      (rawTemplateFormula translation coqRestrictedPADirectImpECoreTemplate)
      (rawTemplateFormula translation
        (tfImp
          (tfImp coqRestrictedPADirectImpEOuterContextTruthTemplate
            coqRestrictedPADirectImpEWitnessContextTruthTemplate)
          (tfImp
            (tfImp coqRestrictedPADirectImpEWitnessConclusionTruthTemplate
              coqRestrictedPADirectImpEOuterConclusionTruthTemplate)
            coqRestrictedPADirectImpERemainingTemplate)))
      (rawTemplateProofCode translation
        (coqRestrictedPADirectImpECompletionRoot tail)) coreRoot
      hcomp0 hcore).
  }

  change (RawCodedPALocalProofOf M context
    (rawTemplateFormula translation
      (tfImp coqRestrictedPADirectImpEOuterContextTruthTemplate
        coqRestrictedPADirectImpEWitnessContextTruthTemplate))
    (rawTemplateProofCode translation
      (coqRestrictedPADirectImpEContextTransportRoot tail))) in hct.
  assert (hc1' : RawCodedPALocalProofOf M context
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        (tfImp coqRestrictedPADirectImpEOuterContextTruthTemplate
          coqRestrictedPADirectImpEWitnessContextTruthTemplate))
      (rawTemplateFormula translation
        (tfImp
          (tfImp coqRestrictedPADirectImpEWitnessConclusionTruthTemplate
            coqRestrictedPADirectImpEOuterConclusionTruthTemplate)
          coqRestrictedPADirectImpERemainingTemplate))) c1).
  { rewrite <- rawTemplateFormula_imp. exact hc1. }
  set (c2 := rawProofImpERoot M context
    (rawTemplateFormula translation
      (tfImp coqRestrictedPADirectImpEOuterContextTruthTemplate
        coqRestrictedPADirectImpEWitnessContextTruthTemplate))
    (rawTemplateFormula translation
      (tfImp
        (tfImp coqRestrictedPADirectImpEWitnessConclusionTruthTemplate
          coqRestrictedPADirectImpEOuterConclusionTruthTemplate)
        coqRestrictedPADirectImpERemainingTemplate))
    c1 (rawTemplateProofCode translation
      (coqRestrictedPADirectImpEContextTransportRoot tail))).
  assert (hc2 : RawCodedPALocalProofOf M context
    (rawTemplateFormula translation
      (tfImp
        (tfImp coqRestrictedPADirectImpEWitnessConclusionTruthTemplate
          coqRestrictedPADirectImpEOuterConclusionTruthTemplate)
        coqRestrictedPADirectImpERemainingTemplate)) c2).
  {
    unfold c2.
    exact (raw_codedPALocalProofOf_impE M hPA context
      (rawTemplateFormula translation
        (tfImp coqRestrictedPADirectImpEOuterContextTruthTemplate
          coqRestrictedPADirectImpEWitnessContextTruthTemplate))
      (rawTemplateFormula translation
        (tfImp
          (tfImp coqRestrictedPADirectImpEWitnessConclusionTruthTemplate
            coqRestrictedPADirectImpEOuterConclusionTruthTemplate)
          coqRestrictedPADirectImpERemainingTemplate))
      c1
      (rawTemplateProofCode translation
        (coqRestrictedPADirectImpEContextTransportRoot tail))
      hc1' hct).
  }

  change (RawCodedPALocalProofOf M context
    (rawTemplateFormula translation
      (tfImp coqRestrictedPADirectImpEWitnessConclusionTruthTemplate
        coqRestrictedPADirectImpEOuterConclusionTruthTemplate))
    (rawTemplateProofCode translation
      (coqRestrictedPADirectImpEConclusionTransportRoot tail))) in hqt.
  assert (hc2' : RawCodedPALocalProofOf M context
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        (tfImp coqRestrictedPADirectImpEWitnessConclusionTruthTemplate
          coqRestrictedPADirectImpEOuterConclusionTruthTemplate))
      (rawTemplateFormula translation coqRestrictedPADirectImpERemainingTemplate)) c2).
  { rewrite <- rawTemplateFormula_imp. exact hc2. }
  set (remainingRoot := rawProofImpERoot M context
    (rawTemplateFormula translation
      (tfImp coqRestrictedPADirectImpEWitnessConclusionTruthTemplate
        coqRestrictedPADirectImpEOuterConclusionTruthTemplate))
    (rawTemplateFormula translation coqRestrictedPADirectImpERemainingTemplate)
    c2 (rawTemplateProofCode translation
      (coqRestrictedPADirectImpEConclusionTransportRoot tail))).
  assert (hremaining : RawCodedPALocalProofOf M context
    (rawTemplateFormula translation coqRestrictedPADirectImpERemainingTemplate)
    remainingRoot).
  {
    unfold remainingRoot.
    exact (raw_codedPALocalProofOf_impE M hPA context
      (rawTemplateFormula translation
        (tfImp coqRestrictedPADirectImpEWitnessConclusionTruthTemplate
          coqRestrictedPADirectImpEOuterConclusionTruthTemplate))
      (rawTemplateFormula translation coqRestrictedPADirectImpERemainingTemplate)
      c2
      (rawTemplateProofCode translation
        (coqRestrictedPADirectImpEConclusionTransportRoot tail))
      hc2' hqt).
  }

  exists (rawProofImpIRoot M
    (rawTemplateContextCode translation
      (coqRestrictedPADirectImpEDeepContext tail))
    (rawTemplateFormula translation coqRestrictedPADirectImpECaseTemplate)
    (rawTemplateFormula translation coqRestrictedPADirectImpERemainingTemplate)
    remainingRoot).
  apply (raw_codedPALocalProofOf_impI M hPA
    (rawTemplateContextCode translation
      (coqRestrictedPADirectImpEDeepContext tail))
    (rawTemplateFormula translation coqRestrictedPADirectImpECaseTemplate)
    (rawTemplateFormula translation coqRestrictedPADirectImpERemainingTemplate)
    remainingRoot).
  change (RawCodedPALocalProofOf M context
    (rawTemplateFormula translation coqRestrictedPADirectImpERemainingTemplate)
    remainingRoot).
  exact hremaining.
Qed.

Corollary raw_coqRestrictedPADirectStrongStepImpEliminationCaseRoot :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  let translation := rawDirectStructuralTemplateTranslation M hPA inputs in
  RawCoqRestrictedPADirectImpERecursiveModusPonensLawRoot
    M translation tail ->
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation
        (rawCoqRestrictedPADirectEndpointWitnessBodyTemplate ::
          rawCoqRestrictedPADirectEndpointDeepTail
            (rawCoqRestrictedPADirectStrongStepEndpointTail tail)))
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          (rawCoqRestrictedPAProofRuleCaseTemplate rawCoqRuleImpElimination
            (liftTerm 8 (tVar 4)) (tVar 7) (liftTerm 8 (tVar 2))
            (tVar 6) (tVar 5) (tVar 4) (tVar 3)
            (tVar 2) (tVar 1) (tVar 0)))
        (rawTemplateFormula translation
          (rawCoqTemplateRenameN 8
            rawCoqRestrictedPADirectStrongStepRemainingTemplate))) root.
Proof.
  intros M hPA inputs tail. cbn zeta. intro hlaw.
  destruct
    (raw_codedPALocalProofOf_coqRestrictedPADirectImpEliminationCase
      M hPA inputs tail hlaw) as [root hroot].
  exists root.
  unfold coqRestrictedPADirectImpEDeepContext in hroot.
  rewrite raw_coqRestrictedPADirectEndpointDeepContext_shape in hroot.
  rewrite <- coqRestrictedPADirectImpE_remaining_shape.
  exact hroot.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectImpEliminationCase.
