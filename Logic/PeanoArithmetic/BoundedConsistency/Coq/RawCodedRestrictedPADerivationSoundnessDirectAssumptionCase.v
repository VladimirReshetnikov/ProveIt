(**
  The genuine assumption-rule case for direct derivation soundness.

  The endpoint relation binds eight rule witnesses.  In its assumption
  branch, the displayed context and formula are not definitionally the
  outer endpoint context and conclusion: the endpoint conjunction supplies

      witnessContext = outerContext

  while the branch itself supplies

      outerConclusion = witnessFormula.

  Consequently the constructor-local soundness proof needs two honest uses
  of equality elimination.  This module compiles those transports, all
  conjunction projections, inherited-assumption lookups, and implication
  plumbing.  Its sole semantic input is the exact pointwise law saying that
  truth of a context plus membership of a formula implies truth of that
  formula.

  The local context below is the semantically ready permutation of the
  context generated while proving the strong step [K(root) -> P(root)]:
  context truth and admissibility have already been introduced, and the
  endpoint premise has been moved to the head so that the eight-existential
  dispatcher can eliminate it.  The permutation is recorded explicitly;
  this file does not silently identify the two coded contexts.
*)

From Stdlib Require Import List Sorting.Permutation.
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
  RawCodedProofRules
  RawCodedProofBinaryConstructors
  RawCodedProofImpIConstructor
  RawCodedProofAssumptionLeaf
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
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAssumptionCase.

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
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedProofImpIConstructor.
Import PABoundedRawCodedProofAssumptionLeaf.
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
    The exact strong-step context surrounding endpoint elimination. *)

Definition coqRestrictedPADirectAssumptionNaturalStepContext
    : TemplateContext :=
  [coqRestrictedPADerivationSoundnessContextTruthTemplate;
   coqRestrictedPADerivationSoundnessAdmissibleTemplate;
   coqRestrictedPADerivationSoundnessEndpointTemplate;
   coqRestrictedPADerivationSoundnessRestrictedProofTemplate;
   coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate].

Definition coqRestrictedPADirectAssumptionEndpointTail
    : TemplateContext :=
  [coqRestrictedPADerivationSoundnessContextTruthTemplate;
   coqRestrictedPADerivationSoundnessAdmissibleTemplate;
   coqRestrictedPADerivationSoundnessRestrictedProofTemplate;
   coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate].

Lemma coqRestrictedPADirectAssumption_endpoint_permutation :
  Permutation
    (coqRestrictedPADerivationSoundnessEndpointTemplate ::
      coqRestrictedPADirectAssumptionEndpointTail)
    coqRestrictedPADirectAssumptionNaturalStepContext.
Proof.
  unfold coqRestrictedPADirectAssumptionEndpointTail,
    coqRestrictedPADirectAssumptionNaturalStepContext.
  etransitivity.
  - apply perm_swap.
  - apply perm_skip. apply perm_swap.
Qed.

(** Every formula inherited from the caller's tail remains available after
    all endpoint witnesses have been opened.  It has, necessarily, been
    renamed once for each existential elimination. *)
Lemma raw_coqTemplateNestedExContext_inherited : forall
    count body tail inherited,
  In inherited tail ->
  In (rawCoqTemplateRenameN count inherited)
    (rawCoqTemplateNestedExContext count body tail).
Proof.
  induction count as [|remaining ih];
    intros body tail inherited hin.
  - cbn [rawCoqTemplateRenameN rawCoqTemplateNestedExContext].
    right. exact hin.
  - cbn [rawCoqTemplateRenameN rawCoqTemplateNestedExContext].
    apply ih.
    unfold templateContextShift, templateContextRename.
    apply in_map. right. exact hin.
Qed.

Definition coqRestrictedPADirectAssumptionDeepContext : TemplateContext :=
  rawCoqRestrictedPADirectEndpointDeepContext
    coqRestrictedPADirectAssumptionEndpointTail.

(** ------------------------------------------------------------------
    Literal witness terms and formulas at the eight-witness depth. *)

Definition coqRestrictedPADirectAssumptionWitnessContextTerm
    : TemplateTerm := ttVar 7.

Definition coqRestrictedPADirectAssumptionWitnessFormulaTerm
    : TemplateTerm := ttVar 6.

Definition coqRestrictedPADirectAssumptionOuterContextTerm
    : TemplateTerm := embedPATerm (liftTerm 8 (tVar 3)).

Definition coqRestrictedPADirectAssumptionOuterConclusionTerm
    : TemplateTerm := embedPATerm (liftTerm 8 (tVar 2)).

Definition coqRestrictedPADirectAssumptionContextEqualityTemplate
    : TemplateFormula :=
  tfEq coqRestrictedPADirectAssumptionWitnessContextTerm
    coqRestrictedPADirectAssumptionOuterContextTerm.

Definition coqRestrictedPADirectAssumptionConclusionEqualityTemplate
    : TemplateFormula :=
  tfEq coqRestrictedPADirectAssumptionOuterConclusionTerm
    coqRestrictedPADirectAssumptionWitnessFormulaTerm.

Definition coqRestrictedPADirectAssumptionMembershipTemplate
    : TemplateFormula :=
  embedPAFormula
    (contextListMemberTermAt (tVar 7) (tVar 6)).

Definition coqRestrictedPADirectAssumptionCodeEqualityTemplate
    : TemplateFormula :=
  embedPAFormula
    (pEq (liftTerm 8 (tVar 4))
      (proofAssCodeTerm (tVar 7) (tVar 6))).

Definition coqRestrictedPADirectAssumptionTerminalTruthTemplate
    : TemplateFormula := embedPAFormula (pEq tZero tZero).

Definition coqRestrictedPADirectAssumptionMembershipSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectAssumptionMembershipTemplate
    coqRestrictedPADirectAssumptionTerminalTruthTemplate.

Definition coqRestrictedPADirectAssumptionConclusionSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectAssumptionConclusionEqualityTemplate
    coqRestrictedPADirectAssumptionMembershipSuffixTemplate.

Definition coqRestrictedPADirectAssumptionCaseTemplate : TemplateFormula :=
  rawCoqRestrictedPAProofRuleCaseTemplate rawCoqRuleAssumption
    (liftTerm 8 (tVar 4)) (tVar 7) (liftTerm 8 (tVar 2))
    (tVar 6) (tVar 5) (tVar 4) (tVar 3)
    (tVar 2) (tVar 1) (tVar 0).

Lemma coqRestrictedPADirectAssumption_case_shape :
  coqRestrictedPADirectAssumptionCaseTemplate =
  tfAnd coqRestrictedPADirectAssumptionCodeEqualityTemplate
    coqRestrictedPADirectAssumptionConclusionSuffixTemplate.
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectAssumption_endpoint_equality_shape :
  rawCoqRestrictedPADirectEndpointWitnessEqualityTemplate =
  coqRestrictedPADirectAssumptionContextEqualityTemplate.
Proof. reflexivity. Qed.

(** Deep truth applications.  The hierarchy parameters are closed template
    parameters; only the three semantic arguments are shifted by the eight
    endpoint witnesses. *)
Definition coqRestrictedPADirectAssumptionOuterContextTruthTemplate
    : TemplateFormula :=
  rawCoqTemplateRenameN 8
    coqRestrictedPADerivationSoundnessContextTruthTemplate.

Definition coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate
    : TemplateFormula :=
  rawCoqTemplateRenameN 8
    coqRestrictedPADerivationSoundnessConclusionTruthTemplate.

Definition coqRestrictedPADirectAssumptionWitnessContextTruthTemplate
    : TemplateFormula :=
  tfOpaque coqRestrictedPAContextTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     coqRestrictedPADirectAssumptionWitnessContextTerm;
     ttVar 9; ttVar 8].

Definition coqRestrictedPADirectAssumptionWitnessFormulaTruthTemplate
    : TemplateFormula :=
  tfOpaque coqRestrictedPAConclusionTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     coqRestrictedPADirectAssumptionWitnessFormulaTerm;
     ttVar 9; ttVar 8].

Lemma coqRestrictedPADirectAssumption_outer_context_truth_shape :
  coqRestrictedPADirectAssumptionOuterContextTruthTemplate =
  tfOpaque coqRestrictedPAContextTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     coqRestrictedPADirectAssumptionOuterContextTerm;
     ttVar 9; ttVar 8].
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectAssumption_outer_conclusion_truth_shape :
  coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate =
  tfOpaque coqRestrictedPAConclusionTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     coqRestrictedPADirectAssumptionOuterConclusionTerm;
     ttVar 9; ttVar 8].
Proof. reflexivity. Qed.

(** The exact remaining semantic law, specialized to the literal rule
    witnesses.  This is not an assumption-case root: it mentions neither
    the rule disjunction nor the endpoint conjunction. *)
Definition coqRestrictedPADirectAssumptionMembershipTruthLawTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectAssumptionWitnessContextTruthTemplate
    (tfImp coqRestrictedPADirectAssumptionMembershipTemplate
      coqRestrictedPADirectAssumptionWitnessFormulaTruthTemplate).

Definition coqRestrictedPADirectAssumptionCaseContext : TemplateContext :=
  coqRestrictedPADirectAssumptionCaseTemplate ::
    coqRestrictedPADirectAssumptionDeepContext.

Definition RawCoqRestrictedPADirectAssumptionMembershipTruthLawRoot
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation
        coqRestrictedPADirectAssumptionCaseContext)
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionMembershipTruthLawTemplate)
      root.

Arguments RawCoqRestrictedPADirectAssumptionMembershipTruthLawRoot
  M translation : clear implicits.

(** Small declarative composition lemmas keep validation opaque at child
    roots.  This matters here because reducing a concrete projection chain
    would otherwise unfold the complete seventeen-branch endpoint formula. *)
Lemma coqRestrictedPADirect_templateRawDerives_andE1 : forall
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

Lemma coqRestrictedPADirect_templateRawDerives_andE2 : forall
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

Lemma coqRestrictedPADirect_templateRawDerives_impI : forall
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

Lemma coqRestrictedPADirect_templateRawDerives_eqElim : forall
    context source target motive equalityChild motiveChild,
  TemplateRawDerives context (tfEq source target) equalityChild ->
  TemplateRawDerives context
    (templateFormulaOpen source motive) motiveChild ->
  TemplateRawDerives context
    (templateFormulaOpen target motive)
    (trpEqElim context source target motive
      equalityChild motiveChild).
Proof.
  intros context source target motive equalityChild motiveChild
    [heqValid [heqContext heqConclusion]]
    [hmotiveValid [hmotiveContext hmotiveConclusion]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; try assumption; reflexivity.
Qed.

(** ------------------------------------------------------------------
    Finite proof objects for projections and equality transports. *)

Definition coqRestrictedPADirectAssumptionEndpointBodyRoot
    : TemplateRawProof :=
  trpAss coqRestrictedPADirectAssumptionCaseContext
    rawCoqRestrictedPADirectEndpointWitnessBodyTemplate.

Definition coqRestrictedPADirectAssumptionContextEqualityRoot
    : TemplateRawProof :=
  trpAndE1 coqRestrictedPADirectAssumptionCaseContext
    coqRestrictedPADirectAssumptionContextEqualityTemplate
    (rawCoqTemplateRuleDisjunction
      rawCoqRestrictedPADirectEndpointRuleCaseTemplates)
    coqRestrictedPADirectAssumptionEndpointBodyRoot.

Definition coqRestrictedPADirectAssumptionCaseRoot : TemplateRawProof :=
  trpAss coqRestrictedPADirectAssumptionCaseContext
    coqRestrictedPADirectAssumptionCaseTemplate.

Definition coqRestrictedPADirectAssumptionConclusionSuffixRoot
    : TemplateRawProof :=
  trpAndE2 coqRestrictedPADirectAssumptionCaseContext
    coqRestrictedPADirectAssumptionCodeEqualityTemplate
    coqRestrictedPADirectAssumptionConclusionSuffixTemplate
    coqRestrictedPADirectAssumptionCaseRoot.

Definition coqRestrictedPADirectAssumptionConclusionEqualityRoot
    : TemplateRawProof :=
  trpAndE1 coqRestrictedPADirectAssumptionCaseContext
    coqRestrictedPADirectAssumptionConclusionEqualityTemplate
    coqRestrictedPADirectAssumptionMembershipSuffixTemplate
    coqRestrictedPADirectAssumptionConclusionSuffixRoot.

Definition coqRestrictedPADirectAssumptionMembershipSuffixRoot
    : TemplateRawProof :=
  trpAndE2 coqRestrictedPADirectAssumptionCaseContext
    coqRestrictedPADirectAssumptionConclusionEqualityTemplate
    coqRestrictedPADirectAssumptionMembershipSuffixTemplate
    coqRestrictedPADirectAssumptionConclusionSuffixRoot.

Definition coqRestrictedPADirectAssumptionMembershipRoot
    : TemplateRawProof :=
  trpAndE1 coqRestrictedPADirectAssumptionCaseContext
    coqRestrictedPADirectAssumptionMembershipTemplate
    coqRestrictedPADirectAssumptionTerminalTruthTemplate
    coqRestrictedPADirectAssumptionMembershipSuffixRoot.

Definition coqRestrictedPADirectAssumptionOuterContextTruthRoot
    : TemplateRawProof :=
  trpAss coqRestrictedPADirectAssumptionCaseContext
    coqRestrictedPADirectAssumptionOuterContextTruthTemplate.

(** A standard equality-symmetry proof, specialized twice below.  The
    renamed fixed side is essential: it remains free when the motive's
    placeholder binder is opened. *)
Definition coqRestrictedPADirectEqSymmetryMotive
    (fixed : TemplateTerm) : TemplateFormula :=
  tfEq (ttVar 0) (templateTermRename S fixed).

Definition coqRestrictedPADirectEqSymmetryRoot
    (context : TemplateContext) (left right : TemplateTerm)
    (equalityRoot : TemplateRawProof) : TemplateRawProof :=
  trpEqElim context left right
    (coqRestrictedPADirectEqSymmetryMotive left)
    equalityRoot (trpEqRefl context left).

Lemma coqRestrictedPADirectEqSymmetryMotive_open : forall left input,
  templateFormulaOpen input
    (coqRestrictedPADirectEqSymmetryMotive left) =
  tfEq input left.
Proof.
  intros left input.
  unfold coqRestrictedPADirectEqSymmetryMotive, templateFormulaOpen.
  cbn. f_equal.
  induction left; cbn; f_equal; assumption || reflexivity.
Qed.

Lemma coqRestrictedPADirectEqSymmetryRoot_valid : forall
    context left right equalityRoot,
  TemplateRawDerives context (tfEq left right) equalityRoot ->
  TemplateRawDerives context (tfEq right left)
    (coqRestrictedPADirectEqSymmetryRoot
      context left right equalityRoot).
Proof.
  intros context left right equalityRoot
    [hequalityValid [hequalityContext hequalityConclusion]].
  unfold TemplateRawDerives,
    coqRestrictedPADirectEqSymmetryRoot.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  rewrite !coqRestrictedPADirectEqSymmetryMotive_open.
  repeat split; try assumption; try reflexivity.
Qed.

(** Motives for the two backwards transports. *)
Definition coqRestrictedPADirectAssumptionContextTruthMotive
    : TemplateFormula :=
  tfOpaque coqRestrictedPAContextTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     ttVar 0; ttVar 10; ttVar 9].

Definition coqRestrictedPADirectAssumptionConclusionTruthMotive
    : TemplateFormula :=
  tfOpaque coqRestrictedPAConclusionTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     ttVar 0; ttVar 10; ttVar 9].

Lemma coqRestrictedPADirectAssumption_context_motive_outer :
  templateFormulaOpen coqRestrictedPADirectAssumptionOuterContextTerm
    coqRestrictedPADirectAssumptionContextTruthMotive =
  coqRestrictedPADirectAssumptionOuterContextTruthTemplate.
Proof.
  rewrite coqRestrictedPADirectAssumption_outer_context_truth_shape.
  reflexivity.
Qed.

Lemma coqRestrictedPADirectAssumption_context_motive_witness :
  templateFormulaOpen coqRestrictedPADirectAssumptionWitnessContextTerm
    coqRestrictedPADirectAssumptionContextTruthMotive =
  coqRestrictedPADirectAssumptionWitnessContextTruthTemplate.
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectAssumption_conclusion_motive_outer :
  templateFormulaOpen coqRestrictedPADirectAssumptionOuterConclusionTerm
    coqRestrictedPADirectAssumptionConclusionTruthMotive =
  coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate.
Proof.
  rewrite coqRestrictedPADirectAssumption_outer_conclusion_truth_shape.
  reflexivity.
Qed.

Lemma coqRestrictedPADirectAssumption_conclusion_motive_witness :
  templateFormulaOpen coqRestrictedPADirectAssumptionWitnessFormulaTerm
    coqRestrictedPADirectAssumptionConclusionTruthMotive =
  coqRestrictedPADirectAssumptionWitnessFormulaTruthTemplate.
Proof. reflexivity. Qed.

(** Context truth is transported backwards along
    [witnessContext = outerContext]. *)
Definition coqRestrictedPADirectAssumptionContextSymmetryRoot
    : TemplateRawProof :=
  coqRestrictedPADirectEqSymmetryRoot
    coqRestrictedPADirectAssumptionCaseContext
    coqRestrictedPADirectAssumptionWitnessContextTerm
    coqRestrictedPADirectAssumptionOuterContextTerm
    coqRestrictedPADirectAssumptionContextEqualityRoot.

Definition coqRestrictedPADirectAssumptionWitnessContextTruthRoot
    : TemplateRawProof :=
  trpEqElim coqRestrictedPADirectAssumptionCaseContext
    coqRestrictedPADirectAssumptionOuterContextTerm
    coqRestrictedPADirectAssumptionWitnessContextTerm
    coqRestrictedPADirectAssumptionContextTruthMotive
    coqRestrictedPADirectAssumptionContextSymmetryRoot
    coqRestrictedPADirectAssumptionOuterContextTruthRoot.

(** The semantic law returns truth of the witness formula.  A second
    backwards transport along [outerConclusion = witnessFormula] gives the
    exact shifted conclusion demanded by the strong step.  Since the
    witness-formula truth is produced by an external semantic root, compile
    the transport as an implication and apply it later by modus ponens. *)
Definition coqRestrictedPADirectAssumptionConclusionTransportChildContext
    : TemplateContext :=
  coqRestrictedPADirectAssumptionWitnessFormulaTruthTemplate ::
    coqRestrictedPADirectAssumptionCaseContext.

Definition coqRestrictedPADirectAssumptionCaseChildRoot
    : TemplateRawProof :=
  trpAss coqRestrictedPADirectAssumptionConclusionTransportChildContext
    coqRestrictedPADirectAssumptionCaseTemplate.

Definition coqRestrictedPADirectAssumptionConclusionSuffixChildRoot
    : TemplateRawProof :=
  trpAndE2 coqRestrictedPADirectAssumptionConclusionTransportChildContext
    coqRestrictedPADirectAssumptionCodeEqualityTemplate
    coqRestrictedPADirectAssumptionConclusionSuffixTemplate
    coqRestrictedPADirectAssumptionCaseChildRoot.

Definition coqRestrictedPADirectAssumptionConclusionEqualityChildRoot
    : TemplateRawProof :=
  trpAndE1 coqRestrictedPADirectAssumptionConclusionTransportChildContext
    coqRestrictedPADirectAssumptionConclusionEqualityTemplate
    coqRestrictedPADirectAssumptionMembershipSuffixTemplate
    coqRestrictedPADirectAssumptionConclusionSuffixChildRoot.

Definition coqRestrictedPADirectAssumptionConclusionSymmetryChildRoot
    : TemplateRawProof :=
  coqRestrictedPADirectEqSymmetryRoot
    coqRestrictedPADirectAssumptionConclusionTransportChildContext
    coqRestrictedPADirectAssumptionOuterConclusionTerm
    coqRestrictedPADirectAssumptionWitnessFormulaTerm
    coqRestrictedPADirectAssumptionConclusionEqualityChildRoot.

Definition coqRestrictedPADirectAssumptionWitnessFormulaTruthChildRoot
    : TemplateRawProof :=
  trpAss coqRestrictedPADirectAssumptionConclusionTransportChildContext
    coqRestrictedPADirectAssumptionWitnessFormulaTruthTemplate.

Definition coqRestrictedPADirectAssumptionOuterConclusionTruthChildRoot
    : TemplateRawProof :=
  trpEqElim coqRestrictedPADirectAssumptionConclusionTransportChildContext
    coqRestrictedPADirectAssumptionWitnessFormulaTerm
    coqRestrictedPADirectAssumptionOuterConclusionTerm
    coqRestrictedPADirectAssumptionConclusionTruthMotive
    coqRestrictedPADirectAssumptionConclusionSymmetryChildRoot
    coqRestrictedPADirectAssumptionWitnessFormulaTruthChildRoot.

Definition coqRestrictedPADirectAssumptionConclusionTransportRoot
    : TemplateRawProof :=
  trpImpI coqRestrictedPADirectAssumptionCaseContext
    coqRestrictedPADirectAssumptionWitnessFormulaTruthTemplate
    coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate
    coqRestrictedPADirectAssumptionOuterConclusionTruthChildRoot.

(** ------------------------------------------------------------------
    Declarative validation of every finite plumbing root. *)

Lemma coqRestrictedPADirectAssumption_outer_context_truth_in :
  In coqRestrictedPADirectAssumptionOuterContextTruthTemplate
    coqRestrictedPADirectAssumptionCaseContext.
Proof.
  right.
  unfold coqRestrictedPADirectAssumptionDeepContext.
  apply raw_coqTemplateNestedExContext_inherited.
  unfold coqRestrictedPADirectAssumptionEndpointTail. cbn. auto.
Qed.

Lemma coqRestrictedPADirectAssumptionEndpointBodyRoot_valid :
  TemplateRawDerives coqRestrictedPADirectAssumptionCaseContext
    rawCoqRestrictedPADirectEndpointWitnessBodyTemplate
    coqRestrictedPADirectAssumptionEndpointBodyRoot.
Proof.
  apply templateRawDerives_assumption.
  unfold coqRestrictedPADirectAssumptionCaseContext.
  right.
  unfold coqRestrictedPADirectAssumptionDeepContext.
  rewrite raw_coqRestrictedPADirectEndpointDeepContext_shape.
  left. reflexivity.
Qed.

Lemma coqRestrictedPADirectAssumptionContextEqualityRoot_valid :
  TemplateRawDerives coqRestrictedPADirectAssumptionCaseContext
    coqRestrictedPADirectAssumptionContextEqualityTemplate
    coqRestrictedPADirectAssumptionContextEqualityRoot.
Proof.
  unfold coqRestrictedPADirectAssumptionContextEqualityRoot.
  apply coqRestrictedPADirect_templateRawDerives_andE1.
  rewrite <- coqRestrictedPADirectAssumption_endpoint_equality_shape.
  exact coqRestrictedPADirectAssumptionEndpointBodyRoot_valid.
Qed.

Lemma coqRestrictedPADirectAssumptionCaseRoot_valid :
  TemplateRawDerives coqRestrictedPADirectAssumptionCaseContext
    coqRestrictedPADirectAssumptionCaseTemplate
    coqRestrictedPADirectAssumptionCaseRoot.
Proof. apply templateRawDerives_assumption. left. reflexivity. Qed.

Lemma coqRestrictedPADirectAssumptionConclusionSuffixRoot_valid :
  TemplateRawDerives coqRestrictedPADirectAssumptionCaseContext
    coqRestrictedPADirectAssumptionConclusionSuffixTemplate
    coqRestrictedPADirectAssumptionConclusionSuffixRoot.
Proof.
  unfold coqRestrictedPADirectAssumptionConclusionSuffixRoot.
  apply coqRestrictedPADirect_templateRawDerives_andE2.
  rewrite <- coqRestrictedPADirectAssumption_case_shape.
  exact coqRestrictedPADirectAssumptionCaseRoot_valid.
Qed.

Lemma coqRestrictedPADirectAssumptionConclusionEqualityRoot_valid :
  TemplateRawDerives coqRestrictedPADirectAssumptionCaseContext
    coqRestrictedPADirectAssumptionConclusionEqualityTemplate
    coqRestrictedPADirectAssumptionConclusionEqualityRoot.
Proof.
  unfold coqRestrictedPADirectAssumptionConclusionEqualityRoot.
  apply coqRestrictedPADirect_templateRawDerives_andE1.
  exact coqRestrictedPADirectAssumptionConclusionSuffixRoot_valid.
Qed.

Lemma coqRestrictedPADirectAssumptionMembershipSuffixRoot_valid :
  TemplateRawDerives coqRestrictedPADirectAssumptionCaseContext
    coqRestrictedPADirectAssumptionMembershipSuffixTemplate
    coqRestrictedPADirectAssumptionMembershipSuffixRoot.
Proof.
  unfold coqRestrictedPADirectAssumptionMembershipSuffixRoot.
  apply coqRestrictedPADirect_templateRawDerives_andE2.
  exact coqRestrictedPADirectAssumptionConclusionSuffixRoot_valid.
Qed.

Lemma coqRestrictedPADirectAssumptionMembershipRoot_valid :
  TemplateRawDerives coqRestrictedPADirectAssumptionCaseContext
    coqRestrictedPADirectAssumptionMembershipTemplate
    coqRestrictedPADirectAssumptionMembershipRoot.
Proof.
  unfold coqRestrictedPADirectAssumptionMembershipRoot.
  apply coqRestrictedPADirect_templateRawDerives_andE1.
  exact coqRestrictedPADirectAssumptionMembershipSuffixRoot_valid.
Qed.

Lemma coqRestrictedPADirectAssumptionOuterContextTruthRoot_valid :
  TemplateRawDerives coqRestrictedPADirectAssumptionCaseContext
    coqRestrictedPADirectAssumptionOuterContextTruthTemplate
    coqRestrictedPADirectAssumptionOuterContextTruthRoot.
Proof.
  apply templateRawDerives_assumption.
  exact coqRestrictedPADirectAssumption_outer_context_truth_in.
Qed.

Lemma coqRestrictedPADirectAssumptionContextSymmetryRoot_valid :
  TemplateRawDerives coqRestrictedPADirectAssumptionCaseContext
    (tfEq coqRestrictedPADirectAssumptionOuterContextTerm
      coqRestrictedPADirectAssumptionWitnessContextTerm)
    coqRestrictedPADirectAssumptionContextSymmetryRoot.
Proof.
  apply coqRestrictedPADirectEqSymmetryRoot_valid.
  exact coqRestrictedPADirectAssumptionContextEqualityRoot_valid.
Qed.

Lemma coqRestrictedPADirectAssumptionWitnessContextTruthRoot_valid :
  TemplateRawDerives coqRestrictedPADirectAssumptionCaseContext
    coqRestrictedPADirectAssumptionWitnessContextTruthTemplate
    coqRestrictedPADirectAssumptionWitnessContextTruthRoot.
Proof.
  unfold coqRestrictedPADirectAssumptionWitnessContextTruthRoot.
  rewrite <- coqRestrictedPADirectAssumption_context_motive_witness.
  apply coqRestrictedPADirect_templateRawDerives_eqElim.
  - exact coqRestrictedPADirectAssumptionContextSymmetryRoot_valid.
  - rewrite coqRestrictedPADirectAssumption_context_motive_outer.
    exact coqRestrictedPADirectAssumptionOuterContextTruthRoot_valid.
Qed.

Lemma coqRestrictedPADirectAssumptionCaseChildRoot_valid :
  TemplateRawDerives
    coqRestrictedPADirectAssumptionConclusionTransportChildContext
    coqRestrictedPADirectAssumptionCaseTemplate
    coqRestrictedPADirectAssumptionCaseChildRoot.
Proof.
  apply templateRawDerives_assumption.
  unfold coqRestrictedPADirectAssumptionConclusionTransportChildContext.
  right.
  unfold coqRestrictedPADirectAssumptionCaseContext.
  left. reflexivity.
Qed.

Lemma coqRestrictedPADirectAssumptionConclusionSuffixChildRoot_valid :
  TemplateRawDerives
    coqRestrictedPADirectAssumptionConclusionTransportChildContext
    coqRestrictedPADirectAssumptionConclusionSuffixTemplate
    coqRestrictedPADirectAssumptionConclusionSuffixChildRoot.
Proof.
  unfold coqRestrictedPADirectAssumptionConclusionSuffixChildRoot.
  apply coqRestrictedPADirect_templateRawDerives_andE2.
  rewrite <- coqRestrictedPADirectAssumption_case_shape.
  exact coqRestrictedPADirectAssumptionCaseChildRoot_valid.
Qed.

Lemma coqRestrictedPADirectAssumptionConclusionEqualityChildRoot_valid :
  TemplateRawDerives
    coqRestrictedPADirectAssumptionConclusionTransportChildContext
    coqRestrictedPADirectAssumptionConclusionEqualityTemplate
    coqRestrictedPADirectAssumptionConclusionEqualityChildRoot.
Proof.
  unfold coqRestrictedPADirectAssumptionConclusionEqualityChildRoot.
  apply coqRestrictedPADirect_templateRawDerives_andE1.
  exact coqRestrictedPADirectAssumptionConclusionSuffixChildRoot_valid.
Qed.

Lemma coqRestrictedPADirectAssumptionConclusionSymmetryChildRoot_valid :
  TemplateRawDerives
    coqRestrictedPADirectAssumptionConclusionTransportChildContext
    (tfEq coqRestrictedPADirectAssumptionWitnessFormulaTerm
      coqRestrictedPADirectAssumptionOuterConclusionTerm)
    coqRestrictedPADirectAssumptionConclusionSymmetryChildRoot.
Proof.
  apply coqRestrictedPADirectEqSymmetryRoot_valid.
  exact coqRestrictedPADirectAssumptionConclusionEqualityChildRoot_valid.
Qed.

Lemma coqRestrictedPADirectAssumptionWitnessFormulaTruthChildRoot_valid :
  TemplateRawDerives
    coqRestrictedPADirectAssumptionConclusionTransportChildContext
    coqRestrictedPADirectAssumptionWitnessFormulaTruthTemplate
    coqRestrictedPADirectAssumptionWitnessFormulaTruthChildRoot.
Proof. apply templateRawDerives_assumption. left. reflexivity. Qed.

Lemma coqRestrictedPADirectAssumptionOuterConclusionTruthChildRoot_valid :
  TemplateRawDerives
    coqRestrictedPADirectAssumptionConclusionTransportChildContext
    coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate
    coqRestrictedPADirectAssumptionOuterConclusionTruthChildRoot.
Proof.
  unfold coqRestrictedPADirectAssumptionOuterConclusionTruthChildRoot.
  rewrite <- coqRestrictedPADirectAssumption_conclusion_motive_outer.
  apply coqRestrictedPADirect_templateRawDerives_eqElim.
  - exact coqRestrictedPADirectAssumptionConclusionSymmetryChildRoot_valid.
  - rewrite coqRestrictedPADirectAssumption_conclusion_motive_witness.
    exact
      coqRestrictedPADirectAssumptionWitnessFormulaTruthChildRoot_valid.
Qed.

Lemma coqRestrictedPADirectAssumptionConclusionTransportRoot_valid :
  TemplateRawDerives coqRestrictedPADirectAssumptionCaseContext
    (tfImp coqRestrictedPADirectAssumptionWitnessFormulaTruthTemplate
      coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate)
    coqRestrictedPADirectAssumptionConclusionTransportRoot.
Proof.
  unfold coqRestrictedPADirectAssumptionConclusionTransportRoot.
  apply coqRestrictedPADirect_templateRawDerives_impI.
  exact coqRestrictedPADirectAssumptionOuterConclusionTruthChildRoot_valid.
Qed.

(** ------------------------------------------------------------------
    The compiled assumption branch. *)

Theorem
    raw_codedPALocalProofOf_coqRestrictedPADirectAssumptionCase :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  let translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs in
  RawCoqRestrictedPADirectAssumptionMembershipTruthLawRoot
    M translation ->
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation
        coqRestrictedPADirectAssumptionDeepContext)
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          coqRestrictedPADirectAssumptionCaseTemplate)
        (rawTemplateFormula translation
          coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate))
      root.
Proof.
  intros M hPA inputs. cbn zeta.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  intros (lawRoot & hlaw).
  set (caseContextCode := rawTemplateContextCode translation
    coqRestrictedPADirectAssumptionCaseContext).

  pose proof (raw_templateProof_localProof M hPA translation
    coqRestrictedPADirectAssumptionWitnessContextTruthRoot
    (proj1 coqRestrictedPADirectAssumptionWitnessContextTruthRoot_valid))
    as hcontextTruth.
  pose proof (raw_templateProof_localProof M hPA translation
    coqRestrictedPADirectAssumptionMembershipRoot
    (proj1 coqRestrictedPADirectAssumptionMembershipRoot_valid))
    as hmembership.
  pose proof (raw_templateProof_localProof M hPA translation
    coqRestrictedPADirectAssumptionConclusionTransportRoot
    (proj1 coqRestrictedPADirectAssumptionConclusionTransportRoot_valid))
    as htransport.

  change (RawCodedPALocalProofOf M caseContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectAssumptionWitnessContextTruthTemplate)
    (rawTemplateProofCode translation
      coqRestrictedPADirectAssumptionWitnessContextTruthRoot))
    in hcontextTruth.
  change (RawCodedPALocalProofOf M caseContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectAssumptionMembershipTemplate)
    (rawTemplateProofCode translation
      coqRestrictedPADirectAssumptionMembershipRoot))
    in hmembership.
  change (RawCodedPALocalProofOf M caseContextCode
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionWitnessFormulaTruthTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate))
    (rawTemplateProofCode translation
      coqRestrictedPADirectAssumptionConclusionTransportRoot))
    in htransport.

  assert (hlawAfterContext : exists firstRoot : M,
    RawCodedPALocalProofOf M caseContextCode
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          coqRestrictedPADirectAssumptionMembershipTemplate)
        (rawTemplateFormula translation
          coqRestrictedPADirectAssumptionWitnessFormulaTruthTemplate))
      firstRoot).
  {
    exists (rawProofImpERoot M caseContextCode
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionWitnessContextTruthTemplate)
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          coqRestrictedPADirectAssumptionMembershipTemplate)
        (rawTemplateFormula translation
          coqRestrictedPADirectAssumptionWitnessFormulaTruthTemplate))
      lawRoot
      (rawTemplateProofCode translation
        coqRestrictedPADirectAssumptionWitnessContextTruthRoot)).
    exact (raw_codedPALocalProofOf_impE M hPA caseContextCode
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionWitnessContextTruthTemplate)
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          coqRestrictedPADirectAssumptionMembershipTemplate)
        (rawTemplateFormula translation
          coqRestrictedPADirectAssumptionWitnessFormulaTruthTemplate))
      lawRoot
      (rawTemplateProofCode translation
        coqRestrictedPADirectAssumptionWitnessContextTruthRoot)
      hlaw hcontextTruth).
  }
  destruct hlawAfterContext as [firstRoot hfirst].

  assert (hwitnessTruth : exists witnessTruthRoot : M,
    RawCodedPALocalProofOf M caseContextCode
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionWitnessFormulaTruthTemplate)
      witnessTruthRoot).
  {
    exists (rawProofImpERoot M caseContextCode
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionMembershipTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionWitnessFormulaTruthTemplate)
      firstRoot
      (rawTemplateProofCode translation
        coqRestrictedPADirectAssumptionMembershipRoot)).
    exact (raw_codedPALocalProofOf_impE M hPA caseContextCode
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionMembershipTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionWitnessFormulaTruthTemplate)
      firstRoot
      (rawTemplateProofCode translation
        coqRestrictedPADirectAssumptionMembershipRoot)
      hfirst hmembership).
  }
  destruct hwitnessTruth as [witnessTruthRoot hwitnessTruth].

  set (conclusionRoot := rawProofImpERoot M caseContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectAssumptionWitnessFormulaTruthTemplate)
    (rawTemplateFormula translation
      coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate)
    (rawTemplateProofCode translation
      coqRestrictedPADirectAssumptionConclusionTransportRoot)
    witnessTruthRoot).
  assert (hconclusion : RawCodedPALocalProofOf M caseContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate)
    conclusionRoot).
  {
    unfold conclusionRoot.
    exact (raw_codedPALocalProofOf_impE M hPA caseContextCode
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionWitnessFormulaTruthTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate)
      (rawTemplateProofCode translation
        coqRestrictedPADirectAssumptionConclusionTransportRoot)
      witnessTruthRoot htransport hwitnessTruth).
  }

  exists (rawProofImpIRoot M
    (rawTemplateContextCode translation
      coqRestrictedPADirectAssumptionDeepContext)
    (rawTemplateFormula translation
      coqRestrictedPADirectAssumptionCaseTemplate)
    (rawTemplateFormula translation
      coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate)
    conclusionRoot).
  apply (raw_codedPALocalProofOf_impI M hPA
    (rawTemplateContextCode translation
      coqRestrictedPADirectAssumptionDeepContext)
    (rawTemplateFormula translation
      coqRestrictedPADirectAssumptionCaseTemplate)
    (rawTemplateFormula translation
      coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate)
    conclusionRoot).
  change (RawCodedPALocalProofOf M caseContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate)
    conclusionRoot).
  exact hconclusion.
Qed.

(** The result inhabits the exact assumption slot of the deep endpoint
    dispatcher, with its conclusion specialized to the original opaque
    conclusion-truth template. *)
Corollary
    raw_coqRestrictedPADirectDeepEndpointAssumptionCaseRoot :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  let translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs in
  RawCoqRestrictedPADirectAssumptionMembershipTruthLawRoot
    M translation ->
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation
        (rawCoqRestrictedPADirectEndpointWitnessBodyTemplate ::
          rawCoqRestrictedPADirectEndpointDeepTail
            coqRestrictedPADirectAssumptionEndpointTail))
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          (rawCoqRestrictedPAProofRuleCaseTemplate rawCoqRuleAssumption
            (liftTerm 8 (tVar 4)) (tVar 7) (liftTerm 8 (tVar 2))
            (tVar 6) (tVar 5) (tVar 4) (tVar 3)
            (tVar 2) (tVar 1) (tVar 0)))
        (rawTemplateFormula translation
          (rawCoqTemplateRenameN 8
            coqRestrictedPADerivationSoundnessConclusionTruthTemplate)))
      root.
Proof.
  intros M hPA inputs. cbn zeta. intro hlaw.
  destruct
    (raw_codedPALocalProofOf_coqRestrictedPADirectAssumptionCase
      M hPA inputs hlaw) as [root hroot].
  exists root.
  unfold coqRestrictedPADirectAssumptionDeepContext in hroot.
  rewrite raw_coqRestrictedPADirectEndpointDeepContext_shape in hroot.
  exact hroot.
Qed.

(** ==================================================================
    Exact adapter for the public strong-step shell.

    The earlier theorem exposes the core [case -> conclusion] argument in a
    convenient semantically ready context.  The shell deliberately retains
    the source implication order instead: its constructor root must prove

      case -> admissible -> contextTruth -> conclusionTruth.

    The following parameterized projection roots let us enter those two
    implications first and then reuse the same equality plumbing in the
    literal resulting context, for an arbitrary caller tail. *)

Definition coqRestrictedPADirectAssumptionDeepAdmissibleTemplate
    : TemplateFormula :=
  rawCoqTemplateRenameN 8
    coqRestrictedPADerivationSoundnessAdmissibleTemplate.

Lemma coqRestrictedPADirectAssumption_strong_step_remaining_shape :
  rawCoqTemplateRenameN 8
    rawCoqRestrictedPADirectStrongStepRemainingTemplate =
  tfImp coqRestrictedPADirectAssumptionDeepAdmissibleTemplate
    (tfImp coqRestrictedPADirectAssumptionOuterContextTruthTemplate
      coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate).
Proof. reflexivity. Qed.

Definition coqRestrictedPADirectStrongStepAssumptionDeepEndpointContext
    (tail : TemplateContext) : TemplateContext :=
  rawCoqRestrictedPADirectEndpointWitnessBodyTemplate ::
    rawCoqRestrictedPADirectEndpointDeepTail
      (rawCoqRestrictedPADirectStrongStepEndpointTail tail).

Definition coqRestrictedPADirectStrongStepAssumptionCaseContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectAssumptionCaseTemplate ::
    coqRestrictedPADirectStrongStepAssumptionDeepEndpointContext tail.

Definition coqRestrictedPADirectStrongStepAssumptionAdmissibleContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectAssumptionDeepAdmissibleTemplate ::
    coqRestrictedPADirectStrongStepAssumptionCaseContext tail.

Definition coqRestrictedPADirectStrongStepAssumptionReadyContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectAssumptionOuterContextTruthTemplate ::
    coqRestrictedPADirectStrongStepAssumptionAdmissibleContext tail.

Arguments coqRestrictedPADirectStrongStepAssumptionDeepEndpointContext
  tail : clear implicits.
Arguments coqRestrictedPADirectStrongStepAssumptionCaseContext
  tail : clear implicits.
Arguments coqRestrictedPADirectStrongStepAssumptionAdmissibleContext
  tail : clear implicits.
Arguments coqRestrictedPADirectStrongStepAssumptionReadyContext
  tail : clear implicits.

(** The exact semantic residual in an arbitrary local context. *)
Definition RawCoqRestrictedPADirectAssumptionMembershipTruthLawRootAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (context : TemplateContext) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation context)
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionMembershipTruthLawTemplate)
      root.

Arguments RawCoqRestrictedPADirectAssumptionMembershipTruthLawRootAt
  M translation context : clear implicits.

Definition
    RawCoqRestrictedPADirectStrongStepAssumptionMembershipTruthLawRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop :=
  RawCoqRestrictedPADirectAssumptionMembershipTruthLawRootAt M
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    (coqRestrictedPADirectStrongStepAssumptionReadyContext tail).

Arguments
  RawCoqRestrictedPADirectStrongStepAssumptionMembershipTruthLawRoot
  M hPA inputs tail : clear implicits.

(** Parameterized versions of the finite projection roots. *)
Definition coqRestrictedPADirectAssumptionEndpointBodyRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAss context rawCoqRestrictedPADirectEndpointWitnessBodyTemplate.

Definition coqRestrictedPADirectAssumptionContextEqualityRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectAssumptionContextEqualityTemplate
    (rawCoqTemplateRuleDisjunction
      rawCoqRestrictedPADirectEndpointRuleCaseTemplates)
    (coqRestrictedPADirectAssumptionEndpointBodyRootAt context).

Definition coqRestrictedPADirectAssumptionCaseRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAss context coqRestrictedPADirectAssumptionCaseTemplate.

Definition coqRestrictedPADirectAssumptionConclusionSuffixRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE2 context
    coqRestrictedPADirectAssumptionCodeEqualityTemplate
    coqRestrictedPADirectAssumptionConclusionSuffixTemplate
    (coqRestrictedPADirectAssumptionCaseRootAt context).

Definition coqRestrictedPADirectAssumptionConclusionEqualityRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectAssumptionConclusionEqualityTemplate
    coqRestrictedPADirectAssumptionMembershipSuffixTemplate
    (coqRestrictedPADirectAssumptionConclusionSuffixRootAt context).

Definition coqRestrictedPADirectAssumptionMembershipSuffixRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE2 context
    coqRestrictedPADirectAssumptionConclusionEqualityTemplate
    coqRestrictedPADirectAssumptionMembershipSuffixTemplate
    (coqRestrictedPADirectAssumptionConclusionSuffixRootAt context).

Definition coqRestrictedPADirectAssumptionMembershipRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectAssumptionMembershipTemplate
    coqRestrictedPADirectAssumptionTerminalTruthTemplate
    (coqRestrictedPADirectAssumptionMembershipSuffixRootAt context).

Definition coqRestrictedPADirectAssumptionOuterContextTruthRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpAss context
    coqRestrictedPADirectAssumptionOuterContextTruthTemplate.

Definition coqRestrictedPADirectAssumptionContextSymmetryRootAt
    (context : TemplateContext) : TemplateRawProof :=
  coqRestrictedPADirectEqSymmetryRoot context
    coqRestrictedPADirectAssumptionWitnessContextTerm
    coqRestrictedPADirectAssumptionOuterContextTerm
    (coqRestrictedPADirectAssumptionContextEqualityRootAt context).

Definition coqRestrictedPADirectAssumptionWitnessContextTruthRootAt
    (context : TemplateContext) : TemplateRawProof :=
  trpEqElim context
    coqRestrictedPADirectAssumptionOuterContextTerm
    coqRestrictedPADirectAssumptionWitnessContextTerm
    coqRestrictedPADirectAssumptionContextTruthMotive
    (coqRestrictedPADirectAssumptionContextSymmetryRootAt context)
    (coqRestrictedPADirectAssumptionOuterContextTruthRootAt context).

(** The conclusion transport is compiled as an implication because its
    witness-truth premise is supplied only after the semantic law fires. *)
Definition coqRestrictedPADirectAssumptionConclusionTransportRootAt
    (context : TemplateContext) : TemplateRawProof :=
  let childContext :=
    coqRestrictedPADirectAssumptionWitnessFormulaTruthTemplate :: context in
  let equalityRoot :=
    coqRestrictedPADirectAssumptionConclusionEqualityRootAt childContext in
  let symmetryRoot :=
    coqRestrictedPADirectEqSymmetryRoot childContext
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      coqRestrictedPADirectAssumptionWitnessFormulaTerm equalityRoot in
  let witnessTruthRoot := trpAss childContext
    coqRestrictedPADirectAssumptionWitnessFormulaTruthTemplate in
  trpImpI context
    coqRestrictedPADirectAssumptionWitnessFormulaTruthTemplate
    coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate
    (trpEqElim childContext
      coqRestrictedPADirectAssumptionWitnessFormulaTerm
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      coqRestrictedPADirectAssumptionConclusionTruthMotive
      symmetryRoot witnessTruthRoot).

Lemma coqRestrictedPADirectAssumptionEndpointBodyRootAt_valid : forall
    context,
  In rawCoqRestrictedPADirectEndpointWitnessBodyTemplate context ->
  TemplateRawDerives context
    rawCoqRestrictedPADirectEndpointWitnessBodyTemplate
    (coqRestrictedPADirectAssumptionEndpointBodyRootAt context).
Proof.
  intros context hin. apply templateRawDerives_assumption. exact hin.
Qed.

Lemma coqRestrictedPADirectAssumptionContextEqualityRootAt_valid : forall
    context,
  In rawCoqRestrictedPADirectEndpointWitnessBodyTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectAssumptionContextEqualityTemplate
    (coqRestrictedPADirectAssumptionContextEqualityRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectAssumptionContextEqualityRootAt.
  apply coqRestrictedPADirect_templateRawDerives_andE1.
  rewrite <- coqRestrictedPADirectAssumption_endpoint_equality_shape.
  apply coqRestrictedPADirectAssumptionEndpointBodyRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectAssumptionCaseRootAt_valid : forall context,
  In coqRestrictedPADirectAssumptionCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectAssumptionCaseTemplate
    (coqRestrictedPADirectAssumptionCaseRootAt context).
Proof.
  intros context hin. apply templateRawDerives_assumption. exact hin.
Qed.

Lemma coqRestrictedPADirectAssumptionConclusionSuffixRootAt_valid : forall
    context,
  In coqRestrictedPADirectAssumptionCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectAssumptionConclusionSuffixTemplate
    (coqRestrictedPADirectAssumptionConclusionSuffixRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectAssumptionConclusionSuffixRootAt.
  apply coqRestrictedPADirect_templateRawDerives_andE2.
  rewrite <- coqRestrictedPADirectAssumption_case_shape.
  apply coqRestrictedPADirectAssumptionCaseRootAt_valid. exact hin.
Qed.

Lemma coqRestrictedPADirectAssumptionConclusionEqualityRootAt_valid : forall
    context,
  In coqRestrictedPADirectAssumptionCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectAssumptionConclusionEqualityTemplate
    (coqRestrictedPADirectAssumptionConclusionEqualityRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectAssumptionConclusionEqualityRootAt.
  apply coqRestrictedPADirect_templateRawDerives_andE1.
  apply coqRestrictedPADirectAssumptionConclusionSuffixRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectAssumptionMembershipSuffixRootAt_valid : forall
    context,
  In coqRestrictedPADirectAssumptionCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectAssumptionMembershipSuffixTemplate
    (coqRestrictedPADirectAssumptionMembershipSuffixRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectAssumptionMembershipSuffixRootAt.
  apply coqRestrictedPADirect_templateRawDerives_andE2.
  apply coqRestrictedPADirectAssumptionConclusionSuffixRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectAssumptionMembershipRootAt_valid : forall
    context,
  In coqRestrictedPADirectAssumptionCaseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectAssumptionMembershipTemplate
    (coqRestrictedPADirectAssumptionMembershipRootAt context).
Proof.
  intros context hin.
  unfold coqRestrictedPADirectAssumptionMembershipRootAt.
  apply coqRestrictedPADirect_templateRawDerives_andE1.
  apply coqRestrictedPADirectAssumptionMembershipSuffixRootAt_valid.
  exact hin.
Qed.

Lemma coqRestrictedPADirectAssumptionOuterContextTruthRootAt_valid : forall
    context,
  In coqRestrictedPADirectAssumptionOuterContextTruthTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectAssumptionOuterContextTruthTemplate
    (coqRestrictedPADirectAssumptionOuterContextTruthRootAt context).
Proof.
  intros context hin. apply templateRawDerives_assumption. exact hin.
Qed.

Lemma coqRestrictedPADirectAssumptionContextSymmetryRootAt_valid : forall
    context,
  In rawCoqRestrictedPADirectEndpointWitnessBodyTemplate context ->
  TemplateRawDerives context
    (tfEq coqRestrictedPADirectAssumptionOuterContextTerm
      coqRestrictedPADirectAssumptionWitnessContextTerm)
    (coqRestrictedPADirectAssumptionContextSymmetryRootAt context).
Proof.
  intros context hendpoint.
  unfold coqRestrictedPADirectAssumptionContextSymmetryRootAt.
  apply coqRestrictedPADirectEqSymmetryRoot_valid.
  apply coqRestrictedPADirectAssumptionContextEqualityRootAt_valid.
  exact hendpoint.
Qed.

Lemma coqRestrictedPADirectAssumptionWitnessContextTruthRootAt_valid : forall
    context,
  In rawCoqRestrictedPADirectEndpointWitnessBodyTemplate context ->
  In coqRestrictedPADirectAssumptionOuterContextTruthTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectAssumptionWitnessContextTruthTemplate
    (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt context).
Proof.
  intros context hendpoint htruth.
  unfold coqRestrictedPADirectAssumptionWitnessContextTruthRootAt.
  rewrite <- coqRestrictedPADirectAssumption_context_motive_witness.
  apply coqRestrictedPADirect_templateRawDerives_eqElim.
  - apply coqRestrictedPADirectAssumptionContextSymmetryRootAt_valid.
    exact hendpoint.
  - rewrite coqRestrictedPADirectAssumption_context_motive_outer.
    apply coqRestrictedPADirectAssumptionOuterContextTruthRootAt_valid.
    exact htruth.
Qed.

Lemma coqRestrictedPADirectAssumptionConclusionTransportRootAt_valid : forall
    context,
  In coqRestrictedPADirectAssumptionCaseTemplate context ->
  TemplateRawDerives context
    (tfImp coqRestrictedPADirectAssumptionWitnessFormulaTruthTemplate
      coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate)
    (coqRestrictedPADirectAssumptionConclusionTransportRootAt context).
Proof.
  intros context hcase.
  unfold coqRestrictedPADirectAssumptionConclusionTransportRootAt.
  cbn zeta.
  apply coqRestrictedPADirect_templateRawDerives_impI.
  rewrite <- coqRestrictedPADirectAssumption_conclusion_motive_outer.
  apply coqRestrictedPADirect_templateRawDerives_eqElim.
  - apply coqRestrictedPADirectEqSymmetryRoot_valid.
    apply coqRestrictedPADirectAssumptionConclusionEqualityRootAt_valid.
    right. exact hcase.
  - rewrite coqRestrictedPADirectAssumption_conclusion_motive_witness.
    apply templateRawDerives_assumption. left. reflexivity.
Qed.

(** The reusable semantic core in an arbitrary semantically ready context. *)
Theorem raw_codedPALocalProofOf_coqRestrictedPADirectAssumptionConclusionAt :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (translation : RawCodedTemplateTranslation M) context,
  In rawCoqRestrictedPADirectEndpointWitnessBodyTemplate context ->
  In coqRestrictedPADirectAssumptionCaseTemplate context ->
  In coqRestrictedPADirectAssumptionOuterContextTruthTemplate context ->
  RawCoqRestrictedPADirectAssumptionMembershipTruthLawRootAt
    M translation context ->
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation context)
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate)
      root.
Proof.
  intros M hPA translation context hendpoint hcase hcontextTruth
    (lawRoot & hlaw).
  unfold coqRestrictedPADirectAssumptionMembershipTruthLawTemplate in hlaw.
  repeat rewrite rawTemplateFormula_imp in hlaw.
  set (contextCode := rawTemplateContextCode translation context).
  change (RawCodedPALocalProofOf M contextCode
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionWitnessContextTruthTemplate)
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          coqRestrictedPADirectAssumptionMembershipTemplate)
        (rawTemplateFormula translation
          coqRestrictedPADirectAssumptionWitnessFormulaTruthTemplate)))
    lawRoot) in hlaw.

  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt context)
    (proj1
      (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt_valid
        context hendpoint hcontextTruth))) as hwitnessContextTruth.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectAssumptionMembershipRootAt context)
    (proj1 (coqRestrictedPADirectAssumptionMembershipRootAt_valid
      context hcase))) as hmembership.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectAssumptionConclusionTransportRootAt context)
    (proj1
      (coqRestrictedPADirectAssumptionConclusionTransportRootAt_valid
        context hcase))) as htransport.

  change (RawCodedPALocalProofOf M contextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectAssumptionWitnessContextTruthTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt context)))
    in hwitnessContextTruth.
  change (RawCodedPALocalProofOf M contextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectAssumptionMembershipTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectAssumptionMembershipRootAt context)))
    in hmembership.
  unfold coqRestrictedPADirectAssumptionConclusionTransportRootAt
    in htransport.
  cbn [templateRawContext templateRawConclusion] in htransport.
  rewrite rawTemplateFormula_imp in htransport.
  change (RawCodedPALocalProofOf M contextCode
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionWitnessFormulaTruthTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate))
    (rawTemplateProofCode translation
      (coqRestrictedPADirectAssumptionConclusionTransportRootAt context)))
    in htransport.

  set (lawAfterContextRoot := rawProofImpERoot M contextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectAssumptionWitnessContextTruthTemplate)
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionMembershipTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionWitnessFormulaTruthTemplate))
    lawRoot
    (rawTemplateProofCode translation
      (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt context))).
  assert (hlawAfterContext : RawCodedPALocalProofOf M contextCode
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionMembershipTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionWitnessFormulaTruthTemplate))
    lawAfterContextRoot).
  {
    unfold lawAfterContextRoot.
    exact (raw_codedPALocalProofOf_impE M hPA contextCode
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionWitnessContextTruthTemplate)
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          coqRestrictedPADirectAssumptionMembershipTemplate)
        (rawTemplateFormula translation
          coqRestrictedPADirectAssumptionWitnessFormulaTruthTemplate))
      lawRoot
      (rawTemplateProofCode translation
        (coqRestrictedPADirectAssumptionWitnessContextTruthRootAt context))
      hlaw hwitnessContextTruth).
  }

  set (witnessTruthRoot := rawProofImpERoot M contextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectAssumptionMembershipTemplate)
    (rawTemplateFormula translation
      coqRestrictedPADirectAssumptionWitnessFormulaTruthTemplate)
    lawAfterContextRoot
    (rawTemplateProofCode translation
      (coqRestrictedPADirectAssumptionMembershipRootAt context))).
  assert (hwitnessTruth : RawCodedPALocalProofOf M contextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectAssumptionWitnessFormulaTruthTemplate)
    witnessTruthRoot).
  {
    unfold witnessTruthRoot.
    exact (raw_codedPALocalProofOf_impE M hPA contextCode
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionMembershipTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionWitnessFormulaTruthTemplate)
      lawAfterContextRoot
      (rawTemplateProofCode translation
        (coqRestrictedPADirectAssumptionMembershipRootAt context))
      hlawAfterContext hmembership).
  }

  exists (rawProofImpERoot M contextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectAssumptionWitnessFormulaTruthTemplate)
    (rawTemplateFormula translation
      coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectAssumptionConclusionTransportRootAt context))
    witnessTruthRoot).
  exact (raw_codedPALocalProofOf_impE M hPA contextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectAssumptionWitnessFormulaTruthTemplate)
    (rawTemplateFormula translation
      coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectAssumptionConclusionTransportRootAt context))
    witnessTruthRoot htransport hwitnessTruth).
Qed.

(** Exact assumption constructor slot from
    [raw_coqRestrictedPADirectStrongStepRuleCaseImplicationRoots_view]. *)
Theorem
    raw_coqRestrictedPADirectStrongStepAssumptionCaseImplicationRoot :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectStrongStepAssumptionMembershipTruthLawRoot
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
          (rawCoqRestrictedPAProofRuleCaseTemplate rawCoqRuleAssumption
            (liftTerm 8 (tVar 4)) (tVar 7) (liftTerm 8 (tVar 2))
            (tVar 6) (tVar 5) (tVar 4) (tVar 3)
            (tVar 2) (tVar 1) (tVar 0)))
        (rawDirectTemplateFormula inputs
          (rawCoqTemplateRenameN 8
            rawCoqRestrictedPADirectStrongStepRemainingTemplate)))
      root.
Proof.
  intros M hPA inputs tail hlaw.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  set (baseContext :=
    coqRestrictedPADirectStrongStepAssumptionDeepEndpointContext tail).
  set (caseContext :=
    coqRestrictedPADirectStrongStepAssumptionCaseContext tail).
  set (admissibleContext :=
    coqRestrictedPADirectStrongStepAssumptionAdmissibleContext tail).
  set (readyContext :=
    coqRestrictedPADirectStrongStepAssumptionReadyContext tail).

  assert (hendpoint :
    In rawCoqRestrictedPADirectEndpointWitnessBodyTemplate readyContext).
  {
    unfold readyContext,
      coqRestrictedPADirectStrongStepAssumptionReadyContext,
      coqRestrictedPADirectStrongStepAssumptionAdmissibleContext,
      coqRestrictedPADirectStrongStepAssumptionCaseContext,
      coqRestrictedPADirectStrongStepAssumptionDeepEndpointContext.
    do 3 right. left. reflexivity.
  }
  assert (hcase :
    In coqRestrictedPADirectAssumptionCaseTemplate readyContext).
  {
    unfold readyContext,
      coqRestrictedPADirectStrongStepAssumptionReadyContext,
      coqRestrictedPADirectStrongStepAssumptionAdmissibleContext,
      coqRestrictedPADirectStrongStepAssumptionCaseContext.
    right. right. left. reflexivity.
  }
  assert (hcontextTruth :
    In coqRestrictedPADirectAssumptionOuterContextTruthTemplate readyContext).
  {
    unfold readyContext,
      coqRestrictedPADirectStrongStepAssumptionReadyContext.
    left. reflexivity.
  }
  destruct
    (raw_codedPALocalProofOf_coqRestrictedPADirectAssumptionConclusionAt
      M hPA translation readyContext
      hendpoint hcase hcontextTruth hlaw) as
    [conclusionRoot hconclusion].

  set (readyContextCode := rawTemplateContextCode translation readyContext).
  set (admissibleContextCode :=
    rawTemplateContextCode translation admissibleContext).
  set (caseContextCode := rawTemplateContextCode translation caseContext).
  set (baseContextCode := rawTemplateContextCode translation baseContext).

  set (contextImpRoot := rawProofImpIRoot M admissibleContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectAssumptionOuterContextTruthTemplate)
    (rawTemplateFormula translation
      coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate)
    conclusionRoot).
  assert (hcontextImp : RawCodedPALocalProofOf M admissibleContextCode
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionOuterContextTruthTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate))
    contextImpRoot).
  {
    unfold contextImpRoot.
    apply (raw_codedPALocalProofOf_impI M hPA admissibleContextCode
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionOuterContextTruthTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate)
      conclusionRoot).
    change (RawCodedPALocalProofOf M readyContextCode
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate)
      conclusionRoot).
    exact hconclusion.
  }

  set (admissibleImpRoot := rawProofImpIRoot M caseContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectAssumptionDeepAdmissibleTemplate)
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionOuterContextTruthTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate))
    contextImpRoot).
  assert (hadmissibleImp : RawCodedPALocalProofOf M caseContextCode
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionDeepAdmissibleTemplate)
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          coqRestrictedPADirectAssumptionOuterContextTruthTemplate)
        (rawTemplateFormula translation
          coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate)))
    admissibleImpRoot).
  {
    unfold admissibleImpRoot.
    apply (raw_codedPALocalProofOf_impI M hPA caseContextCode
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionDeepAdmissibleTemplate)
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          coqRestrictedPADirectAssumptionOuterContextTruthTemplate)
        (rawTemplateFormula translation
          coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate))
      contextImpRoot).
    change (RawCodedPALocalProofOf M admissibleContextCode
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          coqRestrictedPADirectAssumptionOuterContextTruthTemplate)
        (rawTemplateFormula translation
          coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate))
      contextImpRoot).
    exact hcontextImp.
  }

  set (caseImpRoot := rawProofImpIRoot M baseContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectAssumptionCaseTemplate)
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionDeepAdmissibleTemplate)
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          coqRestrictedPADirectAssumptionOuterContextTruthTemplate)
        (rawTemplateFormula translation
          coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate)))
    admissibleImpRoot).
  exists caseImpRoot.
  rewrite coqRestrictedPADirectAssumption_strong_step_remaining_shape.
  change (RawCodedPALocalProofOf M baseContextCode
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionCaseTemplate)
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          coqRestrictedPADirectAssumptionDeepAdmissibleTemplate)
        (rawFormulaImpCode M
          (rawTemplateFormula translation
            coqRestrictedPADirectAssumptionOuterContextTruthTemplate)
          (rawTemplateFormula translation
            coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate))))
    caseImpRoot).
  unfold caseImpRoot.
  apply (raw_codedPALocalProofOf_impI M hPA baseContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectAssumptionCaseTemplate)
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionDeepAdmissibleTemplate)
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          coqRestrictedPADirectAssumptionOuterContextTruthTemplate)
        (rawTemplateFormula translation
          coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate)))
    admissibleImpRoot).
  change (RawCodedPALocalProofOf M caseContextCode
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionDeepAdmissibleTemplate)
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          coqRestrictedPADirectAssumptionOuterContextTruthTemplate)
        (rawTemplateFormula translation
          coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate)))
    admissibleImpRoot).
  exact hadmissibleImp.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAssumptionCase.
