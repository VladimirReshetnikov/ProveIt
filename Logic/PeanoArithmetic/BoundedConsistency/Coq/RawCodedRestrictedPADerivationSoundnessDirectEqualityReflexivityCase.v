(**
  The genuine equality-reflexivity constructor case for the direct
  derivation-soundness strong step.

  The endpoint dispatcher opens eight witnesses before it selects a proof
  rule.  In the equality-reflexivity branch the only semantically relevant
  field is

      formulaEqCode(outerConclusion, witnessTerm, witnessTerm).

  This file projects that field from the literal right-associated branch
  conjunction and compiles all three implications still required by the
  strong-step suffix:

      branch -> admissible -> contextTruth -> conclusionTruth.

  The direct structural input record deliberately says only that the two
  opaque truth selectors commute with represented shift and substitution.
  It does not impose a Tarski law.  An arbitrary selector satisfying those
  structural equations could return bottom at every input, so reflexive
  atomic truth is not derivable from that record alone.  The sole residual
  below is therefore the sharp local law

      formulaEqCode(c,t,t) -> conclusionTruth(c).

  Its conclusion formula mentions neither the rule branch, the endpoint
  disjunction, the admissibility/context-truth assumptions, nor a conclusion
  proof.  Its ambient context is nevertheless the exact semantic child
  context and therefore retains those already-introduced assumptions.  A
  later native dynamic-truth adapter can discharge precisely this law.
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
  RawCodedRestrictedPADerivationSoundnessDirectStrongStepShell.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityReflexivityCase.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedProofConstructors.
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

(** ------------------------------------------------------------------
    The literal reflexivity branch at the eight-witness depth. *)

Definition coqRestrictedPADirectEqualityReflexivityCodeEqualityTemplate
    : TemplateFormula :=
  embedPAFormula
    (pEq (liftTerm 8 (tVar 4))
      (proofEqReflCodeTerm (tVar 7) (tVar 3))).

Definition coqRestrictedPADirectEqualityReflexivityFormulaCodeTemplate
    : TemplateFormula :=
  embedPAFormula
    (formulaEqCodeTermAt
      (liftTerm 8 (tVar 2)) (tVar 3) (tVar 3)).

Definition coqRestrictedPADirectEqualityReflexivityTerminalTruthTemplate
    : TemplateFormula :=
  embedPAFormula (pEq tZero tZero).

Definition coqRestrictedPADirectEqualityReflexivityFormulaSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectEqualityReflexivityFormulaCodeTemplate
    coqRestrictedPADirectEqualityReflexivityTerminalTruthTemplate.

Definition coqRestrictedPADirectEqualityReflexivityCaseTemplate
    : TemplateFormula :=
  rawCoqRestrictedPAProofRuleCaseTemplate rawCoqRuleEqualityReflexivity
    (liftTerm 8 (tVar 4)) (tVar 7) (liftTerm 8 (tVar 2))
    (tVar 6) (tVar 5) (tVar 4) (tVar 3)
    (tVar 2) (tVar 1) (tVar 0).

Lemma coqRestrictedPADirectEqualityReflexivity_case_shape :
  coqRestrictedPADirectEqualityReflexivityCaseTemplate =
  tfAnd coqRestrictedPADirectEqualityReflexivityCodeEqualityTemplate
    coqRestrictedPADirectEqualityReflexivityFormulaSuffixTemplate.
Proof. reflexivity. Qed.

(** ------------------------------------------------------------------
    Exact contexts and the literal renamed strong-step suffix.

    Implication introduction changes only the proof context; unlike an
    eigenvariable rule it does not rename any term variables.  Thus the
    three formulas below remain at the eight-existential depth throughout
    all three introductions. *)

Definition coqRestrictedPADirectEqualityReflexivityAdmissibleTemplate
    : TemplateFormula :=
  rawCoqTemplateRenameN 8
    coqRestrictedPADerivationSoundnessAdmissibleTemplate.

Definition coqRestrictedPADirectEqualityReflexivityContextTruthTemplate
    : TemplateFormula :=
  rawCoqTemplateRenameN 8
    coqRestrictedPADerivationSoundnessContextTruthTemplate.

Definition coqRestrictedPADirectEqualityReflexivityConclusionTruthTemplate
    : TemplateFormula :=
  rawCoqTemplateRenameN 8
    coqRestrictedPADerivationSoundnessConclusionTruthTemplate.

(** Keep the eight-fold renaming opaque in its formula arguments.  Asking
    [reflexivity] to normalize the concrete soundness suffix would duplicate
    its large embedded PA leaves at every pass; this structural lemma proves
    the same homomorphism without expanding either side. *)
Lemma rawCoqTemplateRenameN_imp : forall count left right,
  rawCoqTemplateRenameN count (tfImp left right) =
  tfImp (rawCoqTemplateRenameN count left)
    (rawCoqTemplateRenameN count right).
Proof.
  induction count as [|remaining ih]; intros left right.
  - reflexivity.
  - cbn [rawCoqTemplateRenameN templateFormulaRename].
    apply ih.
Qed.

Lemma coqRestrictedPADirectEqualityReflexivity_remaining_shape :
  rawCoqTemplateRenameN 8
    rawCoqRestrictedPADirectStrongStepRemainingTemplate =
  tfImp coqRestrictedPADirectEqualityReflexivityAdmissibleTemplate
    (tfImp coqRestrictedPADirectEqualityReflexivityContextTruthTemplate
      coqRestrictedPADirectEqualityReflexivityConclusionTruthTemplate).
Proof.
  unfold rawCoqRestrictedPADirectStrongStepRemainingTemplate,
    coqRestrictedPADirectEqualityReflexivityAdmissibleTemplate,
    coqRestrictedPADirectEqualityReflexivityContextTruthTemplate,
    coqRestrictedPADirectEqualityReflexivityConclusionTruthTemplate.
  transitivity
    (tfImp
      (rawCoqTemplateRenameN 8
        coqRestrictedPADerivationSoundnessAdmissibleTemplate)
      (rawCoqTemplateRenameN 8
        (tfImp coqRestrictedPADerivationSoundnessContextTruthTemplate
          coqRestrictedPADerivationSoundnessConclusionTruthTemplate))).
  - apply rawCoqTemplateRenameN_imp.
  - f_equal.
Qed.

Definition coqRestrictedPADirectEqualityReflexivityDeepContext
    (tail : TemplateContext) : TemplateContext :=
  rawCoqRestrictedPADirectEndpointDeepContext
    (rawCoqRestrictedPADirectStrongStepEndpointTail tail).

Definition coqRestrictedPADirectEqualityReflexivityCaseContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectEqualityReflexivityCaseTemplate ::
    coqRestrictedPADirectEqualityReflexivityDeepContext tail.

Definition coqRestrictedPADirectEqualityReflexivityAdmissibleContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectEqualityReflexivityAdmissibleTemplate ::
    coqRestrictedPADirectEqualityReflexivityCaseContext tail.

Definition coqRestrictedPADirectEqualityReflexivitySemanticContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectEqualityReflexivityContextTruthTemplate ::
    coqRestrictedPADirectEqualityReflexivityAdmissibleContext tail.

Arguments coqRestrictedPADirectEqualityReflexivityDeepContext
  tail : clear implicits.
Arguments coqRestrictedPADirectEqualityReflexivityCaseContext
  tail : clear implicits.
Arguments coqRestrictedPADirectEqualityReflexivityAdmissibleContext
  tail : clear implicits.
Arguments coqRestrictedPADirectEqualityReflexivitySemanticContext
  tail : clear implicits.

Lemma coqRestrictedPADirectEqualityReflexivity_deep_context_shape :
  forall tail,
  coqRestrictedPADirectEqualityReflexivityDeepContext tail =
  rawCoqRestrictedPADirectEndpointWitnessBodyTemplate ::
    rawCoqRestrictedPADirectEndpointDeepTail
      (rawCoqRestrictedPADirectStrongStepEndpointTail tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectEqualityReflexivityDeepContext.
  apply raw_coqRestrictedPADirectEndpointDeepContext_shape.
Qed.

(** The only nonstructural input.  It is placed in the exact context in
    which both implications of the renamed suffix have been introduced.
    The antecedent is just the atomic code-constructor field projected from
    the branch.  The branch remains available in the ambient context, as it
    must at this point in the dispatcher, but it is not repackaged as an
    antecedent of the residual law and no branch-result root is assumed. *)
Definition
    RawCoqRestrictedPADirectEqualityReflexivityAtomicTruthLawRoot
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (tail : TemplateContext) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation
        (coqRestrictedPADirectEqualityReflexivitySemanticContext tail))
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          coqRestrictedPADirectEqualityReflexivityFormulaCodeTemplate)
        (rawTemplateFormula translation
          coqRestrictedPADirectEqualityReflexivityConclusionTruthTemplate))
      root.

Arguments RawCoqRestrictedPADirectEqualityReflexivityAtomicTruthLawRoot
  M translation tail : clear implicits.

(** ------------------------------------------------------------------
    A finite projection proof for the formula-code field. *)

Definition coqRestrictedPADirectEqualityReflexivityCaseAssumptionRoot
    (tail : TemplateContext) : TemplateRawProof :=
  trpAss
    (coqRestrictedPADirectEqualityReflexivitySemanticContext tail)
    coqRestrictedPADirectEqualityReflexivityCaseTemplate.

Definition coqRestrictedPADirectEqualityReflexivityFormulaSuffixRoot
    (tail : TemplateContext) : TemplateRawProof :=
  trpAndE2
    (coqRestrictedPADirectEqualityReflexivitySemanticContext tail)
    coqRestrictedPADirectEqualityReflexivityCodeEqualityTemplate
    coqRestrictedPADirectEqualityReflexivityFormulaSuffixTemplate
    (coqRestrictedPADirectEqualityReflexivityCaseAssumptionRoot tail).

Definition coqRestrictedPADirectEqualityReflexivityFormulaCodeRoot
    (tail : TemplateContext) : TemplateRawProof :=
  trpAndE1
    (coqRestrictedPADirectEqualityReflexivitySemanticContext tail)
    coqRestrictedPADirectEqualityReflexivityFormulaCodeTemplate
    coqRestrictedPADirectEqualityReflexivityTerminalTruthTemplate
    (coqRestrictedPADirectEqualityReflexivityFormulaSuffixRoot tail).

Arguments coqRestrictedPADirectEqualityReflexivityCaseAssumptionRoot
  tail : clear implicits.
Arguments coqRestrictedPADirectEqualityReflexivityFormulaSuffixRoot
  tail : clear implicits.
Arguments coqRestrictedPADirectEqualityReflexivityFormulaCodeRoot
  tail : clear implicits.

Lemma coqRestrictedPADirectEqualityReflexivityCaseAssumptionRoot_valid :
  forall tail,
  TemplateRawDerives
    (coqRestrictedPADirectEqualityReflexivitySemanticContext tail)
    coqRestrictedPADirectEqualityReflexivityCaseTemplate
    (coqRestrictedPADirectEqualityReflexivityCaseAssumptionRoot tail).
Proof.
  intro tail.
  apply templateRawDerives_assumption.
  unfold coqRestrictedPADirectEqualityReflexivitySemanticContext,
    coqRestrictedPADirectEqualityReflexivityAdmissibleContext,
    coqRestrictedPADirectEqualityReflexivityCaseContext.
  right. right. left. reflexivity.
Qed.

Lemma coqRestrictedPADirectEqualityReflexivityFormulaSuffixRoot_valid :
  forall tail,
  TemplateRawDerives
    (coqRestrictedPADirectEqualityReflexivitySemanticContext tail)
    coqRestrictedPADirectEqualityReflexivityFormulaSuffixTemplate
    (coqRestrictedPADirectEqualityReflexivityFormulaSuffixRoot tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectEqualityReflexivityFormulaSuffixRoot.
  apply templateAndRightFrom_derives.
  rewrite <- coqRestrictedPADirectEqualityReflexivity_case_shape.
  exact
    (coqRestrictedPADirectEqualityReflexivityCaseAssumptionRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectEqualityReflexivityFormulaCodeRoot_valid :
  forall tail,
  TemplateRawDerives
    (coqRestrictedPADirectEqualityReflexivitySemanticContext tail)
    coqRestrictedPADirectEqualityReflexivityFormulaCodeTemplate
    (coqRestrictedPADirectEqualityReflexivityFormulaCodeRoot tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectEqualityReflexivityFormulaCodeRoot.
  apply templateAndLeftFrom_derives.
  exact
    (coqRestrictedPADirectEqualityReflexivityFormulaSuffixRoot_valid tail).
Qed.

(** ------------------------------------------------------------------
    Compile the exact dispatcher slot.

    The projection and modus ponens occur in [semanticContext].  Three
    literal Imp-I nodes then discharge context truth, admissibility, and the
    selected rule branch, in that order. *)

Theorem
    raw_codedPALocalProofOf_coqRestrictedPADirectEqualityReflexivityCase :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    tail,
  let translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs in
  RawCoqRestrictedPADirectEqualityReflexivityAtomicTruthLawRoot
    M translation tail ->
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation
        (coqRestrictedPADirectEqualityReflexivityDeepContext tail))
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          coqRestrictedPADirectEqualityReflexivityCaseTemplate)
        (rawTemplateFormula translation
          (rawCoqTemplateRenameN 8
            rawCoqRestrictedPADirectStrongStepRemainingTemplate)))
      root.
Proof.
  intros M hPA inputs tail. cbn zeta.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  intros (lawRoot & hlaw).

  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectEqualityReflexivityFormulaCodeRoot tail)
    (proj1
      (coqRestrictedPADirectEqualityReflexivityFormulaCodeRoot_valid
        tail))) as hformulaCode.
  change (RawCodedPALocalProofOf M
    (rawTemplateContextCode translation
      (coqRestrictedPADirectEqualityReflexivitySemanticContext tail))
    (rawTemplateFormula translation
      coqRestrictedPADirectEqualityReflexivityFormulaCodeTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectEqualityReflexivityFormulaCodeRoot tail)))
    in hformulaCode.

  set (semanticContextCode := rawTemplateContextCode translation
    (coqRestrictedPADirectEqualityReflexivitySemanticContext tail)).
  set (formulaCode := rawTemplateFormula translation
    coqRestrictedPADirectEqualityReflexivityFormulaCodeTemplate).
  set (conclusionTruth := rawTemplateFormula translation
    coqRestrictedPADirectEqualityReflexivityConclusionTruthTemplate).
  set (conclusionRoot := rawProofImpERoot M semanticContextCode
    formulaCode conclusionTruth lawRoot
    (rawTemplateProofCode translation
      (coqRestrictedPADirectEqualityReflexivityFormulaCodeRoot tail))).

  assert (hconclusion : RawCodedPALocalProofOf M semanticContextCode
      conclusionTruth conclusionRoot).
  {
    unfold conclusionRoot.
    apply (raw_codedPALocalProofOf_impE M hPA semanticContextCode
      formulaCode conclusionTruth lawRoot
      (rawTemplateProofCode translation
        (coqRestrictedPADirectEqualityReflexivityFormulaCodeRoot tail))).
    - exact hlaw.
    - unfold semanticContextCode, formulaCode.
      exact hformulaCode.
  }

  set (caseContextCode := rawTemplateContextCode translation
    (coqRestrictedPADirectEqualityReflexivityCaseContext tail)).
  set (admissibleContextCode := rawTemplateContextCode translation
    (coqRestrictedPADirectEqualityReflexivityAdmissibleContext tail)).
  set (deepContextCode := rawTemplateContextCode translation
    (coqRestrictedPADirectEqualityReflexivityDeepContext tail)).
  set (caseFormula := rawTemplateFormula translation
    coqRestrictedPADirectEqualityReflexivityCaseTemplate).
  set (admissible := rawTemplateFormula translation
    coqRestrictedPADirectEqualityReflexivityAdmissibleTemplate).
  set (contextTruth := rawTemplateFormula translation
    coqRestrictedPADirectEqualityReflexivityContextTruthTemplate).

  set (contextTruthImpRoot := rawProofImpIRoot M admissibleContextCode
    contextTruth conclusionTruth conclusionRoot).
  assert (hcontextTruthImp : RawCodedPALocalProofOf M
      admissibleContextCode
      (rawFormulaImpCode M contextTruth conclusionTruth)
      contextTruthImpRoot).
  {
    unfold contextTruthImpRoot.
    apply (raw_codedPALocalProofOf_impI M hPA admissibleContextCode
      contextTruth conclusionTruth conclusionRoot).
    change (RawCodedPALocalProofOf M semanticContextCode
      conclusionTruth conclusionRoot).
    exact hconclusion.
  }

  set (admissibleImpRoot := rawProofImpIRoot M caseContextCode
    admissible (rawFormulaImpCode M contextTruth conclusionTruth)
    contextTruthImpRoot).
  assert (hadmissibleImp : RawCodedPALocalProofOf M caseContextCode
      (rawFormulaImpCode M admissible
        (rawFormulaImpCode M contextTruth conclusionTruth))
      admissibleImpRoot).
  {
    unfold admissibleImpRoot.
    apply (raw_codedPALocalProofOf_impI M hPA caseContextCode
      admissible (rawFormulaImpCode M contextTruth conclusionTruth)
      contextTruthImpRoot).
    change (RawCodedPALocalProofOf M admissibleContextCode
      (rawFormulaImpCode M contextTruth conclusionTruth)
      contextTruthImpRoot).
    exact hcontextTruthImp.
  }

  exists (rawProofImpIRoot M deepContextCode caseFormula
    (rawFormulaImpCode M admissible
      (rawFormulaImpCode M contextTruth conclusionTruth))
    admissibleImpRoot).
  rewrite coqRestrictedPADirectEqualityReflexivity_remaining_shape.
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectEqualityReflexivityAdmissibleTemplate
    (tfImp
      coqRestrictedPADirectEqualityReflexivityContextTruthTemplate
      coqRestrictedPADirectEqualityReflexivityConclusionTruthTemplate)).
  rewrite (rawTemplateFormula_imp translation
    coqRestrictedPADirectEqualityReflexivityContextTruthTemplate
    coqRestrictedPADirectEqualityReflexivityConclusionTruthTemplate).
  apply (raw_codedPALocalProofOf_impI M hPA deepContextCode
    caseFormula
    (rawFormulaImpCode M admissible
      (rawFormulaImpCode M contextTruth conclusionTruth))
    admissibleImpRoot).
  change (RawCodedPALocalProofOf M caseContextCode
    (rawFormulaImpCode M admissible
      (rawFormulaImpCode M contextTruth conclusionTruth))
    admissibleImpRoot).
  exact hadmissibleImp.
Qed.

(** The completely literal theorem type expected for the
    [rawCoqRuleEqualityReflexivity] component of
    [RawCoqRestrictedPADirectStrongStepRuleCaseImplicationRoots]. *)
Corollary
    raw_coqRestrictedPADirectStrongStepEqualityReflexivityCaseRoot :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    tail,
  let translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs in
  RawCoqRestrictedPADirectEqualityReflexivityAtomicTruthLawRoot
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
            rawCoqRuleEqualityReflexivity
            (liftTerm 8 (tVar 4)) (tVar 7) (liftTerm 8 (tVar 2))
            (tVar 6) (tVar 5) (tVar 4) (tVar 3)
            (tVar 2) (tVar 1) (tVar 0)))
        (rawTemplateFormula translation
          (rawCoqTemplateRenameN 8
            rawCoqRestrictedPADirectStrongStepRemainingTemplate)))
      root.
Proof.
  intros M hPA inputs tail. cbn zeta. intro hlaw.
  destruct
    (raw_codedPALocalProofOf_coqRestrictedPADirectEqualityReflexivityCase
      M hPA inputs tail hlaw) as [root hroot].
  exists root.
  rewrite <-
    coqRestrictedPADirectEqualityReflexivity_deep_context_shape.
  exact hroot.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityReflexivityCase.
