(**
  The exact seventeen-way proof-rule dispatch needed by the direct
  derivation-soundness strong step.

  This module deliberately stops at the constructor-local truth laws.  It
  does not turn semantic truth into a PA proof and it does not assume the
  desired strong-step root.  Instead, a caller supplies one open local PA
  proof of [case -> conclusion] for each of the seventeen constructors.  The
  checked dispatcher projects the literal rule disjunction from the endpoint
  witness body and combines those roots by ordinary Or elimination.  The
  terminal bottom branch of [proofFormulaDisjunction] is discharged here.

  Keeping the cases in a named finite type makes the residual frontier
  auditable: there is no anonymous list slot in which a proof rule can be
  silently omitted or duplicated.
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
  RawCodedProofRules
  RawCodedFixedLevelTruthTotality
  RawCodedProofAssumptionLeaf
  RawCodedProofAndEConstructors
  RawCodedProofImpIConstructor
  RawCodedProofUnaryConstructors
  RawCodedProofExEConstructor
  RawCodedProofAtomicAdequacyStandard
  RawCodedDynamicTruthPairedSuccessorAdequacy
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofConjunction
  RawCodedPALocalProofPropositionalRules
  RawCodedPALocalProofFiniteDisjunction
  RawCodedPALocalProofFiniteDisjunctionDerivedCases
  RawCodedTemplateSyntax
  RawCodedTemplatePAEmbedding
  RawCodedTemplateProofCompiler
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedRestrictedPAConsistencyFromUniversalSoundness.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier.

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
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedProofAssumptionLeaf.
Import PABoundedRawCodedProofAndEConstructors.
Import PABoundedRawCodedProofImpIConstructor.
Import PABoundedRawCodedProofUnaryConstructors.
Import PABoundedRawCodedProofExEConstructor.
Import PABoundedRawCodedProofAtomicAdequacyStandard.
Import PABoundedRawCodedDynamicTruthPairedSuccessorAdequacy.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofConjunction.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedPALocalProofFiniteDisjunction.
Import PABoundedRawCodedPALocalProofFiniteDisjunctionDerivedCases.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.

(** One constructor for every disjunct in [proofRuleValidCasesTermAt], in
    precisely the source order (and therefore in tag order zero through
    sixteen). *)
Inductive RawCoqRestrictedPAProofRuleCase : Type :=
| rawCoqRuleAssumption
| rawCoqRuleImpIntroduction
| rawCoqRuleImpElimination
| rawCoqRuleBottomElimination
| rawCoqRuleExcludedMiddle
| rawCoqRuleAndIntroduction
| rawCoqRuleAndEliminationLeft
| rawCoqRuleAndEliminationRight
| rawCoqRuleOrIntroductionLeft
| rawCoqRuleOrIntroductionRight
| rawCoqRuleOrElimination
| rawCoqRuleAllIntroduction
| rawCoqRuleAllElimination
| rawCoqRuleExIntroduction
| rawCoqRuleExElimination
| rawCoqRuleEqualityReflexivity
| rawCoqRuleEqualityElimination.

Definition rawCoqRestrictedPAProofRuleCases
    : list RawCoqRestrictedPAProofRuleCase :=
  [rawCoqRuleAssumption;
   rawCoqRuleImpIntroduction;
   rawCoqRuleImpElimination;
   rawCoqRuleBottomElimination;
   rawCoqRuleExcludedMiddle;
   rawCoqRuleAndIntroduction;
   rawCoqRuleAndEliminationLeft;
   rawCoqRuleAndEliminationRight;
   rawCoqRuleOrIntroductionLeft;
   rawCoqRuleOrIntroductionRight;
   rawCoqRuleOrElimination;
   rawCoqRuleAllIntroduction;
   rawCoqRuleAllElimination;
   rawCoqRuleExIntroduction;
   rawCoqRuleExElimination;
   rawCoqRuleEqualityReflexivity;
   rawCoqRuleEqualityElimination].

(** The branch bodies are copied literally from [proofRuleValidCasesTermAt].
    The arguments retain that definition's order. *)
Definition rawCoqRestrictedPAProofRuleCaseFormula
    (selected : RawCoqRestrictedPAProofRuleCase)
    (code context conclusion a b c t child1 child2 child3 : term)
    : formula :=
  match selected with
  | rawCoqRuleAssumption =>
      proofRuleConjunction
        [pEq code (proofAssCodeTerm context a);
         pEq conclusion a;
         contextListMemberTermAt context a]
  | rawCoqRuleImpIntroduction =>
      proofRuleConjunction
        [pEq code (proofImpICodeTerm context a b child1);
         formulaImpCodeTermAt conclusion a b;
         proofEndpointTermAt child1 (nodeTerm a context) b]
  | rawCoqRuleImpElimination =>
      proofRuleConjunction
        [pEq code (proofImpECodeTerm context a b child1 child2);
         pEq conclusion b;
         formulaImpCodeTermAt c a b;
         proofEndpointTermAt child1 context c;
         proofEndpointTermAt child2 context a]
  | rawCoqRuleBottomElimination =>
      proofRuleConjunction
        [pEq code (proofBotECodeTerm context a child1);
         pEq conclusion a;
         formulaBotCodeTermAt b;
         proofEndpointTermAt child1 context b]
  | rawCoqRuleExcludedMiddle =>
      proofRuleConjunction
        [pEq code (proofLemCodeTerm context a);
         formulaBotCodeTermAt c;
         formulaImpCodeTermAt b a c;
         formulaOrCodeTermAt conclusion a b]
  | rawCoqRuleAndIntroduction =>
      proofRuleConjunction
        [pEq code (proofAndICodeTerm context a b child1 child2);
         formulaAndCodeTermAt conclusion a b;
         proofEndpointTermAt child1 context a;
         proofEndpointTermAt child2 context b]
  | rawCoqRuleAndEliminationLeft =>
      proofRuleConjunction
        [pEq code (proofAndE1CodeTerm context a b child1);
         pEq conclusion a;
         formulaAndCodeTermAt c a b;
         proofEndpointTermAt child1 context c]
  | rawCoqRuleAndEliminationRight =>
      proofRuleConjunction
        [pEq code (proofAndE2CodeTerm context a b child1);
         pEq conclusion b;
         formulaAndCodeTermAt c a b;
         proofEndpointTermAt child1 context c]
  | rawCoqRuleOrIntroductionLeft =>
      proofRuleConjunction
        [pEq code (proofOrI1CodeTerm context a b child1);
         formulaOrCodeTermAt conclusion a b;
         proofEndpointTermAt child1 context a]
  | rawCoqRuleOrIntroductionRight =>
      proofRuleConjunction
        [pEq code (proofOrI2CodeTerm context a b child1);
         formulaOrCodeTermAt conclusion a b;
         proofEndpointTermAt child1 context b]
  | rawCoqRuleOrElimination =>
      proofRuleConjunction
        [pEq code (proofOrECodeTerm context a b c child1 child2 child3);
         pEq conclusion c;
         formulaOrCodeTermAt t a b;
         proofEndpointTermAt child1 context t;
         proofEndpointTermAt child2 (nodeTerm a context) c;
         proofEndpointTermAt child3 (nodeTerm b context) c]
  | rawCoqRuleAllIntroduction =>
      proofRuleConjunction
        [pEq code (proofAllICodeTerm context a child1);
         formulaAllCodeTermAt conclusion a;
         contextShiftTermAt context b;
         proofEndpointTermAt child1 b a]
  | rawCoqRuleAllElimination =>
      proofRuleConjunction
        [pEq code (proofAllECodeTerm context a t child1);
         codedFormulaSingleSubstitutionTermAt t a conclusion;
         formulaAllCodeTermAt b a;
         proofEndpointTermAt child1 context b]
  | rawCoqRuleExIntroduction =>
      proofRuleConjunction
        [pEq code (proofExICodeTerm context a t child1);
         formulaExCodeTermAt conclusion a;
         codedFormulaSingleSubstitutionTermAt t a b;
         proofEndpointTermAt child1 context b]
  | rawCoqRuleExElimination =>
      proofRuleConjunction
        [pEq code (proofExECodeTerm context a b child1 child2);
         pEq conclusion b;
         formulaExCodeTermAt child3 a;
         proofEndpointTermAt child1 context child3;
         contextShiftTermAt context c;
         codedFormulaShiftTermAt tZero (Term.numeral 1) b t;
         proofEndpointTermAt child2 (nodeTerm a c) t]
  | rawCoqRuleEqualityReflexivity =>
      proofRuleConjunction
        [pEq code (proofEqReflCodeTerm context t);
         formulaEqCodeTermAt conclusion t t]
  | rawCoqRuleEqualityElimination =>
      proofRuleConjunction
        [pEq code (proofEqElimCodeTerm context a b c child1 child2);
         codedFormulaSingleSubstitutionTermAt b c conclusion;
         formulaEqCodeTermAt t a b;
         proofEndpointTermAt child1 context t;
         codedFormulaSingleSubstitutionTermAt a c child3;
         proofEndpointTermAt child2 context child3]
  end.

Definition rawCoqRestrictedPAProofRuleCaseTemplate
    selected code context conclusion a b c t child1 child2 child3
    : TemplateFormula :=
  embedPAFormula
    (rawCoqRestrictedPAProofRuleCaseFormula selected
      code context conclusion a b c t child1 child2 child3).

Fixpoint rawCoqTemplateRuleDisjunction
    (cases : list TemplateFormula) : TemplateFormula :=
  match cases with
  | [] => tfBot
  | head :: tail => tfOr head (rawCoqTemplateRuleDisjunction tail)
  end.

Definition rawCoqRestrictedPAProofRuleCaseTemplates
    code context conclusion a b c t child1 child2 child3
    : list TemplateFormula :=
  map (fun selected =>
    rawCoqRestrictedPAProofRuleCaseTemplate selected
      code context conclusion a b c t child1 child2 child3)
    rawCoqRestrictedPAProofRuleCases.

(** This computation is the audit-critical identification with the source
    predicate: all seventeen branches, in the exact order, followed by the
    source's terminal bottom. *)
Lemma raw_coqRestrictedPAProofRuleCaseTemplates_exact : forall
    code context conclusion a b c t child1 child2 child3,
  embedPAFormula
    (proofRuleValidCasesTermAt
      code context conclusion a b c t child1 child2 child3) =
  rawCoqTemplateRuleDisjunction
    (rawCoqRestrictedPAProofRuleCaseTemplates
      code context conclusion a b c t child1 child2 child3).
Proof. reflexivity. Qed.

(** Exact specialization under the eight endpoint witnesses in the actual
    carrier soundness predicate.  At this depth the proof root is [#12], the
    endpoint context and conclusion are [#11] and [#10], and the eight local
    rule fields occupy [#7] down to [#0]. *)
Definition rawCoqRestrictedPADirectEndpointWitnessEqualityTemplate
    : TemplateFormula :=
  embedPAFormula (pEq (tVar 7) (liftTerm 8 (tVar 3))).

Definition rawCoqRestrictedPADirectEndpointRuleCaseTemplates
    : list TemplateFormula :=
  rawCoqRestrictedPAProofRuleCaseTemplates
    (liftTerm 8 (tVar 4)) (tVar 7) (liftTerm 8 (tVar 2))
    (tVar 6) (tVar 5) (tVar 4) (tVar 3)
    (tVar 2) (tVar 1) (tVar 0).

Definition rawCoqRestrictedPADirectEndpointWitnessBodyTemplate
    : TemplateFormula :=
  tfAnd rawCoqRestrictedPADirectEndpointWitnessEqualityTemplate
    (rawCoqTemplateRuleDisjunction
      rawCoqRestrictedPADirectEndpointRuleCaseTemplates).

Definition rawCoqTemplateEx8 (body : TemplateFormula) : TemplateFormula :=
  tfEx (tfEx (tfEx (tfEx (tfEx (tfEx (tfEx (tfEx body))))))).

Lemma raw_coqRestrictedPADerivationSoundnessEndpointTemplate_rule_shape :
  coqRestrictedPADerivationSoundnessEndpointTemplate =
  rawCoqTemplateEx8
    rawCoqRestrictedPADirectEndpointWitnessBodyTemplate.
Proof. reflexivity. Qed.

(** Translation of the source-style, bottom-terminated disjunction is the
    native finite-case fold over the seventeen branches plus one explicit
    bottom branch. *)
Lemma raw_coqTemplateRuleDisjunction_finite_code : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    cases,
  rawTemplateFormula translation
    (rawCoqTemplateRuleDisjunction cases) =
  rawFiniteRightDisjunctionCode M
    (map (rawTemplateFormula translation) cases ++
      [rawFormulaBotCode M]).
Proof.
  intros M translation cases.
  induction cases as [|head tail ih].
  - cbn [rawCoqTemplateRuleDisjunction map app
      rawFiniteRightDisjunctionCode].
    exact (rawTemplateFormula_bot translation).
  - cbn [rawCoqTemplateRuleDisjunction map app].
    rewrite rawTemplateFormula_or, ih.
    destruct tail as [|next rest]; reflexivity.
Qed.

(** The finite-case library states its guarded context-transplant resources
    independently of any particular branch syntax.  The next three lemmas
    discharge that bookkeeping whenever every branch is atomically
    adequate. *)
Lemma raw_finiteRightDisjunctionCode_atomically_adequate_of_forall : forall
    (M : RawPAModel), RawPASatisfies M -> forall branches,
  Forall (RawCodedFormulaAtomicallyAdequate M) branches ->
  RawCodedFormulaAtomicallyAdequate M
    (rawFiniteRightDisjunctionCode M branches).
Proof.
  intros M hPA branches hbranches.
  induction branches as [|head tail ih].
  - cbn [rawFiniteRightDisjunctionCode].
    exact (raw_formulaBotCode_atomically_adequate M hPA).
  - inversion hbranches as [|? ? hhead htail]; subst.
    destruct tail as [|next rest].
    + exact hhead.
    + cbn [rawFiniteRightDisjunctionCode].
      apply (raw_formulaOrCode_atomically_adequate M hPA).
      * exact hhead.
      * apply ih. exact htail.
Qed.

Lemma raw_finiteDisjunctionConsTransplantAdequate_of_forall : forall
    (M : RawPAModel), RawPASatisfies M -> forall branches,
  Forall (RawCodedFormulaAtomicallyAdequate M) branches ->
  RawFiniteDisjunctionConsTransplantAdequate M branches.
Proof.
  intros M hPA branches.
  induction branches as [|head tail ih]; intro hbranches.
  - exact I.
  - inversion hbranches as [|? ? hhead htail]; subst.
    destruct tail as [|next rest].
    + exact I.
    + cbn [RawFiniteDisjunctionConsTransplantAdequate].
      repeat split.
      * exact hhead.
      * apply
          (raw_finiteRightDisjunctionCode_atomically_adequate_of_forall
            M hPA (next :: rest)).
        exact htail.
      * apply ih. exact htail.
Qed.

Lemma raw_finiteDisjunctionDerivedCaseResources_of_forall : forall
    (M : RawPAModel), RawPASatisfies M -> forall branches context,
  RawContextListRealizable M context ->
  Forall (RawCodedFormulaAtomicallyAdequate M) branches ->
  RawFiniteDisjunctionDerivedCaseResources M branches context.
Proof.
  intros M hPA branches context hcontext hbranches.
  destruct branches as [|head tail]; [exact I |].
  destruct tail as [|next rest]; [exact I |].
  cbn [RawFiniteDisjunctionDerivedCaseResources].
  split; [exact hcontext |].
  apply (raw_finiteDisjunctionConsTransplantAdequate_of_forall M hPA).
  exact hbranches.
Qed.

(** ------------------------------------------------------------------
    A reusable wrapper for the eight endpoint existentials.

    [rawCoqTemplateNestedExContext] records the literal contexts generated by
    repeated Ex-E.  Intermediate existential bodies are retained (shifted)
    in the tail, exactly as required by the raw natural-deduction rule. *)

Fixpoint rawCoqTemplateExN (count : nat) (body : TemplateFormula)
    : TemplateFormula :=
  match count with
  | 0 => body
  | S remaining => tfEx (rawCoqTemplateExN remaining body)
  end.

Fixpoint rawCoqTemplateRenameN (count : nat) (formula : TemplateFormula)
    : TemplateFormula :=
  match count with
  | 0 => formula
  | S remaining =>
      rawCoqTemplateRenameN remaining (templateFormulaRename S formula)
  end.

Fixpoint rawCoqTemplateNestedExContext
    (count : nat) (body : TemplateFormula) (tail : TemplateContext)
    : TemplateContext :=
  match count with
  | 0 => body :: tail
  | S remaining =>
      rawCoqTemplateNestedExContext remaining body
        (templateContextShift
          (rawCoqTemplateExN (S remaining) body :: tail))
  end.

(** Starting with a proof at the deepest body context, construct every
    existential-elimination node back to the original context.  This is
    proof-theoretic only: the caller's inner root is never replaced by a
    semantic truth assumption. *)
Theorem raw_codedPALocalProofOf_templateNestedExElimination : forall
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (translation : RawCodedTemplateTranslation M)
    count body conclusion tail innerRoot,
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation
      (rawCoqTemplateNestedExContext count body tail))
    (rawTemplateFormula translation
      (rawCoqTemplateRenameN count conclusion))
    innerRoot ->
  exists outerRoot : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation
        (rawCoqTemplateExN count body :: tail))
      (rawTemplateFormula translation conclusion)
      outerRoot.
Proof.
  intros M hPA translation count.
  induction count as [|remaining ih];
    intros body conclusion tail innerRoot hinner.
  - cbn [rawCoqTemplateNestedExContext rawCoqTemplateExN
      rawCoqTemplateRenameN] in hinner |- *.
    exists innerRoot. exact hinner.
  - cbn [rawCoqTemplateNestedExContext rawCoqTemplateRenameN] in hinner.
    destruct (ih body (templateFormulaRename S conclusion)
      (templateContextShift
        (rawCoqTemplateExN (S remaining) body :: tail))
      innerRoot hinner) as [bodyRoot hbody].
    set (outerFormula := rawCoqTemplateExN (S remaining) body).
    set (outerContext := rawTemplateContextCode translation
      (outerFormula :: tail)).
    set (shiftedContext := rawTemplateContextCode translation
      (templateContextShift (outerFormula :: tail))).
    assert (htailRealizable : RawContextListRealizable M
        (rawTemplateContextCode translation tail)).
    {
      apply raw_templateContext_realizable. exact hPA.
    }
    pose proof (raw_codedPALocalProofOf_assumption M hPA
      (rawTemplateContextCode translation tail)
      (rawTemplateFormula translation outerFormula)
      htailRealizable) as hexistential.
    assert (hexistential' : RawCodedPALocalProofOf M outerContext
        (rawFormulaExCode M
          (rawTemplateFormula translation
            (rawCoqTemplateExN remaining body)))
        (rawProofAssumptionRoot M outerContext
          (rawTemplateFormula translation outerFormula))).
    {
      unfold outerContext, outerFormula in *.
      cbn [rawCoqTemplateExN].
      rewrite <- rawTemplateFormula_ex.
      exact hexistential.
    }
    exists (rawProofExERoot M outerContext
      (rawTemplateFormula translation
        (rawCoqTemplateExN remaining body))
      (rawTemplateFormula translation conclusion)
      (rawProofAssumptionRoot M outerContext
        (rawTemplateFormula translation outerFormula))
      bodyRoot).
    apply (raw_codedPALocalProofOf_exE M hPA
      outerContext shiftedContext
      (rawTemplateFormula translation
        (rawCoqTemplateExN remaining body))
      (rawTemplateFormula translation conclusion)
      (rawTemplateFormula translation
        (templateFormulaRename S conclusion))
      (rawProofAssumptionRoot M outerContext
        (rawTemplateFormula translation outerFormula))
      bodyRoot).
    + exact hexistential'.
    + unfold outerContext, shiftedContext.
      apply raw_templateContext_shift. exact hPA.
    + exact (rawTemplateFormula_shift translation conclusion).
    + change (RawCodedPALocalProofOf M
        (rawListNode M
          (rawTemplateFormula translation
            (rawCoqTemplateExN remaining body))
          shiftedContext)
        (rawTemplateFormula translation
          (templateFormulaRename S conclusion)) bodyRoot).
      exact hbody.
Qed.

(** A named family of precisely the seventeen residual constructor roots.
    The endpoint witness conjunction is kept at the head of [tail]'s local
    context, so every root sees the same witnesses and the same earlier
    soundness assumptions. *)
Definition RawCoqRestrictedPADirectRuleCaseImplicationRoots
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (tail : TemplateContext) (equality conclusion : TemplateFormula)
    code context endpoint a b c t child1 child2 child3 : Prop :=
  let cases := rawCoqRestrictedPAProofRuleCaseTemplates
    code context endpoint a b c t child1 child2 child3 in
  let endpointBody := tfAnd equality
    (rawCoqTemplateRuleDisjunction cases) in
  forall selected : RawCoqRestrictedPAProofRuleCase,
    exists root : M,
      RawCodedPALocalProofOf M
        (rawTemplateContextCode translation (endpointBody :: tail))
        (rawFormulaImpCode M
          (rawTemplateFormula translation
            (rawCoqRestrictedPAProofRuleCaseTemplate selected
              code context endpoint a b c t child1 child2 child3))
          (rawTemplateFormula translation conclusion))
        root.

Arguments RawCoqRestrictedPADirectRuleCaseImplicationRoots
  M translation tail equality conclusion
  code context endpoint a b c t child1 child2 child3 : clear implicits.

Lemma raw_coqRestrictedPAProofRuleCases_complete : forall selected,
  In selected rawCoqRestrictedPAProofRuleCases.
Proof. intros []; cbn; tauto. Qed.

(** The checked finite dispatcher.  Its only mathematical inputs are the
    seventeen constructor-local implication roots and the standard
    transplant resources required by Or-E in this exact temporary context.
    In particular, no proof of [conclusion] and no strong-step root occurs in
    the hypotheses. *)
Theorem raw_codedPALocalProofOf_coqRestrictedPADirectRuleDispatch : forall
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (translation : RawCodedTemplateTranslation M)
    tail equality conclusion
    code context endpoint a b c t child1 child2 child3,
  let cases := rawCoqRestrictedPAProofRuleCaseTemplates
    code context endpoint a b c t child1 child2 child3 in
  let endpointBody := tfAnd equality
    (rawCoqTemplateRuleDisjunction cases) in
  RawFiniteDisjunctionDerivedCaseResources M
    (map (rawTemplateFormula translation) cases ++
      [rawFormulaBotCode M])
    (rawTemplateContextCode translation (endpointBody :: tail)) ->
  RawCoqRestrictedPADirectRuleCaseImplicationRoots M translation
    tail equality conclusion
    code context endpoint a b c t child1 child2 child3 ->
  exists resultRoot : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation (endpointBody :: tail))
      (rawTemplateFormula translation conclusion)
      resultRoot.
Proof.
  intros M hPA translation tail equality conclusion
    code context endpoint a b c t child1 child2 child3.
  cbn zeta.
  set (cases := rawCoqRestrictedPAProofRuleCaseTemplates
    code context endpoint a b c t child1 child2 child3).
  set (endpointBody := tfAnd equality
    (rawCoqTemplateRuleDisjunction cases)).
  intros hresources hcaseRoots.
  set (localContext := rawTemplateContextCode translation
    (endpointBody :: tail)).

  assert (htailRealizable : RawContextListRealizable M
      (rawTemplateContextCode translation tail)).
  {
    apply raw_templateContext_realizable. exact hPA.
  }
  pose proof (raw_codedPALocalProofOf_assumption M hPA
    (rawTemplateContextCode translation tail)
    (rawTemplateFormula translation endpointBody)
    htailRealizable) as hendpointBody.
  change (RawCodedPALocalProofOf M localContext
    (rawTemplateFormula translation endpointBody)
    (rawProofAssumptionRoot M localContext
      (rawTemplateFormula translation endpointBody))) in hendpointBody.

  assert (hrow : RawCodedPALocalProofOf M localContext
      (rawTemplateFormula translation
        (rawCoqTemplateRuleDisjunction cases))
      (rawProofAndERoot M RawAndRight localContext
        (rawTemplateFormula translation equality)
        (rawTemplateFormula translation
          (rawCoqTemplateRuleDisjunction cases))
        (rawProofAssumptionRoot M localContext
          (rawTemplateFormula translation endpointBody)))).
  {
    apply (raw_codedPALocalProofOf_andE2 M hPA localContext
      (rawTemplateFormula translation equality)
      (rawTemplateFormula translation
        (rawCoqTemplateRuleDisjunction cases))).
    rewrite <- rawTemplateFormula_and.
    exact hendpointBody.
  }

  assert (hcaseFamily :
      RawCodedPALocalFiniteDisjunctionCaseFamily M localContext
        (map (rawTemplateFormula translation) cases ++
          [rawFormulaBotCode M])
        (rawTemplateFormula translation conclusion)).
  {
    intros branch hbranch.
    apply in_app_or in hbranch.
    destruct hbranch as [hregular | hbottom].
    - apply in_map_iff in hregular.
      destruct hregular as [caseTemplate [hbranch hcaseTemplate]].
      subst branch.
      unfold cases in hcaseTemplate.
      apply in_map_iff in hcaseTemplate.
      destruct hcaseTemplate as [selected [hcaseTemplate hselected]].
      subst caseTemplate.
      apply hcaseRoots.
    - destruct hbottom as [hbottom | himpossible]; [|contradiction].
      subst branch.
      assert (hlocalRealizable : RawContextListRealizable M localContext).
      {
        unfold localContext.
        apply raw_templateContext_realizable. exact hPA.
      }
      pose proof (raw_codedPALocalProofOf_assumption M hPA
        localContext (rawFormulaBotCode M) hlocalRealizable) as hbot.
      pose proof (raw_codedPALocalProofOf_botE M hPA
        (rawListNode M (rawFormulaBotCode M) localContext)
        (rawProofAssumptionRoot M
          (rawListNode M (rawFormulaBotCode M) localContext)
          (rawFormulaBotCode M)) hbot
        (rawTemplateFormula translation conclusion)) as hconclusion.
      exists (rawProofImpIRoot M localContext
        (rawFormulaBotCode M)
        (rawTemplateFormula translation conclusion)
        (rawProofBotERoot M
          (rawListNode M (rawFormulaBotCode M) localContext)
          (rawTemplateFormula translation conclusion)
          (rawProofAssumptionRoot M
            (rawListNode M (rawFormulaBotCode M) localContext)
            (rawFormulaBotCode M)))).
      exact (raw_codedPALocalProofOf_impI M hPA localContext
        (rawFormulaBotCode M)
        (rawTemplateFormula translation conclusion) _ hconclusion).
  }

  apply (raw_codedPALocalProofOf_finiteDisjunctionDerivedCases
    M hPA
    (map (rawTemplateFormula translation) cases ++
      [rawFormulaBotCode M])
    (rawTemplateFormula translation conclusion)
    localContext
    (rawProofAndERoot M RawAndRight localContext
      (rawTemplateFormula translation equality)
      (rawTemplateFormula translation
        (rawCoqTemplateRuleDisjunction cases))
      (rawProofAssumptionRoot M localContext
        (rawTemplateFormula translation endpointBody)))
    hresources).
  - rewrite <- raw_coqTemplateRuleDisjunction_finite_code.
    exact hrow.
  - exact hcaseFamily.
Qed.

(** For the direct translation every named branch is embedded ordinary PA
    syntax.  Agreement with quotation therefore supplies atomic adequacy for
    all seventeen branches; bottom supplies the eighteenth, terminal branch.
    This removes the finite-Or resource from the public direct frontier. *)
Lemma raw_coqRestrictedPADirectRuleCaseCodes_atomically_adequate : forall
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    code context endpoint a b c t child1 child2 child3,
  let translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs in
  let cases := rawCoqRestrictedPAProofRuleCaseTemplates
    code context endpoint a b c t child1 child2 child3 in
  Forall (RawCodedFormulaAtomicallyAdequate M)
    (map (rawTemplateFormula translation) cases ++
      [rawFormulaBotCode M]).
Proof.
  intros M hPA inputs code context endpoint a b c t child1 child2 child3.
  cbn zeta.
  apply Forall_forall.
  intros branch hbranch.
  apply in_app_or in hbranch.
  destruct hbranch as [hcase | hbottom].
  - apply in_map_iff in hcase.
    destruct hcase as [caseTemplate [hbranch hcaseTemplate]].
    subst branch.
    unfold rawCoqRestrictedPAProofRuleCaseTemplates in hcaseTemplate.
    apply in_map_iff in hcaseTemplate.
    destruct hcaseTemplate as [selected [hcaseTemplate _]].
    subst caseTemplate.
    unfold rawCoqRestrictedPAProofRuleCaseTemplate.
    rewrite (rawTemplateFormula_embedPA
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)).
    apply raw_quotedFormula_atomically_adequate. exact hPA.
  - destruct hbottom as [hbottom | himpossible]; [|contradiction].
    subst branch.
    exact (raw_formulaBotCode_atomically_adequate M hPA).
Qed.

Theorem raw_codedPALocalProofOf_coqRestrictedPADirectRuleDispatch_exact :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    tail equality conclusion
    code context endpoint a b c t child1 child2 child3,
  let translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs in
  let cases := rawCoqRestrictedPAProofRuleCaseTemplates
    code context endpoint a b c t child1 child2 child3 in
  let endpointBody := tfAnd equality
    (rawCoqTemplateRuleDisjunction cases) in
  RawCoqRestrictedPADirectRuleCaseImplicationRoots M translation
    tail equality conclusion
    code context endpoint a b c t child1 child2 child3 ->
  exists resultRoot : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation (endpointBody :: tail))
      (rawTemplateFormula translation conclusion)
      resultRoot.
Proof.
  intros M hPA inputs tail equality conclusion
    code context endpoint a b c t child1 child2 child3.
  cbn zeta.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  set (cases := rawCoqRestrictedPAProofRuleCaseTemplates
    code context endpoint a b c t child1 child2 child3).
  set (endpointBody := tfAnd equality
    (rawCoqTemplateRuleDisjunction cases)).
  intro hcaseRoots.
  apply (raw_codedPALocalProofOf_coqRestrictedPADirectRuleDispatch
    M hPA translation tail equality conclusion
    code context endpoint a b c t child1 child2 child3).
  - apply (raw_finiteDisjunctionDerivedCaseResources_of_forall M hPA).
    + apply raw_templateContext_realizable. exact hPA.
    + unfold translation, cases.
      exact (raw_coqRestrictedPADirectRuleCaseCodes_atomically_adequate
        M hPA inputs code context endpoint a b c t child1 child2 child3).
  - exact hcaseRoots.
Qed.

(** The public specialization used by a future eight-Ex wrapper.  Its
    residual roots now mention neither a caller-chosen branch list nor
    caller-chosen rule fields: all ten terms are the literal de Bruijn terms
    from the endpoint relation inside the advertised soundness predicate. *)
Definition RawCoqRestrictedPADirectEndpointRuleCaseImplicationRoots
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) (conclusion : TemplateFormula) : Prop :=
  RawCoqRestrictedPADirectRuleCaseImplicationRoots M
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    tail rawCoqRestrictedPADirectEndpointWitnessEqualityTemplate conclusion
    (liftTerm 8 (tVar 4)) (tVar 7) (liftTerm 8 (tVar 2))
    (tVar 6) (tVar 5) (tVar 4) (tVar 3)
    (tVar 2) (tVar 1) (tVar 0).

Arguments RawCoqRestrictedPADirectEndpointRuleCaseImplicationRoots
  M hPA inputs tail conclusion : clear implicits.

Theorem
    raw_codedPALocalProofOf_coqRestrictedPADirectEndpointRuleDispatch :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    tail conclusion,
  RawCoqRestrictedPADirectEndpointRuleCaseImplicationRoots
    M hPA inputs tail conclusion ->
  exists resultRoot : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawCoqRestrictedPADirectEndpointWitnessBodyTemplate :: tail))
      (rawDirectTemplateFormula inputs conclusion)
      resultRoot.
Proof.
  intros M hPA inputs tail conclusion hcaseRoots.
  exact
    (raw_codedPALocalProofOf_coqRestrictedPADirectRuleDispatch_exact
      M hPA inputs tail
      rawCoqRestrictedPADirectEndpointWitnessEqualityTemplate conclusion
      (liftTerm 8 (tVar 4)) (tVar 7) (liftTerm 8 (tVar 2))
      (tVar 6) (tVar 5) (tVar 4) (tVar 3)
      (tVar 2) (tVar 1) (tVar 0)
      hcaseRoots).
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier.
