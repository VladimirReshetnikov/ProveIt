(**
  Exact opening of a three-variable template universal closure.

  A body scoped by variables [#2], [#1], and [#0] is restored after its
  three enclosing universal binders are eliminated with those same free
  variables, in outer-to-inner order.  The two intermediate formulas are
  not the original prefixes: opening the outer binders temporarily raises
  the still-free variables.  Proving the complete substitution composite
  is the identity avoids the incorrect stronger demand that every
  intermediate opening be a self-substitution.

  The final theorem transports this finite syntax calculation through any
  [RawCodedTemplateTranslation].  Its relational opening field supplies the
  actual represented substitution traces, so the result applies equally to
  standard formulas and genuinely nonstandard opaque formula codes.
*)

From Stdlib Require Import List Arith Lia.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedPALocalProofUniversalEliminationChain.

Module PABoundedRawCodedTemplateTripleUniversalOpening.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedPALocalProofUniversalEliminationChain.

(** A small, general scoping predicate for template syntax.  Named carrier
    parameters never consume a de Bruijn slot; opaque formulas are scoped
    precisely through their displayed term arguments. *)
Fixpoint TemplateTermScoped (scope : nat) (input : TemplateTerm) : Prop :=
  match input with
  | ttVar index => index < scope
  | ttParameter _ => True
  | ttZero => True
  | ttSucc child => TemplateTermScoped scope child
  | ttAdd lhs rhs =>
      TemplateTermScoped scope lhs /\ TemplateTermScoped scope rhs
  | ttMul lhs rhs =>
      TemplateTermScoped scope lhs /\ TemplateTermScoped scope rhs
  end.

Fixpoint TemplateTermsScoped
    (scope : nat) (inputs : list TemplateTerm) : Prop :=
  match inputs with
  | [] => True
  | input :: tail =>
      TemplateTermScoped scope input /\ TemplateTermsScoped scope tail
  end.

Fixpoint TemplateFormulaScoped
    (scope : nat) (input : TemplateFormula) : Prop :=
  match input with
  | tfEq lhs rhs =>
      TemplateTermScoped scope lhs /\ TemplateTermScoped scope rhs
  | tfBot => True
  | tfImp lhs rhs =>
      TemplateFormulaScoped scope lhs /\
      TemplateFormulaScoped scope rhs
  | tfAnd lhs rhs =>
      TemplateFormulaScoped scope lhs /\
      TemplateFormulaScoped scope rhs
  | tfOr lhs rhs =>
      TemplateFormulaScoped scope lhs /\
      TemplateFormulaScoped scope rhs
  | tfAll body => TemplateFormulaScoped (S scope) body
  | tfEx body => TemplateFormulaScoped (S scope) body
  | tfOpaque _ arguments => TemplateTermsScoped scope arguments
  end.

Arguments TemplateTermScoped scope input : clear implicits.
Arguments TemplateTermsScoped scope inputs : clear implicits.
Arguments TemplateFormulaScoped scope input : clear implicits.

(** Open a literal three-binder tower at arbitrary template terms.  Unlike
    the variable-preserving specialization below, this operation also
    covers clients that instantiate a theorem beneath unrelated binders. *)
Definition templateAll3Open (body : TemplateFormula)
    (outer middle inner : TemplateTerm) : TemplateFormula :=
  templateUniversalOpenManyOrBot
    (tfAll (tfAll (tfAll body))) [outer; middle; inner].

(** A syntactic tower containing three leading universals cannot take the
    failure branch of [templateUniversalOpenManyOrBot], independently of
    the body and replacement terms. *)
Lemma templateUniversalOpenMany_all3 : forall body outer middle inner,
  templateUniversalOpenMany (tfAll (tfAll (tfAll body)))
    [outer; middle; inner] =
  Some (templateAll3Open body outer middle inner).
Proof.
  intros body outer middle inner.
  unfold templateAll3Open, templateUniversalOpenManyOrBot.
  cbn [templateUniversalOpenMany].
  reflexivity.
Qed.

(** General represented three-step [All-E] chain.  No scoping premise is
    needed: capture-avoiding opening itself determines the target. *)
Corollary raw_template_all3_elimination_chain : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    body outer middle inner,
  RawCodedUniversalEliminationChain M
    (rawTemplateFormula translation (tfAll (tfAll (tfAll body))))
    (rawTemplateFormula translation
      (templateAll3Open body outer middle inner)).
Proof.
  intros M translation body outer middle inner.
  exact (raw_templateUniversalOpenMany_elimination_chain
    M translation (tfAll (tfAll (tfAll body)))
    [outer; middle; inner]
    (templateAll3Open body outer middle inner)
    (templateUniversalOpenMany_all3 body outer middle inner)).
Qed.

(** Iterating [up] records the additional binders traversed while a formula
    substitution descends. *)
Fixpoint templateIterateUpSubst
    (depth : nat) (substitution : nat -> TemplateTerm)
    : nat -> TemplateTerm :=
  match depth with
  | 0 => substitution
  | S previous =>
      templateTermUpSubst
        (templateIterateUpSubst previous substitution)
  end.

Definition templateOuterOfThreeSubstitution : nat -> TemplateTerm :=
  templateTermUpSubst
    (templateTermUpSubst (templateInstTerm (ttVar 2))).

Definition templateMiddleOfThreeSubstitution : nat -> TemplateTerm :=
  templateTermUpSubst (templateInstTerm (ttVar 1)).

Definition templateInnerOfThreeSubstitution : nat -> TemplateTerm :=
  templateInstTerm (ttVar 0).

(** Substitution below one more binder commutes with the protective variable
    shift.  This is the only algebra needed in the successor case of the
    variable calculation below. *)
Lemma templateTermSubst_up_rename_succ : forall substitution input,
  templateTermSubst (templateTermUpSubst substitution)
    (templateTermRename S input) =
  templateTermRename S (templateTermSubst substitution input).
Proof.
  intros substitution input.
  induction input; cbn; try reflexivity.
  - now rewrite IHinput.
  - now rewrite IHinput1, IHinput2.
  - now rewrite IHinput1, IHinput2.
Qed.

Lemma templateIterateUpSubst_succ : forall depth substitution,
  templateIterateUpSubst (S depth) substitution =
  templateTermUpSubst (templateIterateUpSubst depth substitution).
Proof. reflexivity. Qed.

(** The composite induced by the three eliminations fixes every variable in
    scope [3 + depth].  Variables above that boundary are deliberately not
    claimed to be fixed. *)
Lemma template_three_opening_substitutions_variable : forall depth index,
  index < 3 + depth ->
  templateTermSubst
    (templateIterateUpSubst depth templateInnerOfThreeSubstitution)
    (templateTermSubst
      (templateIterateUpSubst depth templateMiddleOfThreeSubstitution)
      (templateTermSubst
        (templateIterateUpSubst depth templateOuterOfThreeSubstitution)
        (ttVar index))) =
  ttVar index.
Proof.
  induction depth as [|depth ih]; intros index hindex.
  - destruct index as [|[|[|index]]]; cbn in hindex |- *; try lia;
      reflexivity.
  - destruct index as [|index].
    + reflexivity.
    + rewrite !templateIterateUpSubst_succ.
      cbn [templateTermSubst].
      change
        (templateTermSubst
          (templateTermUpSubst
            (templateIterateUpSubst depth
              templateInnerOfThreeSubstitution))
          (templateTermSubst
            (templateTermUpSubst
              (templateIterateUpSubst depth
                templateMiddleOfThreeSubstitution))
            (templateTermRename S
              (templateIterateUpSubst depth
                templateOuterOfThreeSubstitution index))) =
         ttVar (S index)).
      rewrite !templateTermSubst_up_rename_succ.
      change
        (templateTermRename S
          (templateTermSubst
            (templateIterateUpSubst depth
              templateInnerOfThreeSubstitution)
            (templateTermSubst
              (templateIterateUpSubst depth
                templateMiddleOfThreeSubstitution)
              (templateTermSubst
                (templateIterateUpSubst depth
                  templateOuterOfThreeSubstitution)
                (ttVar index)))) = ttVar (S index)).
      rewrite (ih index) by lia.
      reflexivity.
Qed.

Lemma template_three_opening_substitutions_term : forall depth input,
  TemplateTermScoped (3 + depth) input ->
  templateTermSubst
    (templateIterateUpSubst depth templateInnerOfThreeSubstitution)
    (templateTermSubst
      (templateIterateUpSubst depth templateMiddleOfThreeSubstitution)
      (templateTermSubst
        (templateIterateUpSubst depth templateOuterOfThreeSubstitution)
        input)) = input.
Proof.
  intros depth input.
  induction input; intro hscoped; cbn in hscoped |- *; try reflexivity.
  - exact (template_three_opening_substitutions_variable
      depth n hscoped).
  - now rewrite IHinput.
  - destruct hscoped as [hleft hright].
    now rewrite (IHinput1 hleft), (IHinput2 hright).
  - destruct hscoped as [hleft hright].
    now rewrite (IHinput1 hleft), (IHinput2 hright).
Qed.

Lemma template_three_opening_substitutions_terms : forall depth inputs,
  TemplateTermsScoped (3 + depth) inputs ->
  templateTermsSubst
    (templateIterateUpSubst depth templateInnerOfThreeSubstitution)
    (templateTermsSubst
      (templateIterateUpSubst depth templateMiddleOfThreeSubstitution)
      (templateTermsSubst
        (templateIterateUpSubst depth templateOuterOfThreeSubstitution)
        inputs)) = inputs.
Proof.
  intros depth inputs.
  induction inputs as [|input tail ih]; intro hscoped; cbn in hscoped |- *.
  - reflexivity.
  - destruct hscoped as [hinput htail].
    change
      (templateTermSubst
        (templateIterateUpSubst depth templateInnerOfThreeSubstitution)
        (templateTermSubst
          (templateIterateUpSubst depth templateMiddleOfThreeSubstitution)
          (templateTermSubst
            (templateIterateUpSubst depth
              templateOuterOfThreeSubstitution) input)) ::
       templateTermsSubst
        (templateIterateUpSubst depth templateInnerOfThreeSubstitution)
        (templateTermsSubst
          (templateIterateUpSubst depth templateMiddleOfThreeSubstitution)
          (templateTermsSubst
            (templateIterateUpSubst depth
              templateOuterOfThreeSubstitution) tail)) =
       input :: tail).
    rewrite (template_three_opening_substitutions_term
      depth input hinput), (ih htail).
    reflexivity.
Qed.

(** Formula binders increment [depth], so one structural induction proves
    the identity for arbitrary mixtures of connectives, quantifiers, and
    opaque applications. *)
Theorem template_three_opening_substitutions_formula : forall depth input,
  TemplateFormulaScoped (3 + depth) input ->
  templateFormulaSubst
    (templateIterateUpSubst depth templateInnerOfThreeSubstitution)
    (templateFormulaSubst
      (templateIterateUpSubst depth templateMiddleOfThreeSubstitution)
      (templateFormulaSubst
        (templateIterateUpSubst depth templateOuterOfThreeSubstitution)
        input)) = input.
Proof.
  intros depth input.
  revert depth.
  induction input; intros depth hscoped; cbn in hscoped |- *;
    try reflexivity.
  - destruct hscoped as [hleft hright].
    rewrite (template_three_opening_substitutions_term depth t hleft),
      (template_three_opening_substitutions_term depth t0 hright).
    reflexivity.
  - destruct hscoped as [hleft hright].
    now rewrite (IHinput1 depth hleft), (IHinput2 depth hright).
  - destruct hscoped as [hleft hright].
    now rewrite (IHinput1 depth hleft), (IHinput2 depth hright).
  - destruct hscoped as [hleft hright].
    now rewrite (IHinput1 depth hleft), (IHinput2 depth hright).
  - f_equal.
    replace (S (3 + depth)) with (3 + S depth) in hscoped by lia.
    exact (IHinput (S depth) hscoped).
  - f_equal.
    replace (S (3 + depth)) with (3 + S depth) in hscoped by lia.
    exact (IHinput (S depth) hscoped).
  - f_equal.
    exact (template_three_opening_substitutions_terms
      depth l hscoped).
Qed.

(** Compute the three leading [all] openings without pretending that their
    intermediate formulas are fixed points. *)
Theorem templateUniversalOpenMany_all3_variables : forall body,
  TemplateFormulaScoped 3 body ->
  templateUniversalOpenMany
    (tfAll (tfAll (tfAll body)))
    [ttVar 2; ttVar 1; ttVar 0] = Some body.
Proof.
  intros body hscoped.
  cbn [templateUniversalOpenMany templateFormulaOpen
    templateFormulaSubst templateTermUpSubst].
  f_equal.
  unfold templateFormulaOpen.
  change
    (templateFormulaSubst
      (templateIterateUpSubst 0 templateInnerOfThreeSubstitution)
      (templateFormulaSubst
        (templateIterateUpSubst 0 templateMiddleOfThreeSubstitution)
        (templateFormulaSubst
          (templateIterateUpSubst 0 templateOuterOfThreeSubstitution)
          body)) = body).
  exact (template_three_opening_substitutions_formula 0 body hscoped).
Qed.

(** Any honest translation now yields the represented All-E chain.  Opaque
    applications may translate to nonstandard formula codes; their opening
    behavior is supplied by the translation rather than decoded here. *)
Corollary raw_template_all3_variables_elimination_chain : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M) body,
  TemplateFormulaScoped 3 body ->
  RawCodedUniversalEliminationChain M
    (rawTemplateFormula translation (tfAll (tfAll (tfAll body))))
    (rawTemplateFormula translation body).
Proof.
  intros M translation body hscoped.
  exact (raw_templateUniversalOpenMany_elimination_chain
    M translation (tfAll (tfAll (tfAll body)))
    [ttVar 2; ttVar 1; ttVar 0] body
    (templateUniversalOpenMany_all3_variables body hscoped)).
Qed.

End PABoundedRawCodedTemplateTripleUniversalOpening.
