(**
  An honest syntax of model-coded proof templates.

  The existing PA syntax has only de Bruijn variables.  A uniform proof
  compiler additionally needs names for carrier elements which will be
  supplied at run time, and it needs an opaque predicate placeholder for a
  dynamically generated truth formula.  Treating either of those objects as
  an ordinary metatheoretic PA term or formula would silently decode a
  possibly nonstandard carrier value.

  This module therefore defines a separate, purely syntactic template
  language.  Its terms have both bound/free de Bruijn variables and named
  carrier parameters.  Its formulas contain the ordinary PA connectives plus
  an opaque predicate name applied to a finite list of template terms.  The
  predicate application deliberately stores a list instead of fixing one
  arity: a later compiler may impose a signature, while this structural layer
  remains useful for ternary truth predicates and other helper relations.

  Variable renaming and substitution affect only de Bruijn variables.
  Carrier parameters and predicate names remain opaque.  Quantifiers use the
  standard lifted renaming/substitution operations, so capture avoidance is
  built into the definitions rather than imposed as a side condition.

  The final section mirrors all seventeen constructors of
  [CodedProof.RawProof].  The tree is intentionally unindexed: every node
  carries its claimed context and rule data, and [TemplateRawProofValid]
  checks all recursive endpoints declaratively.  No compilation to raw model
  codes is attempted here; that is a separate, later correctness theorem.
*)

From Stdlib Require Import List Arith.
From PAHF Require Import PAHF.

Import ListNotations.

Module PABoundedRawCodedTemplateSyntax.

Import PA.

(** ------------------------------------------------------------------
    Template terms and formulas. *)

Definition TemplateParameterName : Type := nat.
Definition TemplatePredicateName : Type := nat.

Inductive TemplateTerm : Type :=
| ttVar : nat -> TemplateTerm
| ttParameter : TemplateParameterName -> TemplateTerm
| ttZero : TemplateTerm
| ttSucc : TemplateTerm -> TemplateTerm
| ttAdd : TemplateTerm -> TemplateTerm -> TemplateTerm
| ttMul : TemplateTerm -> TemplateTerm -> TemplateTerm.

Inductive TemplateFormula : Type :=
| tfEq : TemplateTerm -> TemplateTerm -> TemplateFormula
| tfBot : TemplateFormula
| tfImp : TemplateFormula -> TemplateFormula -> TemplateFormula
| tfAnd : TemplateFormula -> TemplateFormula -> TemplateFormula
| tfOr : TemplateFormula -> TemplateFormula -> TemplateFormula
| tfAll : TemplateFormula -> TemplateFormula
| tfEx : TemplateFormula -> TemplateFormula
| tfOpaque : TemplatePredicateName -> list TemplateTerm -> TemplateFormula.

Definition TemplateContext : Type := list TemplateFormula.

(** [templateUpRenaming] fixes the newly bound variable zero and moves every
    renamed outer variable beneath it. *)
Definition templateUpRenaming (renaming : nat -> nat) : nat -> nat :=
  fun index =>
    match index with
    | 0 => 0
    | S outerIndex => S (renaming outerIndex)
    end.

Fixpoint templateTermRename (renaming : nat -> nat)
    (input : TemplateTerm) : TemplateTerm :=
  match input with
  | ttVar index => ttVar (renaming index)
  | ttParameter name => ttParameter name
  | ttZero => ttZero
  | ttSucc child => ttSucc (templateTermRename renaming child)
  | ttAdd lhs rhs =>
      ttAdd (templateTermRename renaming lhs)
        (templateTermRename renaming rhs)
  | ttMul lhs rhs =>
      ttMul (templateTermRename renaming lhs)
        (templateTermRename renaming rhs)
  end.

Definition templateTermsRename (renaming : nat -> nat)
    (inputs : list TemplateTerm) : list TemplateTerm :=
  map (templateTermRename renaming) inputs.

Fixpoint templateFormulaRename (renaming : nat -> nat)
    (input : TemplateFormula) : TemplateFormula :=
  match input with
  | tfEq lhs rhs =>
      tfEq (templateTermRename renaming lhs)
        (templateTermRename renaming rhs)
  | tfBot => tfBot
  | tfImp lhs rhs =>
      tfImp (templateFormulaRename renaming lhs)
        (templateFormulaRename renaming rhs)
  | tfAnd lhs rhs =>
      tfAnd (templateFormulaRename renaming lhs)
        (templateFormulaRename renaming rhs)
  | tfOr lhs rhs =>
      tfOr (templateFormulaRename renaming lhs)
        (templateFormulaRename renaming rhs)
  | tfAll body =>
      tfAll (templateFormulaRename
        (templateUpRenaming renaming) body)
  | tfEx body =>
      tfEx (templateFormulaRename
        (templateUpRenaming renaming) body)
  | tfOpaque predicate arguments =>
      tfOpaque predicate (templateTermsRename renaming arguments)
  end.

(** A lifted substitution also fixes the new variable zero.  Every term
    supplied for an outer variable is shifted once before entering the
    binder.  Named parameters inside those terms remain unchanged. *)
Definition templateTermUpSubst
    (substitution : nat -> TemplateTerm) : nat -> TemplateTerm :=
  fun index =>
    match index with
    | 0 => ttVar 0
    | S outerIndex =>
        templateTermRename S (substitution outerIndex)
    end.

Fixpoint templateTermSubst (substitution : nat -> TemplateTerm)
    (input : TemplateTerm) : TemplateTerm :=
  match input with
  | ttVar index => substitution index
  | ttParameter name => ttParameter name
  | ttZero => ttZero
  | ttSucc child => ttSucc (templateTermSubst substitution child)
  | ttAdd lhs rhs =>
      ttAdd (templateTermSubst substitution lhs)
        (templateTermSubst substitution rhs)
  | ttMul lhs rhs =>
      ttMul (templateTermSubst substitution lhs)
        (templateTermSubst substitution rhs)
  end.

Definition templateTermsSubst (substitution : nat -> TemplateTerm)
    (inputs : list TemplateTerm) : list TemplateTerm :=
  map (templateTermSubst substitution) inputs.

Fixpoint templateFormulaSubst (substitution : nat -> TemplateTerm)
    (input : TemplateFormula) : TemplateFormula :=
  match input with
  | tfEq lhs rhs =>
      tfEq (templateTermSubst substitution lhs)
        (templateTermSubst substitution rhs)
  | tfBot => tfBot
  | tfImp lhs rhs =>
      tfImp (templateFormulaSubst substitution lhs)
        (templateFormulaSubst substitution rhs)
  | tfAnd lhs rhs =>
      tfAnd (templateFormulaSubst substitution lhs)
        (templateFormulaSubst substitution rhs)
  | tfOr lhs rhs =>
      tfOr (templateFormulaSubst substitution lhs)
        (templateFormulaSubst substitution rhs)
  | tfAll body =>
      tfAll (templateFormulaSubst
        (templateTermUpSubst substitution) body)
  | tfEx body =>
      tfEx (templateFormulaSubst
        (templateTermUpSubst substitution) body)
  | tfOpaque predicate arguments =>
      tfOpaque predicate (templateTermsSubst substitution arguments)
  end.

(** Opening the innermost binder replaces variable zero and lowers all
    strictly positive variable indices by one. *)
Definition templateInstTerm (replacement : TemplateTerm)
    : nat -> TemplateTerm :=
  fun index =>
    match index with
    | 0 => replacement
    | S outerIndex => ttVar outerIndex
    end.

Definition templateFormulaOpen (replacement : TemplateTerm)
    (body : TemplateFormula) : TemplateFormula :=
  templateFormulaSubst (templateInstTerm replacement) body.

(** Context shift is the operation used by eigenvariable rules. *)
Definition templateContextRename (renaming : nat -> nat)
    (context : TemplateContext) : TemplateContext :=
  map (templateFormulaRename renaming) context.

Definition templateContextSubst (substitution : nat -> TemplateTerm)
    (context : TemplateContext) : TemplateContext :=
  map (templateFormulaSubst substitution) context.

Definition templateContextShift (context : TemplateContext)
    : TemplateContext :=
  templateContextRename S context.

(** ------------------------------------------------------------------
    Structural laws for template syntax. *)

Lemma templateTermRename_ext : forall input first second,
  (forall index, first index = second index) ->
  templateTermRename first input = templateTermRename second input.
Proof.
  induction input; intros first second hext; cbn.
  - now rewrite hext.
  - reflexivity.
  - reflexivity.
  - now rewrite (IHinput first second hext).
  - now rewrite (IHinput1 first second hext),
      (IHinput2 first second hext).
  - now rewrite (IHinput1 first second hext),
      (IHinput2 first second hext).
Qed.

Lemma templateTermsRename_ext : forall inputs first second,
  (forall index, first index = second index) ->
  templateTermsRename first inputs = templateTermsRename second inputs.
Proof.
  induction inputs as [|input inputs ih]; intros first second hext; cbn.
  - reflexivity.
  - rewrite (templateTermRename_ext input first second hext).
    f_equal. exact (ih first second hext).
Qed.

Lemma templateFormulaRename_ext : forall input first second,
  (forall index, first index = second index) ->
  templateFormulaRename first input = templateFormulaRename second input.
Proof.
  induction input; intros first second hext; cbn.
  - now rewrite (templateTermRename_ext t first second hext),
      (templateTermRename_ext t0 first second hext).
  - reflexivity.
  - now rewrite (IHinput1 first second hext),
      (IHinput2 first second hext).
  - now rewrite (IHinput1 first second hext),
      (IHinput2 first second hext).
  - now rewrite (IHinput1 first second hext),
      (IHinput2 first second hext).
  - f_equal. apply IHinput. intros [|index]; cbn; [reflexivity |].
    now rewrite hext.
  - f_equal. apply IHinput. intros [|index]; cbn; [reflexivity |].
    now rewrite hext.
  - f_equal. apply templateTermsRename_ext. exact hext.
Qed.

Lemma templateTermSubst_ext : forall input first second,
  (forall index, first index = second index) ->
  templateTermSubst first input = templateTermSubst second input.
Proof.
  induction input; intros first second hext; cbn.
  - apply hext.
  - reflexivity.
  - reflexivity.
  - now rewrite (IHinput first second hext).
  - now rewrite (IHinput1 first second hext),
      (IHinput2 first second hext).
  - now rewrite (IHinput1 first second hext),
      (IHinput2 first second hext).
Qed.

Lemma templateTermsSubst_ext : forall inputs first second,
  (forall index, first index = second index) ->
  templateTermsSubst first inputs = templateTermsSubst second inputs.
Proof.
  induction inputs as [|input inputs ih]; intros first second hext; cbn.
  - reflexivity.
  - rewrite (templateTermSubst_ext input first second hext).
    f_equal. exact (ih first second hext).
Qed.

Lemma templateFormulaSubst_ext : forall input first second,
  (forall index, first index = second index) ->
  templateFormulaSubst first input = templateFormulaSubst second input.
Proof.
  induction input; intros first second hext; cbn.
  - now rewrite (templateTermSubst_ext t first second hext),
      (templateTermSubst_ext t0 first second hext).
  - reflexivity.
  - now rewrite (IHinput1 first second hext),
      (IHinput2 first second hext).
  - now rewrite (IHinput1 first second hext),
      (IHinput2 first second hext).
  - now rewrite (IHinput1 first second hext),
      (IHinput2 first second hext).
  - f_equal. apply IHinput. intros [|index]; cbn; [reflexivity |].
    now rewrite hext.
  - f_equal. apply IHinput. intros [|index]; cbn; [reflexivity |].
    now rewrite hext.
  - f_equal. apply templateTermsSubst_ext. exact hext.
Qed.

Lemma templateTermRename_id : forall input,
  templateTermRename (fun index => index) input = input.
Proof.
  induction input; cbn; try reflexivity.
  - now rewrite IHinput.
  - now rewrite IHinput1, IHinput2.
  - now rewrite IHinput1, IHinput2.
Qed.

Lemma templateTermsRename_id : forall inputs,
  templateTermsRename (fun index => index) inputs = inputs.
Proof.
  induction inputs as [|input inputs ih]; cbn; [reflexivity |].
  rewrite templateTermRename_id. f_equal. exact ih.
Qed.

Lemma templateFormulaRename_id : forall input,
  templateFormulaRename (fun index => index) input = input.
Proof.
  induction input; cbn.
  - now rewrite !templateTermRename_id.
  - reflexivity.
  - now rewrite IHinput1, IHinput2.
  - now rewrite IHinput1, IHinput2.
  - now rewrite IHinput1, IHinput2.
  - rewrite <- IHinput at 2. f_equal.
    apply templateFormulaRename_ext.
    intros [|index]; reflexivity.
  - rewrite <- IHinput at 2. f_equal.
    apply templateFormulaRename_ext.
    intros [|index]; reflexivity.
  - now rewrite templateTermsRename_id.
Qed.

Lemma templateTermRename_comp : forall input first second,
  templateTermRename first (templateTermRename second input) =
  templateTermRename (fun index => first (second index)) input.
Proof.
  induction input; intros first second; cbn; try reflexivity.
  - now rewrite IHinput.
  - now rewrite IHinput1, IHinput2.
  - now rewrite IHinput1, IHinput2.
Qed.

Lemma templateTermsRename_comp : forall inputs first second,
  templateTermsRename first (templateTermsRename second inputs) =
  templateTermsRename (fun index => first (second index)) inputs.
Proof.
  induction inputs as [|input inputs ih]; intros first second; cbn.
  - reflexivity.
  - rewrite templateTermRename_comp. f_equal. exact (ih first second).
Qed.

Lemma templateUpRenaming_comp : forall first second index,
  templateUpRenaming first (templateUpRenaming second index) =
  templateUpRenaming (fun outer => first (second outer)) index.
Proof.
  intros first second [|index]; reflexivity.
Qed.

Lemma templateFormulaRename_comp : forall input first second,
  templateFormulaRename first (templateFormulaRename second input) =
  templateFormulaRename (fun index => first (second index)) input.
Proof.
  induction input; intros first second; cbn.
  - now rewrite !templateTermRename_comp.
  - reflexivity.
  - now rewrite IHinput1, IHinput2.
  - now rewrite IHinput1, IHinput2.
  - now rewrite IHinput1, IHinput2.
  - rewrite IHinput. f_equal.
    apply templateFormulaRename_ext.
    apply templateUpRenaming_comp.
  - rewrite IHinput. f_equal.
    apply templateFormulaRename_ext.
    apply templateUpRenaming_comp.
  - now rewrite templateTermsRename_comp.
Qed.

Lemma templateTermSubst_id : forall input,
  templateTermSubst (fun index => ttVar index) input = input.
Proof.
  induction input; cbn; try reflexivity.
  - now rewrite IHinput.
  - now rewrite IHinput1, IHinput2.
  - now rewrite IHinput1, IHinput2.
Qed.

Lemma templateTermsSubst_id : forall inputs,
  templateTermsSubst (fun index => ttVar index) inputs = inputs.
Proof.
  induction inputs as [|input inputs ih]; cbn; [reflexivity |].
  rewrite templateTermSubst_id. f_equal. exact ih.
Qed.

Lemma templateFormulaSubst_id : forall input,
  templateFormulaSubst (fun index => ttVar index) input = input.
Proof.
  induction input; cbn.
  - now rewrite !templateTermSubst_id.
  - reflexivity.
  - now rewrite IHinput1, IHinput2.
  - now rewrite IHinput1, IHinput2.
  - now rewrite IHinput1, IHinput2.
  - rewrite <- IHinput at 2. f_equal.
    apply templateFormulaSubst_ext.
    intros [|index]; cbn; [reflexivity |].
    reflexivity.
  - rewrite <- IHinput at 2. f_equal.
    apply templateFormulaSubst_ext.
    intros [|index]; cbn; [reflexivity |].
    reflexivity.
  - now rewrite templateTermsSubst_id.
Qed.

Lemma templateTermSubst_variables : forall input renaming,
  templateTermSubst (fun index => ttVar (renaming index)) input =
  templateTermRename renaming input.
Proof.
  induction input; intros renaming; cbn; try reflexivity.
  - now rewrite IHinput.
  - now rewrite IHinput1, IHinput2.
  - now rewrite IHinput1, IHinput2.
Qed.

Lemma templateTermsSubst_variables : forall inputs renaming,
  templateTermsSubst (fun index => ttVar (renaming index)) inputs =
  templateTermsRename renaming inputs.
Proof.
  induction inputs as [|input inputs ih]; intros renaming; cbn.
  - reflexivity.
  - rewrite templateTermSubst_variables. f_equal. exact (ih renaming).
Qed.

Lemma templateFormulaSubst_variables : forall input renaming,
  templateFormulaSubst (fun index => ttVar (renaming index)) input =
  templateFormulaRename renaming input.
Proof.
  induction input; intros renaming; cbn.
  - now rewrite !templateTermSubst_variables.
  - reflexivity.
  - now rewrite IHinput1, IHinput2.
  - now rewrite IHinput1, IHinput2.
  - now rewrite IHinput1, IHinput2.
  - f_equal.
    rewrite <- (IHinput (templateUpRenaming renaming)).
    apply templateFormulaSubst_ext.
    intros [|index]; reflexivity.
  - f_equal.
    rewrite <- (IHinput (templateUpRenaming renaming)).
    apply templateFormulaSubst_ext.
    intros [|index]; reflexivity.
  - now rewrite templateTermsSubst_variables.
Qed.

Lemma templateOpaqueRename_arity : forall predicate arguments renaming,
  length
    (match templateFormulaRename renaming
      (tfOpaque predicate arguments) with
     | tfOpaque _ renamedArguments => renamedArguments
     | _ => []
     end) = length arguments.
Proof.
  intros. cbn [templateFormulaRename templateTermsRename].
  apply length_map.
Qed.

Lemma templateOpaqueSubst_arity : forall predicate arguments substitution,
  length
    (match templateFormulaSubst substitution
      (tfOpaque predicate arguments) with
     | tfOpaque _ substitutedArguments => substitutedArguments
     | _ => []
     end) = length arguments.
Proof.
  intros. cbn [templateFormulaSubst templateTermsSubst].
  apply length_map.
Qed.

(** ------------------------------------------------------------------
    Embedding ordinary PA syntax.

    The image contains neither named carrier parameters nor opaque predicate
    applications.  These homomorphisms let a future compiler freely mix
    fixed standard PA fragments with genuinely dynamic template fragments.
*)

Fixpoint embedPATerm (input : term) : TemplateTerm :=
  match input with
  | tVar index => ttVar index
  | tZero => ttZero
  | tSucc child => ttSucc (embedPATerm child)
  | tAdd lhs rhs => ttAdd (embedPATerm lhs) (embedPATerm rhs)
  | tMul lhs rhs => ttMul (embedPATerm lhs) (embedPATerm rhs)
  end.

Fixpoint embedPAFormula (input : formula) : TemplateFormula :=
  match input with
  | pEq lhs rhs => tfEq (embedPATerm lhs) (embedPATerm rhs)
  | pBot => tfBot
  | pImp lhs rhs => tfImp (embedPAFormula lhs) (embedPAFormula rhs)
  | pAnd lhs rhs => tfAnd (embedPAFormula lhs) (embedPAFormula rhs)
  | pOr lhs rhs => tfOr (embedPAFormula lhs) (embedPAFormula rhs)
  | pAll body => tfAll (embedPAFormula body)
  | pEx body => tfEx (embedPAFormula body)
  end.

Definition embedPAContext (context : list formula) : TemplateContext :=
  map embedPAFormula context.

Lemma embedPATerm_rename : forall input renaming,
  embedPATerm (Term.rename renaming input) =
  templateTermRename renaming (embedPATerm input).
Proof.
  induction input; intros renaming; cbn; try reflexivity.
  - now rewrite IHinput.
  - now rewrite IHinput1, IHinput2.
  - now rewrite IHinput1, IHinput2.
Qed.

Lemma embedPATerm_upSubst : forall substitution index,
  embedPATerm (Term.upSubst substitution index) =
  templateTermUpSubst
    (fun outer => embedPATerm (substitution outer)) index.
Proof.
  intros substitution [|index]; cbn; [reflexivity |].
  apply embedPATerm_rename.
Qed.

Lemma embedPATerm_subst : forall input substitution,
  embedPATerm (Term.subst substitution input) =
  templateTermSubst (fun index => embedPATerm (substitution index))
    (embedPATerm input).
Proof.
  induction input; intros substitution; cbn; try reflexivity.
  - now rewrite IHinput.
  - now rewrite IHinput1, IHinput2.
  - now rewrite IHinput1, IHinput2.
Qed.

Lemma embedPAFormula_rename : forall input renaming,
  embedPAFormula (Formula.rename renaming input) =
  templateFormulaRename renaming (embedPAFormula input).
Proof.
  induction input; intros renaming; cbn.
  - now rewrite !embedPATerm_rename.
  - reflexivity.
  - now rewrite IHinput1, IHinput2.
  - now rewrite IHinput1, IHinput2.
  - now rewrite IHinput1, IHinput2.
  - now rewrite IHinput.
  - now rewrite IHinput.
Qed.

Lemma embedPAFormula_subst : forall input substitution,
  embedPAFormula (Formula.subst substitution input) =
  templateFormulaSubst
    (fun index => embedPATerm (substitution index))
    (embedPAFormula input).
Proof.
  induction input; intros substitution; cbn.
  - now rewrite !embedPATerm_subst.
  - reflexivity.
  - now rewrite IHinput1, IHinput2.
  - now rewrite IHinput1, IHinput2.
  - now rewrite IHinput1, IHinput2.
  - rewrite IHinput. f_equal.
    apply templateFormulaSubst_ext.
    intro index. apply embedPATerm_upSubst.
  - rewrite IHinput. f_equal.
    apply templateFormulaSubst_ext.
    intro index. apply embedPATerm_upSubst.
Qed.

Lemma embedPAFormula_instTerm : forall body replacement,
  embedPAFormula
    (Formula.subst (Formula.instTerm replacement) body) =
  templateFormulaOpen (embedPATerm replacement) (embedPAFormula body).
Proof.
  intros body replacement.
  rewrite embedPAFormula_subst.
  unfold templateFormulaOpen.
  apply templateFormulaSubst_ext.
  intros [|index]; reflexivity.
Qed.

Lemma embedPAContext_shift : forall context,
  embedPAContext (map (Formula.rename S) context) =
  templateContextShift (embedPAContext context).
Proof.
  intros context.
  unfold embedPAContext, templateContextShift, templateContextRename.
  rewrite !map_map.
  apply map_ext. intro input.
  apply embedPAFormula_rename.
Qed.

Lemma embedPAContext_subst : forall context substitution,
  embedPAContext (map (Formula.subst substitution) context) =
  templateContextSubst
    (fun index => embedPATerm (substitution index))
    (embedPAContext context).
Proof.
  intros context substitution.
  unfold embedPAContext, templateContextSubst.
  rewrite !map_map.
  apply map_ext. intro input.
  apply embedPAFormula_subst.
Qed.

(** ------------------------------------------------------------------
    Unindexed natural-deduction proof templates.

    Constructor parameters follow [CodedProof.RawProof] exactly.  In
    particular, the assumption constructor omits its membership witness;
    validity reconstructs that side condition. *)

Inductive TemplateRawProof : Type :=
| trpAss : TemplateContext -> TemplateFormula -> TemplateRawProof
| trpImpI : TemplateContext -> TemplateFormula -> TemplateFormula ->
    TemplateRawProof -> TemplateRawProof
| trpImpE : TemplateContext -> TemplateFormula -> TemplateFormula ->
    TemplateRawProof -> TemplateRawProof -> TemplateRawProof
| trpBotE : TemplateContext -> TemplateFormula ->
    TemplateRawProof -> TemplateRawProof
| trpLem : TemplateContext -> TemplateFormula -> TemplateRawProof
| trpAndI : TemplateContext -> TemplateFormula -> TemplateFormula ->
    TemplateRawProof -> TemplateRawProof -> TemplateRawProof
| trpAndE1 : TemplateContext -> TemplateFormula -> TemplateFormula ->
    TemplateRawProof -> TemplateRawProof
| trpAndE2 : TemplateContext -> TemplateFormula -> TemplateFormula ->
    TemplateRawProof -> TemplateRawProof
| trpOrI1 : TemplateContext -> TemplateFormula -> TemplateFormula ->
    TemplateRawProof -> TemplateRawProof
| trpOrI2 : TemplateContext -> TemplateFormula -> TemplateFormula ->
    TemplateRawProof -> TemplateRawProof
| trpOrE : TemplateContext -> TemplateFormula -> TemplateFormula ->
    TemplateFormula -> TemplateRawProof -> TemplateRawProof ->
    TemplateRawProof -> TemplateRawProof
| trpAllI : TemplateContext -> TemplateFormula ->
    TemplateRawProof -> TemplateRawProof
| trpAllE : TemplateContext -> TemplateFormula -> TemplateTerm ->
    TemplateRawProof -> TemplateRawProof
| trpExI : TemplateContext -> TemplateFormula -> TemplateTerm ->
    TemplateRawProof -> TemplateRawProof
| trpExE : TemplateContext -> TemplateFormula -> TemplateFormula ->
    TemplateRawProof -> TemplateRawProof -> TemplateRawProof
| trpEqRefl : TemplateContext -> TemplateTerm -> TemplateRawProof
| trpEqElim : TemplateContext -> TemplateTerm -> TemplateTerm ->
    TemplateFormula -> TemplateRawProof -> TemplateRawProof ->
    TemplateRawProof.

Definition templateRawContext (derivation : TemplateRawProof)
    : TemplateContext :=
  match derivation with
  | trpAss context _
  | trpImpI context _ _ _
  | trpImpE context _ _ _ _
  | trpBotE context _ _
  | trpLem context _
  | trpAndI context _ _ _ _
  | trpAndE1 context _ _ _
  | trpAndE2 context _ _ _
  | trpOrI1 context _ _ _
  | trpOrI2 context _ _ _
  | trpOrE context _ _ _ _ _ _
  | trpAllI context _ _
  | trpAllE context _ _ _
  | trpExI context _ _ _
  | trpExE context _ _ _ _
  | trpEqRefl context _
  | trpEqElim context _ _ _ _ _ => context
  end.

Definition templateRawConclusion (derivation : TemplateRawProof)
    : TemplateFormula :=
  match derivation with
  | trpAss _ formula => formula
  | trpImpI _ antecedent consequent _ => tfImp antecedent consequent
  | trpImpE _ _ consequent _ _ => consequent
  | trpBotE _ formula _ => formula
  | trpLem _ formula => tfOr formula (tfImp formula tfBot)
  | trpAndI _ lhs rhs _ _ => tfAnd lhs rhs
  | trpAndE1 _ lhs _ _ => lhs
  | trpAndE2 _ _ rhs _ => rhs
  | trpOrI1 _ lhs rhs _ => tfOr lhs rhs
  | trpOrI2 _ lhs rhs _ => tfOr lhs rhs
  | trpOrE _ _ _ conclusion _ _ _ => conclusion
  | trpAllI _ body _ => tfAll body
  | trpAllE _ body replacement _ =>
      templateFormulaOpen replacement body
  | trpExI _ body _ _ => tfEx body
  | trpExE _ _ conclusion _ _ => conclusion
  | trpEqRefl _ witness => tfEq witness witness
  | trpEqElim _ _ target motive _ _ =>
      templateFormulaOpen target motive
  end.

(** Every clause validates recursive children and their complete endpoints.
    This is the direct declarative analogue of [CodedProof.RawProofValid]. *)
Fixpoint TemplateRawProofValid (derivation : TemplateRawProof) : Prop :=
  match derivation with
  | trpAss context formula => In formula context
  | trpImpI context antecedent consequent child =>
      TemplateRawProofValid child /\
      templateRawContext child = antecedent :: context /\
      templateRawConclusion child = consequent
  | trpImpE context antecedent consequent implicationChild antecedentChild =>
      TemplateRawProofValid implicationChild /\
      templateRawContext implicationChild = context /\
      templateRawConclusion implicationChild = tfImp antecedent consequent /\
      TemplateRawProofValid antecedentChild /\
      templateRawContext antecedentChild = context /\
      templateRawConclusion antecedentChild = antecedent
  | trpBotE context _ bottomChild =>
      TemplateRawProofValid bottomChild /\
      templateRawContext bottomChild = context /\
      templateRawConclusion bottomChild = tfBot
  | trpLem _ _ => True
  | trpAndI context lhs rhs leftChild rightChild =>
      TemplateRawProofValid leftChild /\
      templateRawContext leftChild = context /\
      templateRawConclusion leftChild = lhs /\
      TemplateRawProofValid rightChild /\
      templateRawContext rightChild = context /\
      templateRawConclusion rightChild = rhs
  | trpAndE1 context lhs rhs child
  | trpAndE2 context lhs rhs child =>
      TemplateRawProofValid child /\
      templateRawContext child = context /\
      templateRawConclusion child = tfAnd lhs rhs
  | trpOrI1 context lhs _ child =>
      TemplateRawProofValid child /\
      templateRawContext child = context /\
      templateRawConclusion child = lhs
  | trpOrI2 context _ rhs child =>
      TemplateRawProofValid child /\
      templateRawContext child = context /\
      templateRawConclusion child = rhs
  | trpOrE context lhs rhs conclusion disjunctionChild
      leftChild rightChild =>
      TemplateRawProofValid disjunctionChild /\
      templateRawContext disjunctionChild = context /\
      templateRawConclusion disjunctionChild = tfOr lhs rhs /\
      TemplateRawProofValid leftChild /\
      templateRawContext leftChild = lhs :: context /\
      templateRawConclusion leftChild = conclusion /\
      TemplateRawProofValid rightChild /\
      templateRawContext rightChild = rhs :: context /\
      templateRawConclusion rightChild = conclusion
  | trpAllI context body child =>
      TemplateRawProofValid child /\
      templateRawContext child = templateContextShift context /\
      templateRawConclusion child = body
  | trpAllE context body _ child =>
      TemplateRawProofValid child /\
      templateRawContext child = context /\
      templateRawConclusion child = tfAll body
  | trpExI context body replacement child =>
      TemplateRawProofValid child /\
      templateRawContext child = context /\
      templateRawConclusion child = templateFormulaOpen replacement body
  | trpExE context body conclusion existentialChild bodyChild =>
      TemplateRawProofValid existentialChild /\
      templateRawContext existentialChild = context /\
      templateRawConclusion existentialChild = tfEx body /\
      TemplateRawProofValid bodyChild /\
      templateRawContext bodyChild = body :: templateContextShift context /\
      templateRawConclusion bodyChild = templateFormulaRename S conclusion
  | trpEqRefl _ _ => True
  | trpEqElim context source target motive equalityChild motiveChild =>
      TemplateRawProofValid equalityChild /\
      templateRawContext equalityChild = context /\
      templateRawConclusion equalityChild = tfEq source target /\
      TemplateRawProofValid motiveChild /\
      templateRawContext motiveChild = context /\
      templateRawConclusion motiveChild =
        templateFormulaOpen source motive
  end.

(** A convenient endpoint-packaged judgement. *)
Definition TemplateRawDerives (context : TemplateContext)
    (conclusion : TemplateFormula) (derivation : TemplateRawProof) : Prop :=
  TemplateRawProofValid derivation /\
  templateRawContext derivation = context /\
  templateRawConclusion derivation = conclusion.

(** The assumption and reflexivity leaves demonstrate that the declarative
    relation is directly usable without an executable equality checker. *)
Lemma templateRawDerives_assumption : forall context formula,
  In formula context ->
  TemplateRawDerives context formula (trpAss context formula).
Proof.
  intros context formula hin.
  unfold TemplateRawDerives. cbn. repeat split; assumption.
Qed.

Lemma templateRawDerives_eqRefl : forall context witness,
  TemplateRawDerives context (tfEq witness witness)
    (trpEqRefl context witness).
Proof.
  intros. unfold TemplateRawDerives. cbn. repeat split; reflexivity.
Qed.

End PABoundedRawCodedTemplateSyntax.
