(**
  Abstract one named carrier parameter into an ordinary PA variable.

  Template parameters are deliberately opaque to ordinary de Bruijn
  substitution.  That is the right default for direct compilation, but a
  PA-internal uniformity argument needs the converse operation: select one
  parameter, replace it by a fresh variable, universally quantify that
  variable once, and later open the body at an arbitrary carrier term.

  [templateTermAbstractParameterAt] and
  [templateFormulaAbstractParameterAt] perform this operation beneath an
  explicit binder depth.  Existing variables at or above the insertion
  point are shifted, so no variable is captured.  Descending under a
  quantifier increments the insertion depth in the usual de Bruijn style.

  The final theorems prove the exact round trip needed by represented
  universal elimination: opening the abstracted formula with the selected
  named parameter recovers the original template literally, not merely up
  to semantics or alpha-equivalence.
*)

From Stdlib Require Import List Arith Bool.
From PAHF Require Import PAHF.
From BoundedPAConsistency Require Import
  RawCodedTemplateSyntax
  RawCodedTemplateStructuralTranslation.

Import ListNotations.

Module PABoundedRawCodedTemplateParameterAbstraction.

Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateStructuralTranslation.

Import PA.

(** Insert a variable at [depth].  Variables already at or above that depth
    are shifted by [templateShiftRenamingAt]; the selected named parameter
    becomes the freshly inserted variable. *)
Fixpoint templateTermAbstractParameterAt
    (name : TemplateParameterName) (depth : nat)
    (input : TemplateTerm) : TemplateTerm :=
  match input with
  | ttVar index => ttVar (templateShiftRenamingAt depth index)
  | ttParameter current =>
      if Nat.eqb current name then ttVar depth else ttParameter current
  | ttZero => ttZero
  | ttSucc child =>
      ttSucc (templateTermAbstractParameterAt name depth child)
  | ttAdd lhs rhs =>
      ttAdd
        (templateTermAbstractParameterAt name depth lhs)
        (templateTermAbstractParameterAt name depth rhs)
  | ttMul lhs rhs =>
      ttMul
        (templateTermAbstractParameterAt name depth lhs)
        (templateTermAbstractParameterAt name depth rhs)
  end.

Definition templateTermsAbstractParameterAt
    (name : TemplateParameterName) (depth : nat)
    (inputs : list TemplateTerm) : list TemplateTerm :=
  map (templateTermAbstractParameterAt name depth) inputs.

Fixpoint templateFormulaAbstractParameterAt
    (name : TemplateParameterName) (depth : nat)
    (input : TemplateFormula) : TemplateFormula :=
  match input with
  | tfEq lhs rhs =>
      tfEq
        (templateTermAbstractParameterAt name depth lhs)
        (templateTermAbstractParameterAt name depth rhs)
  | tfBot => tfBot
  | tfImp lhs rhs =>
      tfImp
        (templateFormulaAbstractParameterAt name depth lhs)
        (templateFormulaAbstractParameterAt name depth rhs)
  | tfAnd lhs rhs =>
      tfAnd
        (templateFormulaAbstractParameterAt name depth lhs)
        (templateFormulaAbstractParameterAt name depth rhs)
  | tfOr lhs rhs =>
      tfOr
        (templateFormulaAbstractParameterAt name depth lhs)
        (templateFormulaAbstractParameterAt name depth rhs)
  | tfAll body =>
      tfAll (templateFormulaAbstractParameterAt name (S depth) body)
  | tfEx body =>
      tfEx (templateFormulaAbstractParameterAt name (S depth) body)
  | tfOpaque predicate arguments =>
      tfOpaque predicate
        (templateTermsAbstractParameterAt name depth arguments)
  end.

Definition templateFormulaAbstractParameter
    (name : TemplateParameterName) (input : TemplateFormula)
    : TemplateFormula :=
  templateFormulaAbstractParameterAt name 0 input.

(** Opening cancels the shift of an old variable.  This pointwise identity
    is the variable case of the round-trip proof below. *)
Lemma templateOpeningSubstAt_after_shift : forall depth replacement index,
  templateOpeningSubstAt depth replacement
    (templateShiftRenamingAt depth index) = ttVar index.
Proof.
  induction depth as [|depth ih]; intros replacement index.
  - reflexivity.
  - destruct index as [|index]; cbn
      [templateOpeningSubstAt templateShiftRenamingAt
       templateTermUpSubst].
    + reflexivity.
    + now rewrite ih.
Qed.

(** Named parameters are closed with respect to de Bruijn renaming.  Hence
    opening at any depth sends the newly inserted variable back to the
    selected parameter without an additional shift side condition. *)
Lemma templateOpeningSubstAt_parameter_at : forall name depth,
  templateOpeningSubstAt depth (ttParameter name) depth =
  ttParameter name.
Proof.
  intros name depth. induction depth as [|depth ih].
  - reflexivity.
  - cbn [templateOpeningSubstAt templateTermUpSubst].
    now rewrite ih.
Qed.

Theorem templateTermAbstractParameterAt_open : forall name depth input,
  templateTermSubst
    (templateOpeningSubstAt depth (ttParameter name))
    (templateTermAbstractParameterAt name depth input) = input.
Proof.
  intros name depth input.
  induction input as
      [index | current | | child ih | lhs ihlhs rhs ihrhs |
       lhs ihlhs rhs ihrhs]; cbn
      [templateTermAbstractParameterAt templateTermSubst].
  - apply templateOpeningSubstAt_after_shift.
  - destruct (Nat.eqb current name) eqn:heq.
    + apply Nat.eqb_eq in heq. subst current.
      apply templateOpeningSubstAt_parameter_at.
    + reflexivity.
  - reflexivity.
  - f_equal. exact ih.
  - f_equal; assumption.
  - f_equal; assumption.
Qed.

Lemma templateTermsAbstractParameterAt_open : forall name depth inputs,
  templateTermsSubst
    (templateOpeningSubstAt depth (ttParameter name))
    (templateTermsAbstractParameterAt name depth inputs) = inputs.
Proof.
  intros name depth inputs.
  unfold templateTermsSubst, templateTermsAbstractParameterAt.
  rewrite map_map.
  induction inputs as [|input inputs ih]; cbn.
  - reflexivity.
  - f_equal.
    + apply templateTermAbstractParameterAt_open.
    + exact ih.
Qed.

Theorem templateFormulaAbstractParameterAt_open : forall name depth input,
  templateFormulaSubst
    (templateOpeningSubstAt depth (ttParameter name))
    (templateFormulaAbstractParameterAt name depth input) = input.
Proof.
  intros name depth input. revert depth.
  induction input as
      [lhs rhs | | lhs ihlhs rhs ihrhs | lhs ihlhs rhs ihrhs |
       lhs ihlhs rhs ihrhs | body ihbody | body ihbody |
       predicate arguments]; intro depth;
    cbn [templateFormulaAbstractParameterAt templateFormulaSubst
      templateTermSubst templateTermsSubst].
  - now rewrite !templateTermAbstractParameterAt_open.
  - reflexivity.
  - now rewrite ihlhs, ihrhs.
  - now rewrite ihlhs, ihrhs.
  - now rewrite ihlhs, ihrhs.
  - f_equal. exact (ihbody (S depth)).
  - f_equal. exact (ihbody (S depth)).
  - f_equal. apply templateTermsAbstractParameterAt_open.
Qed.

(** Root-level spelling used by a universally quantified PA source. *)
Corollary templateFormulaAbstractParameter_open : forall name input,
  templateFormulaOpen (ttParameter name)
    (templateFormulaAbstractParameter name input) = input.
Proof.
  intros name input.
  unfold templateFormulaOpen, templateFormulaAbstractParameter.
  change
    (templateFormulaSubst
      (templateOpeningSubstAt 0 (ttParameter name))
      (templateFormulaAbstractParameterAt name 0 input) = input).
  apply templateFormulaAbstractParameterAt_open.
Qed.

(** ------------------------------------------------------------------
    Direct capture-avoiding replacement of a named parameter.

    The abstract/open construction is the proof-producing interface, but
    concrete clients need a transparent syntax normal form.  At binder depth
    [depth], an occurrence of the selected parameter is replaced by exactly
    the lifted term that [templateOpeningSubstAt] assigns to the freshly
    inserted variable.  Ordinary variables are left unchanged because the
    insertion performed by abstraction is cancelled by opening. *)

Fixpoint templateTermReplaceParameterAt
    (name : TemplateParameterName) (depth : nat)
    (replacement : TemplateTerm) (input : TemplateTerm) : TemplateTerm :=
  match input with
  | ttVar index => ttVar index
  | ttParameter current =>
      if Nat.eqb current name
      then templateOpeningSubstAt depth replacement depth
      else ttParameter current
  | ttZero => ttZero
  | ttSucc child =>
      ttSucc (templateTermReplaceParameterAt name depth replacement child)
  | ttAdd lhs rhs =>
      ttAdd
        (templateTermReplaceParameterAt name depth replacement lhs)
        (templateTermReplaceParameterAt name depth replacement rhs)
  | ttMul lhs rhs =>
      ttMul
        (templateTermReplaceParameterAt name depth replacement lhs)
        (templateTermReplaceParameterAt name depth replacement rhs)
  end.

Definition templateTermsReplaceParameterAt
    (name : TemplateParameterName) (depth : nat)
    (replacement : TemplateTerm) (inputs : list TemplateTerm)
    : list TemplateTerm :=
  map (templateTermReplaceParameterAt name depth replacement) inputs.

Fixpoint templateFormulaReplaceParameterAt
    (name : TemplateParameterName) (depth : nat)
    (replacement : TemplateTerm) (input : TemplateFormula)
    : TemplateFormula :=
  match input with
  | tfEq lhs rhs =>
      tfEq
        (templateTermReplaceParameterAt name depth replacement lhs)
        (templateTermReplaceParameterAt name depth replacement rhs)
  | tfBot => tfBot
  | tfImp lhs rhs =>
      tfImp
        (templateFormulaReplaceParameterAt name depth replacement lhs)
        (templateFormulaReplaceParameterAt name depth replacement rhs)
  | tfAnd lhs rhs =>
      tfAnd
        (templateFormulaReplaceParameterAt name depth replacement lhs)
        (templateFormulaReplaceParameterAt name depth replacement rhs)
  | tfOr lhs rhs =>
      tfOr
        (templateFormulaReplaceParameterAt name depth replacement lhs)
        (templateFormulaReplaceParameterAt name depth replacement rhs)
  | tfAll body =>
      tfAll
        (templateFormulaReplaceParameterAt name (S depth) replacement body)
  | tfEx body =>
      tfEx
        (templateFormulaReplaceParameterAt name (S depth) replacement body)
  | tfOpaque predicate arguments =>
      tfOpaque predicate
        (templateTermsReplaceParameterAt name depth replacement arguments)
  end.

Definition templateFormulaReplaceParameter
    (name : TemplateParameterName) (replacement : TemplateTerm)
    (input : TemplateFormula) : TemplateFormula :=
  templateFormulaReplaceParameterAt name 0 replacement input.

Theorem templateTermAbstractParameterAt_open_as_replace : forall
    name depth replacement input,
  templateTermSubst (templateOpeningSubstAt depth replacement)
    (templateTermAbstractParameterAt name depth input) =
  templateTermReplaceParameterAt name depth replacement input.
Proof.
  intros name depth replacement input.
  induction input as
      [index | current | | child ih | lhs ihlhs rhs ihrhs |
       lhs ihlhs rhs ihrhs]; cbn
      [templateTermAbstractParameterAt templateTermSubst
       templateTermReplaceParameterAt].
  - apply templateOpeningSubstAt_after_shift.
  - destruct (Nat.eqb current name); reflexivity.
  - reflexivity.
  - now rewrite ih.
  - now rewrite ihlhs, ihrhs.
  - now rewrite ihlhs, ihrhs.
Qed.

Lemma templateTermsAbstractParameterAt_open_as_replace : forall
    name depth replacement inputs,
  templateTermsSubst (templateOpeningSubstAt depth replacement)
    (templateTermsAbstractParameterAt name depth inputs) =
  templateTermsReplaceParameterAt name depth replacement inputs.
Proof.
  intros name depth replacement inputs.
  unfold templateTermsSubst, templateTermsAbstractParameterAt,
    templateTermsReplaceParameterAt.
  rewrite map_map.
  induction inputs as [|input inputs ih]; cbn.
  - reflexivity.
  - f_equal.
    + apply templateTermAbstractParameterAt_open_as_replace.
    + exact ih.
Qed.

Theorem templateFormulaAbstractParameterAt_open_as_replace : forall
    name depth replacement input,
  templateFormulaSubst (templateOpeningSubstAt depth replacement)
    (templateFormulaAbstractParameterAt name depth input) =
  templateFormulaReplaceParameterAt name depth replacement input.
Proof.
  intros name depth replacement input. revert depth.
  induction input as
      [lhs rhs | | lhs ihlhs rhs ihrhs | lhs ihlhs rhs ihrhs |
       lhs ihlhs rhs ihrhs | body ihbody | body ihbody |
       predicate arguments]; intro depth;
    cbn [templateFormulaAbstractParameterAt templateFormulaSubst
      templateFormulaReplaceParameterAt templateTermSubst
      templateTermsSubst].
  - now rewrite !templateTermAbstractParameterAt_open_as_replace.
  - reflexivity.
  - now rewrite ihlhs, ihrhs.
  - now rewrite ihlhs, ihrhs.
  - now rewrite ihlhs, ihrhs.
  - f_equal. exact (ihbody (S depth)).
  - f_equal. exact (ihbody (S depth)).
  - f_equal. apply templateTermsAbstractParameterAt_open_as_replace.
Qed.

(** Root-level normalization used by finite represented parameter transport. *)
Corollary templateFormulaAbstractParameter_open_as_replace : forall
    name replacement input,
  templateFormulaOpen replacement
    (templateFormulaAbstractParameter name input) =
  templateFormulaReplaceParameter name replacement input.
Proof.
  intros name replacement input.
  unfold templateFormulaOpen, templateFormulaAbstractParameter,
    templateFormulaReplaceParameter.
  change
    (templateFormulaSubst (templateOpeningSubstAt 0 replacement)
      (templateFormulaAbstractParameterAt name 0 input) =
     templateFormulaReplaceParameterAt name 0 replacement input).
  apply templateFormulaAbstractParameterAt_open_as_replace.
Qed.

(** ------------------------------------------------------------------
    Reification of the ordinary PA fragment.

    After every intended carrier parameter has been abstracted, the source
    must be a genuine PA formula before model completeness and universal
    elimination can be applied.  These partial functions make that boundary
    explicit: an unabstracted named parameter or an opaque predicate causes
    failure instead of being silently assigned an arithmetic meaning. *)

Fixpoint templateTermAsPATerm (input : TemplateTerm) : option term :=
  match input with
  | ttVar index => Some (tVar index)
  | ttParameter _ => None
  | ttZero => Some tZero
  | ttSucc child =>
      match templateTermAsPATerm child with
      | Some output => Some (tSucc output)
      | None => None
      end
  | ttAdd lhs rhs =>
      match templateTermAsPATerm lhs, templateTermAsPATerm rhs with
      | Some leftOutput, Some rightOutput =>
          Some (tAdd leftOutput rightOutput)
      | _, _ => None
      end
  | ttMul lhs rhs =>
      match templateTermAsPATerm lhs, templateTermAsPATerm rhs with
      | Some leftOutput, Some rightOutput =>
          Some (tMul leftOutput rightOutput)
      | _, _ => None
      end
  end.

Fixpoint templateFormulaAsPAFormula
    (input : TemplateFormula) : option formula :=
  match input with
  | tfEq lhs rhs =>
      match templateTermAsPATerm lhs, templateTermAsPATerm rhs with
      | Some leftOutput, Some rightOutput =>
          Some (pEq leftOutput rightOutput)
      | _, _ => None
      end
  | tfBot => Some pBot
  | tfImp lhs rhs =>
      match templateFormulaAsPAFormula lhs,
          templateFormulaAsPAFormula rhs with
      | Some leftOutput, Some rightOutput =>
          Some (pImp leftOutput rightOutput)
      | _, _ => None
      end
  | tfAnd lhs rhs =>
      match templateFormulaAsPAFormula lhs,
          templateFormulaAsPAFormula rhs with
      | Some leftOutput, Some rightOutput =>
          Some (pAnd leftOutput rightOutput)
      | _, _ => None
      end
  | tfOr lhs rhs =>
      match templateFormulaAsPAFormula lhs,
          templateFormulaAsPAFormula rhs with
      | Some leftOutput, Some rightOutput =>
          Some (pOr leftOutput rightOutput)
      | _, _ => None
      end
  | tfAll body =>
      match templateFormulaAsPAFormula body with
      | Some output => Some (pAll output)
      | None => None
      end
  | tfEx body =>
      match templateFormulaAsPAFormula body with
      | Some output => Some (pEx output)
      | None => None
      end
  | tfOpaque _ _ => None
  end.

Theorem templateTermAsPATerm_sound : forall input output,
  templateTermAsPATerm input = Some output ->
  embedPATerm output = input.
Proof.
  induction input as
      [index | name | | child ih | lhs ihlhs rhs ihrhs |
       lhs ihlhs rhs ihrhs]; intros output houtput;
    cbn [templateTermAsPATerm] in houtput.
  - inversion houtput. reflexivity.
  - discriminate houtput.
  - inversion houtput. reflexivity.
  - destruct (templateTermAsPATerm child) as [childOutput|]
      eqn:hchild; [|discriminate houtput].
    inversion houtput; subst output. cbn [embedPATerm].
    now rewrite (ih childOutput eq_refl).
  - destruct (templateTermAsPATerm lhs) as [leftOutput|]
      eqn:hleft; [|discriminate houtput].
    destruct (templateTermAsPATerm rhs) as [rightOutput|]
      eqn:hright; [|discriminate houtput].
    inversion houtput; subst output. cbn [embedPATerm].
    now rewrite (ihlhs leftOutput eq_refl),
      (ihrhs rightOutput eq_refl).
  - destruct (templateTermAsPATerm lhs) as [leftOutput|]
      eqn:hleft; [|discriminate houtput].
    destruct (templateTermAsPATerm rhs) as [rightOutput|]
      eqn:hright; [|discriminate houtput].
    inversion houtput; subst output. cbn [embedPATerm].
    now rewrite (ihlhs leftOutput eq_refl),
      (ihrhs rightOutput eq_refl).
Qed.

Theorem templateFormulaAsPAFormula_sound : forall input output,
  templateFormulaAsPAFormula input = Some output ->
  embedPAFormula output = input.
Proof.
  induction input as
      [lhs rhs | | lhs ihlhs rhs ihrhs | lhs ihlhs rhs ihrhs |
       lhs ihlhs rhs ihrhs | body ihbody | body ihbody |
       predicate arguments]; intros output houtput;
    cbn [templateFormulaAsPAFormula] in houtput.
  - destruct (templateTermAsPATerm lhs) as [leftOutput|]
      eqn:hleft; [|discriminate houtput].
    destruct (templateTermAsPATerm rhs) as [rightOutput|]
      eqn:hright; [|discriminate houtput].
    inversion houtput; subst output. cbn [embedPAFormula].
    now rewrite (templateTermAsPATerm_sound lhs leftOutput hleft),
      (templateTermAsPATerm_sound rhs rightOutput hright).
  - inversion houtput. reflexivity.
  - destruct (templateFormulaAsPAFormula lhs) as [leftOutput|]
      eqn:hleft; [|discriminate houtput].
    destruct (templateFormulaAsPAFormula rhs) as [rightOutput|]
      eqn:hright; [|discriminate houtput].
    inversion houtput; subst output. cbn [embedPAFormula].
    now rewrite (ihlhs leftOutput eq_refl),
      (ihrhs rightOutput eq_refl).
  - destruct (templateFormulaAsPAFormula lhs) as [leftOutput|]
      eqn:hleft; [|discriminate houtput].
    destruct (templateFormulaAsPAFormula rhs) as [rightOutput|]
      eqn:hright; [|discriminate houtput].
    inversion houtput; subst output. cbn [embedPAFormula].
    now rewrite (ihlhs leftOutput eq_refl),
      (ihrhs rightOutput eq_refl).
  - destruct (templateFormulaAsPAFormula lhs) as [leftOutput|]
      eqn:hleft; [|discriminate houtput].
    destruct (templateFormulaAsPAFormula rhs) as [rightOutput|]
      eqn:hright; [|discriminate houtput].
    inversion houtput; subst output. cbn [embedPAFormula].
    now rewrite (ihlhs leftOutput eq_refl),
      (ihrhs rightOutput eq_refl).
  - destruct (templateFormulaAsPAFormula body) as [bodyOutput|]
      eqn:hbody; [|discriminate houtput].
    inversion houtput; subst output. cbn [embedPAFormula].
    now rewrite (ihbody bodyOutput eq_refl).
  - destruct (templateFormulaAsPAFormula body) as [bodyOutput|]
      eqn:hbody; [|discriminate houtput].
    inversion houtput; subst output. cbn [embedPAFormula].
    now rewrite (ihbody bodyOutput eq_refl).
  - discriminate houtput.
Qed.

End PABoundedRawCodedTemplateParameterAbstraction.
