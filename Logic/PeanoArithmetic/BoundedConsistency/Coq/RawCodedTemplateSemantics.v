(**
  Raw-model semantics for finite proof templates.

  Template syntax is primarily a code-construction language, but uniform PA
  sources also need a semantic view before model completeness can be used.
  This module interprets de Bruijn variables through an ordinary assignment,
  named parameters through a separate carrier environment, and opaque
  predicates through an explicit relation environment.

  The key theorem is semantic correctness of parameter abstraction.  If a
  carrier value is inserted into a variable assignment at [depth], evaluating
  the abstracted template is the same as evaluating the original template
  with the selected named parameter overridden by that value.  This exactly
  matches the syntactic opening inverse proved by
  [RawCodedTemplateParameterAbstraction].
*)

From Stdlib Require Import List Arith Bool.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedTemplateSyntax
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateParameterAbstraction.

Import ListNotations.

Module PABoundedRawCodedTemplateSemantics.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateParameterAbstraction.

Definition RawTemplateParameterEnvironment (M : RawPAModel) : Type :=
  TemplateParameterName -> M.

Definition RawTemplatePredicateEnvironment (M : RawPAModel) : Type :=
  TemplatePredicateName -> list M -> Prop.

Fixpoint rawTemplateTermEval (M : RawPAModel)
    (variables : nat -> M)
    (parameters : RawTemplateParameterEnvironment M)
    (input : TemplateTerm) : M :=
  match input with
  | ttVar index => variables index
  | ttParameter name => parameters name
  | ttZero => raw_zero M
  | ttSucc child => raw_succ M (rawTemplateTermEval M variables parameters child)
  | ttAdd lhs rhs =>
      raw_add M
        (rawTemplateTermEval M variables parameters lhs)
        (rawTemplateTermEval M variables parameters rhs)
  | ttMul lhs rhs =>
      raw_mul M
        (rawTemplateTermEval M variables parameters lhs)
        (rawTemplateTermEval M variables parameters rhs)
  end.

Definition rawTemplateTermsEval (M : RawPAModel)
    (variables : nat -> M)
    (parameters : RawTemplateParameterEnvironment M)
    (inputs : list TemplateTerm) : list M :=
  map (rawTemplateTermEval M variables parameters) inputs.

Fixpoint rawTemplateFormulaSat (M : RawPAModel)
    (variables : nat -> M)
    (parameters : RawTemplateParameterEnvironment M)
    (predicates : RawTemplatePredicateEnvironment M)
    (input : TemplateFormula) : Prop :=
  match input with
  | tfEq lhs rhs =>
      rawTemplateTermEval M variables parameters lhs =
      rawTemplateTermEval M variables parameters rhs
  | tfBot => False
  | tfImp lhs rhs =>
      rawTemplateFormulaSat M variables parameters predicates lhs ->
      rawTemplateFormulaSat M variables parameters predicates rhs
  | tfAnd lhs rhs =>
      rawTemplateFormulaSat M variables parameters predicates lhs /\
      rawTemplateFormulaSat M variables parameters predicates rhs
  | tfOr lhs rhs =>
      rawTemplateFormulaSat M variables parameters predicates lhs \/
      rawTemplateFormulaSat M variables parameters predicates rhs
  | tfAll body =>
      forall value : M,
        rawTemplateFormulaSat M (scons M value variables)
          parameters predicates body
  | tfEx body =>
      exists value : M,
        rawTemplateFormulaSat M (scons M value variables)
          parameters predicates body
  | tfOpaque predicate arguments =>
      predicates predicate
        (rawTemplateTermsEval M variables parameters arguments)
  end.

Arguments rawTemplateTermEval M variables parameters input : clear implicits.
Arguments rawTemplateTermsEval M variables parameters inputs : clear implicits.
Arguments rawTemplateFormulaSat M variables parameters predicates input
  : clear implicits.

(** ------------------------------------------------------------------
    Extensionality and agreement with embedded PA syntax. *)

Lemma rawTemplateTermEval_variables_ext : forall
    (M : RawPAModel) first second parameters input,
  (forall index, first index = second index) ->
  rawTemplateTermEval M first parameters input =
  rawTemplateTermEval M second parameters input.
Proof.
  intros M first second parameters input hext.
  induction input; cbn [rawTemplateTermEval].
  - apply hext.
  - reflexivity.
  - reflexivity.
  - now rewrite IHinput.
  - now rewrite IHinput1, IHinput2.
  - now rewrite IHinput1, IHinput2.
Qed.

Lemma rawTemplateTermsEval_variables_ext : forall
    (M : RawPAModel) first second parameters inputs,
  (forall index, first index = second index) ->
  rawTemplateTermsEval M first parameters inputs =
  rawTemplateTermsEval M second parameters inputs.
Proof.
  intros M first second parameters inputs hext.
  unfold rawTemplateTermsEval. apply map_ext. intro input.
  apply rawTemplateTermEval_variables_ext. exact hext.
Qed.

Lemma rawTemplateFormulaSat_variables_ext : forall
    (M : RawPAModel) first second parameters predicates input,
  (forall index, first index = second index) ->
  (rawTemplateFormulaSat M first parameters predicates input <->
   rawTemplateFormulaSat M second parameters predicates input).
Proof.
  intros M first second parameters predicates input.
  revert first second.
  induction input as
      [lhs rhs | | lhs ihlhs rhs ihrhs | lhs ihlhs rhs ihrhs |
       lhs ihlhs rhs ihrhs | body ihbody | body ihbody |
       predicate arguments]; intros first second hext;
    cbn [rawTemplateFormulaSat].
  - now rewrite (rawTemplateTermEval_variables_ext M first second
      parameters lhs hext),
      (rawTemplateTermEval_variables_ext M first second
        parameters rhs hext).
  - reflexivity.
  - now rewrite (ihlhs first second hext), (ihrhs first second hext).
  - now rewrite (ihlhs first second hext), (ihrhs first second hext).
  - now rewrite (ihlhs first second hext), (ihrhs first second hext).
  - split; intros hall value.
    + assert (hext' : forall index,
          scons M value first index = scons M value second index).
      { intros [|index]; cbn [scons]; [reflexivity |]. apply hext. }
      exact (proj1 (ihbody (scons M value first)
        (scons M value second) hext') (hall value)).
    + assert (hext' : forall index,
          scons M value first index = scons M value second index).
      { intros [|index]; cbn [scons]; [reflexivity |]. apply hext. }
      exact (proj2 (ihbody (scons M value first)
        (scons M value second) hext') (hall value)).
  - split; intros [value hvalue]; exists value.
    + assert (hext' : forall index,
          scons M value first index = scons M value second index).
      { intros [|index]; cbn [scons]; [reflexivity |]. apply hext. }
      exact (proj1 (ihbody (scons M value first)
        (scons M value second) hext') hvalue).
    + assert (hext' : forall index,
          scons M value first index = scons M value second index).
      { intros [|index]; cbn [scons]; [reflexivity |]. apply hext. }
      exact (proj2 (ihbody (scons M value first)
        (scons M value second) hext') hvalue).
  - now rewrite (rawTemplateTermsEval_variables_ext M first second
      parameters arguments hext).
Qed.

Theorem rawTemplateTermEval_embedPA : forall
    (M : RawPAModel) variables parameters input,
  rawTemplateTermEval M variables parameters (embedPATerm input) =
  raw_term_eval M variables input.
Proof.
  intros M variables parameters input.
  induction input; cbn [embedPATerm rawTemplateTermEval raw_term_eval].
  - reflexivity.
  - reflexivity.
  - now rewrite IHinput.
  - now rewrite IHinput1, IHinput2.
  - now rewrite IHinput1, IHinput2.
Qed.

Theorem rawTemplateFormulaSat_embedPA : forall
    (M : RawPAModel) variables parameters predicates input,
  rawTemplateFormulaSat M variables parameters predicates
    (embedPAFormula input) <->
  raw_formula_sat M variables input.
Proof.
  intros M variables parameters predicates input.
  revert variables.
  induction input as
      [lhs rhs | | lhs ihlhs rhs ihrhs | lhs ihlhs rhs ihrhs |
       lhs ihlhs rhs ihrhs | body ihbody | body ihbody];
    intro variables; cbn [embedPAFormula rawTemplateFormulaSat
      raw_formula_sat].
  - now rewrite !rawTemplateTermEval_embedPA.
  - reflexivity.
  - now rewrite ihlhs, ihrhs.
  - now rewrite ihlhs, ihrhs.
  - now rewrite ihlhs, ihrhs.
  - split; intros hall value.
    + apply (proj1 (ihbody (scons M value variables))). apply hall.
    + apply (proj2 (ihbody (scons M value variables))). apply hall.
  - split; intros [value hvalue]; exists value.
    + apply (proj1 (ihbody (scons M value variables))). exact hvalue.
    + apply (proj2 (ihbody (scons M value variables))). exact hvalue.
Qed.

(** Renaming changes only the variable environment. *)
Theorem rawTemplateTermEval_rename : forall
    (M : RawPAModel) variables parameters renaming input,
  rawTemplateTermEval M variables parameters
    (templateTermRename renaming input) =
  rawTemplateTermEval M (fun index => variables (renaming index))
    parameters input.
Proof.
  intros M variables parameters renaming input.
  induction input; cbn [templateTermRename rawTemplateTermEval].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - now rewrite IHinput.
  - now rewrite IHinput1, IHinput2.
  - now rewrite IHinput1, IHinput2.
Qed.

Lemma rawTemplateTermsEval_rename : forall
    (M : RawPAModel) variables parameters renaming inputs,
  rawTemplateTermsEval M variables parameters
    (templateTermsRename renaming inputs) =
  rawTemplateTermsEval M (fun index => variables (renaming index))
    parameters inputs.
Proof.
  intros M variables parameters renaming inputs.
  unfold rawTemplateTermsEval, templateTermsRename.
  rewrite map_map. apply map_ext. intro input.
  apply rawTemplateTermEval_rename.
Qed.

Theorem rawTemplateFormulaSat_rename : forall
    (M : RawPAModel) variables parameters predicates renaming input,
  rawTemplateFormulaSat M variables parameters predicates
    (templateFormulaRename renaming input) <->
  rawTemplateFormulaSat M
    (fun index => variables (renaming index))
    parameters predicates input.
Proof.
  intros M variables parameters predicates renaming input.
  revert variables renaming.
  induction input as
      [lhs rhs | | lhs ihlhs rhs ihrhs | lhs ihlhs rhs ihrhs |
       lhs ihlhs rhs ihrhs | body ihbody | body ihbody |
       predicate arguments]; intros variables renaming;
    cbn [templateFormulaRename rawTemplateFormulaSat].
  - now rewrite !rawTemplateTermEval_rename.
  - reflexivity.
  - now rewrite ihlhs, ihrhs.
  - now rewrite ihlhs, ihrhs.
  - now rewrite ihlhs, ihrhs.
  - split; intros hall value.
    + pose proof (proj1 (ihbody (scons M value variables)
        (templateUpRenaming renaming)) (hall value)) as hbody.
      assert (henv : forall index,
        (fun index => scons M value variables
          (templateUpRenaming renaming index)) index =
        scons M value (fun index => variables (renaming index)) index).
      { intros [|index]; reflexivity. }
      apply (proj1 (rawTemplateFormulaSat_variables_ext M
        (fun index => scons M value variables
          (templateUpRenaming renaming index))
        (scons M value (fun index => variables (renaming index)))
        parameters predicates body henv)).
      exact hbody.
    + apply (proj2 (ihbody (scons M value variables)
        (templateUpRenaming renaming))).
      assert (henv : forall index,
        (fun index => scons M value variables
          (templateUpRenaming renaming index)) index =
        scons M value (fun index => variables (renaming index)) index).
      { intros [|index]; reflexivity. }
      apply (proj2 (rawTemplateFormulaSat_variables_ext M
        (fun index => scons M value variables
          (templateUpRenaming renaming index))
        (scons M value (fun index => variables (renaming index)))
        parameters predicates body henv)).
      apply hall.
  - split; intros [value hvalue]; exists value.
    + pose proof (proj1 (ihbody (scons M value variables)
        (templateUpRenaming renaming)) hvalue) as hbody.
      assert (henv : forall index,
        (fun index => scons M value variables
          (templateUpRenaming renaming index)) index =
        scons M value (fun index => variables (renaming index)) index).
      { intros [|index]; reflexivity. }
      apply (proj1 (rawTemplateFormulaSat_variables_ext M
        (fun index => scons M value variables
          (templateUpRenaming renaming index))
        (scons M value (fun index => variables (renaming index)))
        parameters predicates body henv)).
      exact hbody.
    + apply (proj2 (ihbody (scons M value variables)
        (templateUpRenaming renaming))).
      assert (henv : forall index,
        (fun index => scons M value variables
          (templateUpRenaming renaming index)) index =
        scons M value (fun index => variables (renaming index)) index).
      { intros [|index]; reflexivity. }
      apply (proj2 (rawTemplateFormulaSat_variables_ext M
        (fun index => scons M value variables
          (templateUpRenaming renaming index))
        (scons M value (fun index => variables (renaming index)))
        parameters predicates body henv)).
      exact hvalue.
  - now rewrite rawTemplateTermsEval_rename.
Qed.

(** ------------------------------------------------------------------
    Semantic correctness of carrier-parameter abstraction. *)

Fixpoint rawTemplateEnvironmentInsertAt {M : RawPAModel}
    (depth : nat) (value : M) (variables : nat -> M) : nat -> M :=
  match depth with
  | 0 => scons M value variables
  | S outerDepth =>
      scons M (variables 0)
        (rawTemplateEnvironmentInsertAt outerDepth value
          (fun index => variables (S index)))
  end.

Definition rawTemplateParameterOverride {M : RawPAModel}
    (name : TemplateParameterName) (value : M)
    (parameters : RawTemplateParameterEnvironment M)
    : RawTemplateParameterEnvironment M :=
  fun current =>
    if Nat.eqb current name then value else parameters current.

Arguments rawTemplateEnvironmentInsertAt {M} depth value variables index.
Arguments rawTemplateParameterOverride {M} name value parameters current.

Lemma rawTemplateEnvironmentInsertAt_shift : forall
    (M : RawPAModel) depth (value : M) (variables : nat -> M) index,
  rawTemplateEnvironmentInsertAt depth value variables
    (templateShiftRenamingAt depth index) = variables index.
Proof.
  intros M depth. induction depth as [|depth ih];
    intros value variables index.
  - reflexivity.
  - destruct index as [|index]; cbn
      [rawTemplateEnvironmentInsertAt templateShiftRenamingAt scons].
    + reflexivity.
    + exact (ih value (fun inner => variables (S inner)) index).
Qed.

Lemma rawTemplateEnvironmentInsertAt_fresh : forall
    (M : RawPAModel) depth (value : M) (variables : nat -> M),
  rawTemplateEnvironmentInsertAt depth value variables depth = value.
Proof.
  intros M depth. induction depth as [|depth ih];
    intros value variables.
  - reflexivity.
  - cbn [rawTemplateEnvironmentInsertAt scons]. apply ih.
Qed.

Theorem rawTemplateTermEval_abstractParameterAt : forall
    (M : RawPAModel) variables parameters name depth value input,
  rawTemplateTermEval M
    (rawTemplateEnvironmentInsertAt depth value variables)
    parameters
    (templateTermAbstractParameterAt name depth input) =
  rawTemplateTermEval M variables
    (rawTemplateParameterOverride name value parameters) input.
Proof.
  intros M variables parameters name depth value input.
  induction input as
      [index | current | | child ih | lhs ihlhs rhs ihrhs |
       lhs ihlhs rhs ihrhs]; cbn
      [templateTermAbstractParameterAt rawTemplateTermEval].
  - apply rawTemplateEnvironmentInsertAt_shift.
  - destruct (Nat.eqb current name) eqn:heq.
    + unfold rawTemplateParameterOverride. rewrite heq.
      apply rawTemplateEnvironmentInsertAt_fresh.
    + unfold rawTemplateParameterOverride. now rewrite heq.
  - reflexivity.
  - now rewrite ih.
  - now rewrite ihlhs, ihrhs.
  - now rewrite ihlhs, ihrhs.
Qed.

Lemma rawTemplateTermsEval_abstractParameterAt : forall
    (M : RawPAModel) variables parameters name depth value inputs,
  rawTemplateTermsEval M
    (rawTemplateEnvironmentInsertAt depth value variables)
    parameters
    (templateTermsAbstractParameterAt name depth inputs) =
  rawTemplateTermsEval M variables
    (rawTemplateParameterOverride name value parameters) inputs.
Proof.
  intros M variables parameters name depth value inputs.
  unfold rawTemplateTermsEval, templateTermsAbstractParameterAt.
  rewrite map_map. apply map_ext. intro input.
  apply rawTemplateTermEval_abstractParameterAt.
Qed.

Theorem rawTemplateFormulaSat_abstractParameterAt : forall
    (M : RawPAModel) variables parameters predicates name depth value input,
  rawTemplateFormulaSat M
    (rawTemplateEnvironmentInsertAt depth value variables)
    parameters predicates
    (templateFormulaAbstractParameterAt name depth input) <->
  rawTemplateFormulaSat M variables
    (rawTemplateParameterOverride name value parameters)
    predicates input.
Proof.
  intros M variables parameters predicates name depth value input.
  revert variables depth.
  induction input as
      [lhs rhs | | lhs ihlhs rhs ihrhs | lhs ihlhs rhs ihrhs |
       lhs ihlhs rhs ihrhs | body ihbody | body ihbody |
       predicate arguments]; intros variables depth;
    cbn [templateFormulaAbstractParameterAt rawTemplateFormulaSat].
  - now rewrite !rawTemplateTermEval_abstractParameterAt.
  - reflexivity.
  - now rewrite ihlhs, ihrhs.
  - now rewrite ihlhs, ihrhs.
  - now rewrite ihlhs, ihrhs.
  - split; intros hall boundValue.
    + apply (proj1 (ihbody (scons M boundValue variables) (S depth))).
      apply hall.
    + apply (proj2 (ihbody (scons M boundValue variables) (S depth))).
      apply hall.
  - split; intros [boundValue hbound]; exists boundValue.
    + apply (proj1 (ihbody (scons M boundValue variables) (S depth))).
      exact hbound.
    + apply (proj2 (ihbody (scons M boundValue variables) (S depth))).
      exact hbound.
  - now rewrite rawTemplateTermsEval_abstractParameterAt.
Qed.

Corollary rawTemplateFormulaSat_abstractParameter : forall
    (M : RawPAModel) variables parameters predicates name value input,
  rawTemplateFormulaSat M (scons M value variables)
    parameters predicates
    (templateFormulaAbstractParameter name input) <->
  rawTemplateFormulaSat M variables
    (rawTemplateParameterOverride name value parameters)
    predicates input.
Proof.
  intros M variables parameters predicates name value input.
  unfold templateFormulaAbstractParameter.
  change
    (rawTemplateFormulaSat M
      (rawTemplateEnvironmentInsertAt 0 value variables)
      parameters predicates
      (templateFormulaAbstractParameterAt name 0 input) <->
     rawTemplateFormulaSat M variables
      (rawTemplateParameterOverride name value parameters)
      predicates input).
  apply rawTemplateFormulaSat_abstractParameterAt.
Qed.

End PABoundedRawCodedTemplateSemantics.
