(** Concrete syntax for the ordered-ring language.

    These constructors factor the term and atomic-formula boilerplate shared
    by Robinson Q, R0, Peano arithmetic without induction, and the induction
    schemata.  Their evaluation laws require only the explicit interpretation
    capability, not any arithmetic axioms. *)

From Stdlib Require Import Vectors.Fin.
From Foundation.Syntax.Predicate Require Import Language Term.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Operator.
From Foundation.FirstOrder.Basic.Semantics Require Import
  Semantics OperatorSemantics.
From Foundation.FirstOrder.Arithmetic.Basic Require Import Misc.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition oring_language_eq_operator :
    semiformula_has_eq_operator oring_language :=
  semiformula_eq_operator_of_language
    (language_oring_eq oring_language_structure).

Definition arithmetic_zero_term {X n} : semiterm oring_language X n :=
  semiterm_operator_const_apply
    (semiterm_zero_operator
      (semiterm_zero_operator_of_language
        (language_oring_zero oring_language_structure))).

Definition arithmetic_one_term {X n} : semiterm oring_language X n :=
  semiterm_one_term
    (semiterm_one_operator_of_language
      (language_oring_one oring_language_structure)).

Definition arithmetic_add_term {X n}
    (t u : semiterm oring_language X n) : semiterm oring_language X n :=
  semiterm_add_term
    (semiterm_add_operator_of_language
      (language_oring_add oring_language_structure)) t u.

Definition arithmetic_mul_term {X n}
    (t u : semiterm oring_language X n) : semiterm oring_language X n :=
  semiterm_operator_apply
    (semiterm_mul_operator
      (semiterm_mul_operator_of_language
        (language_oring_mul oring_language_structure)))
    (fin_two t u).

Definition arithmetic_add_one_term {X n}
    (t : semiterm oring_language X n) : semiterm oring_language X n :=
  arithmetic_add_term t arithmetic_one_term.

Definition arithmetic_eq_formula {X n}
    (t u : semiterm oring_language X n) :
    semiformula oring_language X n :=
  @Semiformula_rel oring_language X n 2 ORing_eq (fin_two t u).

Definition arithmetic_lt_formula {X n}
    (t u : semiterm oring_language X n) :
    semiformula oring_language X n :=
  @Semiformula_rel oring_language X n 2 ORing_lt (fin_two t u).

Lemma arithmetic_zero_term_val : forall M X n
    (Str : first_order_structure oring_language M)
    (b : Fin.t n -> M) (f : X -> M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  semiterm_val Str b f arithmetic_zero_term = oring_zero O.
Proof.
  intros M X n Str b f O Horing.
  unfold arithmetic_zero_term, semiterm_operator_const_apply.
  rewrite semiterm_val_operator_apply, semiterm_val_fin_zero.
  apply structure_zero_operator. exact (structure_oring_zero Horing).
Qed.

Lemma arithmetic_one_term_val : forall M X n
    (Str : first_order_structure oring_language M)
    (b : Fin.t n -> M) (f : X -> M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  semiterm_val Str b f arithmetic_one_term = oring_one O.
Proof.
  intros. unfold arithmetic_one_term.
  apply semiterm_val_one_term. exact (structure_oring_one H).
Qed.

Lemma arithmetic_add_term_val : forall M X n
    (Str : first_order_structure oring_language M)
    (b : Fin.t n -> M) (f : X -> M) (O : oring_carrier M)
    (t u : semiterm oring_language X n),
  structure_interprets_oring Str oring_language_structure O ->
  semiterm_val Str b f (arithmetic_add_term t u) =
  oring_add O (semiterm_val Str b f t) (semiterm_val Str b f u).
Proof.
  intros. unfold arithmetic_add_term.
  apply semiterm_val_add_term. exact (structure_oring_add H).
Qed.

Lemma arithmetic_mul_term_val : forall M X n
    (Str : first_order_structure oring_language M)
    (b : Fin.t n -> M) (f : X -> M) (O : oring_carrier M)
    (t u : semiterm oring_language X n),
  structure_interprets_oring Str oring_language_structure O ->
  semiterm_val Str b f (arithmetic_mul_term t u) =
  oring_mul O (semiterm_val Str b f t) (semiterm_val Str b f u).
Proof.
  intros. unfold arithmetic_mul_term.
  rewrite semiterm_val_operator_apply, semiterm_val_fin_two.
  apply structure_mul_operator. exact (structure_oring_mul H).
Qed.

Lemma arithmetic_add_one_term_val : forall M X n
    (Str : first_order_structure oring_language M)
    (b : Fin.t n -> M) (f : X -> M) (O : oring_carrier M)
    (t : semiterm oring_language X n),
  structure_interprets_oring Str oring_language_structure O ->
  semiterm_val Str b f (arithmetic_add_one_term t) =
  oring_add O (semiterm_val Str b f t) (oring_one O).
Proof.
  intros. unfold arithmetic_add_one_term.
  rewrite (@arithmetic_add_term_val M X n Str b f O
    t arithmetic_one_term H).
  rewrite (@arithmetic_one_term_val M X n Str b f O H).
  reflexivity.
Qed.

Lemma arithmetic_eq_formula_eval : forall M X n
    (Str : first_order_structure oring_language M)
    (b : Fin.t n -> M) (f : X -> M) (O : oring_carrier M)
    (t u : semiterm oring_language X n),
  structure_interprets_oring Str oring_language_structure O ->
  (semiformula_eval Str b f (arithmetic_eq_formula t u) <->
   semiterm_val Str b f t = semiterm_val Str b f u).
Proof.
  intros. unfold arithmetic_eq_formula; simpl.
  rewrite semiterm_val_fin_two.
  change (semiformula_operator_eval Str
    (fin_two (semiterm_val Str b f t) (semiterm_val Str b f u))
    (semiformula_eq_operator
      (semiformula_eq_operator_of_language
        (language_oring_eq oring_language_structure))) <->
    semiterm_val Str b f t = semiterm_val Str b f u).
  apply structure_eq_operator. exact (structure_oring_eq H).
Qed.

Lemma arithmetic_lt_formula_eval : forall M X n
    (Str : first_order_structure oring_language M)
    (b : Fin.t n -> M) (f : X -> M) (O : oring_carrier M)
    (t u : semiterm oring_language X n),
  structure_interprets_oring Str oring_language_structure O ->
  (semiformula_eval Str b f (arithmetic_lt_formula t u) <->
   oring_lt O (semiterm_val Str b f t) (semiterm_val Str b f u)).
Proof.
  intros. unfold arithmetic_lt_formula; simpl.
  rewrite semiterm_val_fin_two.
  change (semiformula_operator_eval Str
    (fin_two (semiterm_val Str b f t) (semiterm_val Str b f u))
    (semiformula_lt_operator
      (semiformula_lt_operator_of_language
        (language_oring_lt oring_language_structure))) <->
    oring_lt O (semiterm_val Str b f t) (semiterm_val Str b f u)).
  apply structure_relation_operator. exact (structure_oring_lt H).
Qed.
