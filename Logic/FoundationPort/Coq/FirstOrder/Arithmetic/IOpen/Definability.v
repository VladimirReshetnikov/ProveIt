(**
  Bounded arithmetic definitions for operations constructed from open
  induction.

  The semantic operations remain in [IOpen.Basic].  This module keeps their
  graph syntax separate, preserving the read-only source architecture while
  allowing the generic hierarchy and bounded-composition libraries to reuse
  the resulting witnesses.
*)

From Stdlib Require Import Vectors.Fin.
From Foundation.Syntax.Predicate Require Import Language Term Rew.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic.Semantics Require Import Semantics.
From Foundation.FirstOrder.Arithmetic.Basic Require Import Misc Syntax Hierarchy.
From Foundation.FirstOrder.Arithmetic Require Import Schemata.
From Foundation.FirstOrder.Arithmetic.Definability Require Import
  Hierarchy Definable BoundedDefinable.
From Foundation.FirstOrder.Arithmetic.PeanoMinus Require Import
  Basic Theory Definability.
From Foundation.FirstOrder.Arithmetic.IOpen Require Import Basic.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Division *)

Definition arithmetic_iopen_div_graph_formula : arithmetic_semisentence 3 :=
  Semiformula_and
    (semiformula_imp
      (arithmetic_lt_formula arithmetic_zero_term
        (@Semiterm_bvar oring_language Empty_set 3
          (Fin.FS (Fin.FS Fin.F1))))
      (Semiformula_and
        (arithmetic_le_formula
          (arithmetic_mul_term
            (@Semiterm_bvar oring_language Empty_set 3
              (Fin.FS (Fin.FS Fin.F1)))
            (@Semiterm_bvar oring_language Empty_set 3 Fin.F1))
          (@Semiterm_bvar oring_language Empty_set 3 (Fin.FS Fin.F1)))
        (arithmetic_lt_formula
          (@Semiterm_bvar oring_language Empty_set 3 (Fin.FS Fin.F1))
          (arithmetic_mul_term
            (@Semiterm_bvar oring_language Empty_set 3
              (Fin.FS (Fin.FS Fin.F1)))
            (arithmetic_add_term
              (@Semiterm_bvar oring_language Empty_set 3 Fin.F1)
              arithmetic_one_term)))))
    (semiformula_imp
      (arithmetic_eq_formula
        (@Semiterm_bvar oring_language Empty_set 3
          (Fin.FS (Fin.FS Fin.F1)))
        arithmetic_zero_term)
      (arithmetic_eq_formula
        (@Semiterm_bvar oring_language Empty_set 3 Fin.F1)
        arithmetic_zero_term)).

Lemma arithmetic_iopen_div_graph_formula_open :
  semiformula_open arithmetic_iopen_div_graph_formula.
Proof. reflexivity. Qed.

Lemma arithmetic_iopen_div_graph_formula_hierarchy :
  arithmetic_hierarchy Empty_set arithmetic_sigma 0 3
    arithmetic_iopen_div_graph_formula.
Proof.
  exact (arithmetic_hierarchy_of_open
    arithmetic_iopen_div_graph_formula_open arithmetic_sigma 0).
Qed.

Definition arithmetic_iopen_div_graph_sorted :
    arithmetic_sorted_formula Empty_set 3 arithmetic_sigma_zero_symbol :=
  ArithmeticSortedSigma 0 arithmetic_iopen_div_graph_formula
    arithmetic_iopen_div_graph_formula_hierarchy.

Theorem arithmetic_iopen_div_graph_formula_eval : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall v : Fin.t 3 -> M,
  semiformula_eval Str v (fun x : Empty_set => match x with end)
    arithmetic_iopen_div_graph_formula <->
  v Fin.F1 = iopen_div O
    (v (Fin.FS Fin.F1)) (v (Fin.FS (Fin.FS Fin.F1))).
Proof.
  intros M Str O Horing Hpa Hleast v.
  unfold arithmetic_iopen_div_graph_formula.
  rewrite peano_minus_eval_and, !semiformula_eval_imp.
  setoid_rewrite peano_minus_eval_and.
  repeat rewrite (@arithmetic_lt_formula_eval M Empty_set 3 Str v
    (fun x : Empty_set => match x with end) O _ _ Horing).
  repeat rewrite (@arithmetic_le_formula_eval M Empty_set 3 Str v
    (fun x : Empty_set => match x with end) O _ _ Horing).
  repeat rewrite (@arithmetic_eq_formula_eval M Empty_set 3 Str v
    (fun x : Empty_set => match x with end) O _ _ Horing).
  repeat rewrite (@arithmetic_mul_term_val M Empty_set 3 Str v
    (fun x : Empty_set => match x with end) O _ _ Horing).
  repeat rewrite (@arithmetic_add_term_val M Empty_set 3 Str v
    (fun x : Empty_set => match x with end) O _ _ Horing).
  repeat rewrite (@arithmetic_zero_term_val M Empty_set 3 Str v
    (fun x : Empty_set => match x with end) O Horing).
  repeat rewrite (@arithmetic_one_term_val M Empty_set 3 Str v
    (fun x : Empty_set => match x with end) O Horing).
  cbn [semiterm_val].
  symmetry. apply (iopen_div_graph Hpa Hleast).
Qed.

Definition arithmetic_iopen_div_defined : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  arithmetic_sorted_defined_function Str
    (fun v : Fin.t 2 -> M =>
      iopen_div O (v Fin.F1) (v (Fin.FS Fin.F1)))
    arithmetic_iopen_div_graph_sorted.
Proof.
  intros M Str O Horing Hpa Hleast.
  unfold arithmetic_sorted_defined_function. constructor. split.
  - exact I.
  - intro v. apply (arithmetic_iopen_div_graph_formula_eval
      Horing Hpa Hleast).
Defined.

Definition arithmetic_iopen_div_definable_zero : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  arithmetic_sorted_definable_function Str arithmetic_sigma_zero_symbol
    (fun v : Fin.t 2 -> M =>
      iopen_div O (v Fin.F1) (v (Fin.FS Fin.F1))).
Proof.
  intros M Str O Horing Hpa Hleast.
  unfold arithmetic_sorted_definable_function.
  exact (arithmetic_sorted_defined_to_definable
    (arithmetic_iopen_div_defined Horing Hpa Hleast)).
Defined.

Definition arithmetic_iopen_div_definable : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall symbol,
  arithmetic_sorted_definable_function Str symbol
    (fun v : Fin.t 2 -> M =>
      iopen_div O (v Fin.F1) (v (Fin.FS Fin.F1))).
Proof.
  intros M Str O Horing Hpa Hleast symbol.
  unfold arithmetic_sorted_definable_function.
  exact (arithmetic_sorted_definable_of_zero
    (arithmetic_iopen_div_definable_zero Horing Hpa Hleast) symbol).
Defined.

Definition arithmetic_iopen_div_bounded : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  arithmetic_bounded_function Str (peano_minus_le O)
    (fun v : Fin.t 2 -> M =>
      iopen_div O (v Fin.F1) (v (Fin.FS Fin.F1))).
Proof.
  intros M Str O Hpa Hleast.
  refine {| arithmetic_bounded_term :=
    @Semiterm_bvar oring_language M 2 Fin.F1 |}.
  intro v. cbn [semiterm_val]. apply (iopen_div_le Hpa Hleast).
Defined.

Definition arithmetic_iopen_div_definably_bounded : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  arithmetic_definably_bounded_function Str (peano_minus_le O)
    (fun v : Fin.t 2 -> M =>
      iopen_div O (v Fin.F1) (v (Fin.FS Fin.F1))).
Proof.
  intros M Str O Horing Hpa Hleast. constructor.
  - exact (arithmetic_iopen_div_bounded Str Hpa Hleast).
  - exact (arithmetic_iopen_div_definable_zero Horing Hpa Hleast).
Defined.
