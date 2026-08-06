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
From Foundation.FirstOrder.Basic Require Import Operator.
From Foundation.FirstOrder.Basic.Semantics Require Import Semantics Elementary.
From Foundation.FirstOrder.Arithmetic.Basic Require Import Misc Syntax Hierarchy.
From Foundation.FirstOrder.Arithmetic Require Import Schemata.
From Foundation.FirstOrder.Arithmetic.Definability Require Import
  Hierarchy Definable BoundedDefinable.
From Foundation.FirstOrder.Arithmetic.PeanoMinus Require Import
  Basic Theory Functions Definability.
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

(** * Remainder by definably-bounded composition *)

(** The source writes an explicit bounded existential joining the division
    and subtraction graphs.  The generic composition theorem constructs the
    same kind of Sigma-zero witness while sharing both component proofs. *)
Definition arithmetic_iopen_rem_definably_bounded : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  arithmetic_definably_bounded_function Str (peano_minus_le O)
    (fun v : Fin.t 2 -> M =>
      iopen_rem O (v Fin.F1) (v (Fin.FS Fin.F1))).
Proof.
  intros M Str O Horing Hpa Hleast.
  pose (Ha := arithmetic_definably_bounded_variable (Str := Str)
    (le := peano_minus_le O) (fun x => peano_minus_le_refl x)
    (structure_oring_eq Horing) (k := 2) Fin.F1).
  pose (Hb := arithmetic_definably_bounded_variable (Str := Str)
    (le := peano_minus_le O) (fun x => peano_minus_le_refl x)
    (structure_oring_eq Horing) (k := 2) (Fin.FS Fin.F1)).
  pose (Hdiv := arithmetic_iopen_div_definably_bounded
    Horing Hpa Hleast).
  assert (Hmul : arithmetic_definably_bounded_function Str
      (peano_minus_le O)
      (fun v : Fin.t 2 -> M =>
        oring_mul O (v (Fin.FS Fin.F1))
          (iopen_div O (v Fin.F1) (v (Fin.FS Fin.F1))))).
  { apply (arithmetic_definably_bounded_compose_peano_minus
      Horing Hpa
      (F := fun w : Fin.t 2 -> M =>
        oring_mul O (w Fin.F1) (w (Fin.FS Fin.F1)))
      (f := fin_two
        (fun v : Fin.t 2 -> M => v (Fin.FS Fin.F1))
        (fun v : Fin.t 2 -> M =>
          iopen_div O (v Fin.F1) (v (Fin.FS Fin.F1))))
      (arithmetic_definably_bounded_mul (Str := Str) (O := O)
        (le := peano_minus_le O) (fun x => peano_minus_le_refl x)
        Horing)).
    intro i. refine (@Fin.caseS' 1 i
      (fun j => arithmetic_definably_bounded_function Str
        (peano_minus_le O)
        (fin_two
          (fun v : Fin.t 2 -> M => v (Fin.FS Fin.F1))
          (fun v : Fin.t 2 -> M =>
            iopen_div O (v Fin.F1) (v (Fin.FS Fin.F1))) j)) Hb _).
    intro j. refine (@Fin.caseS' 0 j
      (fun q => arithmetic_definably_bounded_function Str
        (peano_minus_le O)
        (fin_two
          (fun v : Fin.t 2 -> M => v (Fin.FS Fin.F1))
          (fun v : Fin.t 2 -> M =>
            iopen_div O (v Fin.F1) (v (Fin.FS Fin.F1))) (Fin.FS q)))
      Hdiv _).
    intro q. inversion q. }
  unfold iopen_rem.
  apply (arithmetic_definably_bounded_compose_peano_minus
    Horing Hpa
    (F := fun w : Fin.t 2 -> M =>
      peano_minus_sub O (w Fin.F1) (w (Fin.FS Fin.F1)))
    (f := fin_two
      (fun v : Fin.t 2 -> M => v Fin.F1)
      (fun v : Fin.t 2 -> M =>
        oring_mul O (v (Fin.FS Fin.F1))
          (iopen_div O (v Fin.F1) (v (Fin.FS Fin.F1)))))
    (peano_minus_sub_definably_bounded (Str := Str) (O := O)
      Horing Hpa)).
  intro i. refine (@Fin.caseS' 1 i
    (fun j => arithmetic_definably_bounded_function Str
      (peano_minus_le O)
      (fin_two (fun v : Fin.t 2 -> M => v Fin.F1)
        (fun v : Fin.t 2 -> M =>
          oring_mul O (v (Fin.FS Fin.F1))
            (iopen_div O (v Fin.F1) (v (Fin.FS Fin.F1)))) j)) Ha _).
  intro j. refine (@Fin.caseS' 0 j
    (fun q => arithmetic_definably_bounded_function Str
      (peano_minus_le O)
      (fin_two (fun v : Fin.t 2 -> M => v Fin.F1)
        (fun v : Fin.t 2 -> M =>
          oring_mul O (v (Fin.FS Fin.F1))
            (iopen_div O (v Fin.F1) (v (Fin.FS Fin.F1)))) (Fin.FS q)))
    Hmul _).
  intro q. inversion q.
Defined.

Definition arithmetic_iopen_rem_bounded : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  arithmetic_bounded_function Str (peano_minus_le O)
    (fun v : Fin.t 2 -> M =>
      iopen_rem O (v Fin.F1) (v (Fin.FS Fin.F1))).
Proof.
  intros M Str O Horing Hpa Hleast.
  exact (arithmetic_definably_bounded_bound
    (arithmetic_iopen_rem_definably_bounded Horing Hpa Hleast)).
Defined.

Definition arithmetic_iopen_rem_definable_zero : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  arithmetic_sorted_definable_function Str arithmetic_sigma_zero_symbol
    (fun v : Fin.t 2 -> M =>
      iopen_rem O (v Fin.F1) (v (Fin.FS Fin.F1))).
Proof.
  intros M Str O Horing Hpa Hleast.
  exact (arithmetic_definably_bounded_definition
    (arithmetic_iopen_rem_definably_bounded Horing Hpa Hleast)).
Defined.

Definition arithmetic_iopen_rem_definable : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall symbol,
  arithmetic_sorted_definable_function Str symbol
    (fun v : Fin.t 2 -> M =>
      iopen_rem O (v Fin.F1) (v (Fin.FS Fin.F1))).
Proof.
  intros M Str O Horing Hpa Hleast symbol.
  unfold arithmetic_sorted_definable_function.
  exact (arithmetic_sorted_definable_of_zero
    (arithmetic_iopen_rem_definable_zero Horing Hpa Hleast) symbol).
Defined.

(** * Square root *)

Definition arithmetic_iopen_sqrt_graph_formula : arithmetic_semisentence 2 :=
  Semiformula_and
    (arithmetic_le_formula
      (arithmetic_mul_term
        (@Semiterm_bvar oring_language Empty_set 2 Fin.F1)
        (@Semiterm_bvar oring_language Empty_set 2 Fin.F1))
      (@Semiterm_bvar oring_language Empty_set 2 (Fin.FS Fin.F1)))
    (arithmetic_lt_formula
      (@Semiterm_bvar oring_language Empty_set 2 (Fin.FS Fin.F1))
      (arithmetic_mul_term
        (arithmetic_add_term
          (@Semiterm_bvar oring_language Empty_set 2 Fin.F1)
          arithmetic_one_term)
        (arithmetic_add_term
          (@Semiterm_bvar oring_language Empty_set 2 Fin.F1)
          arithmetic_one_term))).

Lemma arithmetic_iopen_sqrt_graph_formula_open :
  semiformula_open arithmetic_iopen_sqrt_graph_formula.
Proof. reflexivity. Qed.

Lemma arithmetic_iopen_sqrt_graph_formula_hierarchy :
  arithmetic_hierarchy Empty_set arithmetic_sigma 0 2
    arithmetic_iopen_sqrt_graph_formula.
Proof.
  exact (arithmetic_hierarchy_of_open
    arithmetic_iopen_sqrt_graph_formula_open arithmetic_sigma 0).
Qed.

Definition arithmetic_iopen_sqrt_graph_sorted :
    arithmetic_sorted_formula Empty_set 2 arithmetic_sigma_zero_symbol :=
  ArithmeticSortedSigma 0 arithmetic_iopen_sqrt_graph_formula
    arithmetic_iopen_sqrt_graph_formula_hierarchy.

Theorem arithmetic_iopen_sqrt_graph_formula_eval : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall v : Fin.t 2 -> M,
  semiformula_eval Str v (fun x : Empty_set => match x with end)
    arithmetic_iopen_sqrt_graph_formula <->
  v Fin.F1 = iopen_sqrt O (v (Fin.FS Fin.F1)).
Proof.
  intros M Str O Horing Hpa Hleast v.
  unfold arithmetic_iopen_sqrt_graph_formula.
  rewrite peano_minus_eval_and.
  repeat rewrite (@arithmetic_le_formula_eval M Empty_set 2 Str v
    (fun x : Empty_set => match x with end) O _ _ Horing).
  repeat rewrite (@arithmetic_lt_formula_eval M Empty_set 2 Str v
    (fun x : Empty_set => match x with end) O _ _ Horing).
  repeat rewrite (@arithmetic_mul_term_val M Empty_set 2 Str v
    (fun x : Empty_set => match x with end) O _ _ Horing).
  repeat rewrite (@arithmetic_add_term_val M Empty_set 2 Str v
    (fun x : Empty_set => match x with end) O _ _ Horing).
  repeat rewrite (@arithmetic_one_term_val M Empty_set 2 Str v
    (fun x : Empty_set => match x with end) O Horing).
  cbn [semiterm_val].
  symmetry. apply (iopen_sqrt_graph Hpa Hleast).
Qed.

Definition arithmetic_iopen_sqrt_defined : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  arithmetic_sorted_defined_function Str
    (fun v : Fin.t 1 -> M => iopen_sqrt O (v Fin.F1))
    arithmetic_iopen_sqrt_graph_sorted.
Proof.
  intros M Str O Horing Hpa Hleast.
  unfold arithmetic_sorted_defined_function. constructor. split.
  - exact I.
  - intro v. apply (arithmetic_iopen_sqrt_graph_formula_eval
      Horing Hpa Hleast).
Defined.

Definition arithmetic_iopen_sqrt_definable_zero : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  arithmetic_sorted_definable_function Str arithmetic_sigma_zero_symbol
    (fun v : Fin.t 1 -> M => iopen_sqrt O (v Fin.F1)).
Proof.
  intros M Str O Horing Hpa Hleast.
  unfold arithmetic_sorted_definable_function.
  exact (arithmetic_sorted_defined_to_definable
    (arithmetic_iopen_sqrt_defined Horing Hpa Hleast)).
Defined.

Definition arithmetic_iopen_sqrt_definable : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall symbol,
  arithmetic_sorted_definable_function Str symbol
    (fun v : Fin.t 1 -> M => iopen_sqrt O (v Fin.F1)).
Proof.
  intros M Str O Horing Hpa Hleast symbol.
  unfold arithmetic_sorted_definable_function.
  exact (arithmetic_sorted_definable_of_zero
    (arithmetic_iopen_sqrt_definable_zero Horing Hpa Hleast) symbol).
Defined.

Definition arithmetic_iopen_sqrt_bounded : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  arithmetic_bounded_function Str (peano_minus_le O)
    (fun v : Fin.t 1 -> M => iopen_sqrt O (v Fin.F1)).
Proof.
  intros M Str O Hpa Hleast.
  refine {| arithmetic_bounded_term :=
    @Semiterm_bvar oring_language M 1 Fin.F1 |}.
  intro v. cbn [semiterm_val]. apply (iopen_sqrt_le_self Hpa Hleast).
Defined.

Definition arithmetic_iopen_sqrt_definably_bounded : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  arithmetic_definably_bounded_function Str (peano_minus_le O)
    (fun v : Fin.t 1 -> M => iopen_sqrt O (v Fin.F1)).
Proof.
  intros M Str O Horing Hpa Hleast. constructor.
  - exact (arithmetic_iopen_sqrt_bounded Str Hpa Hleast).
  - exact (arithmetic_iopen_sqrt_definable_zero Horing Hpa Hleast).
Defined.

(** * Pairing *)

Definition arithmetic_iopen_pair_graph_formula : arithmetic_semisentence 3 :=
  Semiformula_or
    (Semiformula_and
      (arithmetic_lt_formula
        (@Semiterm_bvar oring_language Empty_set 3 (Fin.FS Fin.F1))
        (@Semiterm_bvar oring_language Empty_set 3
          (Fin.FS (Fin.FS Fin.F1))))
      (arithmetic_eq_formula
        (@Semiterm_bvar oring_language Empty_set 3 Fin.F1)
        (arithmetic_add_term
          (arithmetic_mul_term
            (@Semiterm_bvar oring_language Empty_set 3
              (Fin.FS (Fin.FS Fin.F1)))
            (@Semiterm_bvar oring_language Empty_set 3
              (Fin.FS (Fin.FS Fin.F1))))
          (@Semiterm_bvar oring_language Empty_set 3 (Fin.FS Fin.F1)))))
    (Semiformula_and
      (arithmetic_le_formula
        (@Semiterm_bvar oring_language Empty_set 3
          (Fin.FS (Fin.FS Fin.F1)))
        (@Semiterm_bvar oring_language Empty_set 3 (Fin.FS Fin.F1)))
      (arithmetic_eq_formula
        (@Semiterm_bvar oring_language Empty_set 3 Fin.F1)
        (arithmetic_add_term
          (arithmetic_add_term
            (arithmetic_mul_term
              (@Semiterm_bvar oring_language Empty_set 3 (Fin.FS Fin.F1))
              (@Semiterm_bvar oring_language Empty_set 3 (Fin.FS Fin.F1)))
            (@Semiterm_bvar oring_language Empty_set 3 (Fin.FS Fin.F1)))
          (@Semiterm_bvar oring_language Empty_set 3
            (Fin.FS (Fin.FS Fin.F1)))))).

Lemma arithmetic_iopen_pair_graph_formula_open :
  semiformula_open arithmetic_iopen_pair_graph_formula.
Proof. reflexivity. Qed.

Lemma arithmetic_iopen_pair_graph_formula_hierarchy :
  arithmetic_hierarchy Empty_set arithmetic_sigma 0 3
    arithmetic_iopen_pair_graph_formula.
Proof.
  exact (arithmetic_hierarchy_of_open
    arithmetic_iopen_pair_graph_formula_open arithmetic_sigma 0).
Qed.

Definition arithmetic_iopen_pair_graph_sorted :
    arithmetic_sorted_formula Empty_set 3 arithmetic_sigma_zero_symbol :=
  ArithmeticSortedSigma 0 arithmetic_iopen_pair_graph_formula
    arithmetic_iopen_pair_graph_formula_hierarchy.

Theorem arithmetic_iopen_pair_graph_formula_eval : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  peano_minus_laws O -> forall v : Fin.t 3 -> M,
  semiformula_eval Str v (fun x : Empty_set => match x with end)
    arithmetic_iopen_pair_graph_formula <->
  v Fin.F1 = iopen_pair O
    (v (Fin.FS Fin.F1)) (v (Fin.FS (Fin.FS Fin.F1))).
Proof.
  intros M Str O Horing Hpa v.
  unfold arithmetic_iopen_pair_graph_formula.
  rewrite peano_minus_eval_or.
  setoid_rewrite peano_minus_eval_and.
  repeat rewrite (@arithmetic_lt_formula_eval M Empty_set 3 Str v
    (fun x : Empty_set => match x with end) O _ _ Horing).
  repeat rewrite (@arithmetic_le_formula_eval M Empty_set 3 Str v
    (fun x : Empty_set => match x with end) O _ _ Horing).
  repeat rewrite (@arithmetic_eq_formula_eval M Empty_set 3 Str v
    (fun x : Empty_set => match x with end) O _ _ Horing).
  repeat rewrite (@arithmetic_add_term_val M Empty_set 3 Str v
    (fun x : Empty_set => match x with end) O _ _ Horing).
  repeat rewrite (@arithmetic_mul_term_val M Empty_set 3 Str v
    (fun x : Empty_set => match x with end) O _ _ Horing).
  cbn [semiterm_val].
  symmetry. apply (iopen_pair_graph Hpa).
Qed.

Definition arithmetic_iopen_pair_defined : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  peano_minus_laws O ->
  arithmetic_sorted_defined_function Str
    (fun v : Fin.t 2 -> M =>
      iopen_pair O (v Fin.F1) (v (Fin.FS Fin.F1)))
    arithmetic_iopen_pair_graph_sorted.
Proof.
  intros M Str O Horing Hpa.
  unfold arithmetic_sorted_defined_function. constructor. split.
  - exact I.
  - intro v. apply (arithmetic_iopen_pair_graph_formula_eval Horing Hpa).
Defined.

Definition arithmetic_iopen_pair_definable_zero : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  peano_minus_laws O ->
  arithmetic_sorted_definable_function Str arithmetic_sigma_zero_symbol
    (fun v : Fin.t 2 -> M =>
      iopen_pair O (v Fin.F1) (v (Fin.FS Fin.F1))).
Proof.
  intros M Str O Horing Hpa.
  unfold arithmetic_sorted_definable_function.
  exact (arithmetic_sorted_defined_to_definable
    (arithmetic_iopen_pair_defined Horing Hpa)).
Defined.

Definition arithmetic_iopen_pair_definable : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  peano_minus_laws O -> forall symbol,
  arithmetic_sorted_definable_function Str symbol
    (fun v : Fin.t 2 -> M =>
      iopen_pair O (v Fin.F1) (v (Fin.FS Fin.F1))).
Proof.
  intros M Str O Horing Hpa symbol.
  unfold arithmetic_sorted_definable_function.
  exact (arithmetic_sorted_definable_of_zero
    (arithmetic_iopen_pair_definable_zero Horing Hpa) symbol).
Defined.

Definition arithmetic_iopen_pair_bounded : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  peano_minus_laws O ->
  arithmetic_bounded_function Str (peano_minus_le O)
    (fun v : Fin.t 2 -> M =>
      iopen_pair O (v Fin.F1) (v (Fin.FS Fin.F1))).
Proof.
  intros M Str O Horing Hpa.
  refine {| arithmetic_bounded_term :=
    arithmetic_mul_term
      (arithmetic_add_term
        (arithmetic_add_term
          (@Semiterm_bvar oring_language M 2 Fin.F1)
          (@Semiterm_bvar oring_language M 2 (Fin.FS Fin.F1)))
        arithmetic_one_term)
      (arithmetic_add_term
        (arithmetic_add_term
          (@Semiterm_bvar oring_language M 2 Fin.F1)
          (@Semiterm_bvar oring_language M 2 (Fin.FS Fin.F1)))
        arithmetic_one_term) |}.
  intro v.
  repeat rewrite (@arithmetic_mul_term_val M M 2 Str v (fun x => x) O
    _ _ Horing).
  repeat rewrite (@arithmetic_add_term_val M M 2 Str v (fun x => x) O
    _ _ Horing).
  repeat rewrite (@arithmetic_one_term_val M M 2 Str v (fun x => x) O
    Horing).
  cbn [semiterm_val]. apply (iopen_pair_polybound Hpa).
Defined.

Definition arithmetic_iopen_pair_definably_bounded : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  peano_minus_laws O ->
  arithmetic_definably_bounded_function Str (peano_minus_le O)
    (fun v : Fin.t 2 -> M =>
      iopen_pair O (v Fin.F1) (v (Fin.FS Fin.F1))).
Proof.
  intros M Str O Horing Hpa. constructor.
  - exact (arithmetic_iopen_pair_bounded Horing Hpa).
  - exact (arithmetic_iopen_pair_definable_zero Horing Hpa).
Defined.

(** * Pairing projections *)

Definition arithmetic_iopen_pi1_pair_instance : arithmetic_semisentence 3 :=
  semiformula_rewrite
    (rew_map
      (peano_minus_fin_three
        (Fin.FS (Fin.FS Fin.F1)) (Fin.FS Fin.F1) Fin.F1)
      (fun x : Empty_set => match x with end))
    arithmetic_iopen_pair_graph_formula.

Definition arithmetic_iopen_pi2_pair_instance : arithmetic_semisentence 3 :=
  semiformula_rewrite
    (rew_map
      (peano_minus_fin_three
        (Fin.FS (Fin.FS Fin.F1)) Fin.F1 (Fin.FS Fin.F1))
      (fun x : Empty_set => match x with end))
    arithmetic_iopen_pair_graph_formula.

Definition arithmetic_iopen_pi1_graph_formula : arithmetic_semisentence 2 :=
  peano_minus_bex_lt_succ
    (@Semiterm_bvar oring_language Empty_set 2 (Fin.FS Fin.F1))
    arithmetic_iopen_pi1_pair_instance.

Definition arithmetic_iopen_pi2_graph_formula : arithmetic_semisentence 2 :=
  peano_minus_bex_lt_succ
    (@Semiterm_bvar oring_language Empty_set 2 (Fin.FS Fin.F1))
    arithmetic_iopen_pi2_pair_instance.

Lemma arithmetic_iopen_pi1_graph_formula_hierarchy :
  arithmetic_hierarchy Empty_set arithmetic_sigma 0 2
    arithmetic_iopen_pi1_graph_formula.
Proof.
  unfold arithmetic_iopen_pi1_graph_formula, peano_minus_bex_lt_succ.
  apply (proj2 (@arithmetic_hierarchy_bex_lt_succ_iff Empty_set
    arithmetic_sigma 0 2
    (@Semiterm_bvar oring_language Empty_set 2 (Fin.FS Fin.F1))
    arithmetic_iopen_pi1_pair_instance)).
  unfold arithmetic_iopen_pi1_pair_instance.
  exact (@arithmetic_hierarchy_rewrite Empty_set arithmetic_sigma 0 3
    arithmetic_iopen_pair_graph_formula
    arithmetic_iopen_pair_graph_formula_hierarchy Empty_set 3
    (rew_map
      (peano_minus_fin_three
        (Fin.FS (Fin.FS Fin.F1)) (Fin.FS Fin.F1) Fin.F1)
      (fun x : Empty_set => match x with end))).
Qed.

Lemma arithmetic_iopen_pi2_graph_formula_hierarchy :
  arithmetic_hierarchy Empty_set arithmetic_sigma 0 2
    arithmetic_iopen_pi2_graph_formula.
Proof.
  unfold arithmetic_iopen_pi2_graph_formula, peano_minus_bex_lt_succ.
  apply (proj2 (@arithmetic_hierarchy_bex_lt_succ_iff Empty_set
    arithmetic_sigma 0 2
    (@Semiterm_bvar oring_language Empty_set 2 (Fin.FS Fin.F1))
    arithmetic_iopen_pi2_pair_instance)).
  unfold arithmetic_iopen_pi2_pair_instance.
  exact (@arithmetic_hierarchy_rewrite Empty_set arithmetic_sigma 0 3
    arithmetic_iopen_pair_graph_formula
    arithmetic_iopen_pair_graph_formula_hierarchy Empty_set 3
    (rew_map
      (peano_minus_fin_three
        (Fin.FS (Fin.FS Fin.F1)) Fin.F1 (Fin.FS Fin.F1))
      (fun x : Empty_set => match x with end))).
Qed.

Definition arithmetic_iopen_pi1_graph_sorted :
    arithmetic_sorted_formula Empty_set 2 arithmetic_sigma_zero_symbol :=
  ArithmeticSortedSigma 0 arithmetic_iopen_pi1_graph_formula
    arithmetic_iopen_pi1_graph_formula_hierarchy.

Definition arithmetic_iopen_pi2_graph_sorted :
    arithmetic_sorted_formula Empty_set 2 arithmetic_sigma_zero_symbol :=
  ArithmeticSortedSigma 0 arithmetic_iopen_pi2_graph_formula
    arithmetic_iopen_pi2_graph_formula_hierarchy.

Lemma arithmetic_iopen_pi1_pair_env : forall M (v : Fin.t 2 -> M) y i,
  fin_env_cons y v
      (peano_minus_fin_three
        (Fin.FS (Fin.FS Fin.F1)) (Fin.FS Fin.F1) Fin.F1 i) =
  peano_minus_fin_three (v (Fin.FS Fin.F1)) (v Fin.F1) y i.
Proof.
  intros M v y i.
  refine (@Fin.caseS' 2 i (fun j =>
    fin_env_cons y v
        (peano_minus_fin_three
          (Fin.FS (Fin.FS Fin.F1)) (Fin.FS Fin.F1) Fin.F1 j) =
    peano_minus_fin_three (v (Fin.FS Fin.F1)) (v Fin.F1) y j) _ _).
  - reflexivity.
  - intro j. refine (@Fin.caseS' 1 j (fun q =>
      fin_env_cons y v
          (peano_minus_fin_three
            (Fin.FS (Fin.FS Fin.F1)) (Fin.FS Fin.F1) Fin.F1 (Fin.FS q)) =
      peano_minus_fin_three
        (v (Fin.FS Fin.F1)) (v Fin.F1) y (Fin.FS q)) _ _).
    + reflexivity.
    + intro q. refine (@Fin.caseS' 0 q (fun r =>
        fin_env_cons y v
            (peano_minus_fin_three
              (Fin.FS (Fin.FS Fin.F1)) (Fin.FS Fin.F1) Fin.F1
              (Fin.FS (Fin.FS r))) =
        peano_minus_fin_three
          (v (Fin.FS Fin.F1)) (v Fin.F1) y
          (Fin.FS (Fin.FS r))) _ _).
      * reflexivity.
      * intro r. inversion r.
Qed.

Lemma arithmetic_iopen_pi2_pair_env : forall M (v : Fin.t 2 -> M) x i,
  fin_env_cons x v
      (peano_minus_fin_three
        (Fin.FS (Fin.FS Fin.F1)) Fin.F1 (Fin.FS Fin.F1) i) =
  peano_minus_fin_three (v (Fin.FS Fin.F1)) x (v Fin.F1) i.
Proof.
  intros M v x i.
  refine (@Fin.caseS' 2 i (fun j =>
    fin_env_cons x v
        (peano_minus_fin_three
          (Fin.FS (Fin.FS Fin.F1)) Fin.F1 (Fin.FS Fin.F1) j) =
    peano_minus_fin_three (v (Fin.FS Fin.F1)) x (v Fin.F1) j) _ _).
  - reflexivity.
  - intro j. refine (@Fin.caseS' 1 j (fun q =>
      fin_env_cons x v
          (peano_minus_fin_three
            (Fin.FS (Fin.FS Fin.F1)) Fin.F1 (Fin.FS Fin.F1) (Fin.FS q)) =
      peano_minus_fin_three
        (v (Fin.FS Fin.F1)) x (v Fin.F1) (Fin.FS q)) _ _).
    + reflexivity.
    + intro q. refine (@Fin.caseS' 0 q (fun r =>
        fin_env_cons x v
            (peano_minus_fin_three
              (Fin.FS (Fin.FS Fin.F1)) Fin.F1 (Fin.FS Fin.F1)
              (Fin.FS (Fin.FS r))) =
        peano_minus_fin_three
          (v (Fin.FS Fin.F1)) x (v Fin.F1)
          (Fin.FS (Fin.FS r))) _ _).
      * reflexivity.
      * intro r. inversion r.
Qed.

Lemma arithmetic_iopen_pi1_pair_instance_eval : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  peano_minus_laws O -> forall (v : Fin.t 2 -> M) y,
  semiformula_eval Str (fin_env_cons y v)
    (fun x : Empty_set => match x with end)
    arithmetic_iopen_pi1_pair_instance <->
  v (Fin.FS Fin.F1) = iopen_pair O (v Fin.F1) y.
Proof.
  intros M Str O Horing Hpa v y.
  unfold arithmetic_iopen_pi1_pair_instance.
  rewrite semiformula_eval_map.
  etransitivity.
  - apply semiformula_eval_bound_extensional.
    apply arithmetic_iopen_pi1_pair_env.
  - etransitivity.
    + apply semiformula_eval_free_ext. intros x _. destruct x.
    + exact (arithmetic_iopen_pair_graph_formula_eval Horing Hpa
        (peano_minus_fin_three (v (Fin.FS Fin.F1)) (v Fin.F1) y)).
Qed.

Lemma arithmetic_iopen_pi2_pair_instance_eval : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  peano_minus_laws O -> forall (v : Fin.t 2 -> M) x,
  semiformula_eval Str (fin_env_cons x v)
    (fun z : Empty_set => match z with end)
    arithmetic_iopen_pi2_pair_instance <->
  v (Fin.FS Fin.F1) = iopen_pair O x (v Fin.F1).
Proof.
  intros M Str O Horing Hpa v x.
  unfold arithmetic_iopen_pi2_pair_instance.
  rewrite semiformula_eval_map.
  etransitivity.
  - apply semiformula_eval_bound_extensional.
    apply arithmetic_iopen_pi2_pair_env.
  - etransitivity.
    + apply semiformula_eval_free_ext. intros z _. destruct z.
    + exact (arithmetic_iopen_pair_graph_formula_eval Horing Hpa
        (peano_minus_fin_three (v (Fin.FS Fin.F1)) x (v Fin.F1))).
Qed.

Theorem arithmetic_iopen_pi1_graph_formula_eval : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall v : Fin.t 2 -> M,
  semiformula_eval Str v (fun x : Empty_set => match x with end)
    arithmetic_iopen_pi1_graph_formula <->
  v Fin.F1 = iopen_pi1 O (v (Fin.FS Fin.F1)).
Proof.
  intros M Str O Horing Hpa Hleast v.
  unfold arithmetic_iopen_pi1_graph_formula.
  rewrite (peano_minus_eval_bex_lt_succ Horing Hpa).
  cbn [semiterm_val].
  setoid_rewrite (arithmetic_iopen_pi1_pair_instance_eval Horing Hpa).
  split.
  - intros [y [_ Hpair]].
    rewrite Hpair, (iopen_pi1_pair Hpa Hleast). reflexivity.
  - intro Hpi. exists (iopen_pi2 O (v (Fin.FS Fin.F1))). split.
    + apply (iopen_pi2_le_self Hpa Hleast).
    + rewrite Hpi. symmetry. apply (iopen_pair_pi Hpa Hleast).
Qed.

Theorem arithmetic_iopen_pi2_graph_formula_eval : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall v : Fin.t 2 -> M,
  semiformula_eval Str v (fun x : Empty_set => match x with end)
    arithmetic_iopen_pi2_graph_formula <->
  v Fin.F1 = iopen_pi2 O (v (Fin.FS Fin.F1)).
Proof.
  intros M Str O Horing Hpa Hleast v.
  unfold arithmetic_iopen_pi2_graph_formula.
  rewrite (peano_minus_eval_bex_lt_succ Horing Hpa).
  cbn [semiterm_val].
  setoid_rewrite (arithmetic_iopen_pi2_pair_instance_eval Horing Hpa).
  split.
  - intros [x [_ Hpair]].
    rewrite Hpair, (iopen_pi2_pair Hpa Hleast). reflexivity.
  - intro Hpi. exists (iopen_pi1 O (v (Fin.FS Fin.F1))). split.
    + apply (iopen_pi1_le_self Hpa Hleast).
    + rewrite Hpi. symmetry. apply (iopen_pair_pi Hpa Hleast).
Qed.

Definition arithmetic_iopen_pi1_defined : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  arithmetic_sorted_defined_function Str
    (fun v : Fin.t 1 -> M => iopen_pi1 O (v Fin.F1))
    arithmetic_iopen_pi1_graph_sorted.
Proof.
  intros M Str O Horing Hpa Hleast.
  unfold arithmetic_sorted_defined_function. constructor. split.
  - exact I.
  - intro v. apply (arithmetic_iopen_pi1_graph_formula_eval
      Horing Hpa Hleast).
Defined.

Definition arithmetic_iopen_pi2_defined : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  arithmetic_sorted_defined_function Str
    (fun v : Fin.t 1 -> M => iopen_pi2 O (v Fin.F1))
    arithmetic_iopen_pi2_graph_sorted.
Proof.
  intros M Str O Horing Hpa Hleast.
  unfold arithmetic_sorted_defined_function. constructor. split.
  - exact I.
  - intro v. apply (arithmetic_iopen_pi2_graph_formula_eval
      Horing Hpa Hleast).
Defined.

Definition arithmetic_iopen_pi1_definable_zero : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  arithmetic_sorted_definable_function Str arithmetic_sigma_zero_symbol
    (fun v : Fin.t 1 -> M => iopen_pi1 O (v Fin.F1)).
Proof.
  intros M Str O Horing Hpa Hleast.
  unfold arithmetic_sorted_definable_function.
  exact (arithmetic_sorted_defined_to_definable
    (arithmetic_iopen_pi1_defined Horing Hpa Hleast)).
Defined.

Definition arithmetic_iopen_pi2_definable_zero : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  arithmetic_sorted_definable_function Str arithmetic_sigma_zero_symbol
    (fun v : Fin.t 1 -> M => iopen_pi2 O (v Fin.F1)).
Proof.
  intros M Str O Horing Hpa Hleast.
  unfold arithmetic_sorted_definable_function.
  exact (arithmetic_sorted_defined_to_definable
    (arithmetic_iopen_pi2_defined Horing Hpa Hleast)).
Defined.

Definition arithmetic_iopen_pi1_definable : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  peano_minus_laws O -> arithmetic_least_number_principle O -> forall symbol,
  arithmetic_sorted_definable_function Str symbol
    (fun v : Fin.t 1 -> M => iopen_pi1 O (v Fin.F1)).
Proof.
  intros M Str O Horing Hpa Hleast symbol.
  unfold arithmetic_sorted_definable_function.
  exact (arithmetic_sorted_definable_of_zero
    (arithmetic_iopen_pi1_definable_zero Horing Hpa Hleast) symbol).
Defined.

Definition arithmetic_iopen_pi2_definable : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  peano_minus_laws O -> arithmetic_least_number_principle O -> forall symbol,
  arithmetic_sorted_definable_function Str symbol
    (fun v : Fin.t 1 -> M => iopen_pi2 O (v Fin.F1)).
Proof.
  intros M Str O Horing Hpa Hleast symbol.
  unfold arithmetic_sorted_definable_function.
  exact (arithmetic_sorted_definable_of_zero
    (arithmetic_iopen_pi2_definable_zero Horing Hpa Hleast) symbol).
Defined.

Definition arithmetic_iopen_pi1_bounded : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  arithmetic_bounded_function Str (peano_minus_le O)
    (fun v : Fin.t 1 -> M => iopen_pi1 O (v Fin.F1)).
Proof.
  intros M Str O Hpa Hleast.
  refine {| arithmetic_bounded_term :=
    @Semiterm_bvar oring_language M 1 Fin.F1 |}.
  intro v. cbn [semiterm_val]. apply (iopen_pi1_le_self Hpa Hleast).
Defined.

Definition arithmetic_iopen_pi2_bounded : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  arithmetic_bounded_function Str (peano_minus_le O)
    (fun v : Fin.t 1 -> M => iopen_pi2 O (v Fin.F1)).
Proof.
  intros M Str O Hpa Hleast.
  refine {| arithmetic_bounded_term :=
    @Semiterm_bvar oring_language M 1 Fin.F1 |}.
  intro v. cbn [semiterm_val]. apply (iopen_pi2_le_self Hpa Hleast).
Defined.

Definition arithmetic_iopen_pi1_definably_bounded : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  arithmetic_definably_bounded_function Str (peano_minus_le O)
    (fun v : Fin.t 1 -> M => iopen_pi1 O (v Fin.F1)).
Proof.
  intros M Str O Horing Hpa Hleast. constructor.
  - exact (arithmetic_iopen_pi1_bounded Str Hpa Hleast).
  - exact (arithmetic_iopen_pi1_definable_zero Horing Hpa Hleast).
Defined.

Definition arithmetic_iopen_pi2_definably_bounded : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  arithmetic_definably_bounded_function Str (peano_minus_le O)
    (fun v : Fin.t 1 -> M => iopen_pi2 O (v Fin.F1)).
Proof.
  intros M Str O Horing Hpa Hleast. constructor.
  - exact (arithmetic_iopen_pi2_bounded Str Hpa Hleast).
  - exact (arithmetic_iopen_pi2_definable_zero Horing Hpa Hleast).
Defined.
