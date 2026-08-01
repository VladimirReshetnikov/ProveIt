(**
  Hierarchy-preserving definability of operations in Peano-minus models.

  The semantic operation remains defined in [Functions].  This module keeps
  the syntactic graph separate: modified subtraction is represented by its
  exact quantifier-free uniqueness specification, then promoted uniformly to
  every arithmetical hierarchy symbol.  Its first argument is also a semantic
  majorant, which packages the bounded definability needed by composition.
*)

From Stdlib Require Import Vectors.Fin.
From Foundation.Syntax.Predicate Require Import Language Term Rew.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic.Semantics Require Import Semantics
  RewriteClosure Elementary.
From Foundation.FirstOrder.Arithmetic.Basic Require Import Misc Syntax Model
  Hierarchy.
From Foundation.FirstOrder.Arithmetic.PeanoMinus Require Import Basic Theory
  Functions.
From Foundation.FirstOrder.Arithmetic.Definability Require Import Hierarchy
  Definable BoundedDefinable.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition arithmetic_sub_graph_var (i : Fin.t 3) :
    semiterm oring_language Empty_set 3 :=
  Semiterm_bvar i.

(** With variables ordered [z,x,y], this is exactly
    [(y <= x -> x = y + z) /\ (x < y -> z = 0)]. *)
Definition arithmetic_sub_graph_formula : arithmetic_semisentence 3 :=
  Semiformula_and
    (semiformula_imp
      (arithmetic_le_formula
        (arithmetic_sub_graph_var (Fin.FS (Fin.FS Fin.F1)))
        (arithmetic_sub_graph_var (Fin.FS Fin.F1)))
      (arithmetic_eq_formula
        (arithmetic_sub_graph_var (Fin.FS Fin.F1))
        (arithmetic_add_term
          (arithmetic_sub_graph_var (Fin.FS (Fin.FS Fin.F1)))
          (arithmetic_sub_graph_var Fin.F1))))
    (semiformula_imp
      (arithmetic_lt_formula
        (arithmetic_sub_graph_var (Fin.FS Fin.F1))
        (arithmetic_sub_graph_var (Fin.FS (Fin.FS Fin.F1))))
      (arithmetic_eq_formula
        (arithmetic_sub_graph_var Fin.F1) arithmetic_zero_term)).

Lemma arithmetic_sub_graph_formula_open :
  semiformula_open arithmetic_sub_graph_formula.
Proof. reflexivity. Qed.

Lemma arithmetic_sub_graph_formula_hierarchy :
  arithmetic_hierarchy Empty_set arithmetic_sigma 0 3
    arithmetic_sub_graph_formula.
Proof.
  apply arithmetic_hierarchy_of_open.
  exact arithmetic_sub_graph_formula_open.
Qed.

Definition arithmetic_sub_graph_sorted :
    arithmetic_sorted_formula Empty_set 3 arithmetic_sigma_zero_symbol :=
  ArithmeticSortedSigma 0 arithmetic_sub_graph_formula
    arithmetic_sub_graph_formula_hierarchy.

Theorem arithmetic_sub_graph_formula_eval : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  peano_minus_laws O ->
  forall v : Fin.t 3 -> M,
  semiformula_eval Str v (fun x : Empty_set => match x with end)
    arithmetic_sub_graph_formula <->
  v Fin.F1 = peano_minus_sub O
    (v (Fin.FS Fin.F1)) (v (Fin.FS (Fin.FS Fin.F1))).
Proof.
  intros M Str O Horing Hpa v.
  unfold arithmetic_sub_graph_formula.
  cbn [semiformula_eval].
  rewrite !semiformula_eval_imp.
  rewrite (@arithmetic_le_formula_eval M Empty_set 3 Str v
    (fun x : Empty_set => match x with end) O _ _ Horing).
  rewrite (@arithmetic_eq_formula_eval M Empty_set 3 Str v
    (fun x : Empty_set => match x with end) O _ _ Horing).
  rewrite (@arithmetic_add_term_val M Empty_set 3 Str v
    (fun x : Empty_set => match x with end) O _ _ Horing).
  rewrite (@arithmetic_lt_formula_eval M Empty_set 3 Str v
    (fun x : Empty_set => match x with end) O _ _ Horing).
  rewrite (@arithmetic_eq_formula_eval M Empty_set 3 Str v
    (fun x : Empty_set => match x with end) O _ _ Horing).
  rewrite (@arithmetic_zero_term_val M Empty_set 3 Str v
    (fun x : Empty_set => match x with end) O Horing).
  cbn [arithmetic_sub_graph_var semiterm_val].
  symmetry. apply (peano_minus_sub_eq_iff Hpa).
Qed.

Definition peano_minus_sub_defined : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  peano_minus_laws O ->
  arithmetic_sorted_defined_function Str
    (fun v : Fin.t 2 -> M =>
      peano_minus_sub O (v Fin.F1) (v (Fin.FS Fin.F1)))
    arithmetic_sub_graph_sorted.
Proof.
  intros M Str O Horing Hpa.
  unfold arithmetic_sorted_defined_function.
  constructor. split.
  - exact I.
  - intro v. apply (arithmetic_sub_graph_formula_eval Horing Hpa).
Defined.

Definition peano_minus_sub_definable_zero : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  peano_minus_laws O ->
  arithmetic_sorted_definable_function Str arithmetic_sigma_zero_symbol
    (fun v : Fin.t 2 -> M =>
      peano_minus_sub O (v Fin.F1) (v (Fin.FS Fin.F1))).
Proof.
  intros M Str O Horing Hpa.
  unfold arithmetic_sorted_definable_function.
  exact (arithmetic_sorted_defined_to_definable
    (peano_minus_sub_defined Horing Hpa)).
Defined.

Definition peano_minus_sub_definable : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  peano_minus_laws O ->
  forall symbol,
  arithmetic_sorted_definable_function Str symbol
    (fun v : Fin.t 2 -> M =>
      peano_minus_sub O (v Fin.F1) (v (Fin.FS Fin.F1))).
Proof.
  intros M Str O Horing Hpa symbol.
  unfold arithmetic_sorted_definable_function.
  exact (arithmetic_sorted_definable_of_zero
    (peano_minus_sub_definable_zero Horing Hpa) symbol).
Defined.

Definition peano_minus_sub_bounded : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  peano_minus_laws O ->
  arithmetic_bounded_function Str (peano_minus_le O)
    (fun v : Fin.t 2 -> M =>
      peano_minus_sub O (v Fin.F1) (v (Fin.FS Fin.F1))).
Proof.
  intros M Str O Hpa.
  refine {| arithmetic_bounded_term :=
    @Semiterm_bvar oring_language M 2 Fin.F1 |}.
  intro v. cbn [semiterm_val].
  apply (peano_minus_sub_le_self Hpa).
Defined.

Definition peano_minus_sub_definably_bounded : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  peano_minus_laws O ->
  arithmetic_definably_bounded_function Str (peano_minus_le O)
    (fun v : Fin.t 2 -> M =>
      peano_minus_sub O (v Fin.F1) (v (Fin.FS Fin.F1))).
Proof.
  intros M Str O Horing Hpa. constructor.
  - exact (peano_minus_sub_bounded Str Hpa).
  - exact (peano_minus_sub_definable_zero Horing Hpa).
Defined.

(** * Syntactic composition with a fixed minuend *)

Definition arithmetic_sub_parameter_term :
    semiterm oring_language nat 1 :=
  Semiterm_fvar 0.

Definition arithmetic_sub_graph_instance_rewrite :
    rew oring_language Empty_set 3 nat 2 :=
  rew_bind
    (peano_minus_fin_three
      (@Semiterm_bvar oring_language nat 2 Fin.F1)
      (@Semiterm_fvar oring_language nat 2 0)
      (@Semiterm_bvar oring_language nat 2 (Fin.FS Fin.F1)))
    (fun x : Empty_set => match x with end).

Definition arithmetic_sub_graph_instance :
    semiformula oring_language nat 2 :=
  semiformula_rewrite arithmetic_sub_graph_instance_rewrite
    arithmetic_sub_graph_formula.

Definition arithmetic_sub_predicate_instance
    (phi : arithmetic_semiproposition 1) :
    semiformula oring_language nat 2 :=
  semiformula_rewrite
    (rew_map (fun _ : Fin.t 1 => Fin.F1) S) phi.

Definition arithmetic_substitution_formula
    (phi : arithmetic_semiproposition 1) :
    arithmetic_semiproposition 1 :=
  peano_minus_bex_lt_succ arithmetic_sub_parameter_term
    (Semiformula_and arithmetic_sub_graph_instance
      (arithmetic_sub_predicate_instance phi)).

Lemma arithmetic_sub_graph_instance_hierarchy : forall pol rank,
  arithmetic_hierarchy nat pol rank 2 arithmetic_sub_graph_instance.
Proof.
  intros pol rank. unfold arithmetic_sub_graph_instance.
  apply arithmetic_hierarchy_rewrite.
  apply arithmetic_hierarchy_of_open.
  exact arithmetic_sub_graph_formula_open.
Qed.

Theorem arithmetic_substitution_formula_hierarchy : forall pol rank phi,
  arithmetic_hierarchy nat pol rank 1 phi ->
  arithmetic_hierarchy nat pol rank 1
    (arithmetic_substitution_formula phi).
Proof.
  intros pol rank phi Hphi.
  unfold arithmetic_substitution_formula, peano_minus_bex_lt_succ.
  apply (proj2 (@arithmetic_hierarchy_bex_lt_succ_iff nat pol rank 1
    arithmetic_sub_parameter_term
    (Semiformula_and arithmetic_sub_graph_instance
      (arithmetic_sub_predicate_instance phi)))).
  apply AH_and.
  - apply arithmetic_sub_graph_instance_hierarchy.
  - unfold arithmetic_sub_predicate_instance.
    now apply arithmetic_hierarchy_rewrite.
Qed.

Lemma arithmetic_sub_graph_instance_eval : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  peano_minus_laws O ->
  forall a x z (f : nat -> M),
  semiformula_eval Str
    (fin_env_cons z (fun _ : Fin.t 1 => x)) (nat_env_cons a f)
    arithmetic_sub_graph_instance <->
  z = peano_minus_sub O a x.
Proof.
  intros M Str O Horing Hpa a x z f.
  unfold arithmetic_sub_graph_instance.
  rewrite semiformula_eval_rewrite.
  unfold arithmetic_sub_graph_instance_rewrite.
  etransitivity.
  - apply semiformula_eval_bound_extensional. intro i.
    rewrite rew_bind_bvar.
    refine (@Fin.caseS' 2 i (fun j =>
      semiterm_val Str (fin_env_cons z (fun _ : Fin.t 1 => x))
        (nat_env_cons a f)
        (peano_minus_fin_three (Semiterm_bvar Fin.F1)
          (Semiterm_fvar 0) (Semiterm_bvar (Fin.FS Fin.F1)) j) =
      peano_minus_fin_three z a x j) _ _).
    + reflexivity.
    + intro j. refine (@Fin.caseS' 1 j (fun q =>
        semiterm_val Str (fin_env_cons z (fun _ : Fin.t 1 => x))
          (nat_env_cons a f)
          (peano_minus_fin_three (Semiterm_bvar Fin.F1)
            (Semiterm_fvar 0) (Semiterm_bvar (Fin.FS Fin.F1)) (Fin.FS q)) =
        peano_minus_fin_three z a x (Fin.FS q)) _ _).
      * reflexivity.
      * intro q. refine (@Fin.caseS' 0 q (fun r =>
          semiterm_val Str (fin_env_cons z (fun _ : Fin.t 1 => x))
            (nat_env_cons a f)
            (peano_minus_fin_three (Semiterm_bvar Fin.F1)
              (Semiterm_fvar 0) (Semiterm_bvar (Fin.FS Fin.F1))
              (Fin.FS (Fin.FS r))) =
          peano_minus_fin_three z a x (Fin.FS (Fin.FS r))) _ _).
        -- reflexivity.
        -- intro r. inversion r.
  - etransitivity.
    + apply semiformula_eval_free_ext. intros q _. destruct q.
    + apply (arithmetic_sub_graph_formula_eval Horing Hpa).
Qed.

Lemma arithmetic_sub_predicate_instance_eval : forall M
    (Str : first_order_structure oring_language M)
    (phi : arithmetic_semiproposition 1) a x z (f : nat -> M),
  semiformula_eval Str
    (fin_env_cons z (fun _ : Fin.t 1 => x)) (nat_env_cons a f)
    (arithmetic_sub_predicate_instance phi) <->
  semiformula_eval Str (fun _ : Fin.t 1 => z) f phi.
Proof.
  intros M Str phi a x z f.
  unfold arithmetic_sub_predicate_instance.
  rewrite semiformula_eval_map.
  cbn [nat_env_cons].
  reflexivity.
Qed.

Theorem arithmetic_substitution_formula_eval : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  peano_minus_laws O ->
  forall (phi : arithmetic_semiproposition 1) a x (f : nat -> M),
  semiformula_eval Str (fun _ : Fin.t 1 => x) (nat_env_cons a f)
    (arithmetic_substitution_formula phi) <->
  semiformula_eval Str
    (fun _ : Fin.t 1 => peano_minus_sub O a x) f phi.
Proof.
  intros M Str O Horing Hpa phi a x f.
  unfold arithmetic_substitution_formula.
  rewrite (peano_minus_eval_bex_lt_succ Horing Hpa).
  cbn [arithmetic_sub_parameter_term semiterm_val nat_env_cons].
  split.
  - intros [z [Hz [Hgraph Hphi]]].
    pose proof (proj1 (arithmetic_sub_graph_instance_eval
      Horing Hpa a x z f) Hgraph) as Hzsub.
    subst z. exact (proj1 (arithmetic_sub_predicate_instance_eval
      Str phi a x (peano_minus_sub O a x) f) Hphi).
  - intro Hphi. exists (peano_minus_sub O a x). split.
    + apply (peano_minus_sub_le_self Hpa).
    + split.
      * apply (proj2 (arithmetic_sub_graph_instance_eval
          Horing Hpa a x (peano_minus_sub O a x) f)).
        reflexivity.
      * apply (proj2 (arithmetic_sub_predicate_instance_eval
          Str phi a x (peano_minus_sub O a x) f)).
        exact Hphi.
Qed.

Definition arithmetic_reverse_induction_formula
    (phi : arithmetic_semiproposition 1) :
    arithmetic_semiproposition 1 :=
  semiformula_imp
    (arithmetic_le_formula
      (@Semiterm_bvar oring_language nat 1 Fin.F1)
      arithmetic_sub_parameter_term)
    (arithmetic_substitution_formula phi).

Theorem arithmetic_reverse_induction_formula_hierarchy : forall pol rank phi,
  arithmetic_hierarchy nat pol rank 1 phi ->
  arithmetic_hierarchy nat pol rank 1
    (arithmetic_reverse_induction_formula phi).
Proof.
  intros pol rank phi Hphi.
  unfold arithmetic_reverse_induction_formula.
  apply (proj2 (@arithmetic_hierarchy_imp_iff nat pol rank 1
    (arithmetic_le_formula
      (@Semiterm_bvar oring_language nat 1 Fin.F1)
      arithmetic_sub_parameter_term)
    (arithmetic_substitution_formula phi))). split.
  - apply arithmetic_hierarchy_of_open. reflexivity.
  - now apply arithmetic_substitution_formula_hierarchy.
Qed.

Theorem arithmetic_reverse_induction_formula_eval : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  peano_minus_laws O ->
  forall (phi : arithmetic_semiproposition 1) a x (f : nat -> M),
  semiformula_eval Str (fun _ : Fin.t 1 => x) (nat_env_cons a f)
    (arithmetic_reverse_induction_formula phi) <->
  (peano_minus_le O x a ->
    semiformula_eval Str
      (fun _ : Fin.t 1 => peano_minus_sub O a x) f phi).
Proof.
  intros M Str O Horing Hpa phi a x f.
  unfold arithmetic_reverse_induction_formula.
  rewrite semiformula_eval_imp.
  rewrite (@arithmetic_le_formula_eval M nat 1 Str
    (fun _ : Fin.t 1 => x) (nat_env_cons a f) O _ _ Horing).
  cbn [arithmetic_sub_parameter_term semiterm_val nat_env_cons].
  rewrite (arithmetic_substitution_formula_eval Horing Hpa).
  reflexivity.
Qed.
