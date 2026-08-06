(**
  The concrete finite first-order theory of Peano arithmetic without
  induction.

  The semantic algebra in [Basic] is intentionally reusable independently of
  syntax.  This file connects its seventeen laws to exact closed sentences,
  finite axiom coverage, model characterization, and proof-theoretic
  completeness.
*)

From Stdlib Require Import Lists.List Vectors.Fin.
From FoundationModal Require Import GenericAdjunctiveSet GenericEntailment.
From Foundation.Vorspiel.Set Require Import Cofinite.
From Foundation.Syntax.Predicate Require Import Language Term.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Calculus Eq Operator Soundness.
From Foundation.FirstOrder.Basic.Semantics Require Import
  ModelTheory Semantics.
From Foundation.FirstOrder.Arithmetic.Basic Require Import Misc Syntax Model.
From Foundation.FirstOrder.Arithmetic.R0 Require Import Basic.
From Foundation.FirstOrder.Arithmetic.Q Require Import Basic.
From Foundation.FirstOrder.Arithmetic.PeanoMinus Require Import Basic.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Import ListNotations.

Definition peano_minus_var {n} (i : Fin.t n) :
    semiterm oring_language Empty_set n :=
  Semiterm_bvar i.

(** * The seventeen non-equality axioms *)

Definition peano_minus_add_zero_sentence : sentence oring_language :=
  @arithmetic_all_sentence 1
    (arithmetic_eq_formula
      (arithmetic_add_term (peano_minus_var Fin.F1) arithmetic_zero_term)
      (peano_minus_var Fin.F1)).

Definition peano_minus_add_assoc_sentence : sentence oring_language :=
  @arithmetic_all_sentence 3
    (arithmetic_eq_formula
      (arithmetic_add_term
        (arithmetic_add_term (peano_minus_var Fin.F1)
          (peano_minus_var (Fin.FS Fin.F1)))
        (peano_minus_var (Fin.FS (Fin.FS Fin.F1))))
      (arithmetic_add_term (peano_minus_var Fin.F1)
        (arithmetic_add_term (peano_minus_var (Fin.FS Fin.F1))
          (peano_minus_var (Fin.FS (Fin.FS Fin.F1)))))).

Definition peano_minus_add_comm_sentence : sentence oring_language :=
  @arithmetic_all_sentence 2
    (arithmetic_eq_formula
      (arithmetic_add_term (peano_minus_var Fin.F1)
        (peano_minus_var (Fin.FS Fin.F1)))
      (arithmetic_add_term (peano_minus_var (Fin.FS Fin.F1))
        (peano_minus_var Fin.F1))).

Definition peano_minus_add_eq_of_lt_sentence : sentence oring_language :=
  @arithmetic_all_sentence 2
    (semiformula_imp
      (arithmetic_lt_formula (peano_minus_var Fin.F1)
        (peano_minus_var (Fin.FS Fin.F1)))
      (Semiformula_exists
        (arithmetic_eq_formula
          (arithmetic_add_term (peano_minus_var (Fin.FS Fin.F1))
            (peano_minus_var Fin.F1))
          (peano_minus_var (Fin.FS (Fin.FS Fin.F1)))))).

Definition peano_minus_zero_le_sentence : sentence oring_language :=
  @arithmetic_all_sentence 1
    (arithmetic_le_formula arithmetic_zero_term
      (peano_minus_var Fin.F1)).

Definition peano_minus_zero_lt_one_sentence : sentence oring_language :=
  arithmetic_lt_formula
    (@arithmetic_zero_term Empty_set 0)
    (@arithmetic_one_term Empty_set 0).

Definition peano_minus_one_le_of_zero_lt_sentence :
    sentence oring_language :=
  @arithmetic_all_sentence 1
    (semiformula_imp
      (arithmetic_lt_formula arithmetic_zero_term
        (peano_minus_var Fin.F1))
      (arithmetic_le_formula arithmetic_one_term
        (peano_minus_var Fin.F1))).

Definition peano_minus_add_lt_add_sentence : sentence oring_language :=
  @arithmetic_all_sentence 3
    (semiformula_imp
      (arithmetic_lt_formula (peano_minus_var Fin.F1)
        (peano_minus_var (Fin.FS Fin.F1)))
      (arithmetic_lt_formula
        (arithmetic_add_term (peano_minus_var Fin.F1)
          (peano_minus_var (Fin.FS (Fin.FS Fin.F1))))
        (arithmetic_add_term (peano_minus_var (Fin.FS Fin.F1))
          (peano_minus_var (Fin.FS (Fin.FS Fin.F1)))))).

Definition peano_minus_mul_zero_sentence : sentence oring_language :=
  @arithmetic_all_sentence 1
    (arithmetic_eq_formula
      (arithmetic_mul_term (peano_minus_var Fin.F1) arithmetic_zero_term)
      arithmetic_zero_term).

Definition peano_minus_mul_one_sentence : sentence oring_language :=
  @arithmetic_all_sentence 1
    (arithmetic_eq_formula
      (arithmetic_mul_term (peano_minus_var Fin.F1) arithmetic_one_term)
      (peano_minus_var Fin.F1)).

Definition peano_minus_mul_assoc_sentence : sentence oring_language :=
  @arithmetic_all_sentence 3
    (arithmetic_eq_formula
      (arithmetic_mul_term
        (arithmetic_mul_term (peano_minus_var Fin.F1)
          (peano_minus_var (Fin.FS Fin.F1)))
        (peano_minus_var (Fin.FS (Fin.FS Fin.F1))))
      (arithmetic_mul_term (peano_minus_var Fin.F1)
        (arithmetic_mul_term (peano_minus_var (Fin.FS Fin.F1))
          (peano_minus_var (Fin.FS (Fin.FS Fin.F1)))))).

Definition peano_minus_mul_comm_sentence : sentence oring_language :=
  @arithmetic_all_sentence 2
    (arithmetic_eq_formula
      (arithmetic_mul_term (peano_minus_var Fin.F1)
        (peano_minus_var (Fin.FS Fin.F1)))
      (arithmetic_mul_term (peano_minus_var (Fin.FS Fin.F1))
        (peano_minus_var Fin.F1))).

Definition peano_minus_mul_lt_mul_sentence : sentence oring_language :=
  @arithmetic_all_sentence 3
    (semiformula_imp
      (Semiformula_and
        (arithmetic_lt_formula (peano_minus_var Fin.F1)
          (peano_minus_var (Fin.FS Fin.F1)))
        (arithmetic_lt_formula arithmetic_zero_term
          (peano_minus_var (Fin.FS (Fin.FS Fin.F1)))))
      (arithmetic_lt_formula
        (arithmetic_mul_term (peano_minus_var Fin.F1)
          (peano_minus_var (Fin.FS (Fin.FS Fin.F1))))
        (arithmetic_mul_term (peano_minus_var (Fin.FS Fin.F1))
          (peano_minus_var (Fin.FS (Fin.FS Fin.F1)))))).

Definition peano_minus_mul_add_distr_sentence : sentence oring_language :=
  @arithmetic_all_sentence 3
    (arithmetic_eq_formula
      (arithmetic_mul_term (peano_minus_var Fin.F1)
        (arithmetic_add_term (peano_minus_var (Fin.FS Fin.F1))
          (peano_minus_var (Fin.FS (Fin.FS Fin.F1)))))
      (arithmetic_add_term
        (arithmetic_mul_term (peano_minus_var Fin.F1)
          (peano_minus_var (Fin.FS Fin.F1)))
        (arithmetic_mul_term (peano_minus_var Fin.F1)
          (peano_minus_var (Fin.FS (Fin.FS Fin.F1)))))).

Definition peano_minus_lt_irrefl_sentence : sentence oring_language :=
  @arithmetic_all_sentence 1
    (semiformula_neg
      (arithmetic_lt_formula (peano_minus_var Fin.F1)
        (peano_minus_var Fin.F1))).

Definition peano_minus_lt_trans_sentence : sentence oring_language :=
  @arithmetic_all_sentence 3
    (semiformula_imp
      (Semiformula_and
        (arithmetic_lt_formula (peano_minus_var Fin.F1)
          (peano_minus_var (Fin.FS Fin.F1)))
        (arithmetic_lt_formula (peano_minus_var (Fin.FS Fin.F1))
          (peano_minus_var (Fin.FS (Fin.FS Fin.F1)))))
      (arithmetic_lt_formula (peano_minus_var Fin.F1)
        (peano_minus_var (Fin.FS (Fin.FS Fin.F1))))).

Definition peano_minus_lt_trichotomy_sentence : sentence oring_language :=
  @arithmetic_all_sentence 2
    (Semiformula_or
      (arithmetic_lt_formula (peano_minus_var Fin.F1)
        (peano_minus_var (Fin.FS Fin.F1)))
      (Semiformula_or
        (arithmetic_eq_formula (peano_minus_var Fin.F1)
          (peano_minus_var (Fin.FS Fin.F1)))
        (arithmetic_lt_formula (peano_minus_var (Fin.FS Fin.F1))
          (peano_minus_var Fin.F1)))).

Inductive peano_minus_axiom : theory oring_language :=
| PeanoMinusEquality : forall sigma,
    first_order_equality_axiom oring_language_eq_operator sigma ->
    peano_minus_axiom sigma
| PeanoMinusAddZero : peano_minus_axiom peano_minus_add_zero_sentence
| PeanoMinusAddAssoc : peano_minus_axiom peano_minus_add_assoc_sentence
| PeanoMinusAddComm : peano_minus_axiom peano_minus_add_comm_sentence
| PeanoMinusAddEqOfLt :
    peano_minus_axiom peano_minus_add_eq_of_lt_sentence
| PeanoMinusZeroLe : peano_minus_axiom peano_minus_zero_le_sentence
| PeanoMinusZeroLtOne :
    peano_minus_axiom peano_minus_zero_lt_one_sentence
| PeanoMinusOneLeOfZeroLt :
    peano_minus_axiom peano_minus_one_le_of_zero_lt_sentence
| PeanoMinusAddLtAdd : peano_minus_axiom peano_minus_add_lt_add_sentence
| PeanoMinusMulZero : peano_minus_axiom peano_minus_mul_zero_sentence
| PeanoMinusMulOne : peano_minus_axiom peano_minus_mul_one_sentence
| PeanoMinusMulAssoc : peano_minus_axiom peano_minus_mul_assoc_sentence
| PeanoMinusMulComm : peano_minus_axiom peano_minus_mul_comm_sentence
| PeanoMinusMulLtMul : peano_minus_axiom peano_minus_mul_lt_mul_sentence
| PeanoMinusMulAddDistr :
    peano_minus_axiom peano_minus_mul_add_distr_sentence
| PeanoMinusLtIrrefl : peano_minus_axiom peano_minus_lt_irrefl_sentence
| PeanoMinusLtTrans : peano_minus_axiom peano_minus_lt_trans_sentence
| PeanoMinusLtTrichotomy :
    peano_minus_axiom peano_minus_lt_trichotomy_sentence.

Definition peano_minus_axiom_list : list (sentence oring_language) :=
  first_order_equality_axiom_list oring_language_eq_operator
    oring_language_finite ++
  [peano_minus_add_zero_sentence;
   peano_minus_add_assoc_sentence;
   peano_minus_add_comm_sentence;
   peano_minus_add_eq_of_lt_sentence;
   peano_minus_zero_le_sentence;
   peano_minus_zero_lt_one_sentence;
   peano_minus_one_le_of_zero_lt_sentence;
   peano_minus_add_lt_add_sentence;
   peano_minus_mul_zero_sentence;
   peano_minus_mul_one_sentence;
   peano_minus_mul_assoc_sentence;
   peano_minus_mul_comm_sentence;
   peano_minus_mul_lt_mul_sentence;
   peano_minus_mul_add_distr_sentence;
   peano_minus_lt_irrefl_sentence;
   peano_minus_lt_trans_sentence;
   peano_minus_lt_trichotomy_sentence].

Lemma peano_minus_axiom_list_complete : forall sigma,
  peano_minus_axiom sigma -> In sigma peano_minus_axiom_list.
Proof.
  intros sigma Hsigma. destruct Hsigma; unfold peano_minus_axiom_list.
  - apply in_or_app. left.
    now apply first_order_equality_axiom_list_complete.
  - apply in_or_app. right. simpl; tauto.
  - apply in_or_app. right. simpl; tauto.
  - apply in_or_app. right. simpl; tauto.
  - apply in_or_app. right. simpl; tauto.
  - apply in_or_app. right. simpl; tauto.
  - apply in_or_app. right. simpl; tauto.
  - apply in_or_app. right. simpl; tauto.
  - apply in_or_app. right. simpl; tauto.
  - apply in_or_app. right. simpl; tauto.
  - apply in_or_app. right. simpl; tauto.
  - apply in_or_app. right. simpl; tauto.
  - apply in_or_app. right. simpl; tauto.
  - apply in_or_app. right. simpl; tauto.
  - apply in_or_app. right. simpl; tauto.
  - apply in_or_app. right. simpl; tauto.
  - apply in_or_app. right. simpl; tauto.
  - apply in_or_app. right. simpl; tauto.
Qed.

Theorem peano_minus_axiom_finitely_covered :
  set_finitely_covered peano_minus_axiom.
Proof.
  exists peano_minus_axiom_list.
  intros sigma Hsigma. now apply peano_minus_axiom_list_complete.
Qed.

Theorem peano_minus_proves_equality :
  first_order_theory_proves_equality
    peano_minus_axiom oring_language_eq_operator.
Proof.
  intros sigma Hsigma.
  exact (@generic_axiomatized_by_axiom
    (theory oring_language) (sentence oring_language)
    (first_order_theory_entailment oring_language)
    (generic_predicate_adjunctive_set (sentence oring_language))
    (first_order_theory_axiomatized oring_language)
    peano_minus_axiom sigma (PeanoMinusEquality Hsigma)).
Qed.

(** * Exact semantics *)

Definition peano_minus_fin_three {A : Type} (x y z : A) (i : Fin.t 3) : A :=
  match i with
  | Fin.F1 => x
  | Fin.FS j =>
      match j with
      | Fin.F1 => y
      | Fin.FS _ => z
      end
  end.

Lemma peano_minus_eval_and : forall L M X n
    (Str : first_order_structure L M) (b : Fin.t n -> M) (f : X -> M)
    (p q : semiformula L X n),
  semiformula_eval Str b f (Semiformula_and p q) <->
  semiformula_eval Str b f p /\ semiformula_eval Str b f q.
Proof. reflexivity. Qed.

Lemma peano_minus_eval_or : forall L M X n
    (Str : first_order_structure L M) (b : Fin.t n -> M) (f : X -> M)
    (p q : semiformula L X n),
  semiformula_eval Str b f (Semiformula_or p q) <->
  semiformula_eval Str b f p \/ semiformula_eval Str b f q.
Proof. reflexivity. Qed.

Lemma peano_minus_eval_exists : forall L M X n
    (Str : first_order_structure L M) (b : Fin.t n -> M) (f : X -> M)
    (p : semiformula L X (S n)),
  semiformula_eval Str b f (Semiformula_exists p) <->
  exists x, semiformula_eval Str (fin_env_cons x b) f p.
Proof. reflexivity. Qed.

Ltac peano_minus_normalize_atoms O Horing :=
  repeat match goal with
  | H : context [semiformula_eval ?Str ?b ?f
      (arithmetic_eq_formula ?t ?u)] |- _ =>
      rewrite (@arithmetic_eq_formula_eval _ _ _ Str b f O t u Horing) in H
  | |- context [semiformula_eval ?Str ?b ?f
      (arithmetic_eq_formula ?t ?u)] =>
      rewrite (@arithmetic_eq_formula_eval _ _ _ Str b f O t u Horing)
  | H : context [semiformula_eval ?Str ?b ?f
      (arithmetic_lt_formula ?t ?u)] |- _ =>
      rewrite (@arithmetic_lt_formula_eval _ _ _ Str b f O t u Horing) in H
  | |- context [semiformula_eval ?Str ?b ?f
      (arithmetic_lt_formula ?t ?u)] =>
      rewrite (@arithmetic_lt_formula_eval _ _ _ Str b f O t u Horing)
  | H : context [semiformula_eval ?Str ?b ?f
      (arithmetic_le_formula ?t ?u)] |- _ =>
      rewrite (@arithmetic_le_formula_eval _ _ _ Str b f O t u Horing) in H
  | |- context [semiformula_eval ?Str ?b ?f
      (arithmetic_le_formula ?t ?u)] =>
      rewrite (@arithmetic_le_formula_eval _ _ _ Str b f O t u Horing)
  | H : context [semiterm_val ?Str ?b ?f
      (arithmetic_add_term ?t ?u)] |- _ =>
      rewrite (@arithmetic_add_term_val _ _ _ Str b f O t u Horing) in H
  | |- context [semiterm_val ?Str ?b ?f
      (arithmetic_add_term ?t ?u)] =>
      rewrite (@arithmetic_add_term_val _ _ _ Str b f O t u Horing)
  | H : context [semiterm_val ?Str ?b ?f
      (arithmetic_mul_term ?t ?u)] |- _ =>
      rewrite (@arithmetic_mul_term_val _ _ _ Str b f O t u Horing) in H
  | |- context [semiterm_val ?Str ?b ?f
      (arithmetic_mul_term ?t ?u)] =>
      rewrite (@arithmetic_mul_term_val _ _ _ Str b f O t u Horing)
  | H : context [semiterm_val ?Str ?b ?f arithmetic_zero_term] |- _ =>
      rewrite (@arithmetic_zero_term_val _ _ _ Str b f O Horing) in H
  | |- context [semiterm_val ?Str ?b ?f arithmetic_zero_term] =>
      rewrite (@arithmetic_zero_term_val _ _ _ Str b f O Horing)
  | H : context [semiterm_val ?Str ?b ?f arithmetic_one_term] |- _ =>
      rewrite (@arithmetic_one_term_val _ _ _ Str b f O Horing) in H
  | |- context [semiterm_val ?Str ?b ?f arithmetic_one_term] =>
      rewrite (@arithmetic_one_term_val _ _ _ Str b f O Horing)
  end;
  cbn [peano_minus_var fin_one fin_two peano_minus_fin_three
    fin_env_cons semiterm_val] in *.

Lemma peano_minus_add_zero_realize_iff : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  (sentence_realize Str peano_minus_add_zero_sentence <->
   forall x, oring_add O x (oring_zero O) = x).
Proof.
  intros M Str O Horing. unfold peano_minus_add_zero_sentence.
  rewrite arithmetic_all_sentence_eval. split.
  - intros H x. specialize (H (fin_one x)).
    rewrite (@arithmetic_eq_formula_eval M Empty_set 1 Str (fin_one x)
      arithmetic_empty_free_env O _ _ Horing) in H.
    rewrite (@arithmetic_add_term_val M Empty_set 1 Str (fin_one x)
      arithmetic_empty_free_env O _ _ Horing) in H.
    rewrite (@arithmetic_zero_term_val M Empty_set 1 Str (fin_one x)
      arithmetic_empty_free_env O Horing) in H.
    simpl in H. exact H.
  - intros H e. specialize (H (e Fin.F1)).
    rewrite (@arithmetic_eq_formula_eval M Empty_set 1 Str e
      arithmetic_empty_free_env O _ _ Horing).
    rewrite (@arithmetic_add_term_val M Empty_set 1 Str e
      arithmetic_empty_free_env O _ _ Horing).
    rewrite (@arithmetic_zero_term_val M Empty_set 1 Str e
      arithmetic_empty_free_env O Horing).
    simpl. exact H.
Qed.

Lemma peano_minus_add_assoc_realize_iff : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  (sentence_realize Str peano_minus_add_assoc_sentence <->
   forall x y z,
     oring_add O (oring_add O x y) z =
     oring_add O x (oring_add O y z)).
Proof.
  intros M Str O Horing. unfold peano_minus_add_assoc_sentence.
  rewrite arithmetic_all_sentence_eval. split.
  - intros H x y z. specialize (H (peano_minus_fin_three x y z)).
    peano_minus_normalize_atoms O Horing. exact H.
  - intros H e. specialize (H (e Fin.F1) (e (Fin.FS Fin.F1))
      (e (Fin.FS (Fin.FS Fin.F1)))).
    peano_minus_normalize_atoms O Horing. exact H.
Qed.

Lemma peano_minus_add_comm_realize_iff : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  (sentence_realize Str peano_minus_add_comm_sentence <->
   forall x y, oring_add O x y = oring_add O y x).
Proof.
  intros M Str O Horing. unfold peano_minus_add_comm_sentence.
  rewrite arithmetic_all_sentence_eval. split.
  - intros H x y. specialize (H (fin_two x y)).
    peano_minus_normalize_atoms O Horing. exact H.
  - intros H e. specialize (H (e Fin.F1) (e (Fin.FS Fin.F1))).
    peano_minus_normalize_atoms O Horing. exact H.
Qed.

Lemma peano_minus_zero_le_realize_iff : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  (sentence_realize Str peano_minus_zero_le_sentence <->
   forall x, peano_minus_le O (oring_zero O) x).
Proof.
  intros M Str O Horing. unfold peano_minus_zero_le_sentence.
  rewrite arithmetic_all_sentence_eval. split.
  - intros H x. specialize (H (fin_one x)).
    peano_minus_normalize_atoms O Horing. exact H.
  - intros H e. specialize (H (e Fin.F1)).
    peano_minus_normalize_atoms O Horing. exact H.
Qed.

Lemma peano_minus_zero_lt_one_realize_iff : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  (sentence_realize Str peano_minus_zero_lt_one_sentence <->
   oring_lt O (oring_zero O) (oring_one O)).
Proof.
  intros M Str O Horing. unfold peano_minus_zero_lt_one_sentence,
    sentence_realize, formula_eval.
  peano_minus_normalize_atoms O Horing. reflexivity.
Qed.

Lemma peano_minus_mul_zero_realize_iff : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  (sentence_realize Str peano_minus_mul_zero_sentence <->
   forall x, oring_mul O x (oring_zero O) = oring_zero O).
Proof.
  intros M Str O Horing. unfold peano_minus_mul_zero_sentence.
  rewrite arithmetic_all_sentence_eval. split.
  - intros H x. specialize (H (fin_one x)).
    peano_minus_normalize_atoms O Horing. exact H.
  - intros H e. specialize (H (e Fin.F1)).
    peano_minus_normalize_atoms O Horing. exact H.
Qed.

Lemma peano_minus_mul_one_realize_iff : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  (sentence_realize Str peano_minus_mul_one_sentence <->
   forall x, oring_mul O x (oring_one O) = x).
Proof.
  intros M Str O Horing. unfold peano_minus_mul_one_sentence.
  rewrite arithmetic_all_sentence_eval. split.
  - intros H x. specialize (H (fin_one x)).
    peano_minus_normalize_atoms O Horing. exact H.
  - intros H e. specialize (H (e Fin.F1)).
    peano_minus_normalize_atoms O Horing. exact H.
Qed.

Lemma peano_minus_mul_assoc_realize_iff : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  (sentence_realize Str peano_minus_mul_assoc_sentence <->
   forall x y z,
     oring_mul O (oring_mul O x y) z =
     oring_mul O x (oring_mul O y z)).
Proof.
  intros M Str O Horing. unfold peano_minus_mul_assoc_sentence.
  rewrite arithmetic_all_sentence_eval. split.
  - intros H x y z. specialize (H (peano_minus_fin_three x y z)).
    peano_minus_normalize_atoms O Horing. exact H.
  - intros H e. specialize (H (e Fin.F1) (e (Fin.FS Fin.F1))
      (e (Fin.FS (Fin.FS Fin.F1)))).
    peano_minus_normalize_atoms O Horing. exact H.
Qed.

Lemma peano_minus_mul_comm_realize_iff : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  (sentence_realize Str peano_minus_mul_comm_sentence <->
   forall x y, oring_mul O x y = oring_mul O y x).
Proof.
  intros M Str O Horing. unfold peano_minus_mul_comm_sentence.
  rewrite arithmetic_all_sentence_eval. split.
  - intros H x y. specialize (H (fin_two x y)).
    peano_minus_normalize_atoms O Horing. exact H.
  - intros H e. specialize (H (e Fin.F1) (e (Fin.FS Fin.F1))).
    peano_minus_normalize_atoms O Horing. exact H.
Qed.

Lemma peano_minus_mul_add_distr_realize_iff : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  (sentence_realize Str peano_minus_mul_add_distr_sentence <->
   forall x y z,
     oring_mul O x (oring_add O y z) =
     oring_add O (oring_mul O x y) (oring_mul O x z)).
Proof.
  intros M Str O Horing. unfold peano_minus_mul_add_distr_sentence.
  rewrite arithmetic_all_sentence_eval. split.
  - intros H x y z. specialize (H (peano_minus_fin_three x y z)).
    peano_minus_normalize_atoms O Horing. exact H.
  - intros H e. specialize (H (e Fin.F1) (e (Fin.FS Fin.F1))
      (e (Fin.FS (Fin.FS Fin.F1)))).
    peano_minus_normalize_atoms O Horing. exact H.
Qed.

Lemma peano_minus_add_eq_of_lt_realize_iff : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  (sentence_realize Str peano_minus_add_eq_of_lt_sentence <->
   forall x y, oring_lt O x y ->
     exists z, oring_add O x z = y).
Proof.
  intros M Str O Horing. unfold peano_minus_add_eq_of_lt_sentence.
  rewrite arithmetic_all_sentence_eval. split.
  - intros H x y. specialize (H (fin_two x y)).
    rewrite semiformula_eval_imp in H.
    setoid_rewrite peano_minus_eval_exists in H.
    peano_minus_normalize_atoms O Horing.
    intro Hxy. destruct (H Hxy) as [z Hz]. exists z.
    peano_minus_normalize_atoms O Horing. exact Hz.
  - intros H e. specialize (H (e Fin.F1) (e (Fin.FS Fin.F1))).
    rewrite semiformula_eval_imp.
    setoid_rewrite peano_minus_eval_exists.
    peano_minus_normalize_atoms O Horing.
    intro Hxy. destruct (H Hxy) as [z Hz]. exists z.
    peano_minus_normalize_atoms O Horing. exact Hz.
Qed.

Lemma peano_minus_one_le_of_zero_lt_realize_iff : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  (sentence_realize Str peano_minus_one_le_of_zero_lt_sentence <->
   forall x, oring_lt O (oring_zero O) x ->
     peano_minus_le O (oring_one O) x).
Proof.
  intros M Str O Horing. unfold peano_minus_one_le_of_zero_lt_sentence.
  rewrite arithmetic_all_sentence_eval. split.
  - intros H x. specialize (H (fin_one x)).
    rewrite semiformula_eval_imp in H.
    peano_minus_normalize_atoms O Horing. exact H.
  - intros H e. specialize (H (e Fin.F1)).
    rewrite semiformula_eval_imp.
    peano_minus_normalize_atoms O Horing. exact H.
Qed.

Lemma peano_minus_add_lt_add_realize_iff : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  (sentence_realize Str peano_minus_add_lt_add_sentence <->
   forall x y z, oring_lt O x y ->
     oring_lt O (oring_add O x z) (oring_add O y z)).
Proof.
  intros M Str O Horing. unfold peano_minus_add_lt_add_sentence.
  rewrite arithmetic_all_sentence_eval. split.
  - intros H x y z. specialize (H (peano_minus_fin_three x y z)).
    rewrite semiformula_eval_imp in H.
    peano_minus_normalize_atoms O Horing. exact H.
  - intros H e. specialize (H (e Fin.F1) (e (Fin.FS Fin.F1))
      (e (Fin.FS (Fin.FS Fin.F1)))).
    rewrite semiformula_eval_imp.
    peano_minus_normalize_atoms O Horing. exact H.
Qed.

Lemma peano_minus_mul_lt_mul_realize_iff : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  (sentence_realize Str peano_minus_mul_lt_mul_sentence <->
   forall x y z, oring_lt O x y -> oring_lt O (oring_zero O) z ->
     oring_lt O (oring_mul O x z) (oring_mul O y z)).
Proof.
  intros M Str O Horing. unfold peano_minus_mul_lt_mul_sentence.
  rewrite arithmetic_all_sentence_eval. split.
  - intros H x y z. specialize (H (peano_minus_fin_three x y z)).
    rewrite semiformula_eval_imp in H.
    setoid_rewrite peano_minus_eval_and in H.
    peano_minus_normalize_atoms O Horing.
    intros Hxy Hz. now apply H.
  - intros H e. specialize (H (e Fin.F1) (e (Fin.FS Fin.F1))
      (e (Fin.FS (Fin.FS Fin.F1)))).
    rewrite semiformula_eval_imp.
    setoid_rewrite peano_minus_eval_and.
    peano_minus_normalize_atoms O Horing.
    intros [Hxy Hz]. now apply H.
Qed.

Lemma peano_minus_lt_irrefl_realize_iff : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  (sentence_realize Str peano_minus_lt_irrefl_sentence <->
   forall x, ~ oring_lt O x x).
Proof.
  intros M Str O Horing. unfold peano_minus_lt_irrefl_sentence.
  rewrite arithmetic_all_sentence_eval. split.
  - intros H x. specialize (H (fin_one x)).
    rewrite semiformula_eval_neg in H.
    peano_minus_normalize_atoms O Horing. exact H.
  - intros H e. specialize (H (e Fin.F1)).
    rewrite semiformula_eval_neg.
    peano_minus_normalize_atoms O Horing. exact H.
Qed.

Lemma peano_minus_lt_trans_realize_iff : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  (sentence_realize Str peano_minus_lt_trans_sentence <->
   forall x y z, oring_lt O x y -> oring_lt O y z ->
     oring_lt O x z).
Proof.
  intros M Str O Horing. unfold peano_minus_lt_trans_sentence.
  rewrite arithmetic_all_sentence_eval. split.
  - intros H x y z. specialize (H (peano_minus_fin_three x y z)).
    rewrite semiformula_eval_imp in H.
    setoid_rewrite peano_minus_eval_and in H.
    peano_minus_normalize_atoms O Horing.
    intros Hxy Hyz. now apply H.
  - intros H e. specialize (H (e Fin.F1) (e (Fin.FS Fin.F1))
      (e (Fin.FS (Fin.FS Fin.F1)))).
    rewrite semiformula_eval_imp.
    setoid_rewrite peano_minus_eval_and.
    peano_minus_normalize_atoms O Horing.
    intros [Hxy Hyz]. now apply H.
Qed.

Lemma peano_minus_lt_trichotomy_realize_iff : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  (sentence_realize Str peano_minus_lt_trichotomy_sentence <->
   forall x y, oring_lt O x y \/ x = y \/ oring_lt O y x).
Proof.
  intros M Str O Horing. unfold peano_minus_lt_trichotomy_sentence.
  rewrite arithmetic_all_sentence_eval. split.
  - intros H x y. specialize (H (fin_two x y)).
    repeat setoid_rewrite peano_minus_eval_or in H.
    peano_minus_normalize_atoms O Horing. exact H.
  - intros H e. specialize (H (e Fin.F1) (e (Fin.FS Fin.F1))).
    repeat setoid_rewrite peano_minus_eval_or.
    peano_minus_normalize_atoms O Horing. exact H.
Qed.

(** Modeling the concrete finite theory is exactly the semantic law package
    used by the algebraic development. *)
Theorem first_order_model_models_peano_minus_iff : forall
    (m : first_order_model oring_language)
    (O : oring_carrier (first_order_model_domain m)),
  structure_interprets_oring (first_order_model_structure m)
    oring_language_structure O ->
  (first_order_models_theory m peano_minus_axiom <->
   peano_minus_laws O).
Proof.
  intros m O Horing. split.
  - intro Hmodels. constructor.
    + apply (proj1 (peano_minus_add_zero_realize_iff Horing)).
      exact (first_order_models_of_member Hmodels PeanoMinusAddZero).
    + apply (proj1 (peano_minus_add_assoc_realize_iff Horing)).
      exact (first_order_models_of_member Hmodels PeanoMinusAddAssoc).
    + apply (proj1 (peano_minus_add_comm_realize_iff Horing)).
      exact (first_order_models_of_member Hmodels PeanoMinusAddComm).
    + apply (proj1 (peano_minus_add_eq_of_lt_realize_iff Horing)).
      exact (first_order_models_of_member Hmodels PeanoMinusAddEqOfLt).
    + apply (proj1 (peano_minus_zero_le_realize_iff Horing)).
      exact (first_order_models_of_member Hmodels PeanoMinusZeroLe).
    + apply (proj1 (peano_minus_zero_lt_one_realize_iff Horing)).
      exact (first_order_models_of_member Hmodels PeanoMinusZeroLtOne).
    + apply (proj1 (peano_minus_one_le_of_zero_lt_realize_iff Horing)).
      exact (first_order_models_of_member Hmodels PeanoMinusOneLeOfZeroLt).
    + apply (proj1 (peano_minus_add_lt_add_realize_iff Horing)).
      exact (first_order_models_of_member Hmodels PeanoMinusAddLtAdd).
    + apply (proj1 (peano_minus_mul_zero_realize_iff Horing)).
      exact (first_order_models_of_member Hmodels PeanoMinusMulZero).
    + apply (proj1 (peano_minus_mul_one_realize_iff Horing)).
      exact (first_order_models_of_member Hmodels PeanoMinusMulOne).
    + apply (proj1 (peano_minus_mul_assoc_realize_iff Horing)).
      exact (first_order_models_of_member Hmodels PeanoMinusMulAssoc).
    + apply (proj1 (peano_minus_mul_comm_realize_iff Horing)).
      exact (first_order_models_of_member Hmodels PeanoMinusMulComm).
    + apply (proj1 (peano_minus_mul_lt_mul_realize_iff Horing)).
      exact (first_order_models_of_member Hmodels PeanoMinusMulLtMul).
    + apply (proj1 (peano_minus_mul_add_distr_realize_iff Horing)).
      exact (first_order_models_of_member Hmodels PeanoMinusMulAddDistr).
    + apply (proj1 (peano_minus_lt_irrefl_realize_iff Horing)).
      exact (first_order_models_of_member Hmodels PeanoMinusLtIrrefl).
    + apply (proj1 (peano_minus_lt_trans_realize_iff Horing)).
      exact (first_order_models_of_member Hmodels PeanoMinusLtTrans).
    + apply (proj1 (peano_minus_lt_trichotomy_realize_iff Horing)).
      exact (first_order_models_of_member Hmodels PeanoMinusLtTrichotomy).
  - intro Hlaws. apply (proj2 (first_order_models_theory_iff m _)).
    intros sigma Hsigma. destruct Hsigma.
    + exact (first_order_models_of_member
        (first_order_model_models_equality_theory_of_interprets_eq
          (structure_oring_eq Horing)) H).
    + apply (proj2 (peano_minus_add_zero_realize_iff Horing)).
      exact (peano_minus_add_zero Hlaws).
    + apply (proj2 (peano_minus_add_assoc_realize_iff Horing)).
      exact (peano_minus_add_assoc Hlaws).
    + apply (proj2 (peano_minus_add_comm_realize_iff Horing)).
      exact (peano_minus_add_comm Hlaws).
    + apply (proj2 (peano_minus_add_eq_of_lt_realize_iff Horing)).
      exact (peano_minus_add_eq_of_lt Hlaws).
    + apply (proj2 (peano_minus_zero_le_realize_iff Horing)).
      exact (peano_minus_zero_le Hlaws).
    + apply (proj2 (peano_minus_zero_lt_one_realize_iff Horing)).
      exact (peano_minus_zero_lt_one Hlaws).
    + apply (proj2 (peano_minus_one_le_of_zero_lt_realize_iff Horing)).
      exact (peano_minus_one_le_of_zero_lt Hlaws).
    + apply (proj2 (peano_minus_add_lt_add_realize_iff Horing)).
      exact (peano_minus_add_lt_add Hlaws).
    + apply (proj2 (peano_minus_mul_zero_realize_iff Horing)).
      exact (peano_minus_mul_zero Hlaws).
    + apply (proj2 (peano_minus_mul_one_realize_iff Horing)).
      exact (peano_minus_mul_one Hlaws).
    + apply (proj2 (peano_minus_mul_assoc_realize_iff Horing)).
      exact (peano_minus_mul_assoc Hlaws).
    + apply (proj2 (peano_minus_mul_comm_realize_iff Horing)).
      exact (peano_minus_mul_comm Hlaws).
    + apply (proj2 (peano_minus_mul_lt_mul_realize_iff Horing)).
      exact (peano_minus_mul_lt_mul Hlaws).
    + apply (proj2 (peano_minus_mul_add_distr_realize_iff Horing)).
      exact (peano_minus_mul_add_distr Hlaws).
    + apply (proj2 (peano_minus_lt_irrefl_realize_iff Horing)).
      exact (peano_minus_lt_irrefl Hlaws).
    + apply (proj2 (peano_minus_lt_trans_realize_iff Horing)).
      exact (peano_minus_lt_trans Hlaws).
    + apply (proj2 (peano_minus_lt_trichotomy_realize_iff Horing)).
      exact (peano_minus_lt_trichotomy Hlaws).
Qed.

Theorem nat_standard_model_models_peano_minus :
  first_order_models_theory nat_standard_model peano_minus_axiom.
Proof.
  apply (proj2 (@first_order_model_models_peano_minus_iff
    nat_standard_model nat_oring_carrier nat_standard_structure_interprets)).
  exact nat_peano_minus_laws.
Qed.

Theorem peano_minus_consistent :
  generic_consistent
    (first_order_theory_entailment oring_language) peano_minus_axiom.
Proof.
  exact (first_order_theory_consistent_of_model
    nat_standard_model_models_peano_minus).
Qed.

Theorem peano_minus_proof_complete : forall sigma : sentence oring_language,
  (forall (m : first_order_model oring_language)
          (O : oring_carrier (first_order_model_domain m)),
    structure_interprets_oring (first_order_model_structure m)
      oring_language_structure O ->
    peano_minus_laws O ->
    first_order_model_realize m sigma) ->
  first_order_theory_provable peano_minus_axiom sigma.
Proof.
  intros sigma Hvalid.
  apply (arithmetic_theory_proof_complete peano_minus_proves_equality).
  intros m O Horing Hmodels.
  apply (Hvalid m O Horing).
  now apply (proj1 (@first_order_model_models_peano_minus_iff m O Horing)).
Qed.

Theorem robinson_q_weaker_than_peano_minus :
  generic_weaker_than
    (first_order_theory_entailment oring_language)
    (first_order_theory_entailment oring_language)
    robinson_q_axiom peano_minus_axiom.
Proof.
  apply (arithmetic_theory_weaker_of_models peano_minus_proves_equality).
  intros m O Horing Hmodels.
  apply (proj2 (@first_order_model_models_robinson_q_iff m O Horing)).
  apply peano_minus_robinson_q_laws.
  now apply (proj1 (@first_order_model_models_peano_minus_iff m O Horing)).
Qed.

Theorem r0_weaker_than_peano_minus :
  generic_weaker_than
    (first_order_theory_entailment oring_language)
    (first_order_theory_entailment oring_language)
    r0_axiom peano_minus_axiom.
Proof.
  exact (generic_weaker_than_trans r0_weaker_than_robinson_q
    robinson_q_weaker_than_peano_minus).
Qed.

Theorem r0_strictly_weaker_than_peano_minus :
  generic_strictly_weaker_than
    (first_order_theory_entailment oring_language)
    (first_order_theory_entailment oring_language)
    r0_axiom peano_minus_axiom.
Proof.
  exact (generic_strict_weaker_weaker_trans
    r0_strictly_weaker_than_robinson_q
    robinson_q_weaker_than_peano_minus).
Qed.
