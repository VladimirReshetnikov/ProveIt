(**
  Semantic core of Robinson arithmetic Q.

  Foundation encodes these laws as a finite first-order theory.  This module
  exposes exactly the eight non-equality axioms as a model capability and
  derives their reusable arithmetic consequences without depending on a
  particular entailment calculus.
*)

From Stdlib Require Import Arith.PeanoNat Lia Lists.List Logic.Classical_Prop
  Vectors.Fin.
From FoundationModal Require Import GenericAdjunctiveSet GenericEntailment.
From Foundation.Vorspiel.Set Require Import Cofinite.
From Foundation.Syntax.Predicate Require Import Language Quantifier Term.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Calculus Eq Operator Soundness.
From Foundation.FirstOrder.Basic.Semantics Require Import
  ModelTheory RewriteClosure Semantics OperatorSemantics.
From Foundation.FirstOrder.Arithmetic.Basic Require Import Misc Syntax Model.
From Foundation.FirstOrder.Arithmetic.R0 Require Import Basic.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Import ListNotations.

(** * The concrete Robinson-Q theory *)

Definition arithmetic_empty_free_env {A} : Empty_set -> A :=
  fun x => match x with end.

Definition arithmetic_all_sentence k
    (p : semisentence oring_language k) : sentence oring_language :=
  first_all_closure
    (semiformula_universal_quantifier oring_language Empty_set) k p.

Definition robinson_q_succ_ne_zero_sentence : sentence oring_language :=
  @arithmetic_all_sentence 1
    (semiformula_neg
      (arithmetic_eq_formula
        (arithmetic_add_one_term
          (@Semiterm_bvar oring_language Empty_set 1 Fin.F1))
        arithmetic_zero_term)).

Definition robinson_q_succ_inj_sentence : sentence oring_language :=
  @arithmetic_all_sentence 2
    (semiformula_imp
      (arithmetic_eq_formula
        (arithmetic_add_one_term
          (@Semiterm_bvar oring_language Empty_set 2 Fin.F1))
        (arithmetic_add_one_term
          (@Semiterm_bvar oring_language Empty_set 2 (Fin.FS Fin.F1))))
      (arithmetic_eq_formula
        (@Semiterm_bvar oring_language Empty_set 2 Fin.F1)
        (@Semiterm_bvar oring_language Empty_set 2 (Fin.FS Fin.F1)))).

Definition robinson_q_zero_or_succ_sentence : sentence oring_language :=
  @arithmetic_all_sentence 1
    (Semiformula_or
      (arithmetic_eq_formula
        (@Semiterm_bvar oring_language Empty_set 1 Fin.F1)
        arithmetic_zero_term)
      (Semiformula_exists
        (arithmetic_eq_formula
          (@Semiterm_bvar oring_language Empty_set 2 (Fin.FS Fin.F1))
          (arithmetic_add_one_term
            (@Semiterm_bvar oring_language Empty_set 2 Fin.F1))))).

Definition robinson_q_add_zero_sentence : sentence oring_language :=
  @arithmetic_all_sentence 1
    (arithmetic_eq_formula
      (arithmetic_add_term
        (@Semiterm_bvar oring_language Empty_set 1 Fin.F1)
        arithmetic_zero_term)
      (@Semiterm_bvar oring_language Empty_set 1 Fin.F1)).

Definition robinson_q_add_succ_sentence : sentence oring_language :=
  @arithmetic_all_sentence 2
    (arithmetic_eq_formula
      (arithmetic_add_term
        (@Semiterm_bvar oring_language Empty_set 2 Fin.F1)
        (arithmetic_add_one_term
          (@Semiterm_bvar oring_language Empty_set 2 (Fin.FS Fin.F1))))
      (arithmetic_add_one_term
        (arithmetic_add_term
          (@Semiterm_bvar oring_language Empty_set 2 Fin.F1)
          (@Semiterm_bvar oring_language Empty_set 2 (Fin.FS Fin.F1))))).

Definition robinson_q_mul_zero_sentence : sentence oring_language :=
  @arithmetic_all_sentence 1
    (arithmetic_eq_formula
      (arithmetic_mul_term
        (@Semiterm_bvar oring_language Empty_set 1 Fin.F1)
        arithmetic_zero_term)
      arithmetic_zero_term).

Definition robinson_q_mul_succ_sentence : sentence oring_language :=
  @arithmetic_all_sentence 2
    (arithmetic_eq_formula
      (arithmetic_mul_term
        (@Semiterm_bvar oring_language Empty_set 2 Fin.F1)
        (arithmetic_add_one_term
          (@Semiterm_bvar oring_language Empty_set 2 (Fin.FS Fin.F1))))
      (arithmetic_add_term
        (arithmetic_mul_term
          (@Semiterm_bvar oring_language Empty_set 2 Fin.F1)
          (@Semiterm_bvar oring_language Empty_set 2 (Fin.FS Fin.F1)))
        (@Semiterm_bvar oring_language Empty_set 2 Fin.F1))).

Definition robinson_q_lt_def_sentence : sentence oring_language :=
  @arithmetic_all_sentence 2
    (semiformula_iff
      (arithmetic_lt_formula
        (@Semiterm_bvar oring_language Empty_set 2 Fin.F1)
        (@Semiterm_bvar oring_language Empty_set 2 (Fin.FS Fin.F1)))
      (Semiformula_exists
        (arithmetic_eq_formula
          (arithmetic_add_term
            (@Semiterm_bvar oring_language Empty_set 3 (Fin.FS Fin.F1))
            (arithmetic_add_one_term
              (@Semiterm_bvar oring_language Empty_set 3 Fin.F1)))
          (@Semiterm_bvar oring_language Empty_set 3
            (Fin.FS (Fin.FS Fin.F1)))))).

Inductive robinson_q_axiom : theory oring_language :=
| RobinsonQEquality : forall sigma,
    first_order_equality_axiom oring_language_eq_operator sigma ->
    robinson_q_axiom sigma
| RobinsonQSuccNeZero : robinson_q_axiom robinson_q_succ_ne_zero_sentence
| RobinsonQSuccInj : robinson_q_axiom robinson_q_succ_inj_sentence
| RobinsonQZeroOrSucc : robinson_q_axiom robinson_q_zero_or_succ_sentence
| RobinsonQAddZero : robinson_q_axiom robinson_q_add_zero_sentence
| RobinsonQAddSucc : robinson_q_axiom robinson_q_add_succ_sentence
| RobinsonQMulZero : robinson_q_axiom robinson_q_mul_zero_sentence
| RobinsonQMulSucc : robinson_q_axiom robinson_q_mul_succ_sentence
| RobinsonQLtDef : robinson_q_axiom robinson_q_lt_def_sentence.

Definition robinson_q_axiom_list : list (sentence oring_language) :=
  first_order_equality_axiom_list oring_language_eq_operator
    oring_language_finite ++
  [robinson_q_succ_ne_zero_sentence;
   robinson_q_succ_inj_sentence;
   robinson_q_zero_or_succ_sentence;
   robinson_q_add_zero_sentence;
   robinson_q_add_succ_sentence;
   robinson_q_mul_zero_sentence;
   robinson_q_mul_succ_sentence;
   robinson_q_lt_def_sentence].

Lemma robinson_q_axiom_list_complete : forall sigma,
  robinson_q_axiom sigma -> In sigma robinson_q_axiom_list.
Proof.
  intros sigma Hsigma. destruct Hsigma; unfold robinson_q_axiom_list.
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
Qed.

Theorem robinson_q_axiom_finitely_covered :
  set_finitely_covered robinson_q_axiom.
Proof.
  exists robinson_q_axiom_list.
  intros sigma Hsigma. now apply robinson_q_axiom_list_complete.
Qed.

Theorem robinson_q_proves_equality :
  first_order_theory_proves_equality
    robinson_q_axiom oring_language_eq_operator.
Proof.
  intros sigma Hsigma.
  exact (@generic_axiomatized_by_axiom
    (theory oring_language) (sentence oring_language)
    (first_order_theory_entailment oring_language)
    (generic_predicate_adjunctive_set (sentence oring_language))
    (first_order_theory_axiomatized oring_language)
    robinson_q_axiom sigma (RobinsonQEquality Hsigma)).
Qed.

Lemma arithmetic_all_sentence_eval : forall M k
    (Str : first_order_structure oring_language M)
    (p : semisentence oring_language k),
  sentence_realize Str (@arithmetic_all_sentence k p) <->
  forall e : Fin.t k -> M,
    semiformula_eval Str e arithmetic_empty_free_env p.
Proof.
  intros. unfold sentence_realize, arithmetic_all_sentence.
  apply semiformula_eval_all_closure.
Qed.

#[global] Hint Rewrite arithmetic_zero_term_val arithmetic_one_term_val
  arithmetic_add_term_val arithmetic_mul_term_val
  arithmetic_add_one_term_val arithmetic_eq_formula_eval
  arithmetic_lt_formula_eval : arithmetic_language_eval.

Lemma robinson_q_succ_ne_zero_realize_iff : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  (sentence_realize Str robinson_q_succ_ne_zero_sentence <->
   forall a, oring_add O a (oring_one O) <> oring_zero O).
Proof.
  intros M Str O Horing.
  unfold robinson_q_succ_ne_zero_sentence.
  rewrite arithmetic_all_sentence_eval. split.
  - intros H a. specialize (H (fin_one a)).
    rewrite semiformula_eval_neg in H.
    rewrite (@arithmetic_eq_formula_eval M Empty_set 1 Str (fin_one a)
      arithmetic_empty_free_env O _ _ Horing) in H.
    rewrite (@arithmetic_add_one_term_val M Empty_set 1 Str (fin_one a)
      arithmetic_empty_free_env O _ Horing) in H.
    rewrite (@arithmetic_zero_term_val M Empty_set 1 Str (fin_one a)
      arithmetic_empty_free_env O Horing) in H.
    simpl in H.
    exact H.
  - intros H e. specialize (H (e Fin.F1)).
    rewrite semiformula_eval_neg.
    rewrite (@arithmetic_eq_formula_eval M Empty_set 1 Str e
      arithmetic_empty_free_env O _ _ Horing).
    rewrite (@arithmetic_add_one_term_val M Empty_set 1 Str e
      arithmetic_empty_free_env O _ Horing).
    rewrite (@arithmetic_zero_term_val M Empty_set 1 Str e
      arithmetic_empty_free_env O Horing).
    simpl.
    exact H.
Qed.

Lemma robinson_q_succ_inj_realize_iff : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  (sentence_realize Str robinson_q_succ_inj_sentence <->
   forall a b,
     oring_add O a (oring_one O) = oring_add O b (oring_one O) ->
     a = b).
Proof.
  intros M Str O Horing.
  unfold robinson_q_succ_inj_sentence.
  rewrite arithmetic_all_sentence_eval. split.
  - intros H a b. specialize (H (fin_two a b)).
    rewrite semiformula_eval_imp in H.
    rewrite (@arithmetic_eq_formula_eval M Empty_set 2 Str (fin_two a b)
      arithmetic_empty_free_env O _ _ Horing) in H.
    rewrite (@arithmetic_eq_formula_eval M Empty_set 2 Str (fin_two a b)
      arithmetic_empty_free_env O _ _ Horing) in H.
    repeat rewrite (@arithmetic_add_one_term_val M Empty_set 2 Str
      (fin_two a b) arithmetic_empty_free_env O _ Horing) in H.
    repeat rewrite (@arithmetic_add_term_val M Empty_set 2 Str
      (fin_two a b) arithmetic_empty_free_env O _ _ Horing) in H.
    simpl in H. exact H.
  - intros H e. specialize (H (e Fin.F1) (e (Fin.FS Fin.F1))).
    rewrite semiformula_eval_imp.
    rewrite (@arithmetic_eq_formula_eval M Empty_set 2 Str e
      arithmetic_empty_free_env O _ _ Horing).
    rewrite (@arithmetic_eq_formula_eval M Empty_set 2 Str e
      arithmetic_empty_free_env O _ _ Horing).
    repeat rewrite (@arithmetic_add_one_term_val M Empty_set 2 Str e
      arithmetic_empty_free_env O _ Horing).
    repeat rewrite (@arithmetic_add_term_val M Empty_set 2 Str e
      arithmetic_empty_free_env O _ _ Horing).
    simpl. exact H.
Qed.

Lemma robinson_q_add_zero_realize_iff : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  (sentence_realize Str robinson_q_add_zero_sentence <->
   forall a, oring_add O a (oring_zero O) = a).
Proof.
  intros M Str O Horing. unfold robinson_q_add_zero_sentence.
  rewrite arithmetic_all_sentence_eval. split.
  - intros H a. specialize (H (fin_one a)).
    rewrite (@arithmetic_eq_formula_eval M Empty_set 1 Str (fin_one a)
      arithmetic_empty_free_env O _ _ Horing) in H.
    rewrite (@arithmetic_add_term_val M Empty_set 1 Str (fin_one a)
      arithmetic_empty_free_env O _ _ Horing) in H.
    rewrite (@arithmetic_zero_term_val M Empty_set 1 Str (fin_one a)
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

Lemma robinson_q_add_succ_realize_iff : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  (sentence_realize Str robinson_q_add_succ_sentence <->
   forall a b,
     oring_add O a (oring_add O b (oring_one O)) =
     oring_add O (oring_add O a b) (oring_one O)).
Proof.
  intros M Str O Horing. unfold robinson_q_add_succ_sentence.
  rewrite arithmetic_all_sentence_eval. split.
  - intros H a b. specialize (H (fin_two a b)).
    rewrite (@arithmetic_eq_formula_eval M Empty_set 2 Str (fin_two a b)
      arithmetic_empty_free_env O _ _ Horing) in H.
    repeat rewrite (@arithmetic_add_term_val M Empty_set 2 Str
      (fin_two a b) arithmetic_empty_free_env O _ _ Horing) in H.
    repeat rewrite (@arithmetic_add_one_term_val M Empty_set 2 Str
      (fin_two a b) arithmetic_empty_free_env O _ Horing) in H.
    repeat rewrite (@arithmetic_mul_term_val M Empty_set 2 Str
      (fin_two a b) arithmetic_empty_free_env O _ _ Horing) in H.
    repeat rewrite (@arithmetic_add_term_val M Empty_set 2 Str
      (fin_two a b) arithmetic_empty_free_env O _ _ Horing) in H.
    simpl in H. exact H.
  - intros H e. specialize (H (e Fin.F1) (e (Fin.FS Fin.F1))).
    rewrite (@arithmetic_eq_formula_eval M Empty_set 2 Str e
      arithmetic_empty_free_env O _ _ Horing).
    repeat rewrite (@arithmetic_add_term_val M Empty_set 2 Str e
      arithmetic_empty_free_env O _ _ Horing).
    repeat rewrite (@arithmetic_add_one_term_val M Empty_set 2 Str e
      arithmetic_empty_free_env O _ Horing).
    repeat rewrite (@arithmetic_mul_term_val M Empty_set 2 Str e
      arithmetic_empty_free_env O _ _ Horing).
    repeat rewrite (@arithmetic_add_term_val M Empty_set 2 Str e
      arithmetic_empty_free_env O _ _ Horing).
    simpl. exact H.
Qed.

Lemma robinson_q_mul_zero_realize_iff : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  (sentence_realize Str robinson_q_mul_zero_sentence <->
   forall a, oring_mul O a (oring_zero O) = oring_zero O).
Proof.
  intros M Str O Horing. unfold robinson_q_mul_zero_sentence.
  rewrite arithmetic_all_sentence_eval. split.
  - intros H a. specialize (H (fin_one a)).
    rewrite (@arithmetic_eq_formula_eval M Empty_set 1 Str (fin_one a)
      arithmetic_empty_free_env O _ _ Horing) in H.
    rewrite (@arithmetic_mul_term_val M Empty_set 1 Str (fin_one a)
      arithmetic_empty_free_env O _ _ Horing) in H.
    repeat rewrite (@arithmetic_zero_term_val M Empty_set 1 Str (fin_one a)
      arithmetic_empty_free_env O Horing) in H.
    simpl in H. exact H.
  - intros H e. specialize (H (e Fin.F1)).
    rewrite (@arithmetic_eq_formula_eval M Empty_set 1 Str e
      arithmetic_empty_free_env O _ _ Horing).
    rewrite (@arithmetic_mul_term_val M Empty_set 1 Str e
      arithmetic_empty_free_env O _ _ Horing).
    repeat rewrite (@arithmetic_zero_term_val M Empty_set 1 Str e
      arithmetic_empty_free_env O Horing).
    simpl. exact H.
Qed.

Lemma robinson_q_mul_succ_realize_iff : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  (sentence_realize Str robinson_q_mul_succ_sentence <->
   forall a b,
     oring_mul O a (oring_add O b (oring_one O)) =
     oring_add O (oring_mul O a b) a).
Proof.
  intros M Str O Horing. unfold robinson_q_mul_succ_sentence.
  rewrite arithmetic_all_sentence_eval. split.
  - intros H a b. specialize (H (fin_two a b)).
    rewrite (@arithmetic_eq_formula_eval M Empty_set 2 Str (fin_two a b)
      arithmetic_empty_free_env O _ _ Horing) in H.
    repeat rewrite (@arithmetic_mul_term_val M Empty_set 2 Str
      (fin_two a b) arithmetic_empty_free_env O _ _ Horing) in H.
    repeat rewrite (@arithmetic_add_term_val M Empty_set 2 Str
      (fin_two a b) arithmetic_empty_free_env O _ _ Horing) in H.
    repeat rewrite (@arithmetic_add_one_term_val M Empty_set 2 Str
      (fin_two a b) arithmetic_empty_free_env O _ Horing) in H.
    repeat rewrite (@arithmetic_mul_term_val M Empty_set 2 Str
      (fin_two a b) arithmetic_empty_free_env O _ _ Horing) in H.
    repeat rewrite (@arithmetic_add_term_val M Empty_set 2 Str
      (fin_two a b) arithmetic_empty_free_env O _ _ Horing) in H.
    simpl in H. exact H.
  - intros H e. specialize (H (e Fin.F1) (e (Fin.FS Fin.F1))).
    rewrite (@arithmetic_eq_formula_eval M Empty_set 2 Str e
      arithmetic_empty_free_env O _ _ Horing).
    repeat rewrite (@arithmetic_mul_term_val M Empty_set 2 Str e
      arithmetic_empty_free_env O _ _ Horing).
    repeat rewrite (@arithmetic_add_term_val M Empty_set 2 Str e
      arithmetic_empty_free_env O _ _ Horing).
    repeat rewrite (@arithmetic_add_one_term_val M Empty_set 2 Str e
      arithmetic_empty_free_env O _ Horing).
    repeat rewrite (@arithmetic_mul_term_val M Empty_set 2 Str e
      arithmetic_empty_free_env O _ _ Horing).
    repeat rewrite (@arithmetic_add_term_val M Empty_set 2 Str e
      arithmetic_empty_free_env O _ _ Horing).
    simpl. exact H.
Qed.

Lemma robinson_q_zero_or_succ_realize_iff : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  (sentence_realize Str robinson_q_zero_or_succ_sentence <->
   forall a,
     a = oring_zero O \/
     exists b, a = oring_add O b (oring_one O)).
Proof.
  intros M Str O Horing. unfold robinson_q_zero_or_succ_sentence.
  rewrite arithmetic_all_sentence_eval. split.
  - intros H a. specialize (H (fin_one a)).
    change
      (semiformula_eval Str (fin_one a) arithmetic_empty_free_env
          (arithmetic_eq_formula (Semiterm_bvar Fin.F1)
            arithmetic_zero_term) \/
       exists b,
         semiformula_eval Str (fin_env_cons b (fin_one a))
           arithmetic_empty_free_env
           (arithmetic_eq_formula (Semiterm_bvar (Fin.FS Fin.F1))
             (arithmetic_add_one_term (Semiterm_bvar Fin.F1)))) in H.
    destruct H as [H | [b Hb]].
    + left.
      rewrite (@arithmetic_eq_formula_eval M Empty_set 1 Str (fin_one a)
        arithmetic_empty_free_env O _ _ Horing) in H.
      rewrite (@arithmetic_zero_term_val M Empty_set 1 Str (fin_one a)
        arithmetic_empty_free_env O Horing) in H.
      simpl in H. exact H.
    + right. exists b.
      rewrite (@arithmetic_eq_formula_eval M Empty_set 2 Str
        (fin_env_cons b (fin_one a)) arithmetic_empty_free_env O _ _ Horing)
        in Hb.
      rewrite (@arithmetic_add_one_term_val M Empty_set 2 Str
        (fin_env_cons b (fin_one a)) arithmetic_empty_free_env O _ Horing)
        in Hb.
      simpl in Hb. exact Hb.
  - intros H e. specialize (H (e Fin.F1)).
    change
      (semiformula_eval Str e arithmetic_empty_free_env
          (arithmetic_eq_formula (Semiterm_bvar Fin.F1)
            arithmetic_zero_term) \/
       exists b,
         semiformula_eval Str (fin_env_cons b e) arithmetic_empty_free_env
           (arithmetic_eq_formula (Semiterm_bvar (Fin.FS Fin.F1))
             (arithmetic_add_one_term (Semiterm_bvar Fin.F1)))).
    destruct H as [H | [b Hb]].
    + left.
      rewrite (@arithmetic_eq_formula_eval M Empty_set 1 Str e
        arithmetic_empty_free_env O _ _ Horing).
      rewrite (@arithmetic_zero_term_val M Empty_set 1 Str e
        arithmetic_empty_free_env O Horing).
      simpl. exact H.
    + right. exists b.
      rewrite (@arithmetic_eq_formula_eval M Empty_set 2 Str
        (fin_env_cons b e) arithmetic_empty_free_env O _ _ Horing).
      rewrite (@arithmetic_add_one_term_val M Empty_set 2 Str
        (fin_env_cons b e) arithmetic_empty_free_env O _ Horing).
      simpl. exact Hb.
Qed.

Lemma robinson_q_lt_def_realize_iff : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  (sentence_realize Str robinson_q_lt_def_sentence <->
   forall a b,
     oring_lt O a b <->
     exists c, oring_add O a (oring_add O c (oring_one O)) = b).
Proof.
  intros M Str O Horing. unfold robinson_q_lt_def_sentence.
  rewrite arithmetic_all_sentence_eval. split.
  - intros H a b. specialize (H (fin_two a b)).
    rewrite semiformula_eval_iff in H.
    rewrite (@arithmetic_lt_formula_eval M Empty_set 2 Str (fin_two a b)
      arithmetic_empty_free_env O _ _ Horing) in H.
    change
      (oring_lt O a b <->
       exists c,
         semiformula_eval Str (fin_env_cons c (fin_two a b))
           arithmetic_empty_free_env
           (arithmetic_eq_formula
             (arithmetic_add_term (Semiterm_bvar (Fin.FS Fin.F1))
               (arithmetic_add_one_term (Semiterm_bvar Fin.F1)))
             (Semiterm_bvar (Fin.FS (Fin.FS Fin.F1))))) in H.
    split.
    + intro Hab. destruct (proj1 H Hab) as [c Hc]. exists c.
      rewrite (@arithmetic_eq_formula_eval M Empty_set 3 Str
        (fin_env_cons c (fin_two a b)) arithmetic_empty_free_env O _ _ Horing)
        in Hc.
      repeat rewrite (@arithmetic_add_term_val M Empty_set 3 Str
        (fin_env_cons c (fin_two a b)) arithmetic_empty_free_env O _ _ Horing)
        in Hc.
      rewrite (@arithmetic_add_one_term_val M Empty_set 3 Str
        (fin_env_cons c (fin_two a b)) arithmetic_empty_free_env O _ Horing)
        in Hc.
      simpl in Hc. exact Hc.
    + intros [c Hc]. apply (proj2 H). exists c.
      rewrite (@arithmetic_eq_formula_eval M Empty_set 3 Str
        (fin_env_cons c (fin_two a b)) arithmetic_empty_free_env O _ _ Horing).
      repeat rewrite (@arithmetic_add_term_val M Empty_set 3 Str
        (fin_env_cons c (fin_two a b)) arithmetic_empty_free_env O _ _ Horing).
      rewrite (@arithmetic_add_one_term_val M Empty_set 3 Str
        (fin_env_cons c (fin_two a b)) arithmetic_empty_free_env O _ Horing).
      simpl. exact Hc.
  - intros H e. specialize (H (e Fin.F1) (e (Fin.FS Fin.F1))).
    rewrite semiformula_eval_iff.
    rewrite (@arithmetic_lt_formula_eval M Empty_set 2 Str e
      arithmetic_empty_free_env O _ _ Horing).
    change
      (oring_lt O (e Fin.F1) (e (Fin.FS Fin.F1)) <->
       exists c,
         semiformula_eval Str (fin_env_cons c e) arithmetic_empty_free_env
           (arithmetic_eq_formula
             (arithmetic_add_term (Semiterm_bvar (Fin.FS Fin.F1))
               (arithmetic_add_one_term (Semiterm_bvar Fin.F1)))
             (Semiterm_bvar (Fin.FS (Fin.FS Fin.F1))))).
    split.
    + intro Hab. destruct (proj1 H Hab) as [c Hc]. exists c.
      rewrite (@arithmetic_eq_formula_eval M Empty_set 3 Str
        (fin_env_cons c e) arithmetic_empty_free_env O _ _ Horing).
      repeat rewrite (@arithmetic_add_term_val M Empty_set 3 Str
        (fin_env_cons c e) arithmetic_empty_free_env O _ _ Horing).
      rewrite (@arithmetic_add_one_term_val M Empty_set 3 Str
        (fin_env_cons c e) arithmetic_empty_free_env O _ Horing).
      simpl. exact Hc.
    + intros [c Hc]. apply (proj2 H). exists c.
      rewrite (@arithmetic_eq_formula_eval M Empty_set 3 Str
        (fin_env_cons c e) arithmetic_empty_free_env O _ _ Horing) in Hc.
      repeat rewrite (@arithmetic_add_term_val M Empty_set 3 Str
        (fin_env_cons c e) arithmetic_empty_free_env O _ _ Horing) in Hc.
      rewrite (@arithmetic_add_one_term_val M Empty_set 3 Str
        (fin_env_cons c e) arithmetic_empty_free_env O _ Horing) in Hc.
      simpl in Hc. exact Hc.
Qed.

Record robinson_q_laws {M : Type} (O : oring_carrier M) : Prop := {
  robinson_q_succ_ne_zero : forall a,
    oring_add O a (oring_one O) <> oring_zero O;
  robinson_q_succ_inj : forall a b,
    oring_add O a (oring_one O) = oring_add O b (oring_one O) -> a = b;
  robinson_q_zero_or_succ : forall a,
    a = oring_zero O \/ exists b, a = oring_add O b (oring_one O);
  robinson_q_add_zero : forall a,
    oring_add O a (oring_zero O) = a;
  robinson_q_add_succ : forall a b,
    oring_add O a (oring_add O b (oring_one O)) =
    oring_add O (oring_add O a b) (oring_one O);
  robinson_q_mul_zero : forall a,
    oring_mul O a (oring_zero O) = oring_zero O;
  robinson_q_mul_succ : forall a b,
    oring_mul O a (oring_add O b (oring_one O)) =
    oring_add O (oring_mul O a b) a;
  robinson_q_lt_def : forall a b,
    oring_lt O a b <->
    exists c, oring_add O a (oring_add O c (oring_one O)) = b
}.

Theorem first_order_model_models_robinson_q_iff : forall
    (m : first_order_model oring_language)
    (O : oring_carrier (first_order_model_domain m)),
  structure_interprets_oring (first_order_model_structure m)
    oring_language_structure O ->
  (first_order_models_theory m robinson_q_axiom <-> robinson_q_laws O).
Proof.
  intros m O Horing. split.
  - intro Hmodels. constructor.
    + apply (proj1 (robinson_q_succ_ne_zero_realize_iff Horing)).
      exact (first_order_models_of_member Hmodels RobinsonQSuccNeZero).
    + apply (proj1 (robinson_q_succ_inj_realize_iff Horing)).
      exact (first_order_models_of_member Hmodels RobinsonQSuccInj).
    + apply (proj1 (robinson_q_zero_or_succ_realize_iff Horing)).
      exact (first_order_models_of_member Hmodels RobinsonQZeroOrSucc).
    + apply (proj1 (robinson_q_add_zero_realize_iff Horing)).
      exact (first_order_models_of_member Hmodels RobinsonQAddZero).
    + apply (proj1 (robinson_q_add_succ_realize_iff Horing)).
      exact (first_order_models_of_member Hmodels RobinsonQAddSucc).
    + apply (proj1 (robinson_q_mul_zero_realize_iff Horing)).
      exact (first_order_models_of_member Hmodels RobinsonQMulZero).
    + apply (proj1 (robinson_q_mul_succ_realize_iff Horing)).
      exact (first_order_models_of_member Hmodels RobinsonQMulSucc).
    + apply (proj1 (robinson_q_lt_def_realize_iff Horing)).
      exact (first_order_models_of_member Hmodels RobinsonQLtDef).
  - intro Hlaws. apply (proj2 (first_order_models_theory_iff m _)).
    intros sigma Hsigma. destruct Hsigma.
    + exact (first_order_models_of_member
        (first_order_model_models_equality_theory_of_interprets_eq
          (structure_oring_eq Horing)) H).
    + apply (proj2 (robinson_q_succ_ne_zero_realize_iff Horing)).
      exact (robinson_q_succ_ne_zero Hlaws).
    + apply (proj2 (robinson_q_succ_inj_realize_iff Horing)).
      exact (robinson_q_succ_inj Hlaws).
    + apply (proj2 (robinson_q_zero_or_succ_realize_iff Horing)).
      exact (robinson_q_zero_or_succ Hlaws).
    + apply (proj2 (robinson_q_add_zero_realize_iff Horing)).
      exact (robinson_q_add_zero Hlaws).
    + apply (proj2 (robinson_q_add_succ_realize_iff Horing)).
      exact (robinson_q_add_succ Hlaws).
    + apply (proj2 (robinson_q_mul_zero_realize_iff Horing)).
      exact (robinson_q_mul_zero Hlaws).
    + apply (proj2 (robinson_q_mul_succ_realize_iff Horing)).
      exact (robinson_q_mul_succ Hlaws).
    + apply (proj2 (robinson_q_lt_def_realize_iff Horing)).
      exact (robinson_q_lt_def Hlaws).
Qed.

Lemma robinson_q_exists_succ_of_ne_zero : forall M (O : oring_carrier M),
  robinson_q_laws O -> forall a,
  a <> oring_zero O -> exists b, a = oring_add O b (oring_one O).
Proof.
  intros M O H a Hne.
  destruct (@robinson_q_zero_or_succ M O H a) as [Ha | Ha].
  - contradiction.
  - exact Ha.
Qed.

Lemma robinson_q_exists_succ_of_ne_zero' : forall M (O : oring_carrier M),
  robinson_q_laws O -> forall a,
  a <> oring_zero O -> exists b, oring_add O b (oring_one O) = a.
Proof.
  intros M O H a Hne.
  destruct (robinson_q_exists_succ_of_ne_zero H Hne) as [b Hb].
  exists b. now symmetry.
Qed.

Lemma robinson_q_one_ne_zero : forall M (O : oring_carrier M),
  robinson_q_laws O -> oring_one O <> oring_zero O.
Proof.
  intros M O H Hone.
  apply (@robinson_q_succ_ne_zero M O H (oring_zero O)).
  rewrite Hone. apply (@robinson_q_add_zero M O H).
Qed.

(** The source proof of [0 + 1 = 1] uses only successor decomposition,
    successor injectivity, and successor nonzeroness.  Keeping the excluded
    middle localized here mirrors its noncomputable model section. *)
Lemma robinson_q_zero_add_one : forall M (O : oring_carrier M),
  robinson_q_laws O ->
  oring_add O (oring_zero O) (oring_one O) = oring_one O.
Proof.
  intros M O H.
  destruct (robinson_q_exists_succ_of_ne_zero' H
    (robinson_q_one_ne_zero H)) as [a Ha].
  assert (Hazero : a = oring_zero O).
  { destruct (classic (a = oring_zero O)) as [Ha0 | Ha0]; [exact Ha0|].
    destruct (robinson_q_exists_succ_of_ne_zero' H Ha0) as [b Hb].
    exfalso. apply (@robinson_q_succ_ne_zero M O H
      (oring_add O (oring_zero O) b)).
    apply (@robinson_q_succ_inj M O H).
    rewrite <- (@robinson_q_add_succ M O H (oring_zero O) b).
    rewrite Hb.
    rewrite <- (@robinson_q_add_succ M O H (oring_zero O) a).
    now rewrite Ha. }
  subst a. exact Ha.
Qed.

Lemma robinson_q_eq_zero_of_add_eq_zero : forall M
    (O : oring_carrier M),
  robinson_q_laws O -> forall a b,
  oring_add O a b = oring_zero O ->
  a = oring_zero O /\ b = oring_zero O.
Proof.
  intros M O H a b Hab.
  destruct (@robinson_q_zero_or_succ M O H b)
    as [Hb | [c Hb]].
  - subst b. rewrite (@robinson_q_add_zero M O H) in Hab.
    now split.
  - exfalso. rewrite Hb, (@robinson_q_add_succ M O H) in Hab.
    exact (@robinson_q_succ_ne_zero M O H (oring_add O a c) Hab).
Qed.

Lemma robinson_q_lt_of_add_nonzero : forall M (O : oring_carrier M),
  robinson_q_laws O -> forall a b,
  b <> oring_zero O -> oring_lt O a (oring_add O a b).
Proof.
  intros M O H a b Hb.
  destruct (robinson_q_exists_succ_of_ne_zero H Hb) as [c Hc].
  apply (proj2 (@robinson_q_lt_def M O H a (oring_add O a b))).
  exists c. now rewrite <- Hc.
Qed.

Lemma robinson_q_lt_one_iff_eq_zero : forall M (O : oring_carrier M),
  robinson_q_laws O -> forall a,
  oring_lt O a (oring_one O) <-> a = oring_zero O.
Proof.
  intros M O H a. split.
  - intro Hlt.
    destruct (proj1 (@robinson_q_lt_def M O H a (oring_one O)) Hlt)
      as [c Hc].
    rewrite (@robinson_q_add_succ M O H) in Hc.
    assert (Hsum : oring_add O a c = oring_zero O).
    { apply (@robinson_q_succ_inj M O H).
      rewrite Hc. symmetry. apply (robinson_q_zero_add_one H). }
    exact (proj1 (robinson_q_eq_zero_of_add_eq_zero H Hsum)).
  - intro Ha. subst a.
    apply (proj2 (@robinson_q_lt_def M O H
      (oring_zero O) (oring_one O))).
    exists (oring_zero O).
    now rewrite !(robinson_q_zero_add_one H).
Qed.

Lemma robinson_q_numeral_succ : forall M (O : oring_carrier M),
  robinson_q_laws O -> forall n,
  oring_numeral O (S n) =
  oring_add O (oring_numeral O n) (oring_one O).
Proof.
  intros M O H [|n].
  - simpl. symmetry. apply (robinson_q_zero_add_one H).
  - apply oring_numeral_succ_succ.
Qed.

Lemma robinson_q_numeral_add : forall M (O : oring_carrier M),
  robinson_q_laws O -> forall n m,
  oring_add O (oring_numeral O n) (oring_numeral O m) =
  oring_numeral O (n + m).
Proof.
  intros M O H n m. induction m as [|m IH].
  - cbn. rewrite Nat.add_0_r. apply (@robinson_q_add_zero M O H).
  - rewrite (robinson_q_numeral_succ H m),
      (@robinson_q_add_succ M O H), IH.
    replace (n + S m) with (S (n + m)) by lia.
    symmetry. apply (robinson_q_numeral_succ H).
Qed.

Lemma robinson_q_numeral_mul : forall M (O : oring_carrier M),
  robinson_q_laws O -> forall n m,
  oring_mul O (oring_numeral O n) (oring_numeral O m) =
  oring_numeral O (n * m).
Proof.
  intros M O H n m. induction m as [|m IH].
  - cbn. rewrite Nat.mul_0_r. apply (@robinson_q_mul_zero M O H).
  - rewrite (robinson_q_numeral_succ H m),
      (@robinson_q_mul_succ M O H), IH,
      (robinson_q_numeral_add H).
    f_equal. lia.
Qed.

Lemma robinson_q_numeral_zero_succ_ne : forall M (O : oring_carrier M),
  robinson_q_laws O -> forall n,
  oring_numeral O 0 <> oring_numeral O (S n).
Proof.
  intros M O H n Heq.
  rewrite (robinson_q_numeral_succ H n) in Heq.
  apply (@robinson_q_succ_ne_zero M O H (oring_numeral O n)).
  now symmetry.
Qed.

Lemma robinson_q_numeral_ne : forall M (O : oring_carrier M),
  robinson_q_laws O -> forall n m,
  n <> m -> oring_numeral O n <> oring_numeral O m.
Proof.
  intros M O H n. induction n as [|n IH]; intros [|m] Hne Heq.
  - contradiction.
  - exact (robinson_q_numeral_zero_succ_ne H Heq).
  - exact (robinson_q_numeral_zero_succ_ne H (eq_sym Heq)).
  - apply (IH m); [lia|].
    apply (@robinson_q_succ_inj M O H).
    now rewrite <- !(robinson_q_numeral_succ H).
Qed.

Lemma robinson_q_numeral_eq_iff : forall M (O : oring_carrier M),
  robinson_q_laws O -> forall n m,
  oring_numeral O n = oring_numeral O m <-> n = m.
Proof.
  intros M O H n m. split.
  - intro Heq. destruct (Nat.eq_dec n m); [assumption|].
    exfalso. exact (robinson_q_numeral_ne H n0 Heq).
  - now intros ->.
Qed.

Lemma robinson_q_numeral_lt : forall M (O : oring_carrier M),
  robinson_q_laws O -> forall n m,
  n < m -> oring_lt O (oring_numeral O n) (oring_numeral O m).
Proof.
  intros M O H n m Hnm.
  apply (proj2 (@robinson_q_lt_def M O H
    (oring_numeral O n) (oring_numeral O m))).
  exists (oring_numeral O (m - n - 1)).
  rewrite <- (robinson_q_numeral_succ H (m - n - 1)).
  rewrite (robinson_q_numeral_add H).
  f_equal. lia.
Qed.

Lemma robinson_q_not_lt_zero : forall M (O : oring_carrier M),
  robinson_q_laws O -> forall x,
  ~ oring_lt O x (oring_zero O).
Proof.
  intros M O H x Hlt.
  destruct (proj1 (@robinson_q_lt_def M O H x (oring_zero O)) Hlt)
    as [c Hc].
  rewrite (@robinson_q_add_succ M O H) in Hc.
  exact (@robinson_q_succ_ne_zero M O H (oring_add O x c) Hc).
Qed.

Lemma robinson_q_lt_numeral_iff : forall M (O : oring_carrier M),
  robinson_q_laws O -> forall n x,
  oring_lt O x (oring_numeral O n) <->
  exists m, m < n /\ x = oring_numeral O m.
Proof.
  intros M O H n. induction n as [|n IH]; intro x; split.
  - intro Hlt. exfalso. exact (robinson_q_not_lt_zero H Hlt).
  - intros [m [Hm _]]. lia.
  - intro Hlt.
    destruct (proj1 (@robinson_q_lt_def M O H x
      (oring_numeral O (S n))) Hlt) as [a Ha].
    rewrite (@robinson_q_add_succ M O H) in Ha.
    rewrite (robinson_q_numeral_succ H n) in Ha.
    apply (@robinson_q_succ_inj M O H) in Ha.
    destruct (@robinson_q_zero_or_succ M O H a)
      as [Hazero | [b Hb]].
    + subst a. rewrite (@robinson_q_add_zero M O H) in Ha.
      exists n. split; [lia|exact Ha].
    + rewrite Hb in Ha.
      assert (Hlower : oring_lt O x (oring_numeral O n)).
      { apply (proj2 (@robinson_q_lt_def M O H x
          (oring_numeral O n))). now exists b. }
      destruct (proj1 (IH x) Hlower) as [m [Hmn Hm]].
      exists m. split; [lia|exact Hm].
  - intros [m [Hmn ->]]. now apply (robinson_q_numeral_lt H).
Qed.

Definition robinson_q_r0_laws : forall M (O : oring_carrier M),
  robinson_q_laws O -> r0_laws O.
Proof.
  intros M O H. constructor.
  - apply (robinson_q_numeral_add H).
  - apply (robinson_q_numeral_mul H).
  - apply (robinson_q_numeral_ne H).
  - apply (robinson_q_lt_numeral_iff H).
Defined.

Lemma robinson_q_numeral_lt_iff : forall M (O : oring_carrier M),
  robinson_q_laws O -> forall n m,
  oring_lt O (oring_numeral O n) (oring_numeral O m) <-> n < m.
Proof.
  intros M O H n m.
  exact (r0_numeral_lt_iff (robinson_q_r0_laws H) n m).
Qed.

Lemma robinson_q_numeral_add_one : forall M (O : oring_carrier M),
  robinson_q_laws O -> forall n,
  oring_add O (oring_numeral O n) (oring_one O) =
  oring_numeral O (S n).
Proof.
  intros M O H n. symmetry. apply (robinson_q_numeral_succ H).
Qed.

Lemma robinson_q_numeral_lt_add : forall M (O : oring_carrier M),
  robinson_q_laws O -> forall n m,
  m <> 0 ->
  oring_lt O (oring_numeral O n)
    (oring_add O (oring_numeral O n) (oring_numeral O m)).
Proof.
  intros M O H n m Hm.
  rewrite (robinson_q_numeral_add H).
  apply (robinson_q_numeral_lt H). lia.
Qed.

Lemma robinson_q_numeral_lt_succ : forall M (O : oring_carrier M),
  robinson_q_laws O -> forall n,
  oring_lt O (oring_numeral O n)
    (oring_add O (oring_numeral O n) (oring_one O)).
Proof.
  intros M O H n.
  rewrite (robinson_q_numeral_add_one H).
  apply (robinson_q_numeral_lt H). lia.
Qed.

Definition nat_robinson_q_laws : robinson_q_laws nat_oring_carrier.
Proof.
  constructor.
  - intros a. change (a + 1 <> 0). lia.
  - intros a b. change (a + 1 = b + 1 -> a = b). lia.
  - intro a. destruct a as [|a].
    + left. reflexivity.
    + right. exists a. change (S a = a + 1). lia.
  - apply Nat.add_0_r.
  - intros a b. change (a + (b + 1) = a + b + 1). lia.
  - apply Nat.mul_0_r.
  - intros a b. change (a * (b + 1) = a * b + a). lia.
  - intros a b. change (a < b <-> exists c, a + (c + 1) = b).
    split.
    + intro Hab. exists (b - a - 1). lia.
    + intros [c Hc]. lia.
Defined.

Theorem nat_standard_model_models_robinson_q :
  first_order_models_theory nat_standard_model robinson_q_axiom.
Proof.
  apply (proj2 (@first_order_model_models_robinson_q_iff
    nat_standard_model nat_oring_carrier nat_standard_structure_interprets)).
  exact nat_robinson_q_laws.
Qed.

Theorem robinson_q_consistent :
  generic_consistent
    (first_order_theory_entailment oring_language) robinson_q_axiom.
Proof.
  exact (first_order_theory_consistent_of_model
    nat_standard_model_models_robinson_q).
Qed.

Theorem robinson_q_proof_complete : forall sigma : sentence oring_language,
  (forall (m : first_order_model oring_language)
          (O : oring_carrier (first_order_model_domain m)),
    structure_interprets_oring (first_order_model_structure m)
      oring_language_structure O ->
    robinson_q_laws O ->
    first_order_model_realize m sigma) ->
  first_order_theory_provable robinson_q_axiom sigma.
Proof.
  intros sigma Hvalid.
  apply (arithmetic_theory_proof_complete robinson_q_proves_equality).
  intros m O Horing Hmodels.
  apply (Hvalid m O Horing).
  now apply (proj1 (@first_order_model_models_robinson_q_iff m O Horing)).
Qed.

Theorem r0_weaker_than_robinson_q :
  generic_weaker_than
    (first_order_theory_entailment oring_language)
    (first_order_theory_entailment oring_language)
    r0_axiom robinson_q_axiom.
Proof.
  apply (arithmetic_theory_weaker_of_models robinson_q_proves_equality).
  intros m O Horing Hq.
  apply (proj2 (@first_order_model_models_r0_iff m O Horing)).
  apply robinson_q_r0_laws.
  now apply (proj1 (@first_order_model_models_robinson_q_iff m O Horing)).
Qed.

Lemma robinson_q_add_zero_provable :
  first_order_theory_provable robinson_q_axiom
    robinson_q_add_zero_sentence.
Proof.
  exact (@generic_axiomatized_by_axiom
    (theory oring_language) (sentence oring_language)
    (first_order_theory_entailment oring_language)
    (generic_predicate_adjunctive_set (sentence oring_language))
    (first_order_theory_axiomatized oring_language)
    robinson_q_axiom robinson_q_add_zero_sentence RobinsonQAddZero).
Qed.

Theorem r0_add_zero_unprovable :
  ~ first_order_theory_provable r0_axiom robinson_q_add_zero_sentence.
Proof.
  apply (first_order_theory_unprovable_of_countermodel
    r0_omega_add_one_model_models_r0).
  intro Hreal.
  pose proof (proj1 (@robinson_q_add_zero_realize_iff
    r0_omega_add_one
    (oring_standard_structure r0_omega_add_one_oring)
    r0_omega_add_one_oring
    (oring_standard_structure_interprets r0_omega_add_one_oring))
    Hreal None) as Hbad.
  discriminate Hbad.
Qed.

Theorem r0_strictly_weaker_than_robinson_q :
  generic_strictly_weaker_than
    (first_order_theory_entailment oring_language)
    (first_order_theory_entailment oring_language)
    r0_axiom robinson_q_axiom.
Proof.
  constructor.
  - exact r0_weaker_than_robinson_q.
  - intro Hreverse. apply r0_add_zero_unprovable.
    exact (generic_weaker_subset Hreverse
      robinson_q_add_zero_sentence robinson_q_add_zero_provable).
Qed.
