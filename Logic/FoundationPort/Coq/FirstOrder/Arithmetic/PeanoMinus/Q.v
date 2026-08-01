(**
  The omega-plus-one countermodel separating Robinson Q from PA-minus.

  This ports the semantic content of
  [Foundation/FirstOrder/Arithmetic/PeanoMinus/Q.lean].  Naturals are finite
  points and [None] is the extra top point.  It is a model of the exact
  Robinson laws, but its top is a successor fixed point and is below itself,
  so the Peano-minus strict-order laws cannot hold.
*)

From Stdlib Require Import Arith.PeanoNat Lia.
From FoundationModal Require Import GenericAdjunctiveSet GenericEntailment.
From Foundation.Syntax.Predicate Require Import Language Term.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Calculus Operator Soundness.
From Foundation.FirstOrder.Basic.Semantics Require Import ModelTheory Semantics.
From Foundation.FirstOrder.Arithmetic.Basic Require Import Misc Model Syntax.
From Foundation.FirstOrder.Arithmetic.R0 Require Import Basic.
From Foundation.FirstOrder.Arithmetic.Q Require Import Basic.
From Foundation.FirstOrder.Arithmetic.PeanoMinus Require Import Basic Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition omega_add_one : Type := option nat.

Definition omega_add_one_add (x y : omega_add_one) : omega_add_one :=
  match x, y with
  | Some n, Some m => Some (n + m)
  | None, _ => None
  | _, None => None
  end.

Definition omega_add_one_mul (x y : omega_add_one) : omega_add_one :=
  match x, y with
  | Some n, Some m => Some (n * m)
  | Some 0, None => Some 0
  | None, Some 0 => Some 0
  | _, _ => None
  end.

Definition omega_add_one_lt (x y : omega_add_one) : Prop :=
  match x, y with
  | Some n, Some m => n < m
  | _, None => True
  | None, Some _ => False
  end.

Definition omega_add_one_oring : oring_carrier omega_add_one :=
  {| oring_zero := Some 0;
     oring_one := Some 1;
     oring_add := omega_add_one_add;
     oring_mul := omega_add_one_mul;
     oring_lt := omega_add_one_lt |}.

Lemma omega_add_one_numeral : forall n,
  oring_numeral omega_add_one_oring n = Some n.
Proof.
  induction n as [|n IH]; [reflexivity|].
  destruct n as [|n]; [reflexivity|].
  change (omega_add_one_add
    (oring_numeral omega_add_one_oring (S n)) (Some 1) = Some (S (S n))).
  rewrite IH. cbn [omega_add_one_add]. f_equal. lia.
Qed.

Definition omega_add_one_robinson_q_laws :
    robinson_q_laws omega_add_one_oring.
Proof.
  constructor.
  - intros [n|]; cbn [omega_add_one_oring omega_add_one_add].
    + intro Heq. injection Heq. lia.
    + discriminate.
  - intros [n|] [m|]; cbn [omega_add_one_oring omega_add_one_add]; intro Heq;
      try discriminate; try reflexivity.
    injection Heq. intro Hnm. f_equal. lia.
  - intros [n|].
    + destruct n as [|n].
      * left. reflexivity.
      * right. exists (Some n).
        change (Some (S n) = Some (n + 1)). f_equal. lia.
    + right. exists None. reflexivity.
  - intros [n|]; cbn [omega_add_one_oring omega_add_one_add].
    + change (Some (n + 0) = Some n). f_equal. lia.
    + reflexivity.
  - intros [n|] [m|].
    + change (Some (n + (m + 1)) = Some (n + m + 1)). f_equal. lia.
    + reflexivity.
    + reflexivity.
    + reflexivity.
  - intros [n|].
    + cbv [omega_add_one_oring omega_add_one_mul oring_zero oring_mul].
      destruct n as [|n]; [reflexivity|].
      f_equal. apply Nat.mul_0_r.
    + reflexivity.
  - intros [n|] [m|].
    + destruct n as [|n]; destruct m as [|m];
        cbv [omega_add_one_oring omega_add_one_add omega_add_one_mul
          oring_one oring_add oring_mul]; try reflexivity;
        f_equal; lia.
    + destruct n;
        cbv [omega_add_one_oring omega_add_one_add omega_add_one_mul
          oring_one oring_add oring_mul]; reflexivity.
    + destruct m;
        cbv [omega_add_one_oring omega_add_one_add omega_add_one_mul
          oring_one oring_add oring_mul]; reflexivity.
    + reflexivity.
  - intros [n|] [m|];
      cbv [omega_add_one_oring omega_add_one_lt omega_add_one_add
        oring_zero oring_one oring_add oring_lt].
    + split.
      * intro Hnm. exists (Some (m - n - 1)). f_equal. lia.
      * intros [[c|] Hc].
        -- injection Hc. lia.
        -- discriminate.
    + split.
      * intro Htop. exists None. reflexivity.
      * intros Hexists. exact I.
    + split.
      * contradiction.
      * intros [[c|] Hc]; discriminate.
    + split.
      * intro Htop. exists (Some 0). reflexivity.
      * intros Hexists. exact I.
Defined.

Definition omega_add_one_r0_laws : r0_laws omega_add_one_oring.
Proof.
  constructor.
  - intros n m. rewrite !omega_add_one_numeral.
    cbv [omega_add_one_oring omega_add_one_add oring_add].
    f_equal.
  - intros n m. rewrite !omega_add_one_numeral.
    cbv [omega_add_one_oring omega_add_one_mul oring_mul].
    destruct n as [|n]; [reflexivity|]. f_equal.
  - intros n m Hne. rewrite !omega_add_one_numeral.
    intro Heq. injection Heq. contradiction.
  - intros n [x|].
    + rewrite omega_add_one_numeral.
      cbv [omega_add_one_oring omega_add_one_lt oring_lt]. split.
      * intro Hx. exists x. split; [exact Hx|].
        symmetry. apply omega_add_one_numeral.
      * intros [i [Hin Hi]]. rewrite omega_add_one_numeral in Hi.
        injection Hi. intro Hxi. subst i. exact Hin.
    + rewrite omega_add_one_numeral.
      cbv [omega_add_one_oring omega_add_one_lt oring_lt]. split.
      * contradiction.
      * intros [i [Hin Hi]]. rewrite omega_add_one_numeral in Hi.
        discriminate.
Defined.

Lemma omega_add_one_successor_fixed_point :
  exists x : omega_add_one,
    omega_add_one_add x (oring_one omega_add_one_oring) = x.
Proof. exists None. reflexivity. Qed.

Lemma omega_add_one_top_lt_top :
  omega_add_one_lt None None.
Proof. exact I. Qed.

Theorem omega_add_one_not_peano_minus :
  ~ peano_minus_laws omega_add_one_oring.
Proof.
  intro H.
  exact (@peano_minus_lt_irrefl omega_add_one omega_add_one_oring H
    None omega_add_one_top_lt_top).
Qed.

(** * The concrete Q countermodel and strict theory comparison *)

Definition omega_add_one_model : first_order_model oring_language :=
  first_order_model_of_structure (inhabits None)
    (oring_standard_structure omega_add_one_oring).

Theorem omega_add_one_model_models_robinson_q :
  first_order_models_theory omega_add_one_model robinson_q_axiom.
Proof.
  apply (proj2 (@first_order_model_models_robinson_q_iff
    omega_add_one_model omega_add_one_oring
    (oring_standard_structure_interprets omega_add_one_oring))).
  exact omega_add_one_robinson_q_laws.
Qed.

Definition peano_minus_successor_nonfixed_sentence :
    sentence oring_language :=
  @arithmetic_all_sentence 1
    (semiformula_neg
      (arithmetic_eq_formula
        (arithmetic_add_one_term
          (@Semiterm_bvar oring_language Empty_set 1 Fin.F1))
        (@Semiterm_bvar oring_language Empty_set 1 Fin.F1))).

Lemma peano_minus_successor_nonfixed_realize_iff : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  (sentence_realize Str peano_minus_successor_nonfixed_sentence <->
   forall x, oring_add O x (oring_one O) <> x).
Proof.
  intros M Str O Horing.
  unfold peano_minus_successor_nonfixed_sentence.
  rewrite arithmetic_all_sentence_eval. split.
  - intros H x. specialize (H (fin_one x)).
    rewrite semiformula_eval_neg in H.
    rewrite (@arithmetic_eq_formula_eval M Empty_set 1 Str (fin_one x)
      arithmetic_empty_free_env O _ _ Horing) in H.
    rewrite (@arithmetic_add_one_term_val M Empty_set 1 Str (fin_one x)
      arithmetic_empty_free_env O _ Horing) in H.
    simpl in H. exact H.
  - intros H e. specialize (H (e Fin.F1)).
    rewrite semiformula_eval_neg.
    rewrite (@arithmetic_eq_formula_eval M Empty_set 1 Str e
      arithmetic_empty_free_env O _ _ Horing).
    rewrite (@arithmetic_add_one_term_val M Empty_set 1 Str e
      arithmetic_empty_free_env O _ Horing).
    simpl. exact H.
Qed.

Lemma peano_minus_successor_nonfixed_provable :
  first_order_theory_provable peano_minus_axiom
    peano_minus_successor_nonfixed_sentence.
Proof.
  apply peano_minus_proof_complete.
  intros m O Horing Hpa.
  unfold first_order_model_realize.
  apply (proj2 (peano_minus_successor_nonfixed_realize_iff Horing)).
  intros x Hfixed.
  pose proof (peano_minus_lt_add_one Hpa x) as Hlt.
  rewrite Hfixed in Hlt.
  exact (@peano_minus_lt_irrefl _ O Hpa x Hlt).
Qed.

Theorem robinson_q_successor_nonfixed_unprovable :
  ~ first_order_theory_provable robinson_q_axiom
      peano_minus_successor_nonfixed_sentence.
Proof.
  apply (first_order_theory_unprovable_of_countermodel
    omega_add_one_model_models_robinson_q).
  intro Hreal.
  pose proof (proj1 (@peano_minus_successor_nonfixed_realize_iff
    omega_add_one
    (oring_standard_structure omega_add_one_oring)
    omega_add_one_oring
    (oring_standard_structure_interprets omega_add_one_oring))
    Hreal None) as Hbad.
  exact (Hbad eq_refl).
Qed.

Theorem robinson_q_strictly_weaker_than_peano_minus :
  generic_strictly_weaker_than
    (first_order_theory_entailment oring_language)
    (first_order_theory_entailment oring_language)
    robinson_q_axiom peano_minus_axiom.
Proof.
  constructor.
  - exact robinson_q_weaker_than_peano_minus.
  - intro Hreverse. apply robinson_q_successor_nonfixed_unprovable.
    exact (generic_weaker_subset Hreverse
      peano_minus_successor_nonfixed_sentence
      peano_minus_successor_nonfixed_provable).
Qed.
