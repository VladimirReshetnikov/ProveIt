(** Set-theoretic semantics for monadic second-order logic. *)

From Stdlib Require Import Logic.Classical_Prop Logic.Classical_Pred_Type
  Vectors.Fin.
From Foundation.Syntax.Predicate Require Import Language Term.
From Foundation.FirstOrder.Basic.Semantics Require Import Semantics.
From Foundation.SecondOrder.Syntax Require Import Formula Rew.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** An admissible family is deliberately an arbitrary predicate on unary
    predicates.  Full semantics and Henkin semantics are both instances. *)
Fixpoint second_order_eval_aux {L M P X N n}
    (Str : first_order_structure L M)
    (admissible : (M -> Prop) -> Prop)
    (F : P -> M -> Prop) (f : X -> M)
    (p : second_order_semiformula L P X N n) :
    (Fin.t N -> M -> Prop) -> (Fin.t n -> M) -> Prop :=
  match p with
  | SOFormula_rel r v => fun E e =>
      structure_rel Str r (fun i => semiterm_val Str e f (v i))
  | SOFormula_nrel r v => fun E e =>
      ~ structure_rel Str r (fun i => semiterm_val Str e f (v i))
  | SOFormula_bpred A t => fun E e => E A (semiterm_val Str e f t)
  | SOFormula_nbpred A t => fun E e => ~ E A (semiterm_val Str e f t)
  | SOFormula_fpred A t => fun E e => F A (semiterm_val Str e f t)
  | SOFormula_nfpred A t => fun E e => ~ F A (semiterm_val Str e f t)
  | SOFormula_verum => fun E e => True
  | SOFormula_falsum => fun E e => False
  | SOFormula_and q r => fun E e =>
      second_order_eval_aux Str admissible F f q E e /\
      second_order_eval_aux Str admissible F f r E e
  | SOFormula_or q r => fun E e =>
      second_order_eval_aux Str admissible F f q E e \/
      second_order_eval_aux Str admissible F f r E e
  | SOFormula_all0 q => fun E e => forall x,
      second_order_eval_aux Str admissible F f q E (fin_env_cons x e)
  | SOFormula_exs0 q => fun E e => exists x,
      second_order_eval_aux Str admissible F f q E (fin_env_cons x e)
  | SOFormula_all1 q => fun E e => forall A,
      admissible A ->
      second_order_eval_aux Str admissible F f q (fin_env_cons A E) e
  | SOFormula_exs1 q => fun E e => exists A,
      admissible A /\
      second_order_eval_aux Str admissible F f q (fin_env_cons A E) e
  end.

Definition second_order_eval {L M P X N n}
    (Str : first_order_structure L M)
    (admissible : (M -> Prop) -> Prop)
    (F : P -> M -> Prop) (f : X -> M)
    (E : Fin.t N -> M -> Prop) (e : Fin.t n -> M)
    (p : second_order_semiformula L P X N n) : Prop :=
  second_order_eval_aux Str admissible F f p E e.

(** The constructor equations form the public interface of the evaluator.
    Stating them explicitly keeps downstream proofs independent of the
    implementation chosen for the structurally recursive auxiliary. *)
Section EvaluationEquations.

Context {L M P X N n}
  (Str : first_order_structure L M)
  (admissible : (M -> Prop) -> Prop)
  (F : P -> M -> Prop) (f : X -> M)
  (E : Fin.t N -> M -> Prop) (e : Fin.t n -> M).

Lemma second_order_eval_rel : forall k (r : language_rel L k) v,
  second_order_eval Str admissible F f E e
    (@SOFormula_rel L P X N n k r v) <->
  structure_rel Str r (fun i => semiterm_val Str e f (v i)).
Proof. reflexivity. Qed.

Lemma second_order_eval_nrel : forall k (r : language_rel L k) v,
  second_order_eval Str admissible F f E e
    (@SOFormula_nrel L P X N n k r v) <->
  ~ structure_rel Str r (fun i => semiterm_val Str e f (v i)).
Proof. reflexivity. Qed.

Lemma second_order_eval_bpred : forall A t,
  second_order_eval Str admissible F f E e (SOFormula_bpred A t) <->
  E A (semiterm_val Str e f t).
Proof. reflexivity. Qed.

Lemma second_order_eval_nbpred : forall A t,
  second_order_eval Str admissible F f E e (SOFormula_nbpred A t) <->
  ~ E A (semiterm_val Str e f t).
Proof. reflexivity. Qed.

Lemma second_order_eval_fpred : forall A t,
  second_order_eval Str admissible F f E e (SOFormula_fpred A t) <->
  F A (semiterm_val Str e f t).
Proof. reflexivity. Qed.

Lemma second_order_eval_nfpred : forall A t,
  second_order_eval Str admissible F f E e (SOFormula_nfpred A t) <->
  ~ F A (semiterm_val Str e f t).
Proof. reflexivity. Qed.

Lemma second_order_eval_verum :
  second_order_eval Str admissible F f E e SOFormula_verum <-> True.
Proof. reflexivity. Qed.

Lemma second_order_eval_falsum :
  second_order_eval Str admissible F f E e SOFormula_falsum <-> False.
Proof. reflexivity. Qed.

Lemma second_order_eval_and : forall p q,
  second_order_eval Str admissible F f E e (SOFormula_and p q) <->
  second_order_eval Str admissible F f E e p /\
  second_order_eval Str admissible F f E e q.
Proof. reflexivity. Qed.

Lemma second_order_eval_or : forall p q,
  second_order_eval Str admissible F f E e (SOFormula_or p q) <->
  second_order_eval Str admissible F f E e p \/
  second_order_eval Str admissible F f E e q.
Proof. reflexivity. Qed.

Lemma second_order_eval_all0 : forall
    (p : second_order_semiformula L P X N (S n)),
  second_order_eval Str admissible F f E e (SOFormula_all0 p) <->
  forall x, second_order_eval Str admissible F f E
    (fin_env_cons x e) p.
Proof. reflexivity. Qed.

Lemma second_order_eval_exs0 : forall
    (p : second_order_semiformula L P X N (S n)),
  second_order_eval Str admissible F f E e (SOFormula_exs0 p) <->
  exists x, second_order_eval Str admissible F f E
    (fin_env_cons x e) p.
Proof. reflexivity. Qed.

Lemma second_order_eval_all1 : forall
    (p : second_order_semiformula L P X (S N) n),
  second_order_eval Str admissible F f E e (SOFormula_all1 p) <->
  forall A, admissible A -> second_order_eval Str admissible F f
    (fin_env_cons A E) e p.
Proof. reflexivity. Qed.

Lemma second_order_eval_exs1 : forall
    (p : second_order_semiformula L P X (S N) n),
  second_order_eval Str admissible F f E e (SOFormula_exs1 p) <->
  exists A, admissible A /\ second_order_eval Str admissible F f
    (fin_env_cons A E) e p.
Proof. reflexivity. Qed.

End EvaluationEquations.

Lemma classical_not_forall_iff_exists_not : forall A (P : A -> Prop),
  ~ (forall x, P x) <-> exists x, ~ P x.
Proof.
  intros A P. split.
  - apply not_all_ex_not.
  - firstorder.
Qed.

Lemma classical_not_guarded_all_iff : forall A
    (guard body : A -> Prop),
  ~ (forall x, guard x -> body x) <->
  exists x, guard x /\ ~ body x.
Proof.
  intros A guard body. split.
  - intro H.
    apply (proj1 (classical_not_forall_iff_exists_not
      (fun x => guard x -> body x))) in H.
    destruct H as [x Hx]. exists x.
    destruct (classic (guard x)); tauto.
  - firstorder.
Qed.

Theorem second_order_eval_neg : forall L M P X N n
    (Str : first_order_structure L M)
    (admissible : (M -> Prop) -> Prop)
    (F : P -> M -> Prop) (f : X -> M)
    (E : Fin.t N -> M -> Prop) (e : Fin.t n -> M)
    (p : second_order_semiformula L P X N n),
  second_order_eval Str admissible F f E e (second_order_neg p) <->
  ~ second_order_eval Str admissible F f E e p.
Proof.
  intros L M P X N n Str admissible F f E e p.
  revert E e. induction p; intros; simpl [second_order_eval]; try tauto.
  - rewrite IHp1, IHp2. tauto.
  - rewrite IHp1, IHp2. tauto.
  - setoid_rewrite IHp. symmetry.
    apply classical_not_forall_iff_exists_not.
  - setoid_rewrite IHp. firstorder.
  - setoid_rewrite IHp. symmetry.
    apply classical_not_guarded_all_iff.
  - setoid_rewrite IHp. firstorder.
Qed.

Lemma second_order_eval_imp : forall L M P X N n
    (Str : first_order_structure L M) admissible
    (F : P -> M -> Prop) (f : X -> M) E e
    (p q : second_order_semiformula L P X N n),
  second_order_eval Str admissible F f E e (second_order_imp p q) <->
  (second_order_eval Str admissible F f E e p ->
    second_order_eval Str admissible F f E e q).
Proof.
  intros. unfold second_order_imp. simpl [second_order_eval].
  rewrite second_order_eval_neg. tauto.
Qed.

Lemma second_order_eval_iff : forall L M P X N n
    (Str : first_order_structure L M) admissible
    (F : P -> M -> Prop) (f : X -> M) E e
    (p q : second_order_semiformula L P X N n),
  second_order_eval Str admissible F f E e (second_order_iff p q) <->
  (second_order_eval Str admissible F f E e p <->
    second_order_eval Str admissible F f E e q).
Proof.
  intros. unfold second_order_iff. simpl [second_order_eval].
  rewrite !second_order_eval_neg. tauto.
Qed.

Record second_order_model (L : language) : Type := {
  second_order_model_domain : Type;
  second_order_model_nonempty : inhabited second_order_model_domain;
  second_order_model_structure :
    first_order_structure L second_order_model_domain;
  second_order_model_admissible :
    (second_order_model_domain -> Prop) -> Prop
}.

Definition second_order_model_of {L M}
    (nonempty : inhabited M) (Str : first_order_structure L M)
    (admissible : (M -> Prop) -> Prop) : second_order_model L :=
  {| second_order_model_domain := M;
     second_order_model_nonempty := nonempty;
     second_order_model_structure := Str;
     second_order_model_admissible := admissible |}.

Definition second_order_model_realize {L}
    (m : second_order_model L) (p : second_order_sentence L) : Prop :=
  @second_order_eval L (second_order_model_domain m)
    Empty_set Empty_set 0 0
    (second_order_model_structure m)
    (@second_order_model_admissible L m)
    (fun x : Empty_set => match x with end)
    (fun x : Empty_set => match x with end)
    (fun i : Fin.t 0 => match i with end)
    (fun i : Fin.t 0 => match i with end) p.

Lemma second_order_model_of_realize : forall L M nonempty
    (Str : first_order_structure L M) admissible (p : second_order_sentence L),
  second_order_model_realize (second_order_model_of nonempty Str admissible) p <->
  @second_order_eval L M Empty_set Empty_set 0 0 Str admissible
    (fun x : Empty_set => match x with end)
    (fun x : Empty_set => match x with end)
    (fun i : Fin.t 0 => match i with end)
    (fun i : Fin.t 0 => match i with end) p.
Proof. reflexivity. Qed.

Lemma second_order_model_realize_verum : forall L (m : second_order_model L),
  second_order_model_realize m SOFormula_verum.
Proof. reflexivity. Qed.

Lemma second_order_model_realize_falsum : forall L (m : second_order_model L),
  ~ second_order_model_realize m SOFormula_falsum.
Proof. firstorder. Qed.

Lemma second_order_model_realize_neg : forall L
    (m : second_order_model L) (p : second_order_sentence L),
  second_order_model_realize m (second_order_neg p) <->
  ~ second_order_model_realize m p.
Proof. intros. apply second_order_eval_neg. Qed.

Lemma second_order_model_realize_and : forall L
    (m : second_order_model L) (p q : second_order_sentence L),
  second_order_model_realize m (SOFormula_and p q) <->
  second_order_model_realize m p /\ second_order_model_realize m q.
Proof. reflexivity. Qed.

Lemma second_order_model_realize_or : forall L
    (m : second_order_model L) (p q : second_order_sentence L),
  second_order_model_realize m (SOFormula_or p q) <->
  second_order_model_realize m p \/ second_order_model_realize m q.
Proof. reflexivity. Qed.

Lemma second_order_model_realize_imp : forall L
    (m : second_order_model L) (p q : second_order_sentence L),
  second_order_model_realize m (second_order_imp p q) <->
  (second_order_model_realize m p -> second_order_model_realize m q).
Proof. intros. apply second_order_eval_imp. Qed.

Lemma second_order_model_realize_iff : forall L
    (m : second_order_model L) (p q : second_order_sentence L),
  second_order_model_realize m (second_order_iff p q) <->
  (second_order_model_realize m p <-> second_order_model_realize m q).
Proof. intros. apply second_order_eval_iff. Qed.
