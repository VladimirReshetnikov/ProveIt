(**
  Boolean polarity of first-order formulas.

  This ports [Foundation/FirstOrder/Polarity.lean].  The polarity classifier
  and all of its connective, negation, and rewrite laws are structural and
  constructive.
*)

From Stdlib Require Import Bool.Bool.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.Syntax.Predicate Require Import Language Rew Term.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Fixpoint semiformula_polarity {L X n}
    (p : semiformula L X n) : bool :=
  match p with
  | Semiformula_rel _ _ => true
  | Semiformula_nrel _ _ => false
  | Semiformula_verum _ => true
  | Semiformula_falsum _ => false
  | Semiformula_and p q =>
      orb (semiformula_polarity p) (semiformula_polarity q)
  | Semiformula_or p q =>
      andb (semiformula_polarity p) (semiformula_polarity q)
  | Semiformula_all _ => false
  | Semiformula_exists _ => true
  end.

Definition semiformula_positive {L X n}
    (p : semiformula L X n) : Prop :=
  semiformula_polarity p = true.

Definition semiformula_negative {L X n}
    (p : semiformula L X n) : Prop :=
  semiformula_polarity p = false.

Lemma semiformula_polarity_neg : forall L X n
    (p : semiformula L X n),
  semiformula_polarity (semiformula_neg p) =
  negb (semiformula_polarity p).
Proof.
  intros L X n p. induction p; simpl; try reflexivity;
    rewrite ?IHp, ?IHp1, ?IHp2;
    destruct (semiformula_polarity p1) eqn:Hp1,
      (semiformula_polarity p2) eqn:Hp2; reflexivity.
Qed.

Lemma semiformula_polarity_imp : forall L X n
    (p q : semiformula L X n),
  semiformula_polarity (semiformula_imp p q) =
  andb (negb (semiformula_polarity p))
    (semiformula_polarity q).
Proof.
  intros. unfold semiformula_imp. simpl.
  now rewrite semiformula_polarity_neg.
Qed.

Lemma semiformula_rel_positive : forall L X n k
    (r : language_rel L k) (v : Fin.t k -> semiterm L X n),
  semiformula_positive (Semiformula_rel r v).
Proof. reflexivity. Qed.

Lemma semiformula_rel_not_negative : forall L X n k
    (r : language_rel L k) (v : Fin.t k -> semiterm L X n),
  ~ semiformula_negative (Semiformula_rel r v).
Proof. discriminate. Qed.

Lemma semiformula_nrel_not_positive : forall L X n k
    (r : language_rel L k) (v : Fin.t k -> semiterm L X n),
  ~ semiformula_positive (Semiformula_nrel r v).
Proof. discriminate. Qed.

Lemma semiformula_nrel_negative : forall L X n k
    (r : language_rel L k) (v : Fin.t k -> semiterm L X n),
  semiformula_negative (Semiformula_nrel r v).
Proof. reflexivity. Qed.

Lemma semiformula_verum_positive : forall L X n,
  semiformula_positive (@Semiformula_verum L X n).
Proof. reflexivity. Qed.

Lemma semiformula_verum_not_negative : forall L X n,
  ~ semiformula_negative (@Semiformula_verum L X n).
Proof. discriminate. Qed.

Lemma semiformula_falsum_not_positive : forall L X n,
  ~ semiformula_positive (@Semiformula_falsum L X n).
Proof. discriminate. Qed.

Lemma semiformula_falsum_negative : forall L X n,
  semiformula_negative (@Semiformula_falsum L X n).
Proof. reflexivity. Qed.

Lemma semiformula_and_positive_iff : forall L X n
    (p q : semiformula L X n),
  semiformula_positive (Semiformula_and p q) <->
  semiformula_positive p \/ semiformula_positive q.
Proof.
  intros. unfold semiformula_positive. simpl.
  destruct (semiformula_polarity p), (semiformula_polarity q);
    simpl; tauto.
Qed.

Lemma semiformula_and_negative_iff : forall L X n
    (p q : semiformula L X n),
  semiformula_negative (Semiformula_and p q) <->
  semiformula_negative p /\ semiformula_negative q.
Proof.
  intros. unfold semiformula_negative. simpl.
  destruct (semiformula_polarity p), (semiformula_polarity q);
    simpl; tauto.
Qed.

Lemma semiformula_or_positive_iff : forall L X n
    (p q : semiformula L X n),
  semiformula_positive (Semiformula_or p q) <->
  semiformula_positive p /\ semiformula_positive q.
Proof.
  intros. unfold semiformula_positive. simpl.
  destruct (semiformula_polarity p), (semiformula_polarity q);
    simpl; tauto.
Qed.

Lemma semiformula_or_negative_iff : forall L X n
    (p q : semiformula L X n),
  semiformula_negative (Semiformula_or p q) <->
  semiformula_negative p \/ semiformula_negative q.
Proof.
  intros. unfold semiformula_negative. simpl.
  destruct (semiformula_polarity p), (semiformula_polarity q);
    simpl; tauto.
Qed.

Lemma semiformula_exists_positive : forall L X n
    (p : semiformula L X (S n)),
  semiformula_positive (Semiformula_exists p).
Proof. reflexivity. Qed.

Lemma semiformula_exists_not_negative : forall L X n
    (p : semiformula L X (S n)),
  ~ semiformula_negative (Semiformula_exists p).
Proof. discriminate. Qed.

Lemma semiformula_all_not_positive : forall L X n
    (p : semiformula L X (S n)),
  ~ semiformula_positive (Semiformula_all p).
Proof. discriminate. Qed.

Lemma semiformula_all_negative : forall L X n
    (p : semiformula L X (S n)),
  semiformula_negative (Semiformula_all p).
Proof. reflexivity. Qed.

Lemma semiformula_neg_positive_iff : forall L X n
    (p : semiformula L X n),
  semiformula_positive (semiformula_neg p) <->
  semiformula_negative p.
Proof.
  intros. unfold semiformula_positive, semiformula_negative.
  rewrite semiformula_polarity_neg.
  destruct (semiformula_polarity p); simpl; split; intros H;
    try reflexivity; discriminate.
Qed.

Lemma semiformula_neg_negative_iff : forall L X n
    (p : semiformula L X n),
  semiformula_negative (semiformula_neg p) <->
  semiformula_positive p.
Proof.
  intros. unfold semiformula_positive, semiformula_negative.
  rewrite semiformula_polarity_neg.
  destruct (semiformula_polarity p); simpl; split; intros H;
    try reflexivity; discriminate.
Qed.

Lemma semiformula_polarity_rewrite : forall L X n Y m
    (w : rew L X n Y m) (p : semiformula L X n),
  semiformula_polarity (semiformula_rewrite w p) =
  semiformula_polarity p.
Proof.
  intros L X n Y m w p. revert Y m w.
  induction p; intros; simpl; try reflexivity;
    now rewrite ?IHp, ?IHp1, ?IHp2.
Qed.
