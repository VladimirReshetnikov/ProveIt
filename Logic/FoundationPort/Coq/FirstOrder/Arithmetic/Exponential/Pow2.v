(** Powers of two in the standard natural model.

    Foundation characterizes powers of two internally by saying that every
    nontrivial divisor is even.  Over the standard naturals the canonical,
    executable presentation is an explicit exponent witness.  It makes the
    important algebraic consequences substantially shorter and strengthens
    them by returning the exponent whenever it is useful downstream.

    The internal Delta-zero predicate, its arbitrary-model absoluteness, and
    the open-induction proof that the divisor characterization is equivalent
    to this presentation remain outside this module. *)

From Stdlib Require Import Lia NArith.NArith.

Open Scope N_scope.

Set Implicit Arguments.
Unset Strict Implicit.

Definition nat_pow2 (p : N) : Prop :=
  exists k : N, p = 2 ^ k.

Lemma nat_pow2_iff_exponent : forall p,
  nat_pow2 p <-> exists k, p = 2 ^ k.
Proof. reflexivity. Qed.

Lemma nat_pow2_power : forall k,
  nat_pow2 (2 ^ k).
Proof. intros k. now exists k. Qed.

Lemma nat_pow2_exponent_unique : forall p k l,
  p = 2 ^ k -> p = 2 ^ l -> k = l.
Proof.
  intros p k l Hk Hl.
  apply (N.pow_inj_r 2 k l); [reflexivity | congruence].
Qed.

Lemma nat_pow2_pos : forall p,
  nat_pow2 p -> 0 < p.
Proof.
  intros p [k ->].
  apply (proj1 (N.neq_0_lt_0 (2 ^ k))).
  apply N.pow_nonzero. discriminate.
Qed.

Lemma nat_pow2_nonzero : forall p,
  nat_pow2 p -> p <> 0.
Proof.
  intros p Hp. exact (proj2 (N.neq_0_lt_0 p) (nat_pow2_pos Hp)).
Qed.

Lemma nat_pow2_one : nat_pow2 1.
Proof. exists 0. reflexivity. Qed.

Lemma nat_pow2_two : nat_pow2 2.
Proof. exists 1. reflexivity. Qed.

Lemma nat_pow2_not_zero : ~ nat_pow2 0.
Proof.
  intro H. exact (N.lt_irrefl 0 (nat_pow2_pos H)).
Qed.

(** Multiplication by two shifts the unique exponent by one. *)
Lemma nat_pow2_double_iff : forall p,
  nat_pow2 (2 * p) <-> nat_pow2 p.
Proof.
  intro p. split.
  - intros [k Hk].
    destruct (N.eq_dec k 0) as [-> | Hnz].
    + simpl in Hk. exfalso.
      pose proof (proj1 (N.mul_eq_1 2 p) Hk) as [Htwo _].
      discriminate.
    + exists (N.pred k).
      rewrite <- (N.succ_pred k Hnz) in Hk.
      rewrite N.pow_succ_r' in Hk.
      exact (proj1 (N.mul_cancel_l p (2 ^ N.pred k) 2
        ltac:(discriminate)) Hk).
  - intros [k ->]. exists (N.succ k).
    now rewrite N.pow_succ_r'.
Qed.

Lemma nat_pow2_four_mul_iff : forall p,
  nat_pow2 (4 * p) <-> nat_pow2 p.
Proof.
  intro p. replace (4 * p) with (2 * (2 * p)) by nia.
  now rewrite !nat_pow2_double_iff.
Qed.

(** Structural eliminator corresponding to Foundation's [Pow2.elim]. *)
Lemma nat_pow2_elim : forall p,
  nat_pow2 p <->
  p = 1 \/ exists q, p = 2 * q /\ nat_pow2 q.
Proof.
  intro p. split.
  - intros [k Hk].
    destruct (N.eq_dec k 0) as [-> | Hnz].
    + now left.
    + right. exists (2 ^ N.pred k). split.
      * rewrite Hk. rewrite <- (N.succ_pred k Hnz) at 1.
        rewrite N.pow_succ_r'.
        reflexivity.
      * apply nat_pow2_power.
  - intros [-> | [q [-> Hq]]].
    + exact nat_pow2_one.
    + exact (proj2 (nat_pow2_double_iff q) Hq).
Qed.

Lemma nat_pow2_elim_strict : forall p,
  nat_pow2 p <->
  p = 1 \/ 1 < p /\ exists q, p = 2 * q /\ nat_pow2 q.
Proof.
  intro p. rewrite nat_pow2_elim. split.
  - intros [H | [q [H Hq]]]; [now left |].
    right. split; [|now exists q].
    rewrite H. pose proof (nat_pow2_pos Hq). nia.
  - intros [H | [_ H]]; [now left | now right].
Qed.

Lemma nat_pow2_two_divides : forall p,
  nat_pow2 p -> p <> 1 -> (2 | p).
Proof.
  intros p Hp Hne.
  destruct (proj1 (nat_pow2_elim p) Hp) as [H | [q [H _]]].
  - contradiction.
  - exists q. nia.
Qed.

Lemma nat_pow2_div2 : forall p,
  nat_pow2 p -> p <> 1 -> nat_pow2 (N.div2 p).
Proof.
  intros p Hp Hne.
  destruct (proj1 (nat_pow2_elim p) Hp) as [H | [q [H Hq]]].
  - contradiction.
  - rewrite H, N.div2_even. exact Hq.
Qed.

Lemma nat_pow2_double_div2 : forall p,
  nat_pow2 p -> p <> 1 -> 2 * N.div2 p = p.
Proof.
  intros p Hp Hne.
  destruct (proj1 (nat_pow2_elim p) Hp) as [H | [q [H Hq]]].
  - contradiction.
  - now rewrite H, N.div2_even.
Qed.

Lemma nat_pow2_mul : forall p q,
  nat_pow2 p -> nat_pow2 q -> nat_pow2 (p * q).
Proof.
  intros p q [k ->] [l ->].
  exists (k + l). symmetry. apply N.pow_add_r.
Qed.

Lemma nat_pow2_square : forall p,
  nat_pow2 p -> nat_pow2 (p * p).
Proof. intros p Hp. now apply nat_pow2_mul. Qed.

(** Among powers of two, numerical order and divisibility coincide. *)
Lemma nat_pow2_le_iff_divide : forall p q,
  nat_pow2 p -> nat_pow2 q ->
  (p <= q <-> (p | q)).
Proof.
  intros p q [k Hk] [l Hl]. subst p q. split.
  - intro H.
    assert (Hkl : k <= l).
    { exact (proj2 (N.pow_le_mono_r_iff 2 k l eq_refl) H). }
    destruct (N.le_exists_sub k l Hkl) as [d [Hd _]].
    exists (2 ^ d). rewrite Hd, N.pow_add_r. now rewrite N.mul_comm.
  - intro H.
    apply N.divide_pos_le with (m := 2 ^ l); [|exact H].
    apply (proj1 (N.neq_0_lt_0 (2 ^ l))).
    apply N.pow_nonzero. discriminate.
Qed.

Lemma nat_pow2_two_le : forall p,
  nat_pow2 p -> p <> 1 -> 2 <= p.
Proof.
  intros p Hp Hne.
  destruct (proj1 (nat_pow2_elim p) Hp) as [H | [q [H Hq]]].
  - contradiction.
  - rewrite H. pose proof (nat_pow2_pos Hq). nia.
Qed.

(** Powers of two have no values strictly between [q] and [2*q]. *)
Lemma nat_pow2_le_iff_lt_double : forall p q,
  nat_pow2 p -> nat_pow2 q ->
  (p <= q <-> p < 2 * q).
Proof.
  intros p q [k ->] [l ->].
  rewrite <- N.pow_succ_r'.
  rewrite <- (N.pow_le_mono_r_iff 2 k l eq_refl).
  rewrite <- (N.pow_lt_mono_r_iff 2 k (N.succ l) eq_refl).
  lia.
Qed.

Lemma nat_pow2_lt_iff_double_le : forall p q,
  nat_pow2 p -> nat_pow2 q ->
  (p < q <-> 2 * p <= q).
Proof.
  intros p q [k ->] [l ->].
  rewrite <- N.pow_succ_r'.
  rewrite <- (N.pow_lt_mono_r_iff 2 k l eq_refl).
  rewrite <- (N.pow_le_mono_r_iff 2 (N.succ k) l eq_refl).
  lia.
Qed.

Lemma nat_pow2_not_three : ~ nat_pow2 3.
Proof.
  intro H.
  destruct (proj1 (nat_pow2_elim 3) H) as [E | [q [E _]]]; nia.
Qed.

Lemma nat_pow2_four_le : forall p,
  nat_pow2 p -> 2 < p -> 4 <= p.
Proof.
  intros p Hp Hlt.
  apply (proj1 (@nat_pow2_lt_iff_double_le 2 p nat_pow2_two Hp)).
  exact Hlt.
Qed.

(** Every power of two is either a square or twice a square.  The proof is
    the parity decomposition of its unique exponent. *)
Lemma nat_pow2_square_or_double_square : forall p,
  nat_pow2 p ->
  exists q, p = q * q \/ p = 2 * (q * q).
Proof.
  intros p [k ->].
  pose proof (N.div2_odd k) as Hsplit.
  destruct (N.odd k) eqn:Hodd.
  - exists (2 ^ N.div2 k). right.
    simpl in Hsplit.
    rewrite Hsplit at 1.
    rewrite <- (N.pow_add_r 2 (N.div2 k) (N.div2 k)).
    rewrite <- (N.pow_succ_r' 2 (N.div2 k + N.div2 k)).
    f_equal.
    change (2 * N.div2 k + 1 =
      N.succ (N.div2 k + N.div2 k)). lia.
  - exists (2 ^ N.div2 k). left.
    simpl in Hsplit.
    rewrite Hsplit at 1.
    rewrite <- (N.pow_add_r 2 (N.div2 k) (N.div2 k)).
    f_equal.
    change (2 * N.div2 k + 0 = N.div2 k + N.div2 k). lia.
Qed.

Print Assumptions nat_pow2_double_iff.
Print Assumptions nat_pow2_le_iff_divide.
Print Assumptions nat_pow2_square_or_double_square.
