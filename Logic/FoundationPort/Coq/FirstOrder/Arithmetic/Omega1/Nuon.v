(** Executable binary population count.

    Foundation's [nuon] counts the one bits of a number.  Its long internal
    development constructs a bounded sequence certificate so that this count
    is Delta-zero definable in weak arithmetic.  Standard binary naturals
    already expose their constructors, so the intended function is a direct
    structural recursion.

    The resulting API is constructive and stronger than the source's chosen
    function: computation, uniqueness, positivity, and bounds are explicit.
    Internal segment/series certificates and their formula graphs remain
    outside this module. *)

From Stdlib Require Import Lia NArith.NArith.
From Foundation.FirstOrder.Arithmetic Require Import Exponential.
From Foundation.FirstOrder.Arithmetic.Omega1 Require Import Basic.

Open Scope N_scope.

Set Implicit Arguments.
Unset Strict Implicit.

(** Length bounds used by the source Nuon segment construction.  The
    executable smash length is one more than the product of its factors, so
    the source's nonstandard arithmetic induction collapses to monotonicity
    of multiplication followed by the successor bound. *)
Lemma nat_mul_length_lt_length_smash : forall i I L,
  i <= nat_length I ->
  i * nat_length L < nat_length (nat_smash I L).
Proof.
  intros i I L Hi.
  rewrite nat_length_smash.
  replace (nat_length I * nat_length L + 1) with
      (N.succ (nat_length I * nat_length L)) by lia.
  apply (proj2 (N.lt_succ_r _ _)).
  apply N.mul_le_mono_nonneg_r; [apply N.le_0_l | exact Hi].
Qed.

Lemma nat_mul_length_lt_length_smash_length : forall i z K,
  i <= nat_length z ->
  i * nat_length (nat_length K) <
    nat_length (nat_smash z (nat_length K)).
Proof.
  intros i z K Hi.
  apply nat_mul_length_lt_length_smash.
  exact Hi.
Qed.

(** Executable standard-model versions of the polynomial parameters used by
    the source Nuon construction. *)
Definition nat_polyI (A : N) : N :=
  nat_bexp (2 * A) (N.sqrt (nat_length A)).

Definition nat_polyL (A : N) : N :=
  nat_length (nat_polyI A) ^ 2.

Definition nat_polyU (A : N) : N :=
  (2 * A + 1) ^ 128.

Lemma nat_length_polyI : forall A,
  0 < A ->
  nat_length (nat_polyI A) = N.sqrt (nat_length A) + 1.
Proof.
  intros A HA. unfold nat_polyI.
  apply nat_length_bexp.
  rewrite nat_length_two_mul_of_pos by exact HA.
  pose proof (N.sqrt_le_lin (nat_length A)) as Hsqrt.
  lia.
Qed.

Lemma nat_polyI_le : forall A,
  0 < A ->
  nat_length A < nat_length (nat_polyI A) ^ 2.
Proof.
  intros A HA. rewrite nat_length_polyI by exact HA.
  pose proof (proj2 (N.sqrt_spec (nat_length A) (N.le_0_l _))) as Hroot.
  simpl in Hroot.
  nia.
Qed.

Lemma nat_four_mul_smash_self : forall a,
  nat_smash (4 * a) (4 * a) <= (nat_smash a a) ^ 16.
Proof.
  intro a.
  destruct (N.eq_dec a 0) as [-> | Ha].
  - simpl. reflexivity.
  - pose proof (proj1 (N.neq_0_lt_0 a) Ha) as Hpos.
    apply (proj2 (@nat_smash_le_iff
      ((nat_smash a a) ^ 16) (4 * a) (4 * a))).
    unfold nat_smash.
    replace ((nat_exp (nat_length a * nat_length a)) ^ 16) with
        (nat_exp (nat_length a * nat_length a * 16)) by
      (unfold nat_exp; rewrite <- N.pow_mul_r; reflexivity).
    rewrite nat_length_exp.
    assert (Hlen4 : nat_length (4 * a) = nat_length a + 2).
    { replace (4 * a) with (2 * (2 * a)) by nia.
      rewrite nat_length_two_mul_of_pos.
      - rewrite nat_length_two_mul_of_pos by exact Hpos.
        lia.
      - nia. }
    rewrite Hlen4.
    replace (nat_length a * nat_length a * 16 + 1) with
        (N.succ (nat_length a * nat_length a * 16)) by lia.
    assert (Hone : 1 <= nat_length a).
    { pose proof (@nat_length_pos_iff a) as H. lia. }
    apply (proj2 (N.lt_succ_r _ _)).
    nia.
Qed.

Fixpoint positive_nuon (p : positive) : N :=
  match p with
  | xH => 1
  | xO q => positive_nuon q
  | xI q => N.succ (positive_nuon q)
  end.

Definition nat_nuon (a : N) : N :=
  match a with
  | 0 => 0
  | N.pos p => positive_nuon p
  end.

Definition nat_Nuon (a n : N) : Prop := n = nat_nuon a.

Lemma positive_nuon_pos : forall p,
  0 < positive_nuon p.
Proof.
  induction p; simpl; lia.
Qed.

Lemma positive_nuon_le_size : forall p,
  positive_nuon p <= N.pos (Pos.size p).
Proof.
  induction p; simpl in *.
  - change (N.succ (positive_nuon p) <= N.succ (N.pos (Pos.size p))).
    apply (proj1 (N.succ_le_mono _ _)). exact IHp.
  - eapply N.le_trans; [exact IHp |]. apply N.le_succ_diag_r.
  - reflexivity.
Qed.

Lemma nat_nuon_zero : nat_nuon 0 = 0.
Proof. reflexivity. Qed.

Lemma nat_nuon_one : nat_nuon 1 = 1.
Proof. reflexivity. Qed.

Lemma nat_nuon_double : forall a,
  nat_nuon (2 * a) = nat_nuon a.
Proof.
  intro a. rewrite <- N.double_spec.
  destruct a; reflexivity.
Qed.

Lemma nat_nuon_double_add_one : forall a,
  nat_nuon (2 * a + 1) = nat_nuon a + 1.
Proof.
  intro a. rewrite <- N.succ_double_spec.
  destruct a; simpl; lia.
Qed.

Lemma nat_nuon_pos_iff : forall a,
  0 < nat_nuon a <-> 0 < a.
Proof.
  intro a. destruct a as [|p]; simpl.
  - reflexivity.
  - split; [intro; apply (proj1 (N.neq_0_lt_0 (N.pos p))); discriminate |].
    intro. apply positive_nuon_pos.
Qed.

Lemma nat_nuon_eq_zero_iff : forall a,
  nat_nuon a = 0 <-> a = 0.
Proof.
  intro a. destruct a as [|p]; [reflexivity |].
  split; [|discriminate]. intro H.
  pose proof (positive_nuon_pos p). simpl in H. lia.
Qed.

Lemma nat_nuon_le_length : forall a,
  nat_nuon a <= nat_length a.
Proof.
  intro a. destruct a as [|p]; [apply N.le_refl |].
  exact (@positive_nuon_le_size p).
Qed.

Lemma nat_nuon_le_self : forall a,
  nat_nuon a <= a.
Proof.
  intro a. eapply N.le_trans.
  - apply nat_nuon_le_length.
  - apply nat_length_le_self.
Qed.

Lemma nat_Nuon_exists_unique : forall a,
  exists! n, nat_Nuon a n.
Proof.
  intro a. exists (nat_nuon a). split; [reflexivity |].
  intros n H. symmetry. exact H.
Qed.

Lemma nat_Nuon_functional : forall a n m,
  nat_Nuon a n -> nat_Nuon a m -> n = m.
Proof. intros a n m -> ->. reflexivity. Qed.

Lemma nat_Nuon_graph : forall a n,
  nat_Nuon a n <-> n = nat_nuon a.
Proof. reflexivity. Qed.

Lemma nat_nuon_pow2 : forall k,
  nat_nuon (2 ^ k) = 1.
Proof.
  intro k. induction k using N.peano_ind.
  - reflexivity.
  - rewrite N.pow_succ_r'. rewrite nat_nuon_double. exact IHk.
Qed.

Lemma nat_nuon_under : forall k,
  nat_nuon (N.ones k) = k.
Proof.
  intro k. induction k using N.peano_ind.
  - reflexivity.
  - rewrite N.ones_succ, nat_nuon_double_add_one, IHk. lia.
Qed.

Lemma nat_nuon_singleton : forall k,
  nat_nuon (nat_bit_singleton k) = 1.
Proof.
  intro k. rewrite nat_bit_singleton_eq_pow. apply nat_nuon_pow2.
Qed.

Print Assumptions nat_nuon_double.
Print Assumptions nat_nuon_le_length.
Print Assumptions nat_nuon_under.
