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
