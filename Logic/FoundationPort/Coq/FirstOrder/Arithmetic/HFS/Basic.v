(**
  Executable standard model of hereditary-finite-set coding.

  Foundation develops finite-set operations inside arbitrary nonstandard
  models of ISigma_1.  Their standard interpretation is Ackermann coding:
  a natural number [s] represents the finite set of indices at which its
  binary expansion has a one bit.  Using [N] exposes this interpretation
  directly and lets Stdlib's verified bit operations supply a small,
  executable algebra.

  This module deliberately separates the representation-independent set laws
  from the still-missing arithmetic definability proofs.  In particular, no
  nonstandard-model comprehension principle is postulated.
*)

From Stdlib Require Import Bool.Bool Lists.List NArith.NArith.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.

Definition hfs_code : Type := N.

Definition hfs_mem (x s : hfs_code) : Prop :=
  N.testbit s x = true.

Definition hfs_empty : hfs_code := 0%N.

Definition hfs_insert (x s : hfs_code) : hfs_code :=
  N.setbit s x.

Definition hfs_remove (x s : hfs_code) : hfs_code :=
  N.clearbit s x.

Definition hfs_subset (s t : hfs_code) : Prop :=
  forall x, hfs_mem x s -> hfs_mem x t.

Definition hfs_equiv (s t : hfs_code) : Prop :=
  forall x, hfs_mem x s <-> hfs_mem x t.

Lemma hfs_extensionality : forall s t,
  hfs_equiv s t -> s = t.
Proof.
  intros s t H. apply N.bits_inj. intro x.
  unfold hfs_equiv, hfs_mem in H.
  destruct (N.testbit s x) eqn:Hs,
    (N.testbit t x) eqn:Ht; try reflexivity.
  - exfalso. specialize (proj1 (H x) Hs). congruence.
  - exfalso. specialize (proj2 (H x) Ht). congruence.
Qed.

Lemma hfs_equiv_iff_eq : forall s t,
  hfs_equiv s t <-> s = t.
Proof.
  intros. split; [apply hfs_extensionality|].
  now intros -> x.
Qed.

Lemma hfs_mem_empty_iff : forall x,
  hfs_mem x hfs_empty <-> False.
Proof.
  intro x. unfold hfs_mem, hfs_empty. rewrite N.bits_0.
  split; [discriminate|contradiction].
Qed.

Lemma hfs_not_mem_empty : forall x,
  ~ hfs_mem x hfs_empty.
Proof. intros x H. now apply hfs_mem_empty_iff in H. Qed.

Lemma hfs_mem_insert_iff : forall x y s,
  hfs_mem x (hfs_insert y s) <-> x = y \/ hfs_mem x s.
Proof.
  intros x y s. unfold hfs_mem, hfs_insert.
  rewrite N.setbit_iff. split.
  - intros [H | H]; [now left|now right].
  - intros [-> | H]; [now left|now right].
Qed.

Lemma hfs_mem_insert_self : forall x s,
  hfs_mem x (hfs_insert x s).
Proof. intros. apply hfs_mem_insert_iff. now left. Qed.

Lemma hfs_mem_insert_old : forall x y s,
  hfs_mem x s -> hfs_mem x (hfs_insert y s).
Proof. intros. apply hfs_mem_insert_iff. now right. Qed.

Lemma hfs_mem_remove_iff : forall x y s,
  hfs_mem x (hfs_remove y s) <-> hfs_mem x s /\ x <> y.
Proof.
  intros x y s. unfold hfs_mem, hfs_remove.
  rewrite N.clearbit_iff. split; intros [Hmem Hneq]; split;
    [exact Hmem|congruence|exact Hmem|congruence].
Qed.

Lemma hfs_not_mem_remove_self : forall x s,
  ~ hfs_mem x (hfs_remove x s).
Proof.
  intros x s H. apply hfs_mem_remove_iff in H. tauto.
Qed.

Lemma hfs_subset_refl : forall s, hfs_subset s s.
Proof. firstorder. Qed.

Lemma hfs_subset_trans : forall r s t,
  hfs_subset r s -> hfs_subset s t -> hfs_subset r t.
Proof. firstorder. Qed.

Lemma hfs_subset_antisym : forall s t,
  hfs_subset s t -> hfs_subset t s -> s = t.
Proof.
  intros s t Hst Hts. apply hfs_extensionality. intro x.
  split; [apply Hst|apply Hts].
Qed.

Lemma hfs_empty_subset : forall s,
  hfs_subset hfs_empty s.
Proof. intros s x H. now apply hfs_mem_empty_iff in H. Qed.

Lemma hfs_insert_subset_insert : forall x s t,
  hfs_subset s t ->
  hfs_subset (hfs_insert x s) (hfs_insert x t).
Proof.
  intros x s t H y Hy. apply hfs_mem_insert_iff in Hy.
  apply hfs_mem_insert_iff. destruct Hy as [-> | Hy].
  - now left.
  - right. now apply H.
Qed.

Lemma hfs_remove_subset : forall x s,
  hfs_subset (hfs_remove x s) s.
Proof.
  intros x s y H. now apply hfs_mem_remove_iff in H.
Qed.

Lemma hfs_insert_remove : forall x s,
  hfs_mem x s -> hfs_insert x (hfs_remove x s) = s.
Proof.
  intros x s Hx. apply hfs_extensionality. intro y.
  rewrite hfs_mem_insert_iff, hfs_mem_remove_iff.
  split.
  - intros [-> | [Hy _]]; assumption.
  - intro Hy. destruct (N.eq_dec y x) as [-> | Hneq].
    + now left.
    + right. now split.
Qed.

(** * Singleton and pair codes *)

Definition hfs_singleton (x : hfs_code) : hfs_code :=
  hfs_insert x hfs_empty.

Definition hfs_pair (x y : hfs_code) : hfs_code :=
  hfs_insert x (hfs_singleton y).

Lemma hfs_mem_singleton_iff : forall x y,
  hfs_mem x (hfs_singleton y) <-> x = y.
Proof.
  intros. unfold hfs_singleton. rewrite hfs_mem_insert_iff,
    hfs_mem_empty_iff. tauto.
Qed.

Lemma hfs_mem_pair_iff : forall x y z,
  hfs_mem x (hfs_pair y z) <-> x = y \/ x = z.
Proof.
  intros. unfold hfs_pair. rewrite hfs_mem_insert_iff,
    hfs_mem_singleton_iff. reflexivity.
Qed.

(** * Boolean set operations *)

Definition hfs_union (s t : hfs_code) : hfs_code := N.lor s t.
Definition hfs_inter (s t : hfs_code) : hfs_code := N.land s t.

Lemma hfs_mem_union_iff : forall x s t,
  hfs_mem x (hfs_union s t) <-> hfs_mem x s \/ hfs_mem x t.
Proof.
  intros. unfold hfs_mem, hfs_union. rewrite N.lor_spec.
  apply Bool.orb_true_iff.
Qed.

Lemma hfs_mem_inter_iff : forall x s t,
  hfs_mem x (hfs_inter s t) <-> hfs_mem x s /\ hfs_mem x t.
Proof.
  intros. unfold hfs_mem, hfs_inter. rewrite N.land_spec.
  apply Bool.andb_true_iff.
Qed.

Lemma hfs_union_comm : forall s t,
  hfs_union s t = hfs_union t s.
Proof.
  intros. apply hfs_extensionality. intro x.
  rewrite !hfs_mem_union_iff. tauto.
Qed.

Lemma hfs_inter_comm : forall s t,
  hfs_inter s t = hfs_inter t s.
Proof.
  intros. apply hfs_extensionality. intro x.
  rewrite !hfs_mem_inter_iff. tauto.
Qed.

Lemma hfs_union_empty_left : forall s,
  hfs_union hfs_empty s = s.
Proof.
  intro s. apply hfs_extensionality. intro x.
  rewrite hfs_mem_union_iff, hfs_mem_empty_iff. tauto.
Qed.

Lemma hfs_union_empty_right : forall s,
  hfs_union s hfs_empty = s.
Proof. intro s. rewrite hfs_union_comm. apply hfs_union_empty_left. Qed.

Lemma hfs_inter_empty_left : forall s,
  hfs_inter hfs_empty s = hfs_empty.
Proof.
  intro s. apply hfs_extensionality. intro x.
  rewrite hfs_mem_inter_iff, !hfs_mem_empty_iff. tauto.
Qed.

Lemma hfs_inter_empty_right : forall s,
  hfs_inter s hfs_empty = hfs_empty.
Proof. intro s. rewrite hfs_inter_comm. apply hfs_inter_empty_left. Qed.

Lemma hfs_union_subset_left : forall s t,
  hfs_subset s (hfs_union s t).
Proof. intros s t x H. apply hfs_mem_union_iff. now left. Qed.

Lemma hfs_union_subset_right : forall s t,
  hfs_subset t (hfs_union s t).
Proof. intros s t x H. apply hfs_mem_union_iff. now right. Qed.

Lemma hfs_inter_subset_left : forall s t,
  hfs_subset (hfs_inter s t) s.
Proof. intros s t x H. now apply hfs_mem_inter_iff in H. Qed.

Lemma hfs_inter_subset_right : forall s t,
  hfs_subset (hfs_inter s t) t.
Proof. intros s t x H. now apply hfs_mem_inter_iff in H. Qed.

Lemma hfs_inter_eq_left_of_subset : forall s t,
  hfs_subset s t -> hfs_inter s t = s.
Proof.
  intros s t H. apply hfs_subset_antisym.
  - apply hfs_inter_subset_left.
  - intros x Hx. apply hfs_mem_inter_iff. split; [exact Hx|now apply H].
Qed.

Lemma hfs_insert_eq_union_singleton : forall x s,
  hfs_insert x s = hfs_union (hfs_singleton x) s.
Proof.
  intros. apply hfs_extensionality. intro y.
  rewrite hfs_mem_insert_iff, hfs_mem_union_iff,
    hfs_mem_singleton_iff. reflexivity.
Qed.

(** * Disjointness *)

Definition hfs_disjoint (s t : hfs_code) : Prop :=
  hfs_inter s t = hfs_empty.

Lemma hfs_disjoint_iff : forall s t,
  hfs_disjoint s t <->
  forall x, ~ (hfs_mem x s /\ hfs_mem x t).
Proof.
  intros s t. split.
  - intros H x [Hs Ht].
    assert (Hi : hfs_mem x (hfs_inter s t)).
    { apply hfs_mem_inter_iff. now split. }
    rewrite H in Hi. exact (hfs_not_mem_empty Hi).
  - intro H. unfold hfs_disjoint. apply hfs_extensionality. intro x.
    rewrite hfs_mem_inter_iff, hfs_mem_empty_iff. split.
    + intro Hboth. exfalso. exact (H x Hboth).
    + contradiction.
Qed.

Lemma hfs_disjoint_sym : forall s t,
  hfs_disjoint s t -> hfs_disjoint t s.
Proof.
  intros s t H. unfold hfs_disjoint in *. now rewrite hfs_inter_comm.
Qed.

Lemma hfs_not_disjoint_of_mem : forall x s t,
  hfs_mem x s -> hfs_mem x t -> ~ hfs_disjoint s t.
Proof.
  intros x s t Hs Ht Hdis.
  pose proof (proj1 (hfs_disjoint_iff s t) Hdis) as H.
  exact (H x (conj Hs Ht)).
Qed.
