(** Finite-set operations represented by duplicate-tolerant lists and covers. *)

From Stdlib Require Import Lists.List Arith.Wf_nat Lia.
From Foundation.Vorspiel Require Import Fintype.
From Foundation.Vorspiel.Finset Require Import Card.
From Foundation.Vorspiel.Set Require Import Basic.
From Foundation.Vorspiel.Order Require Import Ideal.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Lemma list_doubleton_incl_iff : forall A (a b : A) s,
  incl (a :: b :: nil) s <-> In a s /\ In b s.
Proof.
  intros A a b s. split.
  - intro H. split; apply H; simpl; tauto.
  - intros [Ha Hb] x [-> | [-> | Hnil]]; [exact Ha | exact Hb | inversion Hnil].
Qed.

Lemma list_strict_inclusion_length_lt : forall A (s t : list A),
  NoDup s -> list_strict_inclusion s t -> length s < length t.
Proof.
  intros A s t Hnodup [Hst Hnot].
  pose proof (NoDup_incl_length Hnodup Hst) as Hle.
  assert (Hcases : length s < length t \/ length t <= length s) by lia.
  destruct Hcases as [Hlt | Hge]; [exact Hlt |].
  exfalso. apply Hnot.
  exact (NoDup_length_incl Hnodup Hge Hst).
Qed.

Theorem no_list_strict_descending_chain : forall A (f : nat -> list A),
  (forall i, NoDup (f i)) ->
  ~ (forall i, exists j, i < j /\ list_strict_inclusion (f j) (f i)).
Proof.
  intros A f Hnodup Hdesc.
  assert (Hstop : forall n i, length (f i) = n -> False).
  { intro n. induction n using lt_wf_ind. intros i Hlen.
    destruct (Hdesc i) as [j [_ Hstrict]].
    assert (Hlt : length (f j) < n).
    { rewrite <- Hlen. apply list_strict_inclusion_length_lt.
      - apply Hnodup.
      - exact Hstrict. }
    exact (@H (length (f j)) Hlt j eq_refl). }
  exact (Hstop (length (f 0)) 0 eq_refl).
Qed.

Definition finite_range {I A} (C : finite_cover_data I)
    (f : I -> A) : list A :=
  map f (finite_cover_list C).

Lemma finite_range_member_iff : forall I A (C : finite_cover_data I)
    (f : I -> A) y,
  In y (finite_range C f) <-> exists i, f i = y.
Proof.
  intros I A C f y. unfold finite_range. rewrite in_map_iff. split.
  - intros [i [Hi _]]. now exists i.
  - intros [i Hi]. exists i. split; [exact Hi | apply finite_cover_complete].
Qed.

Definition list_image {A B} (s : list A) (f : A -> B) : list B :=
  map f s.

Lemma list_image_member_iff : forall A B (s : list A) (f : A -> B) y,
  In y (list_image s f) <-> exists x, In x s /\ f x = y.
Proof.
  intros A B s f y. unfold list_image. rewrite in_map_iff. split.
  - intros [x [Hxy Hx]]. exists x. now split.
  - intros [x [Hx Hxy]]. exists x. now split.
Qed.

Lemma list_image_member : forall A B (s : list A) (f : A -> B) x,
  In x s -> In (f x) (list_image s f).
Proof. intros A B s f x Hx. apply list_image_member_iff. now exists x. Qed.

Definition set_remove {A} (a : A) (s : pred_set A) : pred_set A :=
  fun x => s x /\ x <> a.

Definition set_binary_union {A} (s t : pred_set A) : pred_set A :=
  fun x => s x \/ t x.

Lemma set_remove_union_equiv : forall A (a : A) (s t : pred_set A),
  set_equiv (set_remove a (set_binary_union s t))
    (set_binary_union (set_remove a s) (set_remove a t)).
Proof.
  intros A a s t x. unfold set_remove, set_binary_union. tauto.
Qed.

Record explicit_equiv (A B : Type) := {
  equiv_forward : A -> B;
  equiv_backward : B -> A;
  equiv_left_inverse : forall x, equiv_backward (equiv_forward x) = x;
  equiv_right_inverse : forall y, equiv_forward (equiv_backward y) = y
}.

Arguments equiv_forward {A B} _ _.
Arguments equiv_backward {A B} _ _.

Definition finite_cover_transport {A B} (C : finite_cover_data A)
    (e : explicit_equiv A B) : finite_cover_data B.
Proof.
  refine {| finite_cover_list := map (equiv_forward e) (finite_cover_list C) |}.
  intro y. apply in_map_iff. exists (equiv_backward e y). split.
  - apply equiv_right_inverse.
  - apply finite_cover_complete.
Defined.

Lemma finite_cover_transport_member : forall A B
    (C : finite_cover_data A) (e : explicit_equiv A B) y,
  In y (finite_cover_list (finite_cover_transport C e)).
Proof. intros A B C e y. apply finite_cover_complete. Qed.

Theorem finite_cover_sup_reindex_equiv : forall X A B
    (J : join_order_data X) (CA : finite_cover_data A)
    (CB : finite_cover_data B) (e : explicit_equiv B A) (f : A -> X),
  jo_le J (finite_cover_sup J CB (fun i => f (equiv_forward e i)))
    (finite_cover_sup J CA f) /\
  jo_le J (finite_cover_sup J CA f)
    (finite_cover_sup J CB (fun i => f (equiv_forward e i))).
Proof.
  intros X A B J CA CB e f. split.
  - apply (proj2 (finite_cover_sup_le_iff J CB _ _)). intro i.
    apply finite_cover_elem_le_sup.
  - apply (proj2 (finite_cover_sup_le_iff J CA _ _)). intro i.
    pose proof (finite_cover_elem_le_sup J CB
      (fun j => f (equiv_forward e j)) (equiv_backward e i)) as H.
    rewrite <- (@equiv_right_inverse B A e i). exact H.
Qed.

Theorem list_flat_map_empty_iff : forall A B (s : list A) (f : A -> list B),
  flat_map f s = nil <-> forall x, In x s -> f x = nil.
Proof.
  intros A B s. induction s as [|a s IH]; intro f; simpl.
  - split; [intros _ x Hx; inversion Hx | intros; reflexivity].
  - split.
    + intro Hempty. apply app_eq_nil in Hempty.
      destruct Hempty as [Ha Htail].
      pose proof (proj1 (IH f) Htail) as Hs.
      intros x [<- | Hx]; [exact Ha | now apply Hs].
    + intro Hall.
      assert (Ha : f a = nil) by (apply Hall; now left).
      assert (Hs : flat_map f s = nil).
      { apply (proj2 (IH f)). intros x Hx. apply Hall. now right. }
      now rewrite Ha, Hs.
Qed.
