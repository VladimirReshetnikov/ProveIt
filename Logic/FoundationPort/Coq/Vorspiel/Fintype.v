(** Explicit finite covers, finite suprema, and dependent equality decisions. *)

From Stdlib Require Import Lists.List Logic.FunctionalExtensionality.
From Foundation.Vorspiel.Order Require Import Dense Ideal.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Record finite_cover_data (I : Type) := {
  finite_cover_list : list I;
  finite_cover_complete : forall i, In i finite_cover_list
}.

Arguments finite_cover_list {I} _.

Definition finite_cover_sup {A I} (J : join_order_data A)
    (C : finite_cover_data I) (f : I -> A) : A :=
  ideal_join_list J (map f (finite_cover_list C)).

Lemma finite_cover_elem_le_sup : forall A I (J : join_order_data A)
    (C : finite_cover_data I) (f : I -> A) i,
  jo_le J (f i) (finite_cover_sup J C f).
Proof.
  intros A I J C f i. apply ideal_join_list_member_bound.
  apply in_map. apply finite_cover_complete.
Qed.

Lemma finite_cover_le_sup : forall A I (J : join_order_data A)
    (C : finite_cover_data I) (f : I -> A) i a,
  jo_le J a (f i) -> jo_le J a (finite_cover_sup J C f).
Proof.
  intros A I J C f i a Hai. eapply preorder_trans.
  - exact Hai.
  - apply finite_cover_elem_le_sup.
Qed.

Theorem finite_cover_sup_le_iff : forall A I (J : join_order_data A)
    (C : finite_cover_data I) (f : I -> A) a,
  jo_le J (finite_cover_sup J C f) a <->
  forall i, jo_le J (f i) a.
Proof.
  intros A I J C f a. split.
  - intros H i. eapply preorder_trans.
    + apply finite_cover_elem_le_sup.
    + exact H.
  - intro Hall. apply ideal_join_list_least_upper.
    intros x Hx. apply in_map_iff in Hx.
    destruct Hx as [i [<- _]]. apply Hall.
Qed.

Lemma finite_cover_sup_empty : forall A I (J : join_order_data A)
    (C : finite_cover_data I) (f : I -> A),
  (forall i : I, False) ->
  finite_cover_sup J C f = jo_bottom J.
Proof.
  intros A I J C f Hempty. unfold finite_cover_sup.
  destruct (finite_cover_list C) as [|i rest] eqn:Hcover; [reflexivity |].
  exfalso. exact (Hempty i).
Qed.

Fixpoint list_dependent_eq_dec {I} {B : I -> Type}
    (a b : forall i, B i)
    (dec : forall i, {a i = b i} + {a i <> b i})
    (xs : list I) :
    {forall i, In i xs -> a i = b i} +
    {exists i, In i xs /\ a i <> b i}.
Proof.
  destruct xs as [|i xs].
  - left. intros j Hj. inversion Hj.
  - destruct (dec i) as [Hi | Hi].
    + destruct (@list_dependent_eq_dec I B a b dec xs) as [Hall | Hbad].
      * left. intros j [-> | Hj]; [exact Hi | now apply Hall].
      * right. destruct Hbad as [j [Hj Hneq]].
        exists j. split; [now right | exact Hneq].
    + right. exists i. split; [now left | exact Hi].
Defined.

Theorem finite_cover_dependent_eq_dec : forall I (C : finite_cover_data I)
    (B : I -> Type) (a b : forall i, B i),
  (forall i, {a i = b i} + {a i <> b i}) ->
  {a = b} + {a <> b}.
Proof.
  intros I C B a b dec.
  destruct (@list_dependent_eq_dec I B a b dec (finite_cover_list C))
    as [Hall | Hbad].
  - left. apply functional_extensionality_dep. intro i.
    apply Hall, finite_cover_complete.
  - right. intros Hab. destruct Hbad as [i [_ Hneq]].
    apply Hneq. now rewrite Hab.
Defined.
