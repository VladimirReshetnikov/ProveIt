(** Endpoint-indexed chains with adjacent relation steps. *)

From Stdlib Require Import Lists.List.
From Foundation.Vorspiel.List Require Import Basic.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Inductive list_chainI {A} (R : A -> A -> Prop) :
    A -> A -> list A -> Prop :=
| chainI_singleton : forall a, list_chainI R a a [a]
| chainI_cons : forall a b c xs,
    R a b -> list_chainI R b c xs -> list_chainI R a c (a :: xs).

Arguments chainI_singleton {A R} a.
Arguments chainI_cons {A R a b c xs} _ _.

Lemma list_chainI_not_nil : forall A (R : A -> A -> Prop) a b,
  ~ list_chainI R a b [].
Proof. intros A R a b H. inversion H. Qed.

Lemma list_chainI_singleton_iff : forall A (R : A -> A -> Prop) a b x,
  list_chainI R a b [x] <-> a = x /\ x = b.
Proof.
  intros A R a b x. split.
  - intro H. inversion H; subst.
    + now split.
    + exfalso. now apply (list_chainI_not_nil H5).
  - intros [-> ->]. apply chainI_singleton.
Qed.

Lemma list_chainI_head_eq : forall A (R : A -> A -> Prop) a b x xs,
  list_chainI R a b (x :: xs) -> a = x.
Proof. intros A R a b x xs H. inversion H; reflexivity. Qed.

Lemma list_chainI_cons_cons_iff : forall A (R : A -> A -> Prop)
    a b x y xs,
  list_chainI R a b (x :: y :: xs) <->
  a = x /\ R x y /\ list_chainI R y b (y :: xs).
Proof.
  intros A R a b x y xs. split.
  - intro H. inversion H; subst.
    assert (Hhead : b0 = y) by now apply (list_chainI_head_eq H5).
    subst b0. now repeat split.
  - intros [-> [Hxy Htail]]. exact (chainI_cons Hxy Htail).
Qed.

Lemma list_chainI_tail_exists : forall A (R : A -> A -> Prop)
    a b xs,
  list_chainI R a b xs -> exists tail, xs = a :: tail.
Proof.
  intros A R a b xs H. inversion H; subst.
  - now exists [].
  - now exists xs0.
Qed.

Lemma list_chainI_suffix_exists : forall A (R : A -> A -> Prop)
    a b xs,
  list_chainI R a b xs -> exists prefix, xs = prefix ++ [b].
Proof.
  intros A R a b xs H. induction H.
  - now exists [].
  - destruct IHlist_chainI as [prefix ->].
    exists (a :: prefix). reflexivity.
Qed.

Lemma list_chainI_prefix_suffix : forall A (R : A -> A -> Prop)
    a b xs,
  list_chainI R a b xs ->
  (exists tail, xs = a :: tail) /\ (exists prefix, xs = prefix ++ [b]).
Proof.
  intros A R a b xs H. split.
  - exact (list_chainI_tail_exists H).
  - exact (list_chainI_suffix_exists H).
Qed.

Lemma list_chainI_last_eq : forall A (R : A -> A -> Prop)
    a b xs default,
  list_chainI R a b xs -> last xs default = b.
Proof.
  intros A R a b xs default H.
  destruct (list_chainI_suffix_exists H) as [prefix ->].
  apply last_last.
Qed.

Theorem list_chainI_endpoints_unique : forall A (R : A -> A -> Prop)
    a1 b1 a2 b2 xs,
  list_chainI R a1 b1 xs -> list_chainI R a2 b2 xs ->
  a1 = a2 /\ b1 = b2.
Proof.
  intros A R a1 b1 a2 b2 xs H1 H2.
  destruct (list_chainI_tail_exists H1) as [tail Hxs].
  subst xs. split.
  - now rewrite (list_chainI_head_eq H2).
  - rewrite <- (@list_chainI_last_eq A R a1 b1 (a1 :: tail) a1 H1).
    exact (@list_chainI_last_eq A R a2 b2 (a1 :: tail) a1 H2).
Qed.

Theorem list_chainI_not_mem_predecessor : forall A
    (R : A -> A -> Prop),
  (forall x, ~ R x x) ->
  (forall x y z, R x y -> R y z -> R x z) ->
  forall a b x xs,
    list_chainI R a b xs -> R x a -> ~ In x xs.
Proof.
  intros A R Hirrefl Htrans a b x xs Hchain.
  induction Hchain as [u | u v w tail Huv Hchain IH];
    intro Hxa; simpl.
  - intros [-> | Hnil]; [exact (Hirrefl x Hxa) | contradiction].
  - intros [Heq | Hin].
    + subst x. exact (Hirrefl _ Hxa).
    + apply (IH (Htrans _ _ _ Hxa Huv)). exact Hin.
Qed.

Theorem list_chainI_nodup : forall A (R : A -> A -> Prop),
  (forall x, ~ R x x) ->
  (forall x y z, R x y -> R y z -> R x z) ->
  forall a b xs, list_chainI R a b xs -> NoDup xs.
Proof.
  intros A R Hirrefl Htrans a b xs Hchain.
  induction Hchain as [u | u v w tail Huv Hchain IH].
  - constructor; [simpl; tauto | constructor].
  - constructor.
    + exact (list_chainI_not_mem_predecessor Hirrefl Htrans Hchain Huv).
    + exact IH.
Qed.

Theorem chainI_lists_explicit_finite_cover : forall A
    (R : A -> A -> Prop) (alphabet : list A),
  (forall x : A, In x alphabet) ->
  (forall x, ~ R x x) ->
  (forall x y z, R x y -> R y z -> R x z) ->
  forall a b xs, list_chainI R a b xs ->
    In xs (list_words_up_to alphabet (length alphabet)).
Proof.
  intros A R alphabet Hcover Hirrefl Htrans a b xs Hchain.
  apply nodup_lists_explicit_finite_cover; [exact Hcover |].
  exact (list_chainI_nodup Hirrefl Htrans Hchain).
Qed.

Theorem list_chainI_predecessor_exists : forall A
    (R : A -> A -> Prop) a b xs,
  list_chainI R a b xs -> a <> b ->
  exists tail c,
    R a c /\ xs = a :: c :: tail /\
    list_chainI R c b (c :: tail).
Proof.
  intros A R a b xs Hchain Hneq.
  inversion Hchain as [u | u c d rest Hrel Htail]; subst.
  - contradiction.
  - destruct (list_chainI_tail_exists Htail) as [tail Hrest].
    subst rest. now exists tail, c.
Qed.
