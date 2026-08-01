(** Small generic utilities for empty types, options, and restricted functions. *)

From Stdlib Require Import Logic.FunctionalExtensionality Lists.List.
Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Lemma empty_function_unique : forall A (f : Empty_set -> A),
  f = fun x => match x with end.
Proof.
  intros A f. apply functional_extensionality. intros [].
Qed.

Definition type_is_empty (E : Type) : Prop := E -> False.

Definition empty_type_elim {E A : Type} (h : type_is_empty E) (x : E) : A :=
  False_rect A (h x).

Lemma empty_type_function_unique : forall E A (h : type_is_empty E)
    (f : E -> A),
  f = empty_type_elim h.
Proof.
  intros E A h f. apply functional_extensionality. intro x.
  exact (False_rect _ (h x)).
Qed.

Lemma option_return_eq_some : forall A (a : A), Some a = Some a.
Proof. reflexivity. Qed.

Definition option_to_list {A} (o : option A) : list A :=
  match o with Some a => [a] | None => [] end.

Lemma option_to_list_singleton_iff : forall A (o : option A) a,
  option_to_list o = [a] <-> o = Some a.
Proof.
  intros A [x |] a; simpl; split; congruence.
Qed.

Definition function_equal_on {A B} (P : A -> Prop) (f g : A -> B) : Prop :=
  forall a, P a -> f a = g a.

Lemma function_equal_on_subset : forall A B (P Q : A -> Prop)
    (f g : A -> B),
  function_equal_on P f g ->
  (forall a, Q a -> P a) ->
  function_equal_on Q f g.
Proof.
  intros A B P Q f g Hfg Hsub a Ha. apply Hfg. now apply Hsub.
Qed.
