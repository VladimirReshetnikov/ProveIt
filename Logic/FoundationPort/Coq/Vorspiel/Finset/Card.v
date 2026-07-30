(** Cardinal and bounded-sum laws generalized from finite sets to lists. *)

From Stdlib Require Import Lists.List Lia.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition list_strict_inclusion {A} (s t : list A) : Prop :=
  incl s t /\ ~ incl t s.

Theorem list_strict_inclusion_of_incl_lt_length : forall A
    (s t : list A),
  NoDup t -> incl s t -> length s < length t ->
  list_strict_inclusion s t.
Proof.
  intros A s t Ht Hst Hlen. split; [exact Hst |].
  intro Hts. pose proof (NoDup_incl_length Ht Hts). lia.
Qed.

Lemma list_length_eq_of_eq : forall A (s t : list A),
  s = t -> length s = length t.
Proof. intros A s t ->. reflexivity. Qed.

Fixpoint list_nat_sum {A} (f : A -> nat) (xs : list A) : nat :=
  match xs with
  | nil => 0
  | x :: rest => f x + list_nat_sum f rest
  end.

Theorem list_nat_sum_le_length_mul : forall A (s : list A)
    (f : A -> nat) n,
  (forall a, In a s -> f a <= n) ->
  list_nat_sum f s <= length s * n.
Proof.
  intros A s. induction s as [|a s IH]; intros f n Hbound; simpl; [lia |].
  assert (Ha : f a <= n) by (apply Hbound; now left).
  assert (Hs : list_nat_sum f s <= length s * n).
  { apply IH. intros x Hx. apply Hbound. now right. }
  lia.
Qed.
