(** A bounded natural-list decoder and its fundamental element bound. *)

From Stdlib Require Import Arith.Cantor Lists.List Lia.

Set Implicit Arguments.
Unset Strict Implicit.

Lemma cantor_of_nat_components_le : forall n,
  fst (Cantor.of_nat n) <= n /\ snd (Cantor.of_nat n) <= n.
Proof.
  intro n. pose proof (Cantor.to_nat_non_decreasing
    (fst (Cantor.of_nat n)) (snd (Cantor.of_nat n))) as H.
  rewrite <- (surjective_pairing (Cantor.of_nat n)) in H at 1.
  rewrite Cantor.cancel_to_of in H. lia.
Qed.

(** Fuel is separated from the code so the recursive bound is reusable even
    for truncated decoding.  Taking fuel equal to the code gives the source
    decoder interface. *)
Fixpoint denumerable_nat_list_fuel (fuel code : nat) : list nat :=
  match fuel, code with
  | 0, _ => nil
  | S fuel', 0 => nil
  | S fuel', S n =>
      let '(head, tail) := Cantor.of_nat n in
      head :: denumerable_nat_list_fuel fuel' tail
  end.

Definition denumerable_nat_list (code : nat) : list nat :=
  denumerable_nat_list_fuel code code.

Theorem denumerable_nat_list_fuel_member_lt : forall fuel code i,
  In i (denumerable_nat_list_fuel fuel code) -> i < code.
Proof.
  induction fuel as [|fuel IH]; intros code i Hi;
    [destruct code; inversion Hi |].
  destruct code as [|n]; [inversion Hi |].
  cbn [denumerable_nat_list_fuel] in Hi.
  destruct (Cantor.of_nat n) as [head tail] eqn:Hpair.
  apply in_inv in Hi.
  pose proof (cantor_of_nat_components_le n) as Hbounds.
  rewrite Hpair in Hbounds. simpl in Hbounds.
  destruct Hbounds as [Hhead Htail]. destruct Hi as [Heq | Hmember].
  { subst i. lia. }
  { pose proof (IH tail i Hmember) as Hrec. lia. }
Qed.

Theorem denumerable_nat_list_member_lt : forall code i,
  In i (denumerable_nat_list code) -> i < code.
Proof. intros code i. apply denumerable_nat_list_fuel_member_lt. Qed.
