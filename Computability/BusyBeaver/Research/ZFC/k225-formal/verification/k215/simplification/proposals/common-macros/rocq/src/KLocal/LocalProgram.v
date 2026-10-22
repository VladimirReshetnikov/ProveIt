(** Local transport for the repository's actual structured RM semantics.
    Same design as Lean RMTransfer, including whole-node semantic contracts.
    All result registers and all four exit forms are preserved. *)
From Coq Require Import Lists.List Bool.Bool Arith.Arith Lia.
From K230 Require Import RM.
Import ListNotations.

Definition inside (ok : nat -> bool) (e : edge) : bool :=
  match e with ENode n => ok n | _ => true end.

Definition Closed (p q : prog) (ok : nat -> bool) : Prop :=
  forall n, ok n = true ->
  (nodes p n = nodes q n /\ inside ok (fst (nodes p n)) = true /\
                            inside ok (snd (nodes p n)) = true) \/
  (forall R x R', run p (ENode n) R x R' -> run q (ENode n) R x R').

Theorem run_transfer p q ok : Closed p q ok ->
  forall e R x R', run p e R x R' -> inside ok e = true -> run q e R x R'.
Proof.
  intros HC e R x R' H. induction H; intro Hi;
    try solve [econstructor; eauto].
  all: destruct (HC n Hi) as [[E [HL HR]] | Hcontract].
  all: try solve [apply Hcontract; econstructor; eauto].
  all: try solve [econstructor; rewrite <- E; eauto].
  eapply run_node_cdr_continue1.
  - rewrite <- E. apply IHrun1, HL.
  - rewrite <- E. apply IHrun2, HR.
  - apply IHrun3, Hi.
Qed.

Corollary node_transfer p q ok : Closed p q ok -> forall n,
  ok n = true -> forall R x R', run p (ENode n) R x R' -> run q (ENode n) R x R'.
Proof. intros HC n Hn R x R' H. eapply run_transfer; eauto. Qed.

Theorem iter_transfer p q ok : Closed p q ok -> root p = root q ->
  ok (root p) = true -> forall R, iter_halts p R -> iter_halts q R.
Proof.
  intros HC Er Hr R H. induction H.
  - apply (iter_halt q R R'). rewrite <- Er. eapply node_transfer; eauto.
  - apply (iter_next q R R'); [|exact IHiter_halts].
    rewrite <- Er. eapply node_transfer; eauto.
Qed.

Definition edge_eq_dec (e f : edge) : {e = f} + {e <> f}.
Proof. decide equality; apply Nat.eq_dec. Defined.

Definition pair_eqb (ef gh : edge * edge) : bool :=
  if edge_eq_dec (fst ef) (fst gh) then
    if edge_eq_dec (snd ef) (snd gh) then true else false
  else false.

Lemma pair_eqb_true ef gh : pair_eqb ef gh = true -> ef = gh.
Proof.
  destruct ef as [e f], gh as [g h]. unfold pair_eqb; cbn.
  destruct (edge_eq_dec e g), (edge_eq_dec f h); congruence.
Qed.

Definition check_node (p q : prog) (ok : nat -> bool) (n : nat) : bool :=
  negb (ok n) || (pair_eqb (nodes p n) (nodes q n) &&
    inside ok (fst (nodes p n)) && inside ok (snd (nodes p n))).

Definition check_closed (p q : prog) (ok : nat -> bool) (bound : nat) : bool :=
  forallb (check_node p q ok) (seq 0 bound).

Theorem check_closed_sound p q ok bound :
  (forall n, ok n = true -> n < bound) ->
  check_closed p q ok bound = true -> Closed p q ok.
Proof.
  intros Hbound Hcheck n Hn. left.
  unfold check_closed in Hcheck. apply forallb_forall with (x := n) in Hcheck.
  - unfold check_node in Hcheck. rewrite Hn in Hcheck. cbn in Hcheck.
    apply andb_true_iff in Hcheck as [Hpair Hr].
    apply andb_true_iff in Hpair as [He Hl].
    split; [now apply pair_eqb_true|auto].
  - apply in_seq. split; [lia|]. apply Hbound, Hn.
Qed.

Print Assumptions run_transfer.
Print Assumptions check_closed_sound.
