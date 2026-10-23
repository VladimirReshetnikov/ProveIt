(** Finite-footprint transport for Wade register-machine big-step proofs.
    This is an adapter for the existing K230.RM semantics, not a new semantics.
    It preserves every exit and the exact final register function. *)
From Coq Require Import Lists.List Arith.Arith Bool.Bool.
From K230 Require Import RM.
Import ListNotations.

Definition allowed (S : list nat) (e : edge) : Prop :=
  match e with ENode n => In n S | _ => True end.

Definition closed_agreement (p q : prog) (S : list nat) : Prop :=
  forall n, In n S ->
    nodes p n = nodes q n /\
    allowed S (fst (nodes p n)) /\ allowed S (snd (nodes p n)).

Section Transfer.
Variables (p q : prog) (S : list nat).
Hypothesis HC : closed_agreement p q S.

Lemma same_node n : In n S -> nodes p n = nodes q n.
Proof. intro H; exact (proj1 (HC n H)). Qed.

Lemma allowed_car n : In n S -> allowed S (fst (nodes p n)).
Proof. intro H; exact (proj1 (proj2 (HC n H))). Qed.

Lemma allowed_cdr n : In n S -> allowed S (snd (nodes p n)).
Proof. intro H; exact (proj2 (proj2 (HC n H))). Qed.

Theorem run_transfer e R x R' :
  run p e R x R' -> allowed S e -> run q e R x R'.
Proof.
  intro Hrun. induction Hrun; intro HA.
  - constructor.
  - constructor. assumption.
  - constructor. assumption.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - apply run_node_car_break1.
    rewrite <- (same_node n HA). apply IHHrun, allowed_car, HA.
  - apply run_node_car_breakS.
    rewrite <- (same_node n HA). apply IHHrun, allowed_car, HA.
  - apply run_node_car_continue.
    rewrite <- (same_node n HA). apply IHHrun, allowed_car, HA.
  - apply run_node_car_halt.
    rewrite <- (same_node n HA). apply IHHrun, allowed_car, HA.
  - eapply run_node_cdr_normal.
    + rewrite <- (same_node n HA). apply IHHrun1, allowed_car, HA.
    + rewrite <- (same_node n HA). apply IHHrun2, allowed_cdr, HA.
  - eapply run_node_cdr_break.
    + rewrite <- (same_node n HA). apply IHHrun1, allowed_car, HA.
    + rewrite <- (same_node n HA). apply IHHrun2, allowed_cdr, HA.
  - eapply run_node_cdr_continue1.
    + rewrite <- (same_node n HA). apply IHHrun1, allowed_car, HA.
    + rewrite <- (same_node n HA). apply IHHrun2, allowed_cdr, HA.
    + apply IHHrun3, HA.
  - eapply run_node_cdr_continueS.
    + rewrite <- (same_node n HA). apply IHHrun1, allowed_car, HA.
    + rewrite <- (same_node n HA). apply IHHrun2, allowed_cdr, HA.
  - eapply run_node_cdr_halt.
    + rewrite <- (same_node n HA). apply IHHrun1, allowed_car, HA.
    + rewrite <- (same_node n HA). apply IHHrun2, allowed_cdr, HA.
Qed.

End Transfer.

Lemma closed_agreement_sym p q S :
  closed_agreement p q S -> closed_agreement q p S.
Proof.
  intros HC n Hn. destruct (HC n Hn) as [HE [HL HR]].
  rewrite <- HE. repeat split; assumption || reflexivity.
Qed.

Theorem run_iff p q S e R x R' :
  closed_agreement p q S -> allowed S e ->
  (run p e R x R' <-> run q e R x R').
Proof.
  intros HC HA. split; intro H.
  - exact (run_transfer p q S HC e R x R' H HA).
  - exact (run_transfer q p S (closed_agreement_sym p q S HC) e R x R' H HA).
Qed.

(** The finite gate checks membership, exact table agreement, and closure. *)
Definition memb (n : nat) (S : list nat) : bool :=
  if in_dec Nat.eq_dec n S then true else false.

Lemma memb_sound n S : memb n S = true -> In n S.
Proof. unfold memb. destruct (in_dec Nat.eq_dec n S); auto; discriminate. Qed.

Definition allowedb (S : list nat) (e : edge) : bool :=
  match e with ENode n => memb n S | _ => true end.

Lemma allowedb_sound S e : allowedb S e = true -> allowed S e.
Proof. destruct e; simpl; auto using memb_sound. Qed.

Definition edge_dec : forall a b : edge, {a = b} + {a <> b}.
Proof. decide equality; apply Nat.eq_dec. Defined.

Definition pairb (a b : edge * edge) : bool :=
  if edge_dec (fst a) (fst b) then
    if edge_dec (snd a) (snd b) then true else false
  else false.

Lemma pairb_sound a b : pairb a b = true -> a = b.
Proof.
  destruct a as [a1 a2], b as [b1 b2]. unfold pairb; simpl.
  destruct (edge_dec a1 b1), (edge_dec a2 b2); try discriminate.
  intros _. subst. reflexivity.
Qed.

Definition node_ok (p q : prog) (S : list nat) (n : nat) : bool :=
  pairb (nodes p n) (nodes q n) &&
  allowedb S (fst (nodes p n)) && allowedb S (snd (nodes p n)).

Definition check_footprint (p q : prog) (S : list nat) : bool :=
  forallb (node_ok p q S) S.

Theorem check_footprint_sound p q S :
  check_footprint p q S = true -> closed_agreement p q S.
Proof.
  unfold check_footprint. intros H n Hn.
  rewrite forallb_forall in H. specialize (H n Hn).
  unfold node_ok in H. apply andb_prop in H as [H HR].
  apply andb_prop in H as [HE HL].
  split; [apply pairb_sound, HE|]. split; apply allowedb_sound; assumption.
Qed.

Print Assumptions run_transfer.
Print Assumptions run_iff.
Print Assumptions check_footprint_sound.
