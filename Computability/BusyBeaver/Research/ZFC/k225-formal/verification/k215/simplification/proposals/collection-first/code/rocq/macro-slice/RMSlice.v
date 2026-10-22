(** Program-slice transport for the repository's structured register semantics.
    New proof, 2026-10-21. No hypothesis on register values or exit kinds. *)
From Coq Require Import List Bool Arith.
From K230 Require Import RM.
Import ListNotations.

Definition allowed (S : list nat) (e : edge) : Prop :=
  match e with ENode n => In n S | _ => True end.

Definition closed (p : prog) (S : list nat) : Prop :=
  forall n, In n S ->
    allowed S (fst (nodes p n)) /\ allowed S (snd (nodes p n)).

Definition agrees (p q : prog) (S : list nat) : Prop :=
  forall n, In n S -> nodes p n = nodes q n.

Theorem run_transport p q S : closed p S -> agrees p q S ->
  forall e R x R', run p e R x R' -> allowed S e -> run q e R x R'.
Proof.
  intros HC HA e R x R' H. induction H; cbn [allowed]; intro HS.
  - constructor.
  - constructor; assumption.
  - constructor; assumption.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - apply run_node_car_break1. rewrite <- (HA n HS).
    apply IHrun. exact (proj1 (HC n HS)).
  - apply run_node_car_breakS. rewrite <- (HA n HS).
    apply IHrun. exact (proj1 (HC n HS)).
  - apply run_node_car_continue. rewrite <- (HA n HS).
    apply IHrun. exact (proj1 (HC n HS)).
  - apply run_node_car_halt. rewrite <- (HA n HS).
    apply IHrun. exact (proj1 (HC n HS)).
  - eapply run_node_cdr_normal; rewrite <- (HA n HS).
    + apply IHrun1. exact (proj1 (HC n HS)).
    + apply IHrun2. exact (proj2 (HC n HS)).
  - eapply run_node_cdr_break; rewrite <- (HA n HS).
    + apply IHrun1. exact (proj1 (HC n HS)).
    + apply IHrun2. exact (proj2 (HC n HS)).
  - eapply run_node_cdr_continue1.
    + rewrite <- (HA n HS). apply IHrun1. exact (proj1 (HC n HS)).
    + rewrite <- (HA n HS). apply IHrun2. exact (proj2 (HC n HS)).
    + apply IHrun3. exact HS.
  - eapply run_node_cdr_continueS; rewrite <- (HA n HS).
    + apply IHrun1. exact (proj1 (HC n HS)).
    + apply IHrun2. exact (proj2 (HC n HS)).
  - eapply run_node_cdr_halt; rewrite <- (HA n HS).
    + apply IHrun1. exact (proj1 (HC n HS)).
    + apply IHrun2. exact (proj2 (HC n HS)).
Qed.

Lemma closed_agrees p q S : closed p S -> agrees p q S -> closed q S.
Proof. intros HC HA n Hn. rewrite <- (HA n Hn). exact (HC n Hn). Qed.

Theorem run_iff p q S : closed p S -> agrees p q S ->
  forall e R x R', allowed S e ->
    (run p e R x R' <-> run q e R x R').
Proof.
  intros HC HA e R x R' HE. split; intro H.
  - exact (run_transport p q S HC HA e R x R' H HE).
  - apply (run_transport q p S (closed_agrees p q S HC HA)); auto.
    intros n Hn. symmetry. exact (HA n Hn).
Qed.

(** The untrusted generator supplies only a finite list. The kernel checks
    both its closure and every source/target row equality. *)
Definition edge_eq_dec (a b : edge) : {a = b} + {a <> b}.
Proof. decide equality; apply Nat.eq_dec. Defined.

Definition row_eqb (a b : edge * edge) : bool :=
  if edge_eq_dec (fst a) (fst b) then
    if edge_eq_dec (snd a) (snd b) then true else false
  else false.

Lemma row_eqb_sound a b : row_eqb a b = true -> a = b.
Proof.
  destruct a as [a1 a2], b as [b1 b2]. unfold row_eqb; cbn.
  destruct (edge_eq_dec a1 b1), (edge_eq_dec a2 b2);
    intros H; try discriminate; subst; reflexivity.
Qed.

Definition allowedb (S : list nat) (e : edge) : bool :=
  match e with ENode n => existsb (Nat.eqb n) S | _ => true end.

Lemma allowedb_sound S e : allowedb S e = true -> allowed S e.
Proof.
  destruct e; cbn; try tauto. rewrite existsb_exists.
  intros [m [Hm He]]. apply Nat.eqb_eq in He. now subst m.
Qed.

Definition check_slice (p q : prog) (S : list nat) : bool :=
  forallb (fun n =>
    allowedb S (fst (nodes p n)) &&
    allowedb S (snd (nodes p n)) &&
    row_eqb (nodes p n) (nodes q n)) S.

Theorem check_slice_sound p q S : check_slice p q S = true ->
  closed p S /\ agrees p q S.
Proof.
  unfold check_slice. rewrite forallb_forall. intro H. split.
  - intros n Hn. specialize (H n Hn).
    apply andb_true_iff in H as [H _].
    apply andb_true_iff in H as [Ha Hb].
    split; now apply allowedb_sound.
  - intros n Hn. specialize (H n Hn).
    apply andb_true_iff in H as [_ H]. now apply row_eqb_sound.
Qed.

Corollary checked_run_iff p q S : check_slice p q S = true ->
  forall e R x R', allowed S e ->
    (run p e R x R' <-> run q e R x R').
Proof.
  intros H. destruct (check_slice_sound p q S H) as [HC HA].
  exact (run_iff p q S HC HA).
Qed.

Print Assumptions checked_run_iff.
