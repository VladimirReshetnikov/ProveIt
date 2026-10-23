(** Exactly the two shared increment commutations identified in the earlier
    CFG investigation. This module proves their semantic validity; it does
    not assume the Python flattening comparison as a theorem. *)
From Coq Require Import Arith Lia.
From K230 Require Import RM.
From K215F Require Import DagPerm.
From Refactor Require Import ExtensionalTransfer.

Definition inc_register (r : nat) (R : regs) : regs := upd R r (S (R r)).
Definition inc_pair (R : regs) (a b : nat) : regs := inc_register b (inc_register a R).

Lemma inc_register_congr r R T : regs_eq R T ->
  regs_eq (inc_register r R) (inc_register r T).
Proof. intros E; apply upd_congr; auto. Qed.

Lemma inc_pair_congr R T a b : regs_eq R T -> regs_eq (inc_pair R a b) (inc_pair T a b).
Proof. intro E; apply inc_register_congr, inc_register_congr, E. Qed.

Lemma inc_pair_comm R a b : regs_eq (inc_pair R a b) (inc_pair R b a).
Proof.
  destruct (Nat.eq_dec a b) as [->|Hab]; [apply regs_eq_refl|].
  assert (Eab : Nat.eqb a b = false) by (apply Nat.eqb_neq; exact Hab).
  assert (Eba : Nat.eqb b a = false) by (apply Nat.eqb_neq; lia).
  intros i. unfold inc_pair, inc_register, upd. rewrite Eab, Eba.
  destruct (Nat.eqb i a) eqn:Eia, (Nat.eqb i b) eqn:Eib; try reflexivity.
  apply Nat.eqb_eq in Eia,Eib. congruence.
Qed.

Lemma inc_pair_run p n a b R : nodes p n = (EInc a,EInc b) ->
  run p (ENode n) R XNormal (inc_pair R a b).
Proof.
  intro En. eapply run_node_cdr_normal.
  - rewrite En; cbn. apply run_inc.
  - rewrite En; cbn. apply run_inc.
Qed.

Lemma inc_pair_result p n a b R x R' : nodes p n = (EInc a,EInc b) ->
  run p (ENode n) R x R' -> x = XNormal /\ R' = inc_pair R a b.
Proof.
  intros En H; inversion H; subst; rewrite En in *; cbn [fst snd] in *;
    repeat match goal with
    | Hinc : run _ (EInc _) _ _ _ |- _ => inversion Hinc; subst; clear Hinc
    end; split; reflexivity.
Qed.

Theorem swap_increment_node p q n a b :
  nodes p n = (EInc a,EInc b) -> nodes q n = (EInc b,EInc a) ->
  NodeTransport p q n.
Proof.
  intros Ep Eq R x R' H T E.
  destruct (inc_pair_result p n a b R x R' Ep H) as [-> ->].
  exists (inc_pair T b a); split; [now apply inc_pair_run|].
  eapply regs_eq_trans; [apply inc_pair_congr; exact E|apply inc_pair_comm].
Qed.

(** Keep every source datum unchanged except these two node bodies. *)
Definition comm_nodes (n : nat) : edge * edge :=
  if Nat.eqb n 188 then (EInc 7,EInc 6)
  else if Nat.eqb n 190 then (EInc 1,EInc 6)
  else nodes dagPerm n.

Definition dagPermComm : prog := mkProg comm_nodes (root dagPerm) (nnodes dagPerm).

Lemma nodes_other n : n <> 188 -> n <> 190 -> nodes dagPermComm n = nodes dagPerm n.
Proof.
  intros H1 H2. unfold dagPermComm; cbn. unfold comm_nodes.
  apply Nat.eqb_neq in H1,H2. now rewrite H1,H2.
Qed.

Lemma dagPerm_to_comm : ClosedExt dagPerm dagPermComm.
Proof.
  intros n. destruct (Nat.eq_dec n 188) as [->|H1].
  - right. apply (swap_increment_node dagPerm dagPermComm 188 6 7); reflexivity.
  - destruct (Nat.eq_dec n 190) as [->|H2].
    + right. apply (swap_increment_node dagPerm dagPermComm 190 6 1); reflexivity.
    + left. symmetry. now apply nodes_other.
Qed.

Lemma comm_to_dagPerm : ClosedExt dagPermComm dagPerm.
Proof.
  intros n. destruct (Nat.eq_dec n 188) as [->|H1].
  - right. apply (swap_increment_node dagPermComm dagPerm 188 7 6); reflexivity.
  - destruct (Nat.eq_dec n 190) as [->|H2].
    + right. apply (swap_increment_node dagPermComm dagPerm 190 1 6); reflexivity.
    + left. now apply nodes_other.
Qed.

Theorem dagPerm_comm_iter_iff R : iter_halts dagPerm R <-> iter_halts dagPermComm R.
Proof. apply iter_iff_ext; [exact dagPerm_to_comm|exact comm_to_dagPerm|reflexivity]. Qed.

Theorem dagPerm_comm_runs e R x R' : run dagPerm e R x R' ->
  exists T, run dagPermComm e R x T /\ regs_eq R' T.
Proof. intro H; exact (run_transfer_ext _ _ dagPerm_to_comm _ _ _ _ H R (regs_eq_refl R)). Qed.

Theorem comm_dagPerm_runs e R x R' : run dagPermComm e R x R' ->
  exists T, run dagPerm e R x T /\ regs_eq R' T.
Proof. intro H; exact (run_transfer_ext _ _ comm_to_dagPerm _ _ _ _ H R (regs_eq_refl R)). Qed.

Print Assumptions swap_increment_node.
Print Assumptions dagPerm_comm_iter_iff.
Print Assumptions dagPerm_comm_runs.
Print Assumptions comm_dagPerm_runs.
