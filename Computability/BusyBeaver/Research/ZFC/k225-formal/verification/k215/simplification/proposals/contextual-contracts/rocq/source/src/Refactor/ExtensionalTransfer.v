(** Extensional whole-node replacement for the actual Wade register semantics.
    Result register files are related pointwise, avoiding functional
    extensionality when a replacement reorders independent updates. *)
From Coq Require Import Arith Lia.
From K230 Require Import RM.
#[local] Hint Constructors run : core.

Definition regs_eq (R S : regs) : Prop := forall i, R i = S i.

Lemma regs_eq_refl R : regs_eq R R.
Proof. intros i; reflexivity. Qed.

Lemma regs_eq_sym R S : regs_eq R S -> regs_eq S R.
Proof. intros E i; symmetry; apply E. Qed.

Lemma regs_eq_trans R S T : regs_eq R S -> regs_eq S T -> regs_eq R T.
Proof. intros E F i; rewrite E; apply F. Qed.

Lemma upd_congr R S r v w : regs_eq R S -> v = w ->
  regs_eq (upd R r v) (upd S r w).
Proof. intros E -> i; unfold upd; destruct (Nat.eqb i r); auto. Qed.

Definition NodeTransport (p q : prog) (n : nat) : Prop :=
  forall R x R', run p (ENode n) R x R' ->
  forall S, regs_eq R S -> exists S', run q (ENode n) S x S' /\ regs_eq R' S'.

Definition ClosedExt (p q : prog) : Prop :=
  forall n, nodes p n = nodes q n \/ NodeTransport p q n.

(** There is no rank or acyclicity premise: induction is on finite execution
    evidence, including loop-restart evidence. Nontermination is not assumed. *)
Theorem run_transfer_ext p q : ClosedExt p q ->
  forall e R x R', run p e R x R' ->
  forall S, regs_eq R S -> exists S', run q e S x S' /\ regs_eq R' S'.
Proof.
  intros HC e R x R' H. induction H; intros S E.
  - eexists; split; [constructor|]. apply upd_congr; auto.
  - exists (upd S r v); split; [apply run_decnz_pos; now rewrite <- E|].
    apply upd_congr; auto.
  - exists S; split; [constructor; now rewrite <- E|exact E].
  - exists S; split; [constructor|exact E].
  - exists S; split; [constructor|exact E].
  - exists S; split; [constructor|exact E].
  - exists S; split; [constructor|exact E].
  - destruct (HC n) as [En | C]; [|apply C with (R := R); [eauto 3|exact E]].
    destruct (IHrun S E) as [S' [Hq E']].
    exists S'; split; [apply run_node_car_break1; rewrite <- En; exact Hq|exact E'].
  - destruct (HC n) as [En | C]; [|apply C with (R := R); [eauto 3|exact E]].
    destruct (IHrun S E) as [S' [Hq E']].
    exists S'; split; [apply run_node_car_breakS; rewrite <- En; exact Hq|exact E'].
  - destruct (HC n) as [En | C]; [|apply C with (R := R); [eauto 3|exact E]].
    destruct (IHrun S E) as [S' [Hq E']].
    exists S'; split; [apply run_node_car_continue; rewrite <- En; exact Hq|exact E'].
  - destruct (HC n) as [En | C]; [|apply C with (R := R); [eauto 3|exact E]].
    destruct (IHrun S E) as [S' [Hq E']].
    exists S'; split; [apply run_node_car_halt; rewrite <- En; exact Hq|exact E'].
  - destruct (HC n) as [En | C]; [|apply C with (R := R); [eauto 3|exact E]].
    destruct (IHrun1 S E) as [S1 [Hq1 E1]].
    destruct (IHrun2 S1 E1) as [S' [Hq2 E']].
    exists S'; split; [eapply run_node_cdr_normal; rewrite <- En; eauto|exact E'].
  - destruct (HC n) as [En | C]; [|apply C with (R := R); [eauto 3|exact E]].
    destruct (IHrun1 S E) as [S1 [Hq1 E1]].
    destruct (IHrun2 S1 E1) as [S' [Hq2 E']].
    exists S'; split; [eapply run_node_cdr_break; rewrite <- En; eauto|exact E'].
  - destruct (HC n) as [En | C]; [|apply C with (R := R); [eauto 3|exact E]].
    destruct (IHrun1 S E) as [S1 [Hq1 E1]].
    destruct (IHrun2 S1 E1) as [S2 [Hq2 E2]].
    destruct (IHrun3 S2 E2) as [S' [Hq3 E']].
    exists S'; split; [|exact E'].
    eapply run_node_cdr_continue1; [rewrite <- En; exact Hq1|rewrite <- En; exact Hq2|exact Hq3].
  - destruct (HC n) as [En | C]; [|apply C with (R := R); [eauto 3|exact E]].
    destruct (IHrun1 S E) as [S1 [Hq1 E1]].
    destruct (IHrun2 S1 E1) as [S' [Hq2 E']].
    exists S'; split; [eapply run_node_cdr_continueS; rewrite <- En; eauto|exact E'].
  - destruct (HC n) as [En | C]; [|apply C with (R := R); [eauto 3|exact E]].
    destruct (IHrun1 S E) as [S1 [Hq1 E1]].
    destruct (IHrun2 S1 E1) as [S' [Hq2 E']].
    exists S'; split; [eapply run_node_cdr_halt; rewrite <- En; eauto|exact E'].
Qed.

Theorem iter_transfer_ext p q : ClosedExt p q -> root p = root q ->
  forall R, iter_halts p R -> forall S, regs_eq R S -> iter_halts q S.
Proof.
  intros HC Er R H. induction H; intros S E.
  - destruct (run_transfer_ext p q HC _ _ _ _ H S E) as [S' [Hq E']].
    apply (iter_halt q S S'). now rewrite <- Er.
  - destruct (run_transfer_ext p q HC _ _ _ _ H S E) as [S' [Hq E']].
    apply (iter_next q S S'); [now rewrite <- Er|now apply IHiter_halts].
Qed.

Corollary iter_iff_ext p q : ClosedExt p q -> ClosedExt q p -> root p = root q ->
  forall R, iter_halts p R <-> iter_halts q R.
Proof.
  intros Hpq Hqp Er R; split; intro H.
  - exact (iter_transfer_ext p q Hpq Er R H R (regs_eq_refl R)).
  - exact (iter_transfer_ext q p Hqp (eq_sym Er) R H R (regs_eq_refl R)).
Qed.

Print Assumptions run_transfer_ext.
Print Assumptions iter_iff_ext.
