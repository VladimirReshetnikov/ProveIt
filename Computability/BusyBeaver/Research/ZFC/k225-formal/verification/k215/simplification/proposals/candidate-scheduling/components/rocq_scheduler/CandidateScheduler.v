(** k225-formal/rocqperm/CandidateScheduler.v (SHA256 2ca2be1e82353c35a055a07d34b590665d6901cf5c3f2b430061b73b61a7be92) under namespace K215F. *)
(** A reusable constructive fairness theorem for sequential proof enumerators.
    The scheduling abstraction was proposed in ProveIt's further-interface
    packet.  This implementation allows an arbitrary pending rank after refill:
    only strict decrease inside a candidate and exact index succession matter. *)
From Coq Require Import Arith Lia.

Set Implicit Arguments.

Module CandidateScheduler.
Section Generic.
Context {State : Type}.
Variable step : State -> option State.

Fixpoint run (n : nat) (s : State) : option State :=
  match n with
  | 0 => Some s
  | S n => match step s with Some t => run n t | None => None end
  end.

Definition halts (s : State) : Prop :=
  exists n t, run n s = Some t /\ step t = None.

Lemma run_add n m s :
  run (n + m) s = match run n s with Some t => run m t | None => None end.
Proof.
  revert s; induction n as [|n IH]; intro s; [reflexivity|].
  cbn. destruct (step s); [apply IH|reflexivity].
Qed.

Lemma halts_after n s t : run n s = Some t -> halts t -> halts s.
Proof.
  intros R [m [u [Ru H]]]. exists (n + m), u. split; [|exact H].
  rewrite run_add, R. exact Ru.
Qed.

Variable pending index : State -> nat.

Definition outcome (s : State) (target : nat) : Prop :=
  halts s \/ exists n t,
    run n s = Some t /\ pending t = 0 /\ index t = target.

Lemma outcome_now s : pending s = 0 -> outcome s (index s).
Proof. intro H. right. exists 0, s. repeat split; assumption. Qed.

Lemma outcome_stop s target : step s = None -> outcome s target.
Proof. intro H. left. exists 0, s. now split. Qed.

Lemma outcome_step s t target :
  step s = Some t -> outcome t target -> outcome s target.
Proof.
  intros E [[n [u [R H]]] | [n [u [R [P I]]]]].
  - left. exists (S n), u. cbn. rewrite E. now split.
  - right. exists (S n), u. cbn. rewrite E. now repeat split.
Qed.

Hypothesis advance : forall s t, step s = Some t ->
  pending s = 0 -> index t = S (index s).
Hypothesis descend : forall s t, step s = Some t ->
  pending s <> 0 -> pending t < pending s /\ index t = index s.

(** Outer induction counts candidate boundaries; inner induction drains the
    current candidate.  A refill is allowed to create any finite pending rank. *)
Lemma seek_by_offset k : forall s, outcome s (index s + k).
Proof.
  induction k as [k IHk] using lt_wf_ind.
  intro s. remember (pending s) as p eqn:Ep. revert s Ep.
  induction p as [p IHp] using lt_wf_ind. intros s Ep.
  destruct (Nat.eq_dec (pending s) 0) as [P0|P0].
  - destruct k as [|j].
    + rewrite Nat.add_0_r. now apply outcome_now.
    + destruct (step s) as [t|] eqn:E.
      * eapply outcome_step; [exact E|].
        pose proof (advance E P0) as It.
        replace (index s + S j) with (index t + j) by lia.
        apply IHk. lia.
      * now apply outcome_stop.
  - destruct (step s) as [t|] eqn:E.
    + destruct (descend E P0) as [Pt It].
      eapply outcome_step; [exact E|]. rewrite <- It.
      apply (IHp (pending t)); [lia|reflexivity].
    + now apply outcome_stop.
Qed.

Theorem seek target s : index s <= target -> outcome s target.
Proof.
  intro H. replace target with (index s + (target - index s)) by lia.
  apply seek_by_offset.
Qed.

(** One sufficiently late candidate suffices.  Its success contract need only
    cover boundary payloads actually reachable from this starting state. *)
Theorem complete_at target s : index s <= target ->
  (forall n t, run n s = Some t -> pending t = 0 ->
    index t = target -> halts t) ->
  halts s.
Proof.
  intros bound good.
  destruct (seek bound) as [H|[n [t [R [P I]]]]]; [exact H|].
  eapply halts_after; [exact R|]. exact (good n t R P I).
Qed.

(** A halted or successful candidate is enough; the compiler may choose a
    different sufficiently late candidate for every starting state. *)
Theorem cofinal_complete (accepts : nat -> Prop) :
  (forall lower, exists target, lower <= target /\ accepts target) ->
  (forall s, pending s = 0 -> accepts (index s) -> halts s) ->
  forall s, halts s.
Proof.
  intros cofinal accepts_halt s.
  destruct (cofinal (index s)) as [target [bound good]].
  destruct (seek bound) as [H|[n [t [R [P I]]]]]; [exact H|].
  eapply halts_after; [exact R|]. apply accepts_halt; [exact P|]. now rewrite I.
Qed.

End Generic.

Arguments run {State} step n s.
Arguments halts {State} step s.

End CandidateScheduler.

Print Assumptions CandidateScheduler.seek.
Print Assumptions CandidateScheduler.complete_at.
Print Assumptions CandidateScheduler.cofinal_complete.
