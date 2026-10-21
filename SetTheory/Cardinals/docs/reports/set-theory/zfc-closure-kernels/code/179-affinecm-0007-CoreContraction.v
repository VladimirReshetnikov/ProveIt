From Coq Require Import Arith.PeanoNat NArith Lia.
Require Import DrainCore.

(** A bounded halting predicate supplies the decreasing measure needed when
    normalization contracts an arbitrary number of actual transitions. *)
Inductive within (G : graph) : nat -> N -> regs -> Prop :=
| within_now n v R : G v = Some Halt -> within G n v R
| within_next n v R w Q :
    step G v R w Q -> within G n w Q -> within G (Datatypes.S n) v R.

Lemma within_raise G n v R : within G n v R -> within G (Datatypes.S n) v R.
Proof.
  intro H; induction H.
  - constructor; assumption.
  - eapply within_next; eauto.
Qed.

Lemma within_ext G n v R Q :
  req R Q -> within G n v R -> within G n v Q.
Proof.
  intros E H; inversion H; subst.
  - constructor; assumption.
  - eapply within_next; [eapply step_source_ext; eauto|eassumption].
Qed.

Lemma within_after_step G n v R w Q :
  step G v R w Q -> within G (Datatypes.S n) v R -> within G n w Q.
Proof.
  intros E H; inversion H; subst.
  - exfalso; eapply step_not_halt; eauto.
  - match goal with J : step G v R _ _ |- _ =>
      destruct (step_deterministic _ _ _ _ _ _ _ E J) as [D A]
    end.
    subst; eapply within_ext; [apply req_sym; exact A|eassumption].
Qed.

Lemma within_after_step_weak G n v R w Q :
  step G v R w Q -> within G n v R -> within G n w Q.
Proof.
  intros E H; destruct n as [|n].
  - inversion H; subst; exfalso; eapply step_not_halt; eauto.
  - apply within_raise; eapply within_after_step; eauto.
Qed.

Lemma within_after_steps G m n v R w Q :
  steps G m v R w Q -> within G n v R -> within G n w Q.
Proof.
  intros E; induction E; intro B.
  - eapply within_ext; eauto.
  - apply IHE; eapply within_after_step_weak; eauto.
Qed.

Lemma accelerate_within G v R n :
  drainb G v = true -> within G n v R ->
  within G n (fst (accelerate G v R)) (snd (accelerate G v R)).
Proof.
  unfold drainb; destruct (G v) as [[|r [w a] b]|] eqn:E;
    try discriminate.
  simpl; rewrite Bool.andb_true_iff, N.eqb_eq, Nat.eqb_eq.
  intros [D A] H; subst w; unfold accelerate; rewrite E; simpl.
  eapply within_after_steps; [eapply drain_exact_steps; eauto|exact H].
Qed.

Lemma normalize_within fuel G v R n :
  within G n v R ->
  within G n (fst (normalize fuel G v R)) (snd (normalize fuel G v R)).
Proof.
  revert v R; induction fuel as [|f IH]; intros v R H; simpl; [exact H|].
  destruct (drainb G v) eqn:E; [|exact H].
  pose proof (accelerate_within G v R n E H) as J.
  destruct (accelerate G v R) as [w Q]; simpl in J; apply IH; exact J.
Qed.

Lemma halts_has_budget G v R : halts G v R -> exists n, within G n v R.
Proof.
  intro H; induction H.
  - exists 0; constructor; assumption.
  - destruct IHhalts as [n A]; exists (Datatypes.S n); eapply within_next; eauto.
Qed.

(** The accelerated graph executes a genuine tested edge at each retained
    vertex and then contracts every recognized drain allowed by [fuel].
    A normalized start lies in the finite retained core when the separately
    checked graph/rank certificate says so. *)
Inductive core_halts (fuel : nat) (G : graph) : N -> regs -> Prop :=
| core_now v R : G v = Some Halt -> core_halts fuel G v R
| core_next v R w Q :
    step G v R w Q ->
    core_halts fuel G (fst (normalize fuel G w Q))
                     (snd (normalize fuel G w Q)) ->
    core_halts fuel G v R.

Theorem core_halts_sound fuel G v R :
  core_halts fuel G v R -> halts G v R.
Proof.
  intro H; induction H.
  - constructor; assumption.
  - eapply halt_later; [exact H|].
    apply (proj2 (normalize_halts_iff fuel G w Q)); exact IHcore_halts.
Qed.

Lemma within_core_halts fuel G n :
  forall v R, within G n v R -> core_halts fuel G v R.
Proof.
  induction n as [|n IH]; intros v R H; inversion H; subst.
  - constructor; assumption.
  - constructor; assumption.
  - eapply core_next; [eassumption|].
    apply IH; apply normalize_within; assumption.
Qed.

Theorem core_halts_complete fuel G v R :
  halts G v R -> core_halts fuel G v R.
Proof.
  intro H; destruct (halts_has_budget _ _ _ H) as [n A].
  eapply within_core_halts; exact A.
Qed.

Theorem core_halts_iff fuel G v R :
  core_halts fuel G v R <-> halts G v R.
Proof. split; [apply core_halts_sound|apply core_halts_complete]. Qed.

Theorem normalized_core_halts_iff fuel G v R :
  core_halts fuel G (fst (normalize fuel G v R))
                    (snd (normalize fuel G v R)) <-> halts G v R.
Proof.
  rewrite core_halts_iff; symmetry; apply normalize_halts_iff.
Qed.

Print Assumptions core_halts_iff.
Print Assumptions normalized_core_halts_iff.
