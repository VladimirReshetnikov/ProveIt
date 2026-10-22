From Coq Require Import Lists.List Arith.PeanoNat NArith Lia.
Import ListNotations.

(** Exact checkpoint semantics.  Register files are compared extensionally,
    so no functional-extensionality axiom is used. *)
Definition regs := nat -> nat.
Definition req (R S : regs) := forall i, R i = S i.
Definition increments := list (nat * nat).
Fixpoint amount (a : increments) (r : nat) : nat :=
  match a with
  | [] => 0
  | (s,k)::xs => (if Nat.eqb r s then k else 0) + amount xs r
  end.
Record arc := Arc { destination : N; adds : increments }.
Inductive node := Halt | Test (register : nat) (nonzero zero : arc).
Definition graph := N -> option node.
Definition plus (R : regs) (a : increments) : regs :=
  fun i => R i + amount a i.
Definition decplus (R : regs) (r : nat) (a : increments) : regs :=
  fun i => (if Nat.eqb i r then Nat.pred (R r) else R i) + amount a i.

Inductive step (G : graph) : N -> regs -> N -> regs -> Prop :=
| step_zero v r a b R S :
    G v = Some (Test r a b) -> R r = 0 ->
    req S (plus R (adds b)) -> step G v R (destination b) S
| step_pos v r a b R S :
    G v = Some (Test r a b) -> 0 < R r ->
    req S (decplus R r (adds a)) -> step G v R (destination a) S.

Inductive halts (G : graph) : N -> regs -> Prop :=
| halt_now v R : G v = Some Halt -> halts G v R
| halt_later v R w S : step G v R w S -> halts G w S -> halts G v R.

Lemma req_refl R : req R R.
Proof. intro i; reflexivity. Qed.
Lemma req_sym R S : req R S -> req S R.
Proof. intros H i; symmetry; apply H. Qed.
Lemma req_trans R S T : req R S -> req S T -> req R T.
Proof. intros H J i; rewrite H; apply J. Qed.

Lemma step_source_ext G v R S w T :
  req R S -> step G v R w T -> step G v S w T.
Proof.
  intros E H; destruct H.
  - eapply step_zero; eauto. rewrite <- E; assumption.
    intro i; rewrite H1; unfold plus; rewrite E; reflexivity.
  - eapply step_pos; eauto. rewrite <- E; assumption.
    intro i; rewrite H1; unfold decplus; rewrite E, E; reflexivity.
Qed.

Lemma halts_ext G v R S : req R S -> (halts G v R <-> halts G v S).
Proof.
  assert (one : forall v R, halts G v R -> forall S,
      req R S -> halts G v S).
  { intros v' R' H; induction H; intros T E.
    - constructor; assumption.
    - eapply halt_later. eapply step_source_ext; eauto. exact H0. }
  intro E; split; intro H; eapply one; eauto using req_sym.
Qed.

Lemma step_deterministic G v R w S w' S' :
  step G v R w S -> step G v R w' S' -> w = w' /\ req S S'.
Proof.
  intros H J; destruct H; inversion J; subst;
    match goal with
    | A : G _ = Some _, B : G _ = Some _ |- _ => rewrite A in B; inversion B; subst
    end; try lia.
  all: split; try reflexivity.
  all: eapply req_trans; eauto using req_sym.
Qed.

Lemma step_not_halt G v R w S : step G v R w S -> G v <> Some Halt.
Proof. intros H; destruct H; congruence. Qed.

Lemma halts_after_step G v R w S :
  step G v R w S -> (halts G v R <-> halts G w S).
Proof.
  intro E; split.
  - intro H; inversion H; subst.
    + exfalso; eapply step_not_halt; eauto.
    + match goal with J : step G v R _ _ |- _ =>
        destruct (step_deterministic _ _ _ _ _ _ _ E J) as [D Q]
      end.
      subst; eapply (halts_ext _ _ _ _ (req_sym _ _ Q)); eassumption.
  - intro H; eapply halt_later; eauto.
Qed.

(** n real transitions, with observational equality at the endpoints. *)
Inductive steps (G : graph) : nat -> N -> regs -> N -> regs -> Prop :=
| steps_zero v R S : req R S -> steps G 0 v R v S
| steps_next n v R w Q z T :
    step G v R w Q -> steps G n w Q z T -> steps G (Datatypes.S n) v R z T.

Lemma steps_target_ext G n v R w S T :
  steps G n v R w S -> req S T -> steps G n v R w T.
Proof.
  intros H; induction H; intro E.
  - constructor; eapply req_trans; eauto.
  - econstructor; eauto.
Qed.

Lemma halts_after_steps G n v R w S :
  steps G n v R w S -> (halts G v R <-> halts G w S).
Proof.
  intro H; induction H.
  - apply halts_ext; assumption.
  - rewrite (halts_after_step _ _ _ _ _ H); assumption.
Qed.

(** Affine drain: the tested register is zeroed before exit increments.
    The positive edge may add to any other register, including repeatedly. *)
Definition drain (r : nat) (a b : increments) (R : regs) : regs :=
  fun i => (if Nat.eqb i r then 0 else R i + R r * amount a i) + amount b i.

Lemma drain_one (r : nat) (a b : increments) R n :
  amount a r = 0 -> R r = S n ->
  req (drain r a b (decplus R r a)) (drain r a b R).
Proof.
  intros Az Rn i; unfold drain, decplus.
  destruct (Nat.eqb i r) eqn:E; [reflexivity|].
  rewrite Nat.eqb_refl, Rn, Az; simpl; nia.
Qed.

Theorem drain_exact_steps G v r a b :
  G v = Some (Test r (Arc v a) b) -> amount a r = 0 ->
  forall R, steps G (R r + 1) v R (destination b) (drain r a (adds b) R).
Proof.
  intros Gv Az.
  assert (H : forall n R, R r = n ->
      steps G (n + 1) v R (destination b) (drain r a (adds b) R)).
  { induction n as [|n IH]; intros R Rn.
    - simpl. eapply steps_next with (w:=destination b) (Q:=drain r a (adds b) R).
      + eapply step_zero; eauto.
        intro i; unfold drain, plus.
        destruct (Nat.eqb i r) eqn:E.
        * apply Nat.eqb_eq in E; subst; rewrite Rn; reflexivity.
        * rewrite Rn; simpl; lia.
      + constructor; apply req_refl.
    - change (steps G (S (n + 1)) v R (destination b) (drain r a (adds b) R)).
      eapply steps_next with (w:=v) (Q:=decplus R r a).
      + eapply step_pos with (a:=Arc v a) (b:=b); eauto.
        lia. apply req_refl.
      + eapply steps_target_ext.
        * apply IH. unfold decplus; rewrite Nat.eqb_refl, Rn, Az; simpl; lia.
        * apply drain_one with (n:=n); assumption. }
  intro R; apply H; reflexivity.
Qed.

Theorem drain_halts_iff G v r a b :
  G v = Some (Test r (Arc v a) b) -> amount a r = 0 ->
  forall R, halts G v R <-> halts G (destination b) (drain r a (adds b) R).
Proof.
  intros Hv Ha R; apply halts_after_steps with (n:=R r + 1).
  apply drain_exact_steps; assumption.
Qed.

Definition drainb (G : graph) (v : N) : bool :=
  match G v with
  | Some (Test r a b) => N.eqb (destination a) v && Nat.eqb (amount (adds a) r) 0
  | _ => false
  end.

Definition accelerate (G : graph) (v : N) (R : regs) : N * regs :=
  match G v with
  | Some (Test r a b) => (destination b, drain r (adds a) (adds b) R)
  | _ => (v,R)
  end.

Theorem accelerate_halts_iff G v : drainb G v = true -> forall R,
  halts G v R <-> halts G (fst (accelerate G v R)) (snd (accelerate G v R)).
Proof.
  unfold drainb; destruct (G v) as [[|r [w a] b]|] eqn:E;
    try discriminate.
  simpl; rewrite Bool.andb_true_iff, N.eqb_eq, Nat.eqb_eq.
  intros [D A] R; subst w; unfold accelerate; rewrite E; simpl.
  apply drain_halts_iff; assumption.
Qed.

Fixpoint normalize (fuel : nat) (G : graph) (v : N) (R : regs) : N * regs :=
  match fuel with
  | 0 => (v,R)
  | S f => if drainb G v then
      let '(w,Q) := accelerate G v R in normalize f G w Q
    else (v,R)
  end.

Theorem normalize_halts_iff fuel G v R :
  halts G v R <-> halts G (fst (normalize fuel G v R)) (snd (normalize fuel G v R)).
Proof.
  revert v R; induction fuel as [|f IH]; intros v R; simpl; [reflexivity|].
  destruct (drainb G v) eqn:E; [|reflexivity].
  pose proof (accelerate_halts_iff G v E R) as H.
  destruct (accelerate G v R) as [w Q]; simpl in H.
  rewrite H; apply IH.
Qed.

Fixpoint target (fuel : nat) (G : graph) (v : N) : N :=
  match fuel with
  | 0 => v
  | S f => if drainb G v then
      match G v with
      | Some (Test _ _ b) => target f G (destination b)
      | _ => v
      end
    else v
  end.

Lemma normalize_target fuel G v R : fst (normalize fuel G v R) = target fuel G v.
Proof.
  revert v R; induction fuel as [|f IH]; intros v R; simpl; [reflexivity|].
  destruct (drainb G v) eqn:E; [|reflexivity].
  unfold accelerate; destruct (G v) as [[|r a b]|] eqn:J; simpl.
  - unfold drainb in E; rewrite J in E; discriminate.
  - apply IH.
  - unfold drainb in E; rewrite J in E; discriminate.
Qed.

Print Assumptions drain_exact_steps.
Print Assumptions drain_halts_iff.
Print Assumptions normalize_halts_iff.
