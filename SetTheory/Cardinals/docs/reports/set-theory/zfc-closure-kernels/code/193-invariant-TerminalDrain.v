(** Positive simulation with a finite terminal epilogue.

    Adapted from the repository's standalone PositiveStutter.v proposal,
    not from the checked K215 endpoint.  The change is semantic: a source
    terminal configuration need only lead to a finite target halt; it need
    not itself be related to an already terminal target configuration.

    No extensionality, classical-choice or fairness axiom is required.
*)

From Coq Require Import Arith.PeanoNat Arith.Wf_nat Lia.
Set Implicit Arguments.

Module TerminalDrain.

Fixpoint run {C : Type} (next : C -> option C) (n : nat) (c : C) : option C :=
  match n with
  | 0 => Some c
  | S n => match next c with Some d => run next n d | None => None end
  end.

Definition Halts {C : Type} (next : C -> option C) (c : C) : Prop :=
  exists n d, run next n c = Some d /\ next d = None.

Lemma run_add {C : Type} (next : C -> option C) n m c :
  run next (n + m) c =
  match run next n c with Some d => run next m d | None => None end.
Proof.
  revert c. induction n as [|n IH]; intro c; simpl.
  - reflexivity.
  - destruct (next c); [apply IH | reflexivity].
Qed.

Lemma halts_of_run {C : Type} {next : C -> option C} {n c d} :
  run next n c = Some d -> Halts next d -> Halts next c.
Proof.
  intros Hr (m & e & Hm & He). exists (n + m), e. split; [|exact He].
  rewrite run_add, Hr. exact Hm.
Qed.

Lemma halt_now {C : Type} {next : C -> option C} {c} :
  next c = None -> Halts next c.
Proof. intro H. exists 0, c. split; [reflexivity | exact H]. Qed.

(** A successful prefix of a terminating deterministic execution cannot
    pass its terminal point.  The residual length is strictly smaller if
    the prefix is nonempty. *)
Lemma terminal_suffix {C : Type} {next : C -> option C} (k : nat) :
  forall n c c' d,
  run next n c = Some d -> next d = None ->
  run next k c = Some c' ->
  exists m, n = k + m /\ run next m c' = Some d.
Proof.
  induction k as [|k IH]; intros n c c' d Hwhole Hd Hprefix.
  - simpl in Hprefix. inversion Hprefix; subst c'.
    exists n. split; [reflexivity | exact Hwhole].
  - destruct n as [|n].
    + simpl in Hwhole. inversion Hwhole; subst d.
      simpl in Hprefix. rewrite Hd in Hprefix. discriminate.
    + simpl in Hwhole, Hprefix.
      destruct (next c) as [c1|] eqn:E; [|discriminate].
      destruct (IH n c1 c' d Hwhole Hd Hprefix) as (m & Hm & Hr).
      exists m. split; [lia | exact Hr].
Qed.

Arguments terminal_suffix {C next} k {n c c' d} _ _ _.

Record Simulation {A B : Type}
  (stepA : A -> option A) (stepB : B -> option B)
  (R : A -> B -> Prop) : Prop := {
  finish : forall a b, R a b -> stepA a = None -> Halts stepB b;
  advance : forall a b a', R a b -> stepA a = Some a' ->
    exists k b', 0 < k /\ run stepB k b = Some b' /\ R a' b'
}.

Arguments finish {A B stepA stepB R} _ {a b} _ _.
Arguments advance {A B stepA stepB R} _ {a b a'} _ _.

Section Transport.
  Context {A B : Type}.
  Context {stepA : A -> option A} {stepB : B -> option B}.
  Context {R : A -> B -> Prop}.

  Theorem preserves_halts (HS : Simulation stepA stepB R) :
    forall a b, R a b -> Halts stepA a -> Halts stepB b.
  Proof.
    intros a b Hab (n & d & Hn & Hd). revert a b Hab Hn.
    induction n as [|n IH]; intros a b Hab Hn.
    - simpl in Hn. inversion Hn; subst a. exact (finish HS Hab Hd).
    - simpl in Hn. destruct (stepA a) as [a'|] eqn:E; [|discriminate].
      destruct (advance HS Hab E) as (k & b' & Hpos & Hk & Hab').
      eapply halts_of_run; [exact Hk | exact (IH a' b' Hab' Hn)].
  Qed.

  Arguments preserves_halts _ {a b} _ _.

  (** Reflection needs only positive advancement, not the finish field. *)
  Theorem reflects_halts
    (Hadvance : forall a b a', R a b -> stepA a = Some a' ->
      exists k b', 0 < k /\ run stepB k b = Some b' /\ R a' b') :
    forall a b, R a b -> Halts stepB b -> Halts stepA a.
  Proof.
    intros a b Hab (n & d & Hn & Hd). revert a b Hab Hn.
    induction n using lt_wf_ind; intros a b Hab Hn.
    destruct (stepA a) as [a'|] eqn:E.
    - destruct (Hadvance _ _ _ Hab E) as (k & b' & Hpos & Hk & Hab').
      destruct (terminal_suffix k Hn Hd Hk) as (m & Hnm & Hm).
      assert (Hmn : m < n) by lia.
      eapply (@halts_of_run A stepA 1 a a').
      + simpl. rewrite E. reflexivity.
      + exact (H m Hmn a' b' Hab' Hm).
    - apply halt_now. exact E.
  Qed.

  Arguments reflects_halts _ {a b} _ _.

  Theorem halts_iff (HS : Simulation stepA stepB R) :
    forall a b, R a b -> (Halts stepA a <-> Halts stepB b).
  Proof.
    intros a b Hab. split.
    - exact (preserves_halts HS Hab).
    - exact (reflects_halts (fun a b a' => @advance _ _ _ _ _ HS a b a') Hab).
  Qed.
End Transport.

(** Actual proof examples, not tests of an untrusted evaluator. *)
Module Examples.

Definition stop (_ : unit) : option unit := None.
Definition countdown (n : nat) : option nat :=
  match n with 0 => None | S n => Some n end.
Definition epilogue (_ : unit) (n : nat) : Prop := n = 2.

Example terminal_epilogue : Simulation stop countdown epilogue.
Proof.
  constructor.
  - intros a b -> _. exists 2, 0. split; reflexivity.
  - intros a b a' _ H. discriminate H.
Qed.

Example immediate_terminal_agreement_fails :
  ~ (stop tt = None <-> countdown 2 = None).
Proof. intros [H _]. specialize (H eq_refl). discriminate H. Qed.

Example epilogue_halts_iff : Halts stop tt <-> Halts countdown 2.
Proof. exact (@halts_iff _ _ _ _ _ terminal_epilogue tt 2 eq_refl). Qed.

Definition loop (u : unit) : option unit := Some u.

Example zero_cost_advance : forall a b a',
  True -> loop a = Some a' ->
  exists k b', run stop k b = Some b' /\ True.
Proof. intros. exists 0, b. split; [reflexivity | exact I]. Qed.

Example loop_does_not_halt : ~ Halts loop tt.
Proof. intros (n & d & Hr & Hd). discriminate Hd. Qed.

Example stop_halts : Halts stop tt.
Proof. apply halt_now. reflexivity. Qed.

End Examples.

Print Assumptions halts_iff.
Print Assumptions Examples.epilogue_halts_iff.
Print Assumptions Examples.loop_does_not_halt.

End TerminalDrain.
