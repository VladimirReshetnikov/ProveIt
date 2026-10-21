(** Positive block simulation for deterministic partial transition systems.

    This standalone file is independent of the ProveIt endpoint development.
    A successful finite run has no earlier terminal configuration.  A single
    positive block simulation suffices for equivalence of finite halting.
*)

From Coq Require Import Arith.PeanoNat Arith.Wf_nat Lia.

Set Implicit Arguments.

Module PositiveStutter.

Fixpoint run {C : Type} (next : C -> option C) (n : nat) (c : C) : option C :=
  match n with
  | 0 => Some c
  | S n' =>
      match next c with
      | None => None
      | Some c' => run next n' c'
      end
  end.

Definition Halts {C : Type} (next : C -> option C) (c : C) : Prop :=
  exists n d, run next n c = Some d /\ next d = None.

Lemma run_add {C : Type} (next : C -> option C) (n m : nat) (c : C) :
  run next (n + m) c =
  match run next n c with
  | None => None
  | Some d => run next m d
  end.
Proof.
  revert c. induction n as [|n IH]; intro c; simpl.
  - reflexivity.
  - destruct (next c); [apply IH | reflexivity].
Qed.

Lemma halts_of_run {C : Type} {next : C -> option C}
  {n : nat} {c d : C} :
  run next n c = Some d -> Halts next d -> Halts next c.
Proof.
  intros Hrun (m & e & Hm & He).
  exists (n + m), e. split; [|exact He].
  rewrite run_add, Hrun. exact Hm.
Qed.

Lemma halt_now {C : Type} {next : C -> option C} {c : C} :
  next c = None -> Halts next c.
Proof. intro H. exists 0, c. split; [reflexivity | exact H]. Qed.

(** A successful prefix cannot continue beyond a terminal endpoint. *)
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
  sim_terminal : forall a b, R a b ->
    (stepA a = None <-> stepB b = None);
  sim_advance : forall a b a', R a b -> stepA a = Some a' ->
    exists k b', 0 < k /\ run stepB k b = Some b' /\ R a' b'
}.

Arguments sim_terminal {A B stepA stepB R} _ {a b} _.
Arguments sim_advance {A B stepA stepB R} _ {a b a'} _ _.

Section Transport.
  Context {A B : Type}.
  Context {stepA : A -> option A} {stepB : B -> option B}.
  Context {R : A -> B -> Prop}.

  Theorem preserves_halts (HS : Simulation stepA stepB R) :
    forall a b, R a b -> Halts stepA a -> Halts stepB b.
  Proof.
    intros a b Hab (n & d & Hn & Hd).
    revert a b Hab Hn.
    induction n as [|n IH]; intros a b Hab Hn.
    - simpl in Hn. inversion Hn; subst a.
      apply halt_now. apply (proj1 (sim_terminal HS Hab)). exact Hd.
    - simpl in Hn. destruct (stepA a) as [a'|] eqn:E; [|discriminate].
      destruct (sim_advance HS Hab E) as (k & b' & Hpos & Hk & Hab').
      eapply halts_of_run; [exact Hk | exact (IH a' b' Hab' Hn)].
  Qed.

  Arguments preserves_halts _ {a b} _ _.

  Theorem reflects_halts (HS : Simulation stepA stepB R) :
    forall a b, R a b -> Halts stepB b -> Halts stepA a.
  Proof.
    intros a b Hab (n & d & Hn & Hd).
    revert a b Hab Hn.
    induction n using lt_wf_ind; intros a b Hab Hn.
    destruct (stepA a) as [a'|] eqn:E.
    - destruct (sim_advance HS Hab E) as (k & b' & Hpos & Hk & Hab').
      destruct (terminal_suffix k Hn Hd Hk) as (m & Hnm & Hm).
      assert (Hmn : m < n) by lia.
      assert (Ha' : Halts stepA a').
      { exact (H m Hmn a' b' Hab' Hm). }
      eapply (@halts_of_run A stepA 1 a a');
        [simpl; rewrite E; reflexivity | exact Ha'].
    - apply halt_now. exact E.
  Qed.

  Arguments reflects_halts _ {a b} _ _.

  (** One positive simulation gives both directions, with no fairness axiom. *)
  Theorem halts_iff (HS : Simulation stepA stepB R) :
    forall a b, R a b -> (Halts stepA a <-> Halts stepB b).
  Proof.
    intros a b Hab. split.
    - exact (preserves_halts HS Hab).
    - exact (reflects_halts HS Hab).
  Qed.

  Theorem nonhalting_iff (HS : Simulation stepA stepB R) :
    forall a b, R a b -> (~ Halts stepA a <-> ~ Halts stepB b).
  Proof.
    intros a b Hab. split; intros Hnot Hhalt.
    - apply Hnot. exact (reflects_halts HS Hab Hhalt).
    - apply Hnot. exact (preserves_halts HS Hab Hhalt).
  Qed.
End Transport.

Print Assumptions halts_iff.
Print Assumptions nonhalting_iff.

End PositiveStutter.
