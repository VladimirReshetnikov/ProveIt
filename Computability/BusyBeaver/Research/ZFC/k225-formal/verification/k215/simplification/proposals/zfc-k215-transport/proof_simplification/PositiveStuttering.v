From Coq Require Import Arith.PeanoNat Arith.Wf_nat Lia.

(** Positive finite stuttering for deterministic partial transition systems.
    The map need not be injective. The source invariant is the only invariant.
    Terminal preservation is required in just the source-to-target direction.
    This is a standalone companion to PositiveStuttering.lean. *)

Set Implicit Arguments.

Inductive Steps {C : Type} (step : C -> option C) : nat -> C -> C -> Prop :=
| steps_refl : forall c, Steps step 0 c c
| steps_next : forall n c c' d,
    step c = Some c' -> Steps step n c' d -> Steps step (S n) c d.

Arguments steps_refl {C step} c.
Arguments steps_next {C step n c c' d} _ _.

Definition Halts {C : Type} (step : C -> option C) (c : C) : Prop :=
  exists n d, Steps step n c d /\ step d = None.

Lemma steps_append {C : Type} (step : C -> option C) :
  forall n a b, Steps step n a b ->
  forall m c, Steps step m b c -> Steps step (n + m) a c.
Proof.
  intros n a b h; induction h; intros m z hz.
  - exact hz.
  - simpl. eapply steps_next; eauto.
Qed.

(** No successful prefix can extend beyond a terminal point. *)
Lemma steps_prefix_halt {C : Type} (step : C -> option C) :
  forall m a b, Steps step m a b ->
  forall n z, Steps step n a z -> step z = None ->
    m <= n /\ Steps step (n - m) b z.
Proof.
  intros m a b hp; induction hp as [a | m a a' b hs ht IH].
  - intros n z hn hz. split; [lia | now rewrite Nat.sub_0_r].
  - intros n z hn hz.
    inversion hn as [a0 | n0 a0 a'' z0 hs' hn']; subst.
    + congruence.
    + assert (a' = a'') by congruence. subst a''.
      destruct (IH _ _ hn' hz) as [Hle Htail].
      split; [lia | simpl; exact Htail].
Qed.

Record Simulation {A B : Type} (old : A -> option A) (new : B -> option B)
    (map : A -> B) (Inv : A -> Prop) : Prop := {
  preserve : forall c c', Inv c -> old c = Some c' -> Inv c';
  terminal : forall c, Inv c -> old c = None -> new (map c) = None;
  block : forall c c', Inv c -> old c = Some c' ->
    exists m, 0 < m /\ Steps new m (map c) (map c')
}.

Arguments preserve {A B old new map Inv} _ {c c'} _ _.
Arguments terminal {A B old new map Inv} _ {c} _ _.
Arguments block {A B old new map Inv} _ {c c'} _ _.

Section Transport.
Context {A B : Type} {old : A -> option A} {new : B -> option B}.
Context {map : A -> B} {Inv : A -> Prop}.
Variable sim : Simulation old new map Inv.

Lemma map_steps : forall n a b, Steps old n a b -> Inv a ->
  exists m, Steps new m (map a) (map b) /\ Inv b.
Proof.
  intros n a b h; induction h as [a | n a a' b hs ht IH]; intro ha.
  - exists 0. split; [constructor | exact ha].
  - destruct (block sim ha hs) as [m [hm hb]].
    destruct (IH (preserve sim ha hs)) as [k [hk hi]].
    exists (m + k). split; [eapply steps_append; eauto | exact hi].
Qed.

Theorem halts_forward : forall c, Inv c -> Halts old c -> Halts new (map c).
Proof.
  intros c hc [n [d [hr hs]]].
  destruct (map_steps hr hc) as [m [hm hd]].
  exists m, (map d). split; [exact hm | exact (terminal sim hd hs)].
Qed.

(** Each positive target block strictly shortens a finite halting target run.
    Determinism supplies the cancellation of a successful prefix. *)
Theorem halts_backward : forall c, Inv c -> Halts new (map c) -> Halts old c.
Proof.
  assert (go : forall n a, Inv a ->
    (exists z, Steps new n (map a) z /\ new z = None) -> Halts old a).
  {
    intro n; induction n using lt_wf_ind.
    intros a ha [z [hr hz]].
    destruct (old a) as [a' |] eqn:hs.
    - destruct (block sim ha hs) as [m [hm hb]].
      destruct (steps_prefix_halt hb hr hz) as [hmn ht].
      assert (hlt : n - m < n) by lia.
      destruct (H (n - m) hlt a' (preserve sim ha hs)
        (ex_intro _ z (conj ht hz))) as [k [w [hk hw]]].
      exists (S k), w. split; [eapply steps_next; eauto | exact hw].
    - exists 0, a. split; [constructor | exact hs].
  }
  intros c hc [n [z [hr hz]]].
  exact (go n c hc (ex_intro _ z (conj hr hz))).
Qed.

Theorem halts_iff : forall c, Inv c -> (Halts old c <-> Halts new (map c)).
Proof.
  intros c hc; split; [apply halts_forward | apply halts_backward]; exact hc.
Qed.

End Transport.

Print Assumptions halts_iff.
