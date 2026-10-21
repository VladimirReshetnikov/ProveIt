(* Positive-duration simulation preserves and reflects halting.
   Standalone Rocq/Coq theorem; no machine-specific axioms. *)
From Coq Require Import Arith Lia.

Set Implicit Arguments.

Fixpoint run {A : Type} (f : A -> A) (n : nat) (a : A) : A :=
  match n with
  | 0 => a
  | S k => f (run f k a)
  end.

Lemma run_add {A : Type} (f : A -> A) (n m : nat) (a : A) :
  run f (n + m) a = run f m (run f n a).
Proof.
  induction m as [|m IH].
  - now rewrite Nat.add_0_r.
  - rewrite Nat.add_succ_r. cbn. now rewrite IH.
Qed.

Lemma invariant_run {A : Type} (f : A -> A) (I : A -> Prop)
    (closed : forall a, I a -> I (f a)) (a : A)
    (initial : I a) (n : nat) : I (run f n a).
Proof.
  induction n as [|n IH]; cbn; auto.
Qed.

Section Transfer.
  Context {A B : Type}.
  Variable f : A -> A.
  Variable g : B -> B.
  Variable phi : A -> B.
  Variables I HA : A -> Prop.
  Variable HB : B -> Prop.
  Variable a : A.
  Hypothesis initial : I a.
  Hypothesis closed : forall x, I x -> I (f x).
  Hypothesis terminal : forall y, HB y -> HB (g y).
  Hypothesis reflect_terminal : forall x, HB (phi x) <-> HA x.
  Hypothesis simulate : forall x, I x ->
    exists k, 1 <= k /\ run g k (phi x) = phi (f x).

  Lemma schedule : forall n,
    exists t, n <= t /\ run g t (phi a) = phi (run f n a).
  Proof.
    induction n as [|n [t [Ht Et]]].
    - exists 0. split; [lia | reflexivity].
    - destruct (@simulate (run f n a)
        (@invariant_run A f I closed a initial n)) as [k [Hk Ek]].
      exists (t+k). split; [lia |].
      rewrite run_add, Et, Ek. reflexivity.
  Qed.

  (* A target halt at time n already forces a source halt by source time n. *)
  Lemma reflect_halt_at : forall n,
    HB (run g n (phi a)) -> HA (run f n a).
  Proof.
    intros n Hn.
    destruct (schedule n) as [t [Ht Et]].
    pose proof (@invariant_run B g HB terminal
      (run g n (phi a)) Hn (t-n)) as H.
    rewrite <- run_add in H.
    replace (n + (t-n)) with t in H by lia.
    rewrite Et in H. now apply (proj1 (reflect_terminal _)) in H.
  Qed.

  Theorem equihalting :
    (exists n, HA (run f n a)) <-> (exists t, HB (run g t (phi a))).
  Proof.
    split.
    - intros [n Hn]. destruct (schedule n) as [t [Ht Et]].
      exists t. rewrite Et. now apply (proj2 (reflect_terminal _)).
    - intros [n Hn]. exists n. now apply reflect_halt_at.
  Qed.
End Transfer.

Print Assumptions equihalting.
Print Assumptions reflect_halt_at.
