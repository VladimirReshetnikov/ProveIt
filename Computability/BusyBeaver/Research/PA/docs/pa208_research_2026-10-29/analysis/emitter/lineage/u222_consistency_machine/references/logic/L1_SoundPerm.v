(** k225-formal/rocqperm/L1_SoundPerm.v (SHA256 24da86a2195bb2cf74bdea06a9b1252f4ce7ebf5319dbb1ccc363c9d41e58080) under namespace K215F. *)
(** * L1_SoundPerm: a halting step of the 215's enumerator yields [thm222 1].

    As L1_Sound222: the current formula, the cache and every entry of the stack stream are
    theorems (stream entries past the end read as 0 = truth). *)
From Coq Require Import Arith Lia Bool.
From K230L Require Import Codes230.
From K215F Require Import Codes222 EnumPerm Thm222.

Definition popn (k w : nat) : nat := Nat.iter k (fun w => snd (unP w)) w.
Definition goodstack (w : nat) : Prop := forall k, thm222 (fst (unP (popn k w))).

Lemma popn_S k w : popn (S k) w = popn k (snd (unP w)).
Proof.
  unfold popn. revert w. induction k as [|k IH]; intro w; [reflexivity|].
  change (snd (unP (Nat.iter (S k) (fun w => snd (unP w)) w)) =
          snd (unP (Nat.iter k (fun w => snd (unP w)) (snd (unP w))))).
  now rewrite IH.
Qed.

Lemma good_push x w : thm222 x -> goodstack w -> goodstack (P x w).
Proof.
  intros Hx Hw [|k].
  - cbn. now rewrite unP_P.
  - rewrite popn_S, unP_P. apply Hw.
Qed.

Lemma good_pop w : goodstack w -> thm222 (fst (unP w)) /\ goodstack (snd (unP w)).
Proof. intro H. split; [exact (H 0)|]. intro k. specialize (H (S k)). now rewrite popn_S in H. Qed.

Lemma good_0 : goodstack 0.
Proof.
  assert (E : forall k, popn k 0 = 0) by (induction k; [reflexivity|]; rewrite popn_S; exact IHk).
  intro k. rewrite E. exact W_true.
Qed.

Definition Inv (s : state) : Prop := thm222 (tw s) /\ thm222 (h s) /\ goodstack (ws s).

Lemma gate_thm a b c : thm222 (gate a b c).
Proof.
  unfold gate. destruct (Nat.eqb c a) eqn:E1; [exact W_true|].
  destruct (Nat.eqb c b) eqn:E2; [exact W_true|].
  apply Nat.eqb_neq in E1, E2. now apply W_bundle.
Qed.

Lemma Inv_step s s' : Inv s -> enum_step s = Some s' -> Inv s'.
Proof.
  intros [Ht [Hh Hw]]. unfold enum_step.
  destruct (if Nat.eqb (pl s) 0 then _ else _) as [pl1 np1].
  destruct (unP pl1) as [ac pl2].
  destruct ac as [|[|[|c]]].
  - destruct (Nat.eqb (h s) 1); [discriminate|].
    destruct (good_pop _ Hw) as [H1 H2]. destruct (unP (ws s)) as [h1 w1] eqn:E.
    intro H; injection H as <-. repeat split; cbn [tw h ws]; [exact Ht | exact H1 | exact H2].
  - intro H; injection H as <-. repeat split; cbn [tw h ws]; [exact Hh | exact Hh | now apply good_push].
  - destruct (unP pl2) as [x pl3].
    destruct (Nat.eqb (wim (tw s) (d s + x)) (h s)) eqn:E; intro H; injection H as <-.
    + apply Nat.eqb_eq in E. repeat split; cbn [tw h ws].
      * apply (W_mp (tw s)); [exact Ht | now rewrite E].
      * exact W_true.
      * apply good_push; [exact W_true | exact Hw].
    + repeat split; cbn [tw h ws]; [exact W_true | exact W_true | exact Hw].
  - destruct (unP pl2) as [y pl3]. destruct (unP pl3) as [x pl4].
    intro H; injection H as <-. repeat split; cbn [tw h ws].
    + apply gate_thm.
    + exact W_true.
    + unfold ax_stack.
      repeat apply good_push; try assumption; constructor; assumption.
Qed.

Lemma Inv_run n s s' : Inv s -> run n s = Some s' -> Inv s'.
Proof.
  revert s. induction n as [|n IH]; intros s Hs H; cbn in H.
  - now injection H as <-.
  - destruct (enum_step s) as [s1|] eqn:E; [|discriminate].
    exact (IH s1 (Inv_step s s1 Hs E) H).
Qed.

Lemma halt_step s : Inv s -> enum_step s = None -> thm222 1.
Proof.
  intros [Ht [Hh Hw]]. unfold enum_step.
  destruct (if Nat.eqb (pl s) 0 then _ else _) as [pl1 np1].
  destruct (unP pl1) as [ac pl2].
  destruct ac as [|[|[|c]]]; try discriminate.
  - destruct (Nat.eqb (h s) 1) eqn:E.
    + intros _. apply Nat.eqb_eq in E. now rewrite <- E.
    + destruct (unP (ws s)); discriminate.
  - destruct (unP pl2). discriminate.
  - destruct (unP pl2) as [y pl3]. destruct (unP pl3). discriminate.
Qed.
