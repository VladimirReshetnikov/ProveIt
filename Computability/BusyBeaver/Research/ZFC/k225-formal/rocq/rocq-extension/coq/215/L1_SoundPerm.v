(** k225-formal/rocqperm/L1_SoundPerm.v (SHA256 ad1cf5cc3ab147d17ed61e4ffe6637fd0362955b5372cab074295492b3c7833b) under namespace K215F. *)
(** * L1_SoundPerm: if the 215's enumerator halts, then [thm222 1].

    As L1_Sound222: the current formula, the cache and every entry of the stack stream are
    theorems (stream entries past the end read as 0 = truth). Every command preserves this,
    and only NIP halts, on the cached code 1. *)
From Coq Require Import Arith Lia Bool.
From K230L Require Import Codes230.
From K215F Require Import Codes222 EnumPerm Thm222.

(** The proof uses constructor lemmas, never numeric expansion of formula codes. *)
Local Opaque P wim wal wex weq wel.

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

(** the working registers hold theorems *)
Definition InvT (q : tup) : Prop :=
  let '(t, w, _, hh) := q in thm222 t /\ thm222 hh /\ goodstack w.

Definition Inv (s : state) : Prop := InvT (tupof s).

Lemma gate_thm a b c : thm222 (gate a b c).
Proof.
  unfold gate. destruct (Nat.eqb c a) eqn:E1; [exact W_true|].
  destruct (Nat.eqb c b) eqn:E2; [exact W_true|].
  apply Nat.eqb_neq in E1, E2. now apply W_bundle.
Qed.

Lemma xstep_inv k q q' : InvT q -> xstep k q = Some q' -> InvT q'.
Proof.
  destruct q as [[[t w] dd] hh]. intros [Ht [Hh Hw]].
  destruct k as [| |x|c x y]; cbn [xstep].
  - destruct (Nat.eqb hh 1); [discriminate|]. destruct (good_pop _ Hw) as [H1 H2].
    intro E; injection E as <-. cbn [InvT]. now repeat split.
  - intro E; injection E as <-. cbn [InvT]. repeat split; [exact Hh | exact Hh | now apply good_push].
  - destruct (Nat.eqb (wim t (dd + x)) hh) eqn:E; intro H; injection H as <-; cbn [InvT].
    + apply Nat.eqb_eq in E. repeat split.
      * apply (W_mp t); [exact Ht | now rewrite E].
      * exact W_true.
      * apply good_push; [exact W_true | exact Hw].
    + repeat split; [exact W_true | exact W_true | exact Hw].
  - intro E; injection E as <-. cbn [InvT]. repeat split.
    + apply gate_thm.
    + exact W_true.
    + unfold ax_stack. repeat apply good_push; try assumption; constructor; assumption.
Qed.

Lemma xstep_none k q : InvT q -> xstep k q = None -> thm222 1.
Proof.
  destruct q as [[[t w] dd] hh]. intros [_ [Hh _]].
  destruct k as [| |x|c x y]; cbn [xstep]; try discriminate.
  destruct (Nat.eqb hh 1) eqn:E; [|discriminate].
  intros _. apply Nat.eqb_eq in E. now rewrite <- E.
Qed.

Lemma Inv_step s s' : Inv s -> enum_step s = Some s' -> Inv s'.
Proof.
  unfold enum_step, Inv. intros Hs.
  destruct (if Nat.eqb (pl s) 0 then _ else _) as [pl1 np1].
  destruct (decode pl1) as [k r].
  destruct (xstep k (tupof s)) as [[[[t w] dd] hh]|] eqn:X; [|discriminate].
  intro E; injection E as <-. exact (xstep_inv k _ _ Hs X).
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
  unfold enum_step, Inv. intros Hs.
  destruct (if Nat.eqb (pl s) 0 then _ else _) as [pl1 np1].
  destruct (decode pl1) as [k r].
  destruct (xstep k (tupof s)) as [[[[t w] dd] hh]|] eqn:X; [discriminate|].
  intros _. exact (xstep_none k _ Hs X).
Qed.
