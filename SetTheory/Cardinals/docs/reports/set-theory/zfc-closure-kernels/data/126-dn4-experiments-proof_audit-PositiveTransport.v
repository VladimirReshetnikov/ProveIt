(* A self-contained positive-block transport theorem.
   No claim that a particular transition-table certificate has been instantiated.
   The theorem isolates the finitary argument used by the local fold checker. *)
From Stdlib Require Import Arith.PeanoNat Arith.Wf_nat Lia.

Set Implicit Arguments.

Section Machine.
  Context {C : Type}.
  Variable step : C -> option C.

  Fixpoint halts_within (fuel : nat) (c : C) : Prop :=
    match fuel with
    | O => step c = None
    | S fuel' =>
      match step c with
      | None => True
      | Some c' => halts_within fuel' c'
      end
    end.

  Definition halts (c : C) : Prop := exists fuel, halts_within fuel c.

  Inductive steps : nat -> C -> C -> Prop :=
  | steps_zero c : steps 0 c c
  | steps_next n c c' d :
      step c = Some c' -> steps n c' d -> steps (S n) c d.

  Lemma steps_prepend n c d :
    steps n c d -> forall k, halts_within k d -> halts_within (n + k) c.
  Proof.
    intros H; induction H; intros k Hk; simpl in *.
    - exact Hk.
    - rewrite H. apply IHsteps. exact Hk.
  Qed.

  Lemma steps_consume n c d :
    steps n c d -> forall k, halts_within k c ->
      exists rest, k = n + rest /\ halts_within rest d.
  Proof.
    intros H; induction H; intros k Hk.
    - exists k. split; [reflexivity | exact Hk].
    - destruct k as [|k].
      + simpl in Hk. rewrite H in Hk. discriminate.
      + simpl in Hk. rewrite H in Hk.
        destruct (IHsteps k Hk) as [rest [Eq Hr]].
        exists rest. split; [lia | exact Hr].
  Qed.
End Machine.

Section Transport.
  Context {Old New : Type}.
  Variable oldstep : Old -> option Old.
  Variable newstep : New -> option New.
  Variable related : Old -> New -> Prop.

  (* Halting endpoints need no equality of terminal head or tape. *)
  Hypothesis terminal : forall c d,
    related c d -> oldstep c = None -> newstep d = None.

  (* Every old transition is replaced by a finite, strictly positive block.
     The [steps] judgment implies that no block interior is terminal. *)
  Hypothesis progress : forall c d c',
    related c d -> oldstep c = Some c' ->
    exists length d', 0 < length /\
      steps newstep length d d' /\ related c' d'.

  Theorem positive_block_halts_forward c d :
    related c d -> halts oldstep c -> halts newstep d.
  Proof.
    intros Hr [fuel Hfuel]. revert c d Hr Hfuel.
    induction fuel as [|fuel IH]; intros c d Hr Hfuel.
    - exists 0. simpl in *. exact (terminal Hr Hfuel).
    - simpl in Hfuel. destruct (oldstep c) as [c'|] eqn:Hs.
      + destruct (progress Hr Hs) as [length [d' [Hpos [Hsteps Hr']]]].
        destruct (IH _ _ Hr' Hfuel) as [k Hk].
        exists (length + k). eapply steps_prepend; eauto.
      + exists 0. simpl. exact (terminal Hr Hs).
  Qed.

  Theorem positive_block_halts_reverse c d :
    related c d -> halts newstep d -> halts oldstep c.
  Proof.
    intros Hr [fuel Hfuel]. revert c d Hr Hfuel.
    induction fuel as [fuel IH] using lt_wf_ind.
    intros c d Hr Hfuel. destruct (oldstep c) as [c'|] eqn:Hs.
    - destruct (progress Hr Hs) as [length [d' [Hpos [Hsteps Hr']]]].
      destruct (steps_consume Hsteps fuel Hfuel) as [rest [Eq Hrest]].
      assert (Hlt : rest < fuel) by lia.
      destruct (IH rest Hlt _ _ Hr' Hrest) as [k Hk].
      exists (S k). simpl. rewrite Hs. exact Hk.
    - exists 0. exact Hs.
  Qed.

  Theorem positive_block_halting_equivalence c d :
    related c d -> (halts oldstep c <-> halts newstep d).
  Proof.
    intros Hr. split.
    - exact (positive_block_halts_forward Hr).
    - exact (positive_block_halts_reverse Hr).
  Qed.

  Corollary positive_block_nonhalting_equivalence c d :
    related c d -> (~ halts oldstep c <-> ~ halts newstep d).
  Proof.
    intros Hr. split; intros Hnh Hh; apply Hnh.
    - apply (positive_block_halts_reverse Hr), Hh.
    - apply (positive_block_halts_forward Hr), Hh.
  Qed.
End Transport.

Print Assumptions positive_block_halting_equivalence.
Print Assumptions positive_block_nonhalting_equivalence.
