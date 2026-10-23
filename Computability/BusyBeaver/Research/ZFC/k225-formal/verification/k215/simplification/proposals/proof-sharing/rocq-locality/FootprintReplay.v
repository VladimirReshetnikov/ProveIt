(** Generic exact replay under a table footprint.
    New proof core, 2026-10-22. No machine or arithmetic assumptions.
    A successful replay preserves fuel, target, and the progress Boolean.
    This is the Rocq counterpart of the existing proof-fusion Lean locality idea. *)
From Coq Require Import List Bool.
Import ListNotations.

Section Replay.
Variables Key State Action : Type.
Variable step : (Key -> Action) -> State -> option (State * bool).
Variable reads : State -> list Key.

Fixpoint fp_exec (table : Key -> Action) (fuel : nat)
    (target : State -> bool) (s : State) (moved : bool) : option State :=
  match fuel with
  | 0 => None
  | S f =>
      if (if moved then target s else false) then Some s
      else match step table s with
           | None => None
           | Some (s', m) => fp_exec table f target s' (orb moved m)
           end
  end.

Fixpoint footprint (table : Key -> Action) (fuel : nat)
    (target : State -> bool) (s : State) (moved : bool) : list Key :=
  match fuel with
  | 0 => []
  | S f =>
      if (if moved then target s else false) then []
      else reads s ++
           match step table s with
           | None => []
           | Some (s', m) => footprint table f target s' (orb moved m)
           end
  end.

Definition agree (a b : Key -> Action) (keys : list Key) : Prop :=
  forall k, In k keys -> a k = b k.

Hypothesis step_local : forall a b s,
  agree a b (reads s) -> step a s = step b s.

Lemma agree_app_left a b xs ys : agree a b (xs ++ ys) -> agree a b xs.
Proof.
  intros H k Hk. apply H, in_or_app. now left.
Qed.

Lemma agree_app_right a b xs ys : agree a b (xs ++ ys) -> agree a b ys.
Proof.
  intros H k Hk. apply H, in_or_app. now right.
Qed.

(** A source trace supplies all row comparisons needed to replay it exactly.
    Both failure and success are preserved. No reverse simulation is needed. *)
Theorem footprint_replay fuel : forall a b target s moved,
  agree a b (footprint a fuel target s moved) ->
  fp_exec a fuel target s moved = fp_exec b fuel target s moved /\
  footprint a fuel target s moved = footprint b fuel target s moved.
Proof.
  induction fuel as [|fuel IH]; intros a b target s moved H.
  - split; reflexivity.
  - cbn [footprint] in H.
    cbn [fp_exec footprint].
    destruct (if moved then target s else false) eqn:T.
    + split; reflexivity.
    + assert (Hs : step a s = step b s).
      { apply step_local. eapply agree_app_left. exact H. }
      rewrite <- Hs.
      destruct (step a s) as [[s' m]|] eqn:E.
      * specialize (IH a b target s' (orb moved m)).
        assert (Ht : agree a b (footprint a fuel target s' (orb moved m))).
        { eapply agree_app_right. exact H. }
        destruct (IH Ht) as [He Hf]. split; [exact He|]. now rewrite Hf.
      * split; reflexivity.
Qed.

Corollary footprint_result fuel a b target s moved :
  agree a b (footprint a fuel target s moved) ->
  fp_exec a fuel target s moved = fp_exec b fuel target s moved.
Proof. intro H. exact (proj1 (footprint_replay fuel a b target s moved H)). Qed.

Corollary success_transport fuel a b target s moved out :
  agree a b (footprint a fuel target s moved) ->
  fp_exec a fuel target s moved = Some out ->
  fp_exec b fuel target s moved = Some out.
Proof. intros H E. rewrite <- (footprint_result fuel a b target s moved H). exact E. Qed.
End Replay.

Print Assumptions footprint_replay.
Print Assumptions success_transport.
