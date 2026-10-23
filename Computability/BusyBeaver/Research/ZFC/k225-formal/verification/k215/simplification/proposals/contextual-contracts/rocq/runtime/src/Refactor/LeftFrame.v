(** Guarded framing for the unchanged K215 Runtime230Core symbolic step.
    No prefix length, register valuation, or gap bound is imposed. *)
From Coq Require Import Lists.List Bool.Bool Arith.Arith.
From BusyCoq Require Import TM.
From K215F Require Import TM230 Zip Boot230 Runtime230Core.
Import ListNotations.

Definition add_left (F : list seg) (s : sconf) : sconf :=
  let '(q,onl,l,r) := s in (q,onl,l ++ F,r).
Definition safe_left (s : sconf) : bool :=
  match s with (_,true,[],_) => false | _ => true end.
Definition map_step (F : list seg) (x : option (sconf * bool)) :=
  option_map (fun '(s,m) => (add_left F s,m)) x.

Lemma peel_left_frame F l r q b a c :
  peel_left q b a c (l ++ F) r = map_step F (peel_left q b a c l r).
Proof. destruct c,a; reflexivity. Qed.

Lemma peel_right_frame F l r q b a c :
  peel_right q b a c (l ++ F) r = map_step F (peel_right q b a c l r).
Proof. destruct c,a; reflexivity. Qed.

(** The guard excludes the sole branch that manufactures a blank at an empty
    left side. Every other branch commutes with an arbitrary appended frame. *)
Theorem sstep_natural br F s : safe_left s = true ->
  sstep br (add_left F s) = map_step F (sstep br s).
Proof.
  destruct s as [[[q onl] l] r]. destruct onl; intro Hsafe.
  - destruct l as [|[x|b a c|x] l]; [discriminate|reflexivity| |reflexivity].
    cbn [add_left app sstep].
    destruct (tmn q b) as [[[w [|]] q2]|].
    + destruct (Nat.eqb q2 q); [reflexivity|apply peel_left_frame].
    + apply peel_left_frame.
    + apply peel_left_frame.
  - destruct r as [|[x|b a c|x] r]; [reflexivity| | |].
    + cbn [add_left sstep]. destruct (tmn q x) as [[[w [|]] q2]|]; reflexivity.
    + cbn [add_left sstep]. destruct (tmn q b) as [[[w [|]] q2]|].
      * apply peel_right_frame.
      * destruct (Nat.eqb q2 q); [reflexivity|apply peel_right_frame].
      * apply peel_right_frame.
    + destruct r as [|y r]; [|reflexivity]. cbn [add_left sstep].
      destruct (oracle q br x) as [[[q2 x2] extra]|].
      * destruct extra; reflexivity.
      * destruct (tmn q false) as [[[[|] [|]] q2]|]; reflexivity.
Qed.

Corollary sstep_add_left br s t m F :
  safe_left s = true -> sstep br s = Some (t,m) ->
  sstep br (add_left F s) = Some (add_left F t,m).
Proof. intros Hs H; rewrite sstep_natural by exact Hs. rewrite H; reflexivity. Qed.

Lemma safe_add_left F s : safe_left s = true -> safe_left (add_left F s) = true.
Proof. destruct s as [[[q []] l] r]; destruct l; easy. Qed.

Example unsafe_frame_counterexample :
  sstep None (add_left [SB true] (0,true,[],[])) <>
  map_step [SB true] (sstep None (0,true,[],[])).
Proof. discriminate. Qed.

Fixpoint run_local (br : branch) (steps : nat) (s : sconf) : option sconf :=
  match steps with
  | 0 => Some s
  | S k => if safe_left s then
      match sstep br s with None => None | Some (t,_) => run_local br k t end
      else None
  end.

Theorem run_local_frame br steps s t F : run_local br steps s = Some t ->
  run_local br steps (add_left F s) = Some (add_left F t).
Proof.
  revert s t. induction steps as [|steps IH]; intros s t H.
  - injection H as <-. reflexivity.
  - cbn in H. destruct (safe_left s) eqn:Hs; [|discriminate].
    destruct (sstep br s) as [[s' m]|] eqn:He; [|discriminate].
    cbn. rewrite (safe_add_left F s Hs), (sstep_add_left br s s' m F Hs He).
    now apply IH.
Qed.

Section Sound.
Hypothesis box_mark : forall q r l vs, skip_target q = Some r -> 10 <= length vs ->
  zc (st q) l (sepsR vs) -->* zl (st (mark_exit r)) l (sepsM r vs).
Hypothesis box_inc : forall r l vs, r < 9 -> 10 <= length vs ->
  zc (st 64) l (sepsM r vs) -->* zl (st 40) l (sepsR (incr r vs ++ [1])).
Hypothesis box_dec0 : forall r l vs, r < 9 -> 10 <= length vs -> nth r vs 0 = 0 ->
  zc (st 0) l (sepsM r vs) -->* zl (st 97) l (sepsR vs).
Hypothesis box_decp : forall r l vs, r < 9 -> 10 <= length vs -> nth r vs 0 <> 0 ->
  zc (st 0) l (sepsM r vs) -->* zl (st 40) (true :: l) (sepsR (decr r vs)).

Theorem run_local_sound br steps s t F n vs :
  run_local br steps s = Some t -> valid br vs ->
  conc n vs (add_left F s) -->* conc n vs (add_left F t).
Proof.
  revert s t. induction steps as [|steps IH]; intros s t H V.
  - injection H as <-. apply evstep_refl.
  - cbn in H. destruct (safe_left s) eqn:Hs; [|discriminate].
    destruct (sstep br s) as [[s' m]|] eqn:He; [|discriminate].
    pose proof (sstep_sound box_mark box_inc box_dec0 box_decp _ _ _ _ n vs
      (sstep_add_left br s s' m F Hs He) V) as [Hreach _].
    eapply evstep_trans; [exact Hreach|now apply IH].
Qed.
End Sound.

Print Assumptions sstep_natural.
Print Assumptions unsafe_frame_counterexample.
Print Assumptions run_local_frame.
Print Assumptions run_local_sound.
