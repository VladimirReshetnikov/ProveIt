(** UNCOMPILED PROPOSAL for cbf94cb552a3b49509e0eee80e7455d4eb5974c6.
    Insert the definitions before Interpreter230Sites.v's check_site,
    and the lemmas inside that existing section, after run_to_sound.
    This file is an integration fragment, not a standalone module.
    The four existing box hypotheses are reused unchanged. *)

Definition dec_cut (r : nat) (s : sconf) : bool :=
  match s with
  | (0, false, _, [SBox (BMark r')]) => Nat.eqb r r'
  | _ => false
  end.

Definition run_from (br : branch) (s e : sconf) : bool :=
  match exec FUEL br (fun t => matches t e) s true with
  | Some _ => true | None => false
  end.

Definition fork_to (r : nat) (s e0 ep : sconf) : bool :=
  match exec FUEL None (dec_cut r) s false with
  | None => false
  | Some c => run_from (Some (r,true)) c e0 &&
              run_from (Some (r,false)) c ep
  end.

(** Inside the existing Sound section. This is the complete new
    semantic argument; no extra simulation induction is needed. *)
Lemma exec_cut_sound f g cut br s c t tgt n vs :
  exec f None cut s false = Some c ->
  exec g br tgt c true = Some t -> valid br vs ->
  tgt t = true /\ conc n vs s -->+ conc n vs t.
Proof.
  intros Hp Ht V.
  destruct (exec_sound box_mark box_inc box_dec0 box_decp
    _ _ _ _ _ _ n vs Hp (conj (proj1 V) I)) as (_ & _ & P).
  destruct (exec_sound box_mark box_inc box_dec0 box_decp
    _ _ _ _ _ _ n vs Ht V) as (Hmatch & R & _).
  split; [exact Hmatch|].
  eapply progress_evstep_trans; [apply P; reflexivity|exact R].
Qed.

Lemma fork_to_sound r s e0 ep z : fork_to r s e0 ep = true ->
  forall n vs, valid (Some (r,z)) vs ->
  conc n vs s -->+ conc n vs (if z then e0 else ep).
Proof.
  unfold fork_to.
  destruct (exec FUEL None (dec_cut r) s false) as [c|] eqn:Hp;
    [|discriminate].
  intros H n vs V. apply andb_prop in H as [H0 H1].
  assert (H : run_from (Some (r,z)) c (if z then e0 else ep) = true)
    by (destruct z; assumption).
  unfold run_from in H.
  destruct (exec FUEL (Some (r,z))
      (fun t => matches t (if z then e0 else ep)) c true) as [t|] eqn:Ht;
    [|discriminate].
  destruct (exec_cut_sound _ _ _ _ _ _ _ _ n vs Hp Ht V) as [Hm Hr].
  rewrite <- (matches_conc _ _ n vs Hm). exact Hr.
Qed.

(** Integration: replace only check_site's ODec branch with

    fork_to r (start Q)
      (tgt_conf (brk 1 Q) (allones (strip_path false 1 Q)) (BPlain FNone))
      (tgt_conf (inc_path Q) (allones Q) (BPlain (FDec r))).

    site_dec retains its statement. In each branch, apply fork_to_sound
    to H with z=true/false and the existing valid proof. Other operations,
    whole-leaf coverage, startup, and endpoint statements are untouched.
    Regenerate all_leaves_check and rebuild all dependent endpoints. *)
