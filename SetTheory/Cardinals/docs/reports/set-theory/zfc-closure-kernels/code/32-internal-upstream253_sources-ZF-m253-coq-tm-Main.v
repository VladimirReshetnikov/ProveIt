(** Exact blank-tape candidate253 to the unchanged accepted register program. *)
From Coq Require Import Lists.List Arith.Arith Lia.
From BusyCoq Require Import TM.
From M254 Require Import RM RMEquiv Prog254.
From M253 Require Import TM253 Zip SymExec Check253 Boot253 Prefix Sim.
Import ListNotations.

Definition boot_conf := zc (st 96) [true] boot_right.

Lemma inv_boot330 : Inv 330 boot_conf.
Proof.
  exists P330, R330, 37, ext158. split; [exact rm_prefix330|].
  split; [unfold Site.D0, P330; simpl; lia|]. reflexivity.
Qed.

Theorem tm253_rm : halts tm c0 <-> rm_halts p254 ([], R0).
Proof.
  split.
  - intros H.
    assert (Hb : halts tm boot_conf) by exact (halts_evstep' tm _ _ H boot).
    destruct (progress_halts tm (fun T => exists N, Inv N T)
                (fun _ => rm_halts p254 ([], R0)) boot_conf) as (T & _ & HZ).
    + intros T [N HI]. destruct (inv_next N T HI) as [(c & Hr & Ha) | (c' & Hr')].
      * left. exists N, c. split; assumption.
      * right. destruct (inv_step N T c' HI Hr') as (T' & HI' & HT').
        exists T'. split; [exists (S N); exact HI' | exact HT'].
    + exists 330. exact inv_boot330.
    + exact Hb.
    + exact HZ.
  - intros H.
    apply (proj1 (rm_halts_prefix p254 330 ([], R0) (P330, R330) rm_prefix330)) in H.
    destruct H as (k & c & Hr & Ha).
    assert (Hrun : rm_run p254 (330 + k) ([], R0) = Some c).
    { rewrite rm_run_add, rm_prefix330. exact Hr. }
    destruct (reach_from 330 boot_conf inv_boot330 k c Hrun) as (T & HT & HI).
    apply (halts_evstep tm _ _ (inv_halt (330 + k) T c HI Hrun Ha)).
    eapply evstep_trans; [exact boot | exact HT].
Qed.

Corollary tm253_iter : halts tm c0 <-> iter_halts p254 R0.
Proof. rewrite tm253_rm. apply rm_halts_iff_iter, p254_wf. Qed.

Print tm253_rm.
Print Assumptions inv_boot330.
Print Assumptions tm253_rm.
Print Assumptions tm253_iter.
