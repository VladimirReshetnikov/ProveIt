(** * Main: the 254-state machine zfc_254.tm halts from the blank tape iff the register-machine
    program [p254] (Prog254.v, the decoder tree of paths.json under the path semantics of RM.v)
    halts from [R0] (nextproof = 2, all other registers 0). *)

From Coq Require Import Lists.List.
From BusyCoq Require Import TM.
From M254 Require Import RM RMEquiv Prog254 TM254 Zip Boot Sim.
Import ListNotations.

Theorem tm254_rm : halts tm c0 <-> rm_halts p254 ([], R0).
Proof.
  split.
  - intros H.
    assert (Hb : halts tm (zc (st 96) [true] boot_right)) by exact (halts_evstep' tm _ _ H boot).
    destruct (progress_halts tm (fun T => exists N, Inv N T) (fun _ => rm_halts p254 ([], R0))
                (zc (st 96) [true] boot_right)) as (T & _ & HZ).
    + intros T [N HI]. destruct (inv_next N T HI) as [(c & Hr & Ha) | (c' & Hr')].
      * left. exists N, c. split; assumption.
      * right. destruct (inv_step N T c' HI Hr') as (T' & HI' & HT').
        exists T'. split; [exists (S N); exact HI' | exact HT'].
    + exists 0. exact inv_boot.
    + exact Hb.
    + exact HZ.
  - intros (N & c & Hr & Ha).
    destruct (reach N c Hr) as (T & HT & HI).
    exact (halts_evstep tm _ _ (inv_halt N T c HI Hr Ha) HT).
Qed.

Corollary tm254_iter : halts tm c0 <-> iter_halts p254 R0.
Proof. rewrite tm254_rm. apply rm_halts_iff_iter, p254_wf. Qed.

Print Assumptions tm254_rm.
Print Assumptions tm254_iter.
