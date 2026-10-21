(** Exact source theorem: normalized pointers, one checked direction,
    balanced lookup, no register offsets, no new semantic hypothesis. *)
From Coq Require Import List.
From K230 Require Import RM.
From K230P Require Import Bisim230.
From K215F Require Import Prog215 DagPerm.
Require Import BalancedNormalized NormalizedTree215.
Import ListNotations.

Lemma composed215_forward :
  nbcheck (ptree p215) (ptree dagPerm) NTree215 = true.
Proof. Time vm_compute. reflexivity. Qed.

Theorem p215_dagPerm_composed R :
  rm_halts p215 ([],R) <-> rm_halts dagPerm ([],R).
Proof.
  exact (nbcheck_halts_iff p215 dagPerm NTree215 ntree215_valid
    composed215_forward R).
Qed.

Print Assumptions composed215_forward.
Print Assumptions p215_dagPerm_composed.
