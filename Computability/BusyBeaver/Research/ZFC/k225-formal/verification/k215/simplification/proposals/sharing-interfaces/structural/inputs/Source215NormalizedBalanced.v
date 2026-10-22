(** Exact all-register source equivalence: normalized checkpoints and tree lookup. *)
From Coq Require Import List.
From K230 Require Import RM.
From K230P Require Import Bisim230.
From K215F Require Import Prog215 DagPerm.
Require Import NormalizedBalanced NormalizedTree215.
Import ListNotations.

Theorem normalized_balanced215_forward :
  ncheckTree (ptree p215) (ptree dagPerm) NormalizedTree215 = true.
Proof. Time vm_compute. reflexivity. Qed.

Theorem p215_dagPerm_normalized_balanced R :
  rm_halts p215 ([],R) <-> rm_halts dagPerm ([],R).
Proof.
  exact (ncheckTree_halts_iff p215 dagPerm NormalizedTree215
    normalized_tree215_valid normalized_balanced215_forward R).
Qed.

Print Assumptions normalized_balanced215_forward.
Print Assumptions p215_dagPerm_normalized_balanced.
