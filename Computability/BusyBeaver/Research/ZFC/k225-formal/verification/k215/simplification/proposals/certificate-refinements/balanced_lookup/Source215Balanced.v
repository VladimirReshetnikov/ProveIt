(** The exact source theorem, using one balanced, ordinary certificate. *)
From Coq Require Import List.
From K230 Require Import RM.
From K230P Require Import Bisim230.
From K215F Require Import Prog215 DagPerm.
Require Import BalancedBisim Cert215Tree.
Import ListNotations.

Lemma certificate_forward_balanced :
  checkTree (ptree p215) (ptree dagPerm) Tree215 = true.
Proof. Time vm_compute. reflexivity. Qed.

Theorem p215_dagPerm_balanced R :
  rm_halts p215 ([],R) <-> rm_halts dagPerm ([],R).
Proof.
  exact (checkTree_halts_iff p215 dagPerm Tree215 tree215_valid
    certificate_forward_balanced R).
Qed.

Print Assumptions certificate_forward_balanced.
Print Assumptions p215_dagPerm_balanced.
