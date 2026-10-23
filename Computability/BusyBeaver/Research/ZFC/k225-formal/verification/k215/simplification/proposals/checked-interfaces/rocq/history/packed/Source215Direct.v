(** Exact current K215 source equivalence through checked lookup coverage.
    The only concrete semantic premise is the passing normalized check. *)
From Coq Require Import List.
From K230 Require Import RM.
From K230P Require Import Bisim230.
From K215F Require Import Prog215 DagPerm PathCodec NormalizedCert215.
Require Import CheckedTree.
Import ListNotations.

Definition tree215 : CTree packed_entry := Eval vm_compute in
  buildTree 11 normalized_packed.

Lemma direct215_check : check expand_msb (ptree p215) (ptree dagPerm) tree215 = true.
Proof. Time vm_compute. reflexivity. Qed.

Theorem p215_dagPerm_direct R :
  rm_halts p215 ([],R) <-> rm_halts dagPerm ([],R).
Proof. exact (check_halts_iff p215 dagPerm expand_msb tree215 direct215_check R). Qed.

Print Assumptions direct215_check.
Print Assumptions p215_dagPerm_direct.
