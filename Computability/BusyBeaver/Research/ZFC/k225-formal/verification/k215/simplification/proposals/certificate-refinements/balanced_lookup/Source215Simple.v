(** K215 source correspondence with compact data, the ordinary bisimulation
    checker, and only one direction evaluated.  The signed-offset layer is absent. *)
From Coq Require Import List.
From K230 Require Import RM.
From K230P Require Import Bisim230.
From K215F Require Import Prog215 DagPerm.
Require Import Cert215Compact BisimMirror.
Import ListNotations.

Lemma certificate_forward_plain :
  check (ptree p215) (ptree dagPerm) Plain215 = true.
Proof. Time vm_compute. reflexivity. Qed.

Theorem p215_dagPerm_simple R :
  rm_halts p215 ([],R) <-> rm_halts dagPerm ([],R).
Proof.
  exact (check_one_sided_iff p215 dagPerm Plain215 certificate_forward_plain R).
Qed.

Print Assumptions certificate_forward_plain.
Print Assumptions p215_dagPerm_simple.
