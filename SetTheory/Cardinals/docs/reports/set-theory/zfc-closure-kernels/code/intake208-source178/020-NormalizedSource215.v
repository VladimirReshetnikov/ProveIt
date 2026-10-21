(** Exact all-register source correspondence for K215 using 1,426 normalized
    entries, plain register equality, and one checked direction. *)
From Coq Require Import List.
From K230 Require Import RM.
From K230P Require Import Bisim230.
From K215F Require Import Prog215 DagPerm.
Require Import NormalizedBisim NormalizedCert215.
Import ListNotations.

Lemma normalized215_forward :
  ncheck (ptree p215) (ptree dagPerm) Normalized215 = true.
Proof. Time vm_compute. reflexivity. Qed.

Theorem p215_dagPerm_normalized R :
  rm_halts p215 ([],R) <-> rm_halts dagPerm ([],R).
Proof.
  exact (ncheck_one_sided_iff p215 dagPerm Normalized215 normalized215_forward R).
Qed.

Print Assumptions normalized215_forward.
Print Assumptions p215_dagPerm_normalized.
