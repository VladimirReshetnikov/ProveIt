(** Kernel-checked equivalence of the 215's source with dagPerm, for every natural-valued
    register file. *)
From Coq Require Import List.
From K230 Require Import RM Prog230.
From K230P Require Import Bisim230.
From K215F Require Import Prog215 OffsetBisim230 Cert215Offsets DagPerm.
Import ListNotations.
Lemma certificate_forward : ocheck (ptree p215) (ptree dagPerm) Cert215 = true.
Proof. Time vm_compute. reflexivity. Qed.
Lemma certificate_backward : ocheck (ptree dagPerm) (ptree p215) (omirror Cert215) = true.
Proof. Time vm_compute. reflexivity. Qed.
Theorem p215_dagPerm R : rm_halts p215 ([],R) <-> rm_halts dagPerm ([],R).
Proof. exact (ocheck_iff p215 dagPerm Cert215 certificate_forward certificate_backward R). Qed.
Print Assumptions p215_dagPerm.

