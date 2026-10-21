(** Research prototype, not compiled. Existing endpoint APIs need not change. *)
From Coq Require Import List.
From K230 Require Import RM.
From K230P Require Import Bisim230.
From K215F Require Import Prog215 DagPerm.
Require Import PackedCert215.
Import ListNotations.

Lemma certificate_forward_plain : check (ptree p215) (ptree dagPerm) Cert215Plain = true.
Proof. vm_compute. reflexivity. Qed.
Lemma certificate_backward_plain : check (ptree dagPerm) (ptree p215) (mirror Cert215Plain) = true.
Proof. vm_compute. reflexivity. Qed.
Theorem p215_dagPerm_plain R : rm_halts p215 ([],R) <-> rm_halts dagPerm ([],R).
Proof. exact (check_iff p215 dagPerm Cert215Plain certificate_forward_plain certificate_backward_plain R). Qed.
Print Assumptions p215_dagPerm_plain.
