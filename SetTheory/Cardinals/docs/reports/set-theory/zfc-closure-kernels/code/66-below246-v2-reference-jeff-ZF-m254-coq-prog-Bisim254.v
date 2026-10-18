(** * Bisim254: p254 (the decoder tree the TM runs) and dag254 (the Wade compile of the source) halt
    on the same register files, by the certificate of Cert254.v checked with vm_compute. *)
From Coq Require Import Lists.List.
From M254 Require Import RM Prog254.
From M254P Require Import Bisim Dag254 Cert254.
Import ListNotations.

Lemma cert_fwd : check (ptree p254) (ptree dag254) cert254 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma cert_bwd : check (ptree dag254) (ptree p254) (mirror cert254) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem p254_dag R : rm_halts p254 ([], R) <-> rm_halts dag254 ([], R).
Proof. exact (check_iff p254 dag254 cert254 cert_fwd cert_bwd R). Qed.

Print Assumptions p254_dag.
