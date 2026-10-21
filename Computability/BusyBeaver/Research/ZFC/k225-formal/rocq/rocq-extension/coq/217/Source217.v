(** Kernel-checked equivalence of the 217's source with dagDom, for every natural-valued
    register file. *)
From Coq Require Import List.
From K230 Require Import RM Prog230.
From K230P Require Import Bisim230.
From K217F Require Import Prog217 OffsetBisim230 Cert217Offsets DagDom.
Import ListNotations.
Lemma certificate_forward : ocheck (ptree p217) (ptree dagDom) Cert217 = true.
Proof. Time vm_compute. reflexivity. Qed.
Lemma certificate_backward : ocheck (ptree dagDom) (ptree p217) (omirror Cert217) = true.
Proof. Time vm_compute. reflexivity. Qed.
Theorem p217_dagDom R : rm_halts p217 ([],R) <-> rm_halts dagDom ([],R).
Proof. exact (ocheck_iff p217 dagDom Cert217 certificate_forward certificate_backward R). Qed.
Print Assumptions p217_dagDom.
