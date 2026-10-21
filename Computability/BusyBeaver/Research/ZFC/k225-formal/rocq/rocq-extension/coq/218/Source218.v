(** Kernel-checked equivalence of the 218's source with dag219, for every natural-valued
    register file. *)
From Coq Require Import List.
From K230 Require Import RM Prog230.
From K230P Require Import Bisim230.
From K218F Require Import Prog218 OffsetBisim230 Cert218Offsets Dag219.
Import ListNotations.
Lemma certificate_forward : ocheck (ptree p218) (ptree dag219) Cert218 = true.
Proof. Time vm_compute. reflexivity. Qed.
Lemma certificate_backward : ocheck (ptree dag219) (ptree p218) (omirror Cert218) = true.
Proof. Time vm_compute. reflexivity. Qed.
Theorem p218_dag219 R : rm_halts p218 ([],R) <-> rm_halts dag219 ([],R).
Proof. exact (ocheck_iff p218 dag219 Cert218 certificate_forward certificate_backward R). Qed.
Print Assumptions p218_dag219.
