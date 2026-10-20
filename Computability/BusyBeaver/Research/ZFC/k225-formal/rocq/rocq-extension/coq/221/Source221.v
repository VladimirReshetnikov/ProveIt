(** Kernel-checked equivalence of the 221's rotated source with dag222, for every
    natural-valued register file. *)
From Coq Require Import List.
From K230 Require Import RM Prog230.
From K230P Require Import Bisim230.
From K221F Require Import Prog221 OffsetBisim230 Cert221Offsets Dag222.
Import ListNotations.
Lemma certificate_forward : ocheck (ptree p221) (ptree dag222) Cert221 = true.
Proof. Time vm_compute. reflexivity. Qed.
Lemma certificate_backward : ocheck (ptree dag222) (ptree p221) (omirror Cert221) = true.
Proof. Time vm_compute. reflexivity. Qed.
Theorem p221_dag222 R : rm_halts p221 ([],R) <-> rm_halts dag222 ([],R).
Proof. exact (ocheck_iff p221 dag222 Cert221 certificate_forward certificate_backward R). Qed.
Print Assumptions p221_dag222.
