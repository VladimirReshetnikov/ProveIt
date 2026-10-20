(** Kernel-checked source equivalence for every natural-valued register file. *)
From Coq Require Import List.
From K230 Require Import RM Prog230.
From K230P Require Import Bisim230.
From K225F Require Import Prog225 OffsetBisim230 Cert225Offsets.
Import ListNotations.
Lemma certificate_forward : ocheck (ptree p225) (ptree p230) cert225_offsets = true.
Proof. Time vm_compute. reflexivity. Qed.
Lemma certificate_backward : ocheck (ptree p230) (ptree p225) (omirror cert225_offsets) = true.
Proof. Time vm_compute. reflexivity. Qed.
Theorem p225_p230 R : rm_halts p225 ([],R) <-> rm_halts p230 ([],R).
Proof. exact (ocheck_iff p225 p230 cert225_offsets certificate_forward certificate_backward R). Qed.
Print Assumptions p225_p230.
