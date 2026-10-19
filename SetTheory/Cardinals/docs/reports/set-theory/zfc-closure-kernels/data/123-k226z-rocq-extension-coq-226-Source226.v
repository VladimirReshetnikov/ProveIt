(** Kernel-checked source equivalence for every natural-valued register file. *)
From Coq Require Import List.
From K230 Require Import RM Prog230.
From K230P Require Import Bisim230.
From K226F Require Import Prog226 OffsetBisim230 Cert226Offsets.
Import ListNotations.
Lemma certificate_forward : ocheck (ptree p226) (ptree p230) cert226_offsets = true.
Proof. Time vm_compute. reflexivity. Qed.
Lemma certificate_backward : ocheck (ptree p230) (ptree p226) (omirror cert226_offsets) = true.
Proof. Time vm_compute. reflexivity. Qed.
Theorem p226_p230 R : rm_halts p226 ([],R) <-> rm_halts p230 ([],R).
Proof. exact (ocheck_iff p226 p230 cert226_offsets certificate_forward certificate_backward R). Qed.
Print Assumptions p226_p230.
