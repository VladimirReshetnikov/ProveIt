(** Kernel-checked source equivalence for every natural-valued register file. *)
From Coq Require Import List.
From K230 Require Import RM Prog230.
From K230P Require Import Bisim230.
From K227F Require Import Prog227 OffsetBisim230 Cert227Offsets.
Import ListNotations.

Lemma certificate_forward : ocheck (ptree p227) (ptree p230) cert227_offsets = true.
Proof. Time vm_compute. reflexivity. Qed.
Lemma certificate_backward : ocheck (ptree p230) (ptree p227) (omirror cert227_offsets) = true.
Proof. Time vm_compute. reflexivity. Qed.
Theorem p227_p230 R : rm_halts p227 ([],R) <-> rm_halts p230 ([],R).
Proof. exact (ocheck_iff p227 p230 cert227_offsets certificate_forward certificate_backward R). Qed.
Print Assumptions p227_p230.
