(** Type probe of the unchanged maintained public source contract. *)
From Coq Require Import List.
From K230 Require Import RM.
From K215F Require Import Prog215 DagPerm Source215.
Import ListNotations.

Theorem current_source_interface R :
  rm_halts p215 ([],R) <-> rm_halts dagPerm ([],R).
Proof. exact (K215F.Source215.p215_dagPerm R). Qed.

Print Assumptions current_source_interface.
