(** This validates the public source-layer interface, not the full ZFC endpoint. *)
From Coq Require Import List.
From K230 Require Import RM.
From K215F Require Import Prog215 DagPerm Source215.
Import ListNotations.

Theorem existing_source_interface R :
  rm_halts Prog215.p215 ([],R) <-> rm_halts DagPerm.dagPerm ([],R).
Proof. exact (K215F.Source215.p215_dagPerm R). Qed.

Print Assumptions existing_source_interface.
