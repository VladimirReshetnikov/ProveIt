(** Proposed replacement facade. In the focused build this file is installed as
    K215F.Source215 and preserves the existing public theorem name and type.
    The helper modules are in the unqualified namespace of this proof packet. *)
From Coq Require Import List.
From K230 Require Import RM.
From K215F Require Import Prog215 DagPerm.
Require Import NormalizedSource215.
Import ListNotations.

Theorem p215_dagPerm R :
  rm_halts p215 ([],R) <-> rm_halts dagPerm ([],R).
Proof. exact (p215_dagPerm_normalized R). Qed.

Print Assumptions p215_dagPerm.
