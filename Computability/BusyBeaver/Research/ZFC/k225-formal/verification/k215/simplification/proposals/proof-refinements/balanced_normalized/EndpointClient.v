From Coq Require Import List.
From K230 Require Import RM.
From K215F Require Import Prog215 DagPerm Source215.
Import ListNotations.

Theorem preserved_public_type : forall R : regs,
  rm_halts p215 ([],R) <-> rm_halts dagPerm ([],R).
Proof. exact p215_dagPerm. Qed.

Print Assumptions preserved_public_type.
