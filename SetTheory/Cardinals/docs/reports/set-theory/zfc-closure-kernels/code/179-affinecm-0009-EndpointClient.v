From Coq Require Import Lists.List.
From K230 Require Import RM.
From K215F Require Import Prog215 DagPerm Source215.
Import ListNotations.

Definition exact_source_client : forall R : RM.regs,
  rm_halts Prog215.p215 ([],R) <-> rm_halts DagPerm.dagPerm ([],R) :=
  K215F.Source215.p215_dagPerm.

Print Assumptions exact_source_client.
