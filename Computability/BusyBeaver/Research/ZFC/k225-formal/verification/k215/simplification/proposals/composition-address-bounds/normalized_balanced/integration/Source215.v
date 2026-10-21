From Coq Require Import List.
From K230 Require Import RM.
From K215F Require Import Prog215 DagPerm.
Require Import Source215NormalizedBalanced.
Import ListNotations.
Theorem p215_dagPerm R : rm_halts p215 ([],R) <-> rm_halts dagPerm ([],R).
Proof. exact (p215_dagPerm_normalized_balanced R). Qed.
Print Assumptions p215_dagPerm.
