From Coq Require Import List.
From K230 Require Import RM.
From K215F Require Import Prog215 DagPerm Source215.
Import ListNotations.
Definition public_client : forall R, rm_halts p215 ([],R) <-> rm_halts dagPerm ([],R) := K215F.Source215.p215_dagPerm.
Print Assumptions public_client.
