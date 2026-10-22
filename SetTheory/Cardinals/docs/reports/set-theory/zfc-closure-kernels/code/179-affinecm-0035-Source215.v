From Coq Require Import Lists.List.
From K230 Require Import RM.
From K215F Require Import Prog215 DagPerm.
Require Import K215GraphBinding.
Import ListNotations.

(** Same public name and exact all-register statement as production Source215. *)
Theorem p215_dagPerm : forall R,
  rm_halts p215 ([],R) <-> rm_halts dagPerm ([],R).
Proof. exact p215_dagPerm_affine. Qed.

Print Assumptions p215_dagPerm.
