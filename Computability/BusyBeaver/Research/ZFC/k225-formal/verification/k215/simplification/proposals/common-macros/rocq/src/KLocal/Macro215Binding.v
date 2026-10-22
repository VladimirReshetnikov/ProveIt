(** Literal 215 binding; imports no other candidate program. *)
From K230 Require Import RM.
From KLocal Require Export MacroInterface.
From K215F Require Import DagPerm.
Lemma canonical_to_215 : Closed macro_prog DagPerm.dagPerm macro_ok.
Proof.
  eapply check_closed_sound with (bound := 467); [exact macro_bound|].
  vm_compute. reflexivity.
Qed.
Lemma macros_215_to_canonical : Closed DagPerm.dagPerm macro_prog macro_ok.
Proof.
  eapply check_closed_sound with (bound := 467); [exact macro_bound|].
  vm_compute. reflexivity.
Qed.
Print Assumptions canonical_to_215.
