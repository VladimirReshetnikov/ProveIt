(** Literal 217 binding; imports no other candidate program. *)
From K230 Require Import RM.
From KLocal Require Export MacroInterface.
From K217F Require Import DagDom.
Lemma canonical_to_217 : Closed macro_prog DagDom.dagDom macro_ok.
Proof.
  eapply check_closed_sound with (bound := 467); [exact macro_bound|].
  vm_compute. reflexivity.
Qed.
Lemma macros_217_to_canonical : Closed DagDom.dagDom macro_prog macro_ok.
Proof.
  eapply check_closed_sound with (bound := 467); [exact macro_bound|].
  vm_compute. reflexivity.
Qed.
Print Assumptions canonical_to_217.
