(** Small kernel-checked controls for the representation boundary.
    These examples supplement the universal theorem; they do not replace it. *)
From Coq Require Import List NArith.
From K230 Require Import RM.
From K230P Require Import Bisim230.
Require Import CheckedTree.
Import ListNotations.

Definition e0 : entry := ([],[],0%N,0%N).
Definition e1 : entry := ([true],[true],0%N,0%N).
Definition halt_tree := TN (TL EHalt) (TL EHalt).
Definition dec_tree := TN (TL (EDecnz 0)) (TL EHalt).

Example leaf_rejects_nonzero : lookup (CLeaf e0) 1 = None.
Proof. reflexivity. Qed.

Example zero_cut_routes_right :
  lookup (CNode 0 (CLeaf e0) (CLeaf e1)) 0 = Some e1.
Proof. reflexivity. Qed.

Example oversized_cut_routes_left :
  lookup (CNode 100 (CLeaf e0) (CLeaf e1)) 0 = Some e0.
Proof. reflexivity. Qed.

Example duplicate_rows_pass :
  check halt_tree halt_tree (CNode 1 (CLeaf e0) (CLeaf e0)) = true.
Proof. vm_compute. reflexivity. Qed.

Example zero_cut_can_pass :
  check halt_tree halt_tree (CNode 0 (CLeaf e0) (CLeaf e0)) = true.
Proof. vm_compute. reflexivity. Qed.

Example oversized_cut_can_pass :
  check halt_tree halt_tree (CNode 100 (CLeaf e0) (CLeaf e0)) = true.
Proof. vm_compute. reflexivity. Qed.

Example missing_initial_rejected : check halt_tree halt_tree CEmpty = false.
Proof. reflexivity. Qed.

Example mismatched_halt_rejected :
  check halt_tree dec_tree (CLeaf e0) = false.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions zero_cut_can_pass.
Print Assumptions oversized_cut_can_pass.
Print Assumptions mismatched_halt_rejected.
