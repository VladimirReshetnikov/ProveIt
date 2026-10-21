(** Balanced storage of the existing 1,426-entry normalized certificate. *)
From Coq Require Import List NArith.
Require Import BalancedBisim NormalizedCert215.

Definition NormalizedTree215 : CTree := Eval vm_compute in buildTree 11 Normalized215.

Theorem normalized_tree215_exact : flatten NormalizedTree215 = Normalized215.
Proof. vm_compute. reflexivity. Qed.

Theorem normalized_tree215_valid : validb NormalizedTree215 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem normalized_tree215_size : csize NormalizedTree215 = 1426%N.
Proof. vm_compute. reflexivity. Qed.

Theorem normalized_tree215_height : height NormalizedTree215 = 12.
Proof. vm_compute. reflexivity. Qed.

Theorem normalized_tree215_lookup_bound j : lookupDepth NormalizedTree215 j <= 12.
Proof. rewrite <- normalized_tree215_height. apply lookupDepth_le_height. Qed.

Print Assumptions normalized_tree215_exact.
Print Assumptions normalized_tree215_lookup_bound.
