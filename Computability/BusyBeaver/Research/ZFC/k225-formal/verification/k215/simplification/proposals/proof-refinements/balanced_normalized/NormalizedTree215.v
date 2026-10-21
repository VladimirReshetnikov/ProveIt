(** Exactly the existing 1,426 normalized entries, in balanced storage. *)
From Coq Require Import List NArith.
Require Import BalancedBisim NormalizedCert215.

Definition NTree215 : CTree := Eval vm_compute in buildTree 12 Normalized215.

Theorem ntree215_exact : flatten NTree215 = Normalized215.
Proof. Time vm_compute. reflexivity. Qed.

Theorem ntree215_valid : validb NTree215 = true.
Proof. Time vm_compute. reflexivity. Qed.

Theorem ntree215_entries : csize NTree215 = 1426%N.
Proof. Time vm_compute. reflexivity. Qed.

Theorem ntree215_height : height NTree215 = 12.
Proof. Time vm_compute. reflexivity. Qed.

Theorem ntree215_lookup_bound j : lookupDepth NTree215 j <= 12.
Proof. rewrite <- ntree215_height. apply lookupDepth_le_height. Qed.

Print Assumptions ntree215_exact.
Print Assumptions ntree215_valid.
Print Assumptions ntree215_lookup_bound.
