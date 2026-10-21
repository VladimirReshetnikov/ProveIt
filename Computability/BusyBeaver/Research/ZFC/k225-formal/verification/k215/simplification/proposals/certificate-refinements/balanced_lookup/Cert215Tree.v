(** Exact balanced representation of the existing 2,240-row certificate. *)
From Coq Require Import List NArith.
Require Import BalancedBisim Cert215Compact.

Definition Tree215 : CTree := Eval vm_compute in buildTree 12 Plain215.

Theorem tree215_exact : flatten Tree215 = Plain215.
Proof. Time vm_compute. reflexivity. Qed.

Theorem tree215_valid : validb Tree215 = true.
Proof. Time vm_compute. reflexivity. Qed.

Theorem tree215_entries : csize Tree215 = 2240%N.
Proof. Time vm_compute. reflexivity. Qed.

Theorem tree215_height : height Tree215 = 13.
Proof. Time vm_compute. reflexivity. Qed.

Theorem tree215_lookup_bound j : lookupDepth Tree215 j <= 13.
Proof. rewrite <- tree215_height. apply lookupDepth_le_height. Qed.

Print Assumptions tree215_exact.
Print Assumptions tree215_valid.
