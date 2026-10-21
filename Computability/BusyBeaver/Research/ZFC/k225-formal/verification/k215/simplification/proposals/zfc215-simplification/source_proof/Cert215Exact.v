(** Exact equality of all ordered certificate entries, not a hash-only check. *)
From Coq Require Import List.
Require Import OriginalCert215 Cert215Compact.
Theorem certificate_exact : Cert215Compact.Cert215 = OriginalCert215.Cert215.
Proof. vm_compute. reflexivity. Qed.
Theorem certificate_length : length Cert215Compact.Cert215 = 2240.
Proof. vm_compute. reflexivity. Qed.
Print Assumptions certificate_exact.
Print Assumptions certificate_length.
