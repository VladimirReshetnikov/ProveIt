Require Import OriginalCertificate CompactCertificate.

Theorem compact_certificate_exact :
  CompactCertificate.Cert215 = OriginalCertificate.Cert215.
Proof. reflexivity. Qed.

Print Assumptions compact_certificate_exact.
