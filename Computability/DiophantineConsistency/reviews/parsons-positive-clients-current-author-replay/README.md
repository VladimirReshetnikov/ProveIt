# Positive-rule proof clients

Six new source/check modules are `ParsonsPositiveGuard{,Checks}.lean`, `ParsonsPositiveCertificate{,Checks}.lean`, and `ParsonsPositiveComparison{,Checks}.lean`. The author run authenticated 75 unchanged local parent sources/objects; root and private replay matched all six source/object/full-log hashes. Root provider is `/tmp/parsons-positive-clients-independent-emdqz3ja/lib`; author/root source snapshots, full logs and both terminal states are preserved. Foundation and Mathlib remain inherited.

`ParsonsPositiveGuard.three_disjunctions` performs Joosten's local guarded reduction in the restricted proof calculus when the induction predicate and existential side are positive. `ParsonsPositiveCertificate` defines `AllPositive` on an actual unrestricted Parsons proof, constructs a restricted proof from that certificate, and proves the embedding round trip. It does not prove that the existing cut-free translator output carries that certificate.

`ParsonsPositiveComparison.comparison` translates actual positive-rule proofs into candidate PRA only under its explicit `PositiveAdmissible` premise, a proof transformer for the positive induction rule. That premise has not been discharged. No general Parsons conservation theorem is claimed. The separate HA proof-existence theorem for the maintained 14-variable equation was already complete.
