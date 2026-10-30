# Positive certificate for the existing guarded reducer

The two new sources are `ParsonsPositiveGuardCertificate.lean` and `ParsonsPositiveGuardCertificateChecks.lean`. The author build and two independent builds passed with matching source, object and complete-log hashes and 43 unchanged local parent source/object hashes. Root provider `/tmp/parsons-positive-guard-cert-independent-w8wdhtsq/lib`; private provider `/tmp/parsons-positive-guard-cert-independent-yixk2w83/lib`. Author/root source snapshots, complete logs and terminal states are preserved here. Foundation and Mathlib are inherited from the parent provider. An audit after the subsequent upstream merge found no changed local source among this packet's manifest, but its parent provider is the previously accepted 89-module snapshot; no claim is made that unrelated inherited objects were recompiled.

`three_disjunctions_positive` proves that the existing `ParsonsRule.three_disjunctions` output carries `AllPositive`, provided its predicate and existential side are positive and its three actual input proofs carry the same certificate. It does not prove the global strict cut-free translator output has `AllPositive`, or general Parsons conservation. The maintained 14-variable equation's separate HA proof-existence theorem was already complete.

The HA endpoint statement refers to its previously checked snapshot; its
current-source dependency replay is still pending after upstream changes.
