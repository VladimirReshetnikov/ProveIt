# IΣ₁ comparison preserving original source sentences

The author and private builds passed two modules with matching source/object/full-log hashes, authenticating 187 unchanged local parent source/object hashes. The parent was the audited 74-module author provider. Foundation and Mathlib remain inherited. A subsequent upstream change to `PRAPiOneImplication` required a suffix refresh; that later [15-module replay](../pra-strict-surrogate-postmerge-author-replay/README.md) has passed twice independently.

`PRAISigmaOneOriginalEquivalence.comparison` takes an actual IΣ₁ proof of `α ↔ β` and two actual candidate-PRA proofs representing the mapped source sentences α and β by unary open-matrix Π₁ sentences. It concludes candidate PRA proves the mapped original equivalence. Both representation proofs are explicit inputs. This module does not supply the Foundation ZFC-consistency representation or claim the maintained equation's original consistency equivalence in candidate PRA. The equation's separate HA proof-existence theorem was checked at an earlier snapshot; its full current-source replay remains pending.

The accepted-parent replay compiled both modules but FAILED final source authentication when the queued merge changed `PRAPiOneImplication.lean`; exact expected/actual hashes and phase are in `merge-failure-state.json`. It is not a source-current PASS.
