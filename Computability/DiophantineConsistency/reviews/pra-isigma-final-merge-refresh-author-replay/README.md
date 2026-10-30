# IΣ₁ open-existential comparison: merged snapshot

The author and two independent replays rebuilt 60 affected/new modules, matched every source/object/full-log hash, and authenticated 143 unchanged local source/object parents before and after. Root provider `/tmp/pra-isigma-final-merge-independent-2tnjbnht/lib`; private provider `/tmp/pra-isigma-final-merge-independent-y8xz6pb4/lib`. Author/root source snapshots, complete logs and both terminal states are preserved here. Foundation and Mathlib are inherited. A later upstream merge may change sources, in which case this remains a pre-merge snapshot until its affected graph is rebuilt.

The source-current checkpoint establishes candidate-PRA admissibility of positive induction rules, a strict-induction certificate for positive Foundation predicates with arbitrary finite free parameters, and `PRAISigmaOneOpenComparison.comparison`. The latter takes an actual IΣ₁ proof of an arithmetic sentence and a candidate-PRA proof that its mapped sentence implies a chosen universally closed open-existential goal; it produces an actual candidate-PRA proof of that goal. Its remaining mapped-source implication is an explicit premise. It does not, by itself, prove the maintained equation/consistency equivalence in candidate PRA. The equation's separate HA proof-existence theorem was already complete.

The HA endpoint statement refers to its previously checked snapshot; a full
current-source replay is pending. At this checkpoint, fetched `origin/main`
at `731f29e4bd` changes `HerbrandPackedContextTransfer`, so that later merge
will require another affected-source rebuild of this comparison graph.
