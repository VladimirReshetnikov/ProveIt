# Bounded comparison after preparation merge

This replays the six existing bounded-only comparison modules on the refreshed
candidate-PRA graph. The author build `/tmp/parsons-bounded-post-preparation-tqydajij`,
private replay `/tmp/parsons-bounded-post-preparation-independent-ymuz50k8`, and
root replay `/tmp/parsons-bounded-post-preparation-independent-s8ymvqke` passed
with matching source/object/full-log hashes. Root used the independently
checked 47-module provider `/tmp/pra-after-preparation-merge-independent-blp1ky5k/lib`.

Replay: `python Computability/DiophantineConsistency/reviews/parsons-bounded-post-preparation-replay/replay.py --parent /tmp/pra-after-preparation-merge-independent-blp1ky5k/lib`.
The listed candidate source/object pairs and direct `ParsonsRule` source/object
are authenticated before and after. Other Parsons overlay objects and
Foundation/Mathlib are inherited. This is a bounded-induction-only comparison;
it does not establish the Σ₁ rule comparison or full Parsons conservation.
