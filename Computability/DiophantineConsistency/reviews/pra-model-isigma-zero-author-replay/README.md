# Candidate-PRA arithmetic reduct: replay

`PRAModelISigmaZero.modelReductISigmaZero` and `modelReductIOpen` prove that
the ordered-ring reduct of every candidate-PRA model satisfies Foundation's
IΣ₀ and IOpen theories. These are model theorems, not yet candidate-PRA code
representations of pairing or its projections.

The author build `/tmp/pra-model-isigma-zero-author-4_u32vuq`, private replay
`/tmp/pra-model-isigma-zero-independent-ekqddzm6`, and root replay
`/tmp/pra-model-isigma-zero-independent-sgcnimv0` passed with matching
source/object/full-log hashes. Root replay used the bounded-comparison provider
`/tmp/parsons-bounded-post-preparation-independent-ymuz50k8/lib`.

Replay: `python Computability/DiophantineConsistency/reviews/pra-model-isigma-zero-author-replay/replay.py --parent /tmp/parsons-bounded-post-preparation-independent-ymuz50k8/lib`.
All listed parent source/object pairs are authenticated. Foundation and Mathlib
are inherited; the parent comparison also inherits the Parsons overlay except
for its authenticated direct `ParsonsRule` object. The check logs show only
standard Lean axioms and no `sorryAx`.
