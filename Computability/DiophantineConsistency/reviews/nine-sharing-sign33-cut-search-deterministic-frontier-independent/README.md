# Independent review: deterministic bounded signed-cut search

The only source change from the earlier search sorts the initial baseline before the seeded random operations. Two new isolated independent runs reproduce the retained result byte-for-byte. The best examined set has 19 cuts plus 14 inputs, so 33 witnesses; an independent two-component syntactic-degree propagation verifies degree ≤2 for all 60 source rows under its selected orientations. The same four nontrivial sign obligations remain: gap, tau, cTminusR nonnegative and V2minusY2 nonpositive.

This is a restricted finite heuristic and degree bookkeeping only: no exact residual construction, proofs of those signs, all-model bridge, Lean theorem, smaller candidate or global lower bound follows. The earlier nondeterministic packet and its independent replay remain separately retained.

Checker SHA-256 `e803cc8f98494a1a08bbe0beea8de0f032dc6238dcf8bcbc77c889817b2a0f3a`; result SHA-256 `d1b3ad6b551ad8bf61b91f3c2afc62e0cfef23d963ae94c127a5ed6691095103`.
