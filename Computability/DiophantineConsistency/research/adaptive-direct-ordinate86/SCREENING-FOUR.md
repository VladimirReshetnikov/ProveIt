# Three restricted four-operation screens for an 85-gate graph

These scripts adapt three earlier 87-graph screens to the pinned 86-operation candidate JSON, SHA-256 `e9889a81a491b85491dde749e82158109ea98ff94ed41fc0f05dc810ec58b91f`. The original liveness-count checks and thresholds are changed to `len(rows)` so that only counts below 86 are reported. Each targets one row at a time, draws operands from earlier nodes, inputs, symbolic ports and literals 0–4, evaluates three deterministic samples in the prime field modulo `2305843009213693951` with seed `80281234`, and recounts output liveness.

- `screen-four-affine-product.py` screens `(x ± y)*(u ± v) ± w`, including both final subtraction orientations. Its output reports 21 eligible targets, zero candidates and zero encountered zero-divisor skips.
- `screen-four-affine-scaled.py` screens `((x*y ± u)*z) ± w`. Its output reports 21 targets, zero candidates and 21 multiplier zero-sample skips; reverse subtraction forms are omitted.
- `screen-four-scaled-products.py` screens `(x*y ± u*v)*z`. Its output reports 21 targets, zero candidates and 21 multiplier zero-sample skips.

These are restricted heuristic screens, not exhaustive searches or a minimality proof. They skip a divisor with any zero sample and exclude intermediates whose signatures match existing earlier nodes; recomputing such nodes could change liveness and is not covered. The affine-product zero-skip count refers only to cases reaching its division test. Signature collisions can also miss or invent matches. Other shapes, simultaneous multi-row changes, different constants and merely zero-equivalent polynomials are outside scope. Any prospective match would require exact polynomial verification, full liveness and Lean binding.

Reproduce each saved output by running the corresponding `screen-four-*.py` from the repository root. No 85-operation equation is claimed.
