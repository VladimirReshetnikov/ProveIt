# Independent review: general fixed-width obstruction

The ordinary-integer argument is valid with the stated same-tuple gap,
projection and size assumptions. In particular, rearranging the affine
threshold makes `3n−10c` positive, so the final exponent comparison and
cancellation of `q^c` are justified. The Pell gap supplies `r≥2`, and the
projection argument then gives the stated bound on `X`. The symbolic
`betaNat` identity and the conditional ordinary-integer lower bound on `q`
were checked against the repository definitions.

Reviewed note SHA-256:
`9e3466fe31984f83d3134469d6e7989c73dd0f4e0ac3fc0f68f8d6019be744c5`.
Checker SHA-256:
`9f4e128de4d024ccaa5f5ee273d518b4925628371f4b0b187c35e0cd6624e293`.
The checker was independently rerun with `python3 -I -S -B` and exited 0;
it validates only the finite example thresholds and constants.

This review is not a Lean replay, a nonstandard-model proof, a graph-zero
binding, an external payload binding, a reverse guard or an iPRA endpoint.
