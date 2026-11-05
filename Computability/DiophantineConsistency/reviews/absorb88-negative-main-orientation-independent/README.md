# Independent review of negative-main orientation

On 2026-11-04 an independent reviewer examined
[`Absorb88NegativeMainOrientation.lean`](../../research/ordinary12-absorb88-negative-main-orientation-draft/Absorb88NegativeMainOrientation.lean)
and the intended 88-graph substitution. The stated ordered-ring implication
is mathematically sound: the source's identity expresses its target as a sum
of nonnegative terms and the strictly positive term `aWE`. The source retains
all the sign and inequality assumptions in its theorem, including the
signed-rank lower bound. This is a source review; no fresh Lean replay was run.

The intended graph parameters are `W = Yq²`, `E = XY`, `P = XY²`, and
`Q = q²`, giving `QP = WE`. For a positive graph tuple and positive `beta`,
`q ≥ 2` and `Y ≥ q³ ≥ 8`, making `WY − 7 − W ≥ 0`; with
`a = XY + Y ≥ 1` and `H = 3 + 4a`, also `H ≤ 7a`. The previously checked
two-norm gap gives `k ≥ 8P + 4`, and `Y ≥ 1` yields `k ≥ 8E`. These are
mathematical parameter observations, not a new Lean graph-binding theorem.

A plausible route to the **still unproved in this packet** signed-rank
bound is as follows. Write `L = K₀ + w`, `P = XY²`, and
`G = alpha + (q − 1)(q − F)`. If `F ≤ q`, then `G ≥ 0`. If `F > q`,
the negative-transport bound
`q[L(F + alpha − q) + F] ≤ P` implies `q(F − q) ≤ P`; the displayed
formula for `G` then gives `G ≥ −q(F − q) ≥ −P`. With nonnegative fixed
ports and `J`, the graph rank is
`G(q² − 1) + J(MC + q MF) ≥ −q²P`. This case split requires an actual
graph-to-difference-ring proof, the checked negative-branch bound, and its
positivity assumptions; no such composed theorem is claimed here.

The conditional orientation result does not establish the branch premises,
transport normalization, reverse 88/89 existence, an iPRA endpoint, or a
graph zero. The author's captured-provider check and its inherited ancestry
limitations remain separate from this review.

Reviewed Lean source SHA-256:
`1899f09347f49ccd0416a325b1593100a208d4d5c68ccd4f37b6322350c424bb`.
