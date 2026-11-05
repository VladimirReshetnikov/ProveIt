# Independent review of signed cancellation and the 88 rank congruence

On 2026-11-04 an independent reviewer inspected
[`Absorb88SignedCancel.lean`](../../research/ordinary12-absorb88-signed-cancel-draft/Absorb88SignedCancel.lean),
[`Absorb88SignedRankCongruence.lean`](../../research/ordinary12-absorb88-signed-rank-congruence-draft/Absorb88SignedRankCongruence.lean),
their stated model hypotheses, and the referenced natural factor-three
cancellation and graph divisor sources. No sign, factor, or parameter
mismatch was found. No fresh Lean replay was run.

For divisibility of embedded model elements, a nonnegative difference-ring
quotient is itself an embedded model element. If the quotient is negative,
the product of the nonnegative embedded divisor and that quotient is
nonpositive; equality to a nonnegative embedded dividend forces that dividend
to zero. This justifies the natural divisibility transfer, including the zero
edge case. The signed cancellation then handles an embedded natural `x` and
its negative separately, invokes the natural cancellation theorem in either
case, and restores the sign of the quotient. Its explicit assumptions are
`q > 0`, `q³ ∣ Y`, and `q⁵ ∣ Hx`, with `H = 3 + 4Y(X + 1)`.

The referenced natural theorem explicitly treats both `3 ∣ q` and `3 ∤ q`:
in the former case it loses one factor of `q`, and in the latter it supplies
a unit certificate. Thus no unstated coprimality of `q` and `3` is needed.
In the graph specialization, `Y = q³s` supplies the divisibility, and
`a = XY + Y` gives `3 + 4a = H`. The input graph divisor and the output use
the same signed difference `k − rank − 1`, not a natural truncated
subtraction; embedding powers via `map_pow` preserves the intended `q⁵` and
`q⁴`. The positive actual graph zero, positive `beta`, and the additional
negative-transport inequality remain explicit hypotheses.

The conclusion is the signed `q⁴` divisibility only. It does not establish
nonnegative rank, a rank window or early-index equality, an 89 witness, or an
iPRA endpoint. The author's checks use temporary providers whose full project,
package, dynamic, and search-path ancestry is not authenticated here.

Reviewed source SHA-256 values:

- `Absorb88SignedCancel.lean`: `1117e85e01cdd1c5bc7946dd41c4a27536bcf0a0175f7299d30cdbd136cc290f`.
- `Absorb88SignedRankCongruence.lean`: `3988c507f929a41c9b7b0bca01b9f030a209399661c3778f0f48add56e11cf78`.
