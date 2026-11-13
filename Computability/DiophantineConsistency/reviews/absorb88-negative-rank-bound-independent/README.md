# Independent review of the 88 negative-branch rank bound

On 2026-11-04 an independent reviewer inspected
[`Absorb88NegativeRankBound.lean`](../../research/ordinary12-absorb88-negative-rank-bound-draft/Absorb88NegativeRankBound.lean),
the actual 88 graph, and the directly used negative-transport bound. No
mathematical sign, parameter, or coercion mismatch was found. This is a
source review; no fresh Lean replay was performed.

For the generic ordered-ring lemma, `b > 0` and `q = b + 1` imply
`q² − 1 ≥ 0`. Put `G = alpha + b(q − F)`. If `G ≥ 0`, then `G + P ≥ 0`.
If `G < 0`, the positivity assumptions imply `F > q`, and the explicit
transport expression and `A ≥ 1` imply
`−G < bF < qF < U ≤ P`. Thus `G + P ≥ 0` in either case. Multiplying by
`q² − 1`, using `P ≥ 0`, and adding the assumed nonnegative `RJ` gives
`−q²P ≤ (q² − 1)G + RJ`. The theorem retains its explicit assumptions;
the documented unused-`hF` warning does not invalidate the implication.

In the graph specialization, the explicit branch condition is
`ι Bp < ι Bn`, and the imported bound applies to the same tuple and yields
`ι q * (ι Bn − ι Bp) ≤ ι P`. The ring identity used to put this into the
generic lemma is
`q(Bn − Bp) = q((F + alpha − q)A + F)`, where
`A = K0 + w`, `Bp = qA` and `Bn = (F + alpha)A + F`. The theorem defines
`P = XY²` with `X = qw` and `Y = q³s`, as in that imported bound. The
right-hand side is exactly the actual graph's signed rank
`(q² − 1)(alpha + b(q − F)) + J(MC + MFq)` after commutation of factors.
All subtractions are in the model difference ring. Positivity of the natural
port `beta` and every coordinate is explicit; the other natural ports and
`J` make the remaining rank contribution nonnegative.

This is a conditional lower bound on the negative branch, not a claim that
the rank is nonnegative or that the branch exists, can be normalized, or
implies the reverse 88/89 equivalence. The author's Lean result uses captured
temporary providers; this review does not authenticate their complete source,
package, dynamic, or search-path ancestry.

Reviewed source SHA-256:
`36563548a7dae1bf2b4188cf5ef27127548cb1afb62073914a202d1951b971c1`.
The examined 88 graph and negative-transport graph-binding source SHA-256s
were `423e9f8b4a6099231e1ec20dc48680c56d3e5fc3f0f7f7ae1538a4a12c11aa5c`
and `276a6248cebf7c674661f6f04216f75d68dd2570f83e6374ff47818260f87517`.
