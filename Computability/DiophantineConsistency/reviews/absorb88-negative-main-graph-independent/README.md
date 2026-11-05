# Independent review of the 88 negative-branch main expression

On 2026-11-04 an independent reviewer inspected
[`Absorb88NegativeMainGraph.lean`](../../research/ordinary12-absorb88-negative-main-graph-draft/Absorb88NegativeMainGraph.lean),
its generic orientation theorem, the graph gap and rank-bound statements,
and the actual 88 graph source. No mathematical sign, positivity, or
parameter-substitution defect was found. This source review did not run Lean.

The theorem assumes one positive zero of the actual 88 graph, positive
`beta`, and explicitly assumes the negative-transport branch `Bp < Bn` in
the model difference ring. These are the assumptions of the imported graph
gap and rank bound. The proof derives `q ≥ 2`, `Y = q³s ≥ 8` and
`W = Yq² ≥ 8`; consequently `WY − 7 − W ≥ 0`. It has `E = XY > 0`,
`a = E + Y ≥ 1` and `H = 3 + 4a`, giving `H ≤ 7a`. The graph gap gives
`k ≥ 8P + 4` for `P = XY²`; `Y ≥ 1` yields `P ≥ E` and therefore
`k ≥ 8E`.

The generic orientation theorem is instantiated with its `Q = q²`, so
`QP = WE`; its signed rank lower bound is exactly the conclusion imported
from the negative-branch rank theorem. The resulting positive expression is
`W(X + a(eta + Yk)) + H(W direct − k + rank + 1)`. In the graph's source,
`c = eta + Yk`, `b0 = X + ac`, `r0 = k − rank − 1`, and the squared
main term is `Dstar = W b0 + H(W direct − r0)`. Thus this expanded expression
matches `Dstar` by source-level algebra, with the difference-ring coercions
and signs in the expected places. The reviewed theorem states the expanded
expression; it does not itself state a separate Lean equality to the
`mainParts` evaluator.

The conclusion is conditional strict positivity. It does not by itself
establish the oriented Pell balance, rule out the negative branch, normalize
transport, prove the reverse 88/89 existence implication, or establish an
iPRA endpoint. The author's captured-provider check is separate; complete
project, package, dynamic and search-path ancestry remains unaudited here.

Reviewed join source SHA-256:
`ac1cab154cad9756e331018b1bdb59ced747c2dadb258c7217b75c8e3801dcf7`.
Reviewed 88 graph source SHA-256:
`423e9f8b4a6099231e1ec20dc48680c56d3e5fc3f0f7f7ae1538a4a12c11aa5c`.
