# Trace75 weighted whole-product divisor

`Trace75GraphProduct.graph_entire_product` proves in every IΣ₁ model with
β≥31, `MC<β`, `MF<2β`, and an actual positive trace75 zero that, in the
model's difference ring,

`H ∣ (h*X)*(X−2^rankNat)*(2^rankNat*X+1)`.

The proof keeps the extra `X` factor from the carrier projection. It uses
the graph's exact main ordinate, the standard Pell projection quotient and
norm, and the generic whole-product algebra. `K0` is arbitrary. This is
divisibility, not the equality `X=2^rankNat`, nor a halt/iPRA equivalence.

Accepted `run-graphproduct-v2.py`, `observations/graphproduct-attempt02/`:
Lean exit 0, no warning/error; object
`/tmp/trace75-graphproduct-a_f7xzko/Trace75GraphProduct.olean`, SHA-256
`82aff3b3fa8a20751434ecf00942304837f966d4fc3b9e282379eed7b7b7abe4`.
Attempt 01 is retained with failed cast simplification and ring normalization.
Selected direct imports are pinned; historical transitive/package ancestry
and external graph/file binding remain inherited limits.
