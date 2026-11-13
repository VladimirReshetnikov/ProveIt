# Natural cancel-86 to positive-shifted 74 — source draft

This proposed source-only bridge compares the literal natural-86 graph to the
literal positive-74 graph after replacing every ring valuation coordinate by
`v_j+1`. It states the two exact qF and guard cancellations separately, then
uses them to compare the four restricted factors, guard factor and full
output over an arbitrary commutative ring and arbitrary signed integer ports.
A generic expression induction states that ring evaluation of `positiveShift`
is evaluation at the shifted valuation. Finally the proposed model client uses
`ModelDifferenceRing.internalZero_iff` in both directions to compare the two
literal expressions at the **same natural-model valuation**, without a
positivity or fixed-port premise.

These proofs are source text only. The graph modules, `simp` cut rewrites,
expression induction and model conversion have not been elaborated; their
resource use is unmeasured. The model client is not a theorem yet, and it does
not establish provider coherence, an iPRA endpoint, the operation count of the
Lean expression, symbolic-port-to-byte correspondence, or PDF binding. The
separately reviewed external SLP is the source of the 86-operation bound. No
Lean run occurred.

Independent source review: [natural-86 ring/model bridge](../../reviews/ordinary14-natural-cancel86-ring-bridge-independent/README.md).
