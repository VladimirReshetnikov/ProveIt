# Positive-83 reverse first-root construction

This is an **unelaborated source draft**, not a verified Lean theorem or an
iPRA endpoint. It proposes the missing reverse first-residual witness and
composes it with the previously proposed forward witness to form the source
statement `CrossRootCut`. The exact positive-83 parent `PolynomialBridge`
remains an explicit premise of the native client. All inherited graph,
arithmetic, calibration, cast, model, provider and axiom obligations remain
open until the entire source/provider chain is checked by Lean.

For a positive 83 valuation at natural ports, the first norm supplies a
positive signed 83 carrier and a natural common-root magnitude by the
separate `PositiveCarrierDataDraft.root_data` proposal. With `b=J*beta`,
`q=1+b`, `X=q*w`, the source and target first carriers are

```
C = q-F-alpha
Q = C*(X+K0*q)-F*q       -- source, positive 83 graph
P = C*(X+K0)-F           -- target, positive 81 graph
Q-P = b*(C*K0-F).
```

The sign argument in `gap_of_carrier` uses natural K0, X, q and F: if
`C<=0`, then the first product is nonpositive and `F*q>=0`, contradicting
`Q>0`. Thus the same graph zero yields `F+alpha<q` and a represented
positive model-natural C; it is not necessary to assume a gap or any
large-X calibration in this reverse direction. With positive J, beta and w,
`b`, `q`, and X are positive. The previous `reduced_companion` source then
proposes P>0 and signed `b | P`; signed-to-natural reflection and the common
norm yield a strictly positive replacement r for the exact 81 first row.

`Positive83ReverseRoot.lean.src` contains the proposed actual first-row
bindings, gap extraction, and reverse root witness. Its `hbeta` is explicit
and concerns the cast of the natural first port into the model. The compact
wrapper in `Positive83CrossRoot.lean.src` proposes to obtain that positivity
from `CompactFixedBeta.bounds`, applied to the actual positive J coordinate.
It composes this reverse proposal with the prior source-only
`Positive81ForwardCompactDraft.forward`, which depends on the more demanding
same-model positive-81 exact-index and power calibration. The forward and
reverse clients use the same compact tuple and replace only coordinate 8.
They do not independently establish graph/provider soundness or the parent
bridge.

The receipt pins the exact graph and direct source bytes and checks the row
changes and bounded integer instances of the sign, divisibility, and positive
branch formulas. The checks are not a proof in all models, do not elaborate
Lean, and do not establish the physical PDF linkage. From
`Computability/DiophantineConsistency` run:

```
python3 -I -S -B research/ordinary13-positive83-reverse-root-model-draft/check.py
```
