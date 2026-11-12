# Independent source review: positive-81 carrier data

The author receipt reproduces for the pinned bytes in `pins.json`. The source
is unelaborated; no Lean, provider/axiom replay, complete graph bridge or
physical-file interpretation is established by this review. The independent
checker exercises literal graph evaluations, signed positivity, companion
positivity and divisibility with finite values only.

The source first root is `z=b*(ell+k+r-k*P)-P` with b>0, k≥2 and r≥0.
If P≤0 then `z≥b*(ell+k)>0`; but
`(ell+k)²−(1+ell*(ell+k))=ell*k+k²−1>0`, contradicting the stated scaled
norm. Thus the signed P is positive and can be represented by a positive
model natural. The natural magnitude theorem permits either sign for z;
the scaled quotient then yields a natural tau and `tau²=1+ell*(ell+k)`.
This indeed gives tau>ell without fixing the sign of the original root.
Both signs give b|z, and the exact rearrangement
`P=b*(ell+k+r-k*P−z/b)` produces a signed divisibility witness. Natural
reflection supplies `Pn=b*t` with positive t; here `z/b` denotes the signed
witness, not an assumption of built-in division. The source's explicit
`linear_combination hz-hw` has this orientation.

With q=1+b, `P=C*(X+K)−F` and `Q=C*(X+K*q)−F*q`, one has
`Q−P=b*(C*K−F)`. Thus the signed divisibility transfers in either direction;
the two explicit witness signs match this identity. For the forward carrier,
C≥1, F+2≤q, q>0 and q²≤X give `F*q<q²≤X≤C*(X+K*q)`, hence Q>0.
The reverse helper assumes C>0 and X>0 and uses Q=C*X+q*(C*K−F)>0 to infer
P=C*X+(C*K−F)>0, splitting by the sign of C*K−F. It does not establish C>0
from an 83 zero. The positive target formula follows by substituting
`Qn=b*t`: `r'=k*(Qn−1)+t+(tau−ell)>0` and the new signed root is +b*tau.
This is a fresh witness, not preservation of the old root's sign.

For the literal graph connection, the two pinned JSON inputs have the same
positive coordinates and the carrier delta claimed above. The draft's 81
first-root equation and 83 r-updated first-root equation use the same q, X,
Y, ell and k. The compact wrapper's port beta positivity comes from
`CompactFixedBeta.bounds`; its gap and q²≤X come respectively from the mapped
85 graph and the source-only exact-main calibration on the same original
81 valuation. The 81→85 image and all imported source theorems remain subject
to their own unelaborated proof, casts, coherent-provider and compact-port
obligations. The wrapper only proposes a forward *first residual* witness;
it is not the reverse `CrossRootCut`, parent `PolynomialBridge`, or endpoint.

No concrete algebraic or premise mismatch was found. Finite checks cover
400 actual graph-field evaluations, 22,680 nonpositive-P controls, and the
reported forward/reverse companion cases; they do not establish arbitrary
IΣ₁-model results or Lean tactic elaboration.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary13-positive81-carrier-data-independent/check.py | cmp - reviews/ordinary13-positive81-carrier-data-independent/receipt.json
```
