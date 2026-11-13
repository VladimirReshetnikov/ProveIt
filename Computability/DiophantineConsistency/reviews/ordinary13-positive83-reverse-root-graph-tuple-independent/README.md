# Independent graph/tuple review: positive 83 reverse-root source

This bounded source review covers the graph and composition interfaces in
`research/ordinary13-positive83-reverse-root-model-draft/`. A separate review
is assigned to the signed/natural arithmetic proofs. No Lean, builds, staging,
provider authentication or endpoint replay was performed here.

The deterministic receipt compares every named 81 and 83 graph row to both
JSONs and their proposed Lean literals, and checks the exact first-carrier
row delta. Both witness orders are
`J,F,alpha,f,i,T,w,s,r,eta,zeta,y,gamma`; r is position 8. Both port orders
are beta, K0, MC, MF. In the source's notation, with `b=J*beta`, `q=1+b`
and signed `C=q-F-alpha`, the actual **83** first carrier is
`Q=C*(X+K0*q)-F*q` and the target **81** carrier is `P=C*(X+K0)-F`.
The checker independently proves `Q−P=b*(C*K0−F)` in a free integer
polynomial ring. It verifies that the main, auxiliary and strong residual
dependency graphs contain no r; a new first-root coordinate therefore leaves
those residual expressions unchanged.

The unelaborated `first83` statement binds the **83 source** first residual
to the Q-root square. `first81_update` binds the **81 target** first residual
to the P-root square at `putR v r`, leaving the other coordinates unchanged.
The helper application passes the Q-root/norm as source and P as target; its
returned target square is then used to set the 81 first residual to zero.
Thus the source's declared direction is positive 83 zero → positive 81 first
residual witness. The actual residual evaluation reductions, casts, companion
positivity/divisibility and all related tactics remain unelaborated.

`Positive83CrossRootDraft.crossRootCut` supplies the **first** clause of
`CrossRootCut` (81 zero → 83 target) using the separate compact forward
draft, and the **second** clause (83 zero → 81 target) using this reverse
client. It uses the same arbitrary natural K and the same `ports K` throughout.
The compact wrapper's `hbeta` uses the positive input J at coordinate 0 and
the source signature of `CompactFixedBeta.bounds`. The pinned compact tuple
definition has natural positions `[beta,K,low,beta+high]`; casts into the
model/difference ring still need a coherent provider build. The previously
reviewed forward client carries its own unelaborated exact-index/power
calibration; this tuple review does not establish it.

The proposed `native85` client uses the assembled cut while retaining an
explicit `PolynomialBridge` for the **positiveShift of the exact 83 graph**
at that K. It does not discharge that parent bridge. The author receipt is
reproduced as a byte check; finite scalar controls and the free-ring identity
do not prove either all-model direction. All proof scripts, source/object
providers, axiom reports, fixed physical bytes/PDF binding and the final
internal iPRA/ZFC endpoint remain open.

Reproduce from `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary13-positive83-reverse-root-graph-tuple-independent/check.py
```
