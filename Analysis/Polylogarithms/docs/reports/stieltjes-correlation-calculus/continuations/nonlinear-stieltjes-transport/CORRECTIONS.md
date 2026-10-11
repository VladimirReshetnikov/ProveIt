# Correction and safeguard ledger

## 1. No demonstrated error in the preceding fixed-coordinate theorem

The incoming `Periodic Stieltjes Collisions` report explicitly says that its absence of lower delta derivatives belongs to its stated, fixed-coordinate comparison. Its further-research section asks how this changes under a genuinely nonlinear coordinate. The present article answers that question; it does **not** label the original theorem false.

A rejected extrapolation is: “A coordinate with slope one creates no new contact term.” For `phi(y)=y+a*y^2*(1-y)` with sufficiently small nonzero real `a`, the actual density discrepancy for trigamma is `a*delta`. Thus the quadratic coordinate coefficient cannot be omitted. For the second derivative of `gamma_0`, the full discrepancy is `-2a*delta' + (2b-3a^2)*delta` when `phi(y)=y+a*y^2+b*y^3+...`.

## 2. Transport the existing contact distribution as well as the off-point density

Given `K=FP(f dx)+kappa delta^(d)`, transporting only `f` is incomplete. Add the local two-endpoint finite-part discrepancy **and** the explicit pullback of `delta^(d)`. The Lagrange coefficient formula in Proposition 3.3 provides every lower derivative. This is pullback of the already defined correlation, not an assertion that nonlinear pullback preserves convolution.

## 3. Retain the entire spectral numerator

The Poisson/Stieltjes generator requires `P_p(u) F_p(0;q)`, not just `F_p(0;q)`. At Stieltjes index zero the omitted correction is controlled by `H_p`; higher indices retain `e_{p,m+1}`. This is consistent with, and not a correction to, the incoming full-numerator lemma.

## 4. Continuous circle branch and density conventions

The principal arctangent alone is not the circle lift on `(1/2,1)`. Add one on that half. A density pullback includes `phi'`, while an unweighted composition average does not. The test factor `1/phi'` is essential in the latter transport calculation. These are implementation and editorial safeguards; no uninspected source is accused of making either error.

## 5. Existing special-value status

The inspected canonical discovery chapter says S4 is proved, the specified frozen weight-nine/S8 vector is rejected by a rigorous signed residual, and a remaining S6 relation is conjectural. Do not relabel all S8 identities as disproved or present the frozen rejection as a period-independence result. This continuation proves none of those outstanding restricted-basket reductions.

## 6. Evidence labels

All all-index mathematical claims rest on the supplied proofs. The exact scripts test finite rational and polynomial statements. The mpmath quadratures and power-series evaluations are floating-point diagnostics with recorded truncations, not interval certificates. No proof-assistant formalization is included.
