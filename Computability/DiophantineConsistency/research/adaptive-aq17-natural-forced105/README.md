# Six forced positive witnesses: 17 natural inputs, 105 operations, degree 20

This external natural-input graph starts from the [17/94/20 positive graph](../adaptive-aq17-factored-root94/).
The straightforward shift of all 17 witnesses would use 111 operations. This
graph shifts only 11 witnesses and leaves `f`, `T`, `y`, `firstQuotient`,
`mainQuotient`, and `vValueVariable` as natural inputs, using 105 operations. The graph is a sum
of eight squares and has exact degree 20. No global minimum is claimed.

## Model zero equivalence

Work in an ordered natural-number model of IΣ₁ with the repository's
`ORingStructure` interface, evaluating subtraction in its signed difference
ring. The 11 shifted inputs are positive. In particular, with their values
write `k=eta+zeta`, `E=X*Y`, `ell=E*Y*k`, `c=eta+Y*k`,
`Delta=3+4*(E+Y)+(E+Y)²`, `I=c²*i`, and `Q=Delta*(f²-1)`. Here
`k, ell, c, I` are positive, `I >= 2`, and `Delta >= 3`. These statements depend only
on the shifted inputs, not on any port value.

At a zero of the sum of squares, each residual is zero. The two norm residuals
give

```
firstQuotient² = 1 + ell*(ell+k)
mainQuotient²  = 1 + Delta*c².
```

Both right sides are at least one, so each **unshifted** natural quotient is
positive. For the unshifted ordinate `z=vValueVariable`, the strong residual
is `I²-Q` and the auxiliary residual is
`y² - Q*(y²-z²) - 1`. If `z=0`, their vanishing gives
`Q=I² >= 1` and `y² = 1 + Q*y²`. Since `Q*y² >= y²`, the latter equality is
impossible in the ordered difference ring. Thus `z>0` as well. This argument
also works if `Q` is initially represented as a signed expression: the strong
equality identifies it with the positive square `I²` before the inequality
is used. It does not assume positivity or any sign of a fixed port.

The other three unshifted inputs are also forced positive:

- If `f=0`, then `Q=Delta*(f²-1)=-Delta<0`, but the strong residual gives `Q=I²>0`.
- If `y=0`, the auxiliary and strong residuals give `Q*z²=1` and `Q=I²>=4`. If `z=0`, the product is zero; otherwise `z²>=1`, so the product is at least four. Both alternatives contradict the equality. Natural equality with zero is decidable in the stated model.
- If `T=0`, the binding `vDifference=0` gives `z=f²*(T*c-rank)-c=-f²*rank-c<0`, while `z` is natural; here shifted `rank` and `c` are positive.

All six conclusions apply simultaneously: none of the six arguments assumes
another unshifted input is positive. Consequently each mixed-shift zero is a
positive zero of the parent graph. Conversely, given a positive parent zero,
use predecessors for the 11 shifted coordinates and use the positive values
themselves for the six unshifted coordinates. Thus the two zero-existence
statements agree for every integer port tuple in the stated models. Equivalently,
relative to the fully shifted 111-row natural graph, move between natural input
tuples by adding or subtracting one on the six forced coordinates; subtraction
is available because the mixed-graph zero forces them positive.

The new polynomial is **exactly** the parent polynomial with this mixed
substitution, as checked by sparse polynomial identities for each residual.
It is generally a different polynomial from the fully shifted graph at the
same natural tuple; their relationship is zero-set equivalence via the maps
above, not pointwise polynomial identity.

## Proof status and reproduction

The parent's earlier transfer chain retains its `beta>0` condition and stated
historical proof provenance. **Neither this mixed-shift transfer nor its iPRA
endpoint has been elaborated in Lean.** The finite checker is evidence for the
formulas and degree, not an iPRA derivation.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/adaptive-aq17-natural-forced105/build.py
python3 -I -S -B research/adaptive-aq17-natural-forced105/check.py
```

The checker pins the parent and child; matches all mixed shifts and graph rows;
checks topology, liveness, all eight exact residual identities and the output
sum; inspects the definitions used in the positivity argument; and verifies
degree 20. The degree witness is the `g72` monomial
`n_Y⁴*n_eta⁴*n_i²` with coefficient one, independent of the ports. Its output
is stored in [receipt.json](receipt.json). No Lean process is run.
