# Positive folded-root zeros map to positive 88-graph zeros

This source-level mathematical argument is submitted for independent review.
For arbitrary integer fixed ports with **beta > 0**, every strictly positive
zero of the 86/26 folded-root graph yields a strictly positive zero of its
88/30 parent. The maps preserve the other twelve inputs and use
`r_old=rho+k*Bt`. The converse existence implication remains open; the
independently reviewed full toy-port zero already shows that the direct
inverse can fail with the other twelve inputs fixed. No new Lean/iPRA theorem,
PDF/file binding or compact44 zero is asserted.

In the 86 source, the input slot named `r` denotes `rho`. For positive inputs
and beta>0, let `b=J*beta`, `q=1+b`, `M=q³*b`, `k=eta+zeta` and
`ell=E*Y*k`; all are positive and `k>=2`. The first residual is

```
Z = M*(ell+k+rho) + Y*b − q³*Bt,
A0 = Z² − M²*(1+ell*(ell+k)).
```

The final output is a sum of four integer squares, so any zero has `A0=0`.
Suppose for contradiction `Bt<=0`. Since rho,Y,b,M are positive,

```
Z > M*(ell+k) > 0,
[M*(ell+k)]² − M²*(1+ell*(ell+k))
    = M²*(ell*k+k²−1) > 0.
```

Thus `A0>0`, a contradiction. Hence **Bt>0** on every positive 86 zero, and
`r_old=rho+k*Bt>0`. The independently reviewed polynomial substitution in
`../ordinary13-folded-root86-probe/` gives equality of the two outputs over
all integer inputs. It follows that the substituted positive tuple is an
88 zero. This uses no condition on K0, MC or MF and no Pell/transport theorem.

The reverse implication would require a possibly different positive 86 zero
for every positive 88 zero; neither the above sign argument nor the toy-port
same-other-coordinate obstruction decides it.

The checker pins both exact source graphs, checks the two-row fold and all
other source rows and inputs, and exhaustively tests small positive controls
for the first-residual sign implication. These checks support but do not
replace the unbounded algebraic argument above. No Lean run is made.

Independent external review is recorded in
`../../reviews/ordinary13-folded-root86-positive-reverse-independent/`.
