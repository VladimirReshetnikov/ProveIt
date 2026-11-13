# A leading-form obstruction to low-degree residual shears

This is a bounded external obstruction, submitted for independent review. At
the authenticated compact44 port integers, no integer-polynomial coefficients
`P,Q,S` of total degrees at most 2, 2, and 5 can make

```
A0' = A0 + P*A1 + Q*(Fa−1) + S*g72
```

have total degree less than 15. Thus this family of exact residual shears
cannot lower the degree of the dominant first square in the 88/30 graph. It
does not exclude other circuits, simultaneous changes to other residuals,
higher-degree multiplier cancellations, positive-domain-only reductions,
or global improvement. No Lean, iPRA, PDF/file-semantics, or minimality claim
is made.

## Degree conventions and argument

Treat all 13 witness coordinates as degree-one indeterminates and the four
compact44 port integers as degree-zero constants. The reviewed first-residual
cancellation proves `deg(A0)<=15`. For the main residual set
`W=U*X+H*shift` and use the exact identity

```
A1 = 2*U*a*c*W + W² − U²*(1+H*c²).
```

The source gives `deg(U,a,c,H,shift,W)<=(3,2,2,2,4,6)`; hence
`deg(A1)<=13`. The auxiliary residual `Fa−1` has degree at most 13 and
`g72` has degree at most 10. A generic all-ones witness ray modulo the prime
1,000,000,007 gives their respective degrees 15,13,13,10, confirming these
bounds are attained at the actual fixed port bytes.

Now work modulo the same prime and substitute every witness by a constant
times t. Use coefficient 1 for all witness variables except

```
f=0, i=0, u=0, gamma=−beta*(beta−1)   (mod prime).
```

Here beta is the actual compact44 beta reduced modulo the prime. Direct
whole-graph evaluation gives

```
A0: [t^15] = 142738814,
A1: [t^13] = 0,
Fa−1: [t^13] = 0,
g72: [t^10] = 0.
```

Thus on this ray their degrees are respectively 15, at most 12, at most 12
and at most 9. Polynomial substitution cannot increase degree, so on the
same ray all three allowed correction terms have degree at most 14, whereas
A0 retains its nonzero degree-15 term. Consequently A0' cannot have integer
polynomial degree below 15. Using a modular ray is valid even though some
witness coefficients are zero: an exact identity between integer
polynomials would hold over the finite field at every valuation.

## Reproducibility

The checker pins the 88/30 graph, authenticates all P72 and P115 port hashes,
verifies the exact main cancellation in a sparse integer-polynomial ring,
computes all four generic and annihilating ray polynomials, and records their
coefficients. It does not run Lean or establish a same-zero theorem beyond
the displayed residual-shear observation.

Independent external review is recorded in
`../../reviews/ordinary13-88-residual-shear-obstruction-independent/`.
