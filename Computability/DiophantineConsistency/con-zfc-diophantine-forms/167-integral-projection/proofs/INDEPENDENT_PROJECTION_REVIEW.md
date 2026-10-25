# Independent review of the frozen 218-variable quartic

Prepared on 25 October 2026 by a separately assigned AI research agent. This is an ordinary mathematical and executable-artifact review, not external peer review or a newly compiled Lean/Rocq certificate.

## Reviewed object and conclusion

The reviewed equation is `compression_work/package/equation/equation.json`, SHA-256

```
998edb5ba0c94778dbc5ccca5bdac5d51034bc3955e98044651d3b9416c7fa94
```

Its collected quartic has SHA-256

```
e7f9b777bc324ed0bfb28ed144465404b7bd05740586e0a600c11db905f00310
```

I found the seven coordinate eliminations and the subsequent centering and row operations mathematically sound over unrestricted integers. The finite replay passed. The final object has 218 variables, 155 quadratic residuals, 1,296 residual terms, exact degree four, 14,410 collected monomials, residual coefficient height 1,920, and polynomial coefficient height 5,023,040.

The conclusion established by this review is an integral bijection between the zero set of the pinned 225-variable parent residual system and the zero set of this 218-variable system. The parent's Diophantine-to-C222-to-ZFC calibration remains an identified imported mathematical theorem. The new algebraic work does not independently replace that calibration or prove that either zero set is empty.

## Why the five common-Hessian projections are valid

For a quadratic residual R, if its Hessian annihilates an integer vector d, then the exact identity is

```
R(y+t*d) = R(y) + t*(linear_part(R) dot d).
```

At each recorded step a coordinate p has d[p]=1, and a selected residual has slope +1 or -1. Put old_x[p]=t and old_x[i]=y[i]+d[i]*t for i different from p. This is an integral unimodular change of variables. The selected row is `a*t+q(y)`, with a=+1 or -1, so its unique restoration is `t=-a*q(y)`. The common-Hessian condition ensures that every other transformed residual has coordinate-independent t-slope; substitution therefore keeps its degree at most two.

The inverse projection on old solutions is `y[i]=old_x[i]-d[i]*old_x[p]`. Thus the transformation has both an integer restoration and an integer inverse on the zero loci; no rational-division or sign premise is missing.

In each successive input's own zero-based coordinates, the five directions are:

- `e44-e45`, slope +1;
- `e60-e61-2*e62`, slope -1;
- `-e62+e64`, slope +1;
- `e31-e32-2*e33`, slope +1;
- `e25-e27-2*e28`, slope +1.

These remove five variables and five rows: 225/162 becomes 220/157. The local coordinate conventions must be retained; the displayed indices are not all indices of the original parent.

## Why the two affine projections are valid

The certificate gives exact integer combinations of existing residuals whose normalized results are affine and have a unit coefficient on the selected coordinate. Solving that affine equation therefore gives an integer affine restoration. Substituting it preserves degree two even in rows that previously used the coordinate quadratically.

The omitted residual is recoverable from the recorded combination: after restoration that combination vanishes, every retained residual vanishes, and the omitted residual's net coefficient is nonzero. In the two actual records these net coefficients are respectively +1 and -1. I checked the net coefficients, not merely the presence of a row index in the combination. Thus there is no cancellation loophole in the supplied certificate.

The first projection eliminates local coordinate 95 and the second local coordinate 34. Together they give 218 variables and 155 rows. No nonnegativity assumptions are needed or introduced.

## Centering, residual basis, and the single equation

The final coordinate replacement is the integral affine shear

```
old_x21 = new_x21 + 2 + 6*x9 + 8*x10 + 2*x20.
```

Its inverse subtracts the same correction. The 43 following row operations are of the form `Ri <- Ri+k*Rj`, with integer k and distinct row indices; subtracting `k*Rj` is the inverse operation. These preserve the simultaneous zero set. They change the particular sum-of-squares polynomial, so equality of the old and new polynomials is not claimed.

For integer inputs, a finite sum of integer squares is zero exactly when all of its summands are zero. Therefore the simultaneous residual equations are equivalent to the supplied single quartic. This last step uses the ordered-integer domain; a claim about complex zero sets of the sums of squares would be incorrect. The intermediate residual zero-set projections themselves remain algebraic, but the final sum-of-squares interpretation is specifically over integers (or another ordered field).

I checked that the actual input and final residual monomials have canonical sorted indices, no repeated monomial entries, and indices within their declared coordinate range. The independent exponent-vector verifier reconstructed every final quartic coefficient and rejected its four supplied perturbations. The review receipt is `frozen218_verification.json` beside this note.

## Scope of the Macaulay rank result

I read the sparse modular elimination implementation and reran it on the frozen final equation, rather than relying only on the earlier uncentered presentation. Let M be the matrix whose rows are the degree-two and degree-three coefficient vectors of

```
R_i, x_0*R_i, ..., x_217*R_i       (i=0,...,154).
```

The run processed all 33,945 rows, found rank 33,945 modulo 1,000,003, and reported no skipped rows, no timeout, and no affine remainder. A full-rank minor modulo a prime is a nonzero integer minor, so M also has full row rank over the rationals.

Consequently no nonzero combination `sum_i L_i(x)*R_i(x)` with affine rational multiplier polynomials L_i can be affine. This includes the constant-multiplier search and answers the specific degree-three affine-consequence question for the supplied presentation.

It does not prove minimum arity. It does not exclude higher-degree multipliers, a different quadratic presentation, nonlinear changes of variables, consequences in a real radical, or semantic changes to the proof encoding. For example, a positivity argument may force a linear relation that is not in the ordinary residual ideal. The rank calculation says nothing against such a possibility.

An additional modular exploratory closure generated 196 new quadratic consequences and stabilized at 351 quadratic rows without an affine consequence. That experiment was not lifted to a complete rational certificate and should remain a research note, not an additional theorem of this release. The separate exact expansion of the first thirty gates was incomplete at higher degree and likewise supplies no general exhaustion claim.

## Evidence boundary

All new transformations are finite integer-polynomial identities and integral coordinate maps, hence their ordinary proofs are formalizable in ZFC without a consistency assumption. Composing them with an internally formalizable proof of the parent's calibration yields the requested consistency equivalence for this polynomial. The algebraic replay alone proves only the transfer from the precise pinned parent, whose SHA-256 is

```
fee84c408828aba3e7ceebe9a37f58509327063aa7fd078fd49c80adf3af4e56
```

It does not certify the whole inherited proof-assistant dependency closure, establish worldwide novelty, or justify calling this polynomial globally simplest.
