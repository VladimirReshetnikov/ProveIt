# Proof audit and dependency boundaries

## Central claim

For arbitrary positive weights N with N[0] = 1, let S be their finite
max-product (least supermultiplicative) envelope. When N[n]^(1/n) tends
to infinity, the coefficient h[n+1](C) of the positive extremal inverse
satisfies (h[n+1](C)/S[n])^(1/n) -> 1 for every fixed C > 0.
The article also proves the weaker sufficient hypothesis that the
primitive roots are merely unbounded, equivalently S[n]^(1/n) -> infinity.

The argument uses:
1. A finite Lagrange formula, with excess degree n and ordinary degree n+1.
2. Sublinear length of every maximizing composition.
3. A finite sparse/dense inequality, valid without limiting hypotheses.
4. Subexponential sparse entropy and dense suppression against S.

The full root limit of N, not just unboundedness, is still necessary for
universal type invariance. The inverse of z-z^2 proves this necessity.

## Conclusions established by conventional proofs

- Complete scalar arbitrary-weight zero-loss classification.
- Exact optimal universal inversion distortion, including failure at
  type zero and the infinite-type endpoint.
- Minimal envelope repair up to subexponential domination.
- Exact maximum law for composition when the two types differ, and a
  complete possible-output spectrum when the input types are equal.
- Invariance under divergent type-zero coordinate changes.
- Dimension-free formal Banach-map inversion and composition for the
  explicitly chosen symmetric multilinear operator norm.
- Sharp two-sided general-Jacobian bounds, with an example proving that
  a matrix and one scalar type do not determine the inverse type.
- Explicit separating weights with complete proofs of their envelopes.

## Sensitive points checked in the written argument

- Every coefficient computation is finite; there is no interchange of
  unconditionally infinite sums.
- The positive amplitude C is fixed before taking a limit; C < 1 is
  handled by sparse maximizing partitions, not by h >= S.
- A full root limit is used in the one-part replacement proof; the
  unbounded-root strengthening replaces by a whole maximizing partition.
- B and eta are fixed before the degree tends to infinity; eta tends to
  zero only after that limit.
- The geometric dilation divides excess-degree coefficients by A^n.
- The ratio S/N need not be bounded in the central theorem.
- Minimality among all admissible majorants is only asymptotic. Exact
  pointwise minimality applies to supermultiplicative majorants.
- Symmetrization is normalized by 1/m!, and the coefficient norm is
  multilinear, not an unacknowledged diagonal polynomial norm.
- The finite bivariate implementation uses a separate coefficient-l1 norm
  satisfying its own scalar-majorization inequality.
- No equality under a general Jacobian is claimed beyond the sharp bounds.

## What is not claimed

No Lean formalization, independent peer review, exhaustive priority check,
analytic realization, angular summability, Stokes data, optimal truncation
error, arbitrary Hahn-support theorem, or polynomial bit complexity.
The finite tests audit formulas and examples, not limiting assertions.
Classical Lagrange inversion and classical nonlinear class stability are
explicitly credited. No unverified upstream theorem is used as a premise.
