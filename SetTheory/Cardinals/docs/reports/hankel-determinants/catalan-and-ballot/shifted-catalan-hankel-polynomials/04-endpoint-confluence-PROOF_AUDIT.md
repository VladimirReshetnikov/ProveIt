# Proof audit and trust boundary

This is a mathematical dependency audit, not a proof-assistant certificate.

## Universal proof chain

1. **Moment normalization.** A beta integral gives the Catalan moments.
   Half-integer sine orthogonality fixes the monic orthogonal polynomial
   norms at one. The two trigonometric formulas are checked against the
   polynomial recurrence.

2. **Christoffel reduction.** A Gram integral and Laplace expansion of an
   enlarged Vandermonde yield the fixed-size determinant. This is a
   classical identity. Alternation and normalized Taylor rows justify
   confluence, including factorials and cross-block powers.

3. **Exact centered alternant.** Apply the ordinary Vandermonde identity
   to nodes -exp(h u_i) and exp(h w_a). Centering the columns cancels
   every exponential prefactor. The remaining product of sinhc and cosh
   functions is even and generates every coefficient.

4. **Analytic removal and parity.** Distinct derivative orders within
   each cluster force a zero of order rho. Coordinate alternation removes
   each Vandermonde. Column reversal proves exact evenness after dividing
   by h^rho. The remaining denominators are nonzero at h=0, uniformly on
   compact coordinate sets. This supplies convergent Taylor series, not
   merely formal asymptotic expansions.

5. **First correction.** The quadratic term of the exact alternant gives
   the five coefficient-minor ratios. The row differential equation and
   determinant differentiation reduce them to derivatives of the base
   kernels. The geometric denominator correction is included separately.
   No division by the leading kernel is used.

6. **Effective uniformity.** Explicit power-series bounds control all
   denominator factors. Divided differences and Cauchy estimates bound
   the numerator even at collisions. A Cauchy geometric-tail estimate
   then gives the stated error bound.

7. **Positive profiles.** Cauchy–Binet applied to the entire cosine/sine
   series produces a positive Schur expansion. The coefficient of the
   first symmetric power sum is strictly positive. The diagonal majorant
   gives convergence on complex compact sets.

8. **Sharp outward threshold.** Finite-size Gram-integral monotonicity
   combines with the compact-limit theorem and the positive Schur
   expansion. The divergence statement compares with arbitrarily large
   fixed scaled displacements; it does not assume uniform asymptotics at
   unbounded scaled coordinates.

## Delicate conventions checked

- Degree d means the total degree of the multiplier, not the determinant size.
- The effective size is N + d/2.
- The upper endpoint contributes binom(ell+1,2); the lower contributes binom(m,2).
- The sign removed from H_N is (-1)^(N ell).
- Repeated coordinate rows use derivative/factorial; kernel derivative
  columns do not.
- Square-root notation is defined by entire power series.
- Leading-profile zeros cause no singularity in the first-correction formula.
- Original N-based scaling has an N^-1 correction even though the centered
  formulation has only even inverse powers.
- Outward nonnegative displacements are essential to the sharp iff criterion.

## Computation

The recorded suite has 710 exact checks and 100 high-precision diagnostics.
The original and Christoffel determinant paths use different mathematical
constructions but share scalar Gaussian elimination. The coefficient-minor
checks are independent of the first-correction kernel formula. The
high-precision tests include repeated roots, zero coordinates, inward roots,
and complex coordinates.

No Lean, Rocq, interval-arithmetic, or external peer-review certification is
claimed. The shipped code is a verification program, not an optimized
all-orders computational library. Worldwide novelty remains unestablished.
