# Claims and validation boundary

## Mathematical claims proved in the article

1. Critical square-root pressure and splitting of the two central eigenvalues,
   for every integer base b >= 2 and every error exponent 1-eta with
   0 < eta < 1/2.
2. Exact pointwise Hölder exponent 1/2 at the critical atomic phase. This is
   not a claimed two-point C^{0,1/2} theorem on an entire neighborhood.
3. Explicit digamma generalized eigenfunction; rank-two commuting projection;
   a genuine size-two Jordan block; and exponential complementary decay on
   C^alpha for 0 < alpha < 1.
4. Uniform detuning with s-1 = u sqrt(|c|), for bounded u; an operator-norm
   finite-size crossover for bounded rescaled time n sqrt(|c|).
5. Explicit linear cusp for every fixed 1/2 < s < 1, via a localized scalar
   integral and a controlled norm-square spectral perturbation remainder.
6. A singular-translation integral valid for all 0 < s < 1 and masks with
   finitely many simple zeros; the linear spectral response is only proved
   in the smaller range in item 5.
7. A cylinder-supremum/integral comparison for digital polynomials at every
   positive absolute-moment exponent, including exponents below one.

## Prior work, not claimed as new

- The binary atomic pressure max{(1-2q) log 2, 0}.
- Positive-order phase continuity and the order-two analytic case in the
  cited Gohlke/Kesseböhmer/Schindler and Gohlke/Lamprinakis/Schmeling papers.
- The repository predecessor's supercritical phase expansion and its
  integer-order results.
- General Riesz projection and matrix perturbation technology, elementary
  subharmonic-function inequalities, and standard special-function identities.

## What has actually been executed

- `code/verify.py --full` ran successfully.
- 120 generalized-eigenfunction checks at 70-digit working precision, maximum
  absolute residual less than 1.3e-67.
- The digamma/cosecant integral for ell(1), with a stated endpoint cutoff.
- The singular-integral beta/digamma representation at three subcritical
  exponents. The largest raw quadrature discrepancy is about 3.18e-7.
- An exact symbolic check of the 2x2 generator characteristic polynomial.
- Sparse collocation pressure checks in bases 2, 3, and 5.
- Fixed-exponent subcritical checks, detuned crossover checks, finite-size
  matrix iterations, and mesh-doubling comparisons.
- LaTeX compilation and visual PDF inspection.

The data files record actual floating-point outputs; they were not generated
from the target theorem formulas alone. Predicted limits are separately labeled.

## What these checks do not establish

- They do not independently verify every infinite analytic estimate.
- Matrix residuals do not bound the discretization error of the transfer operator.
- Mesh agreement does not provide rigorous interval enclosures.
- Compiling a PDF is not mathematical verification.
- No Lean or Rocq proof has been compiled for this new article.
- The literature search does not establish worldwide priority.

## Explicit open boundaries

- Pressure response for 0 < s <= 1/2.
- Next-order critical coefficients and explicit constants in the remainder.
- Uniform matching when the detuning parameter tends to infinity.
- Full local two-point endpoint Hölder regularity.
- Regularity at arbitrary nonzero phases.
- A general theorem for other digital masks or higher Jordan collisions.

The paper is a substantive research draft with supplied proofs, not a claim
of independent peer-reviewed or formally certified completion.
