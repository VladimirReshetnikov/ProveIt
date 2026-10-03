# Proof status and dependency boundaries

## Claims with conventional proofs in the article

1. Existence of the formal inverse and the frozen-parameter marked Lagrange
   expansion, with explicit degreewise finiteness.
2. The positive bare action saddle and its fixed real exponential tilt.
3. Arbitrarily strong algebraic suppression of the inverse remainder after
   a sufficiently large fixed analytic core.
4. The full signed inverse equivalent for an eventually exact quadratic tail
   and arbitrary finite real changes to weights and slopes.
5. Eventual negativity of the inverse coefficients in that model.
6. Sufficiency of any fixed core of size at least two for the leading
   equivalent; the one-action criterion w_2=0.
7. A finite exact two-action response formula in the pure model.
8. Coefficient ratio/root laws, zero convergence radius, exact Gevrey threshold,
   flatness in fixed positive factorial scales, and a formal least-term index.
9. Entire Borel continuation, its positive-ray and maximum-modulus equivalents,
   and divergence of the ordinary positive-direction Borel-Laplace integral.

The signed remainder estimate is the principal new proof step. Its bound is
not a transfer from a positive forward theorem. It combines an analytic core
estimate with an exact quadratic merger defect and counts the remaining
ordered tuples absolutely. The first-jet majorant is independent of the
auxiliary core size; the analytic neighborhood is allowed to shrink with
that fixed size. All limits keep the core and model data fixed.

## External dependencies

Classical analytic inverse/implicit-function theory, Cauchy's formula,
Lagrange inversion, Stirling estimates, and lattice Gaussian summation are
used with their hypotheses in the text. The key uniform estimates are derived.

Only the pure forward/inverse comparison in equation (6.7) additionally uses
the repository's forward coefficient equivalent. It is labeled as an external
dependency; it is not an input to the main inverse or Borel proof.

## Computation versus proof

The 32 recorded exact assertions validate finite algebraic and differential
identities. Coefficients are computed through degree 220 in four integer
models. Numerical ratios use mpmath at 80 decimal digits, not interval
arithmetic. These computations neither establish limit theorems nor certify
an onset value. The asymptotic arguments are conventional proofs, not
proof-assistant output.

## Not claimed

- A proof-assistant-checked development, independent peer review, or global
  originality/priority certification.
- A general theorem for subquadratic feedback or arbitrary regularly varying
  tails; the tail is exactly a*j^2 after finitely many exceptions.
- Uniformity when parameters or core sizes vary with the coefficient index.
- A complete first-correction or all-orders expansion.
- Quantitative finite-n error bounds with explicit certified onset.
- A general complex-direction Borel indicator, acceleration, Stokes theory,
  or summation theorem for these inverses.
- An analytic positive-real solution of the original divergent quadratic
  kernel obtained by ordinary termwise summation.
- An analytic optimal-truncation remainder theorem from the formal least-term
  index alone.

These remaining problems are described as further research, not used as
unproved intermediate claims in the main results.
