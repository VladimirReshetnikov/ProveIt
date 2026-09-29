# Proof and verification status

## Assumptions

The main theory assumes a_j = a/j^3 + delta_j >= 0, a > 0, a_1 > 0,
with only finitely many nonzero delta_j. Finite perturbations can be signed
as long as the actual weights remain nonnegative. The critical coupling,
normalization, and large Lambert-W branch are specified in the article.

Uniform expansions are for a fixed compact real coupling window and a
fixed compact positive normalized-cutoff interval. A moving beta window
uses rho_n as a boundary normalization, not necessarily the true radius.

## Proof structure

- Formal Lagrange inversion gives the exact coefficient identity.
- A compound-Poisson interpretation gives positivity, cutoff monotonicity,
  and an exact retention ratio.
- The integer polylogarithm expansion is derived by differentiating three
  times; the local remainder is holomorphic in a disc of radius 2 pi.
- Analytic implicit functions and a quantitative contraction give the
  convergent Lambert-core chart and a geometric tail estimate.
- Explicit Fourier damping from the positive exact tail controls all
  complementary frequency ranges in the local limit proof.
- Gaussian-logarithmic integral coefficients give the full fixed-order
  asymptotic expansion.
- A truncated triangular-array Gaussian estimate, through absolute error
  O(H^-3/2), gives the cutoff ratio and finite-prefix cancellation.
- Monotonicity upgrades the compact profile to the entire cutoff trichotomy
  and permits inversion of the threshold to obtain the minimal budget.
- A Poisson shift identity and an elementary Fourier majorant give a separate
  finite-n inequality; this does not depend on asymptotic remainder constants.
- Analytic Riemann sums give finite-fold drift and curvature with algebraic
  errors, while a separate reduced logarithmic equation has a convergent series.

## Exact checks

Main program: 96 independent rational partition comparisons, four reduced
inverse-equation coefficients, one cubic cancellation, and one critical
cutoff-correction cancellation: 102 checks.

Supplementary program: eight finite-fold residual coefficients and one
moving-window prefix cancellation: 9 checks.

The count is 111 finite exact checks, including simple zero-degree residual
identities. It is not an infinite formal proof or a theorem count.

## Numerical checks

Main run: 50 decimal working digits. Supplementary: 40.
Gaussian moment constants, independent n=256 recurrence comparisons,
Lambert inverse roots, sector coefficients, cutoff ratios, moving coupling
windows, finite-fold roots and curvatures, and finite-inequality diagnostics
were evaluated. Both scripts completed successfully.

The numerical model covers a=1 and two prefixes delta_1=0,1/2. It is a
subclass of the theorem's assumptions. Quadrature and analytic-series
truncations are finite and not enclosed using interval arithmetic.

## Explicit limits

No Lean verification, independent peer review, or exhaustive novelty audit.
No claim that the all-orders Gaussian-log expansion converges or is Borel
summable. No arbitrary-support transseries closure theorem. No signed-weight
cutoff extension. No global complex singularity classification. No certified
floating-point enclosures are produced by the supplied scripts.

All new analytical claims rely on the conventional proofs in the article.
