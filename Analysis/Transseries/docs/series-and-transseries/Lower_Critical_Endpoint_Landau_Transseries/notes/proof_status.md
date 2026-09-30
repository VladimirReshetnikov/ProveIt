# Proof status and audit boundaries

## Theorem-level content

The article gives conventional proofs, not just numerical conjectures.

1. **Exact confluence.** Pure polylogarithmic tails, 0 <= epsilon <= eta < 1/2;
   the coupling is fixed by an exact positive fold delta. The polylogarithm
   continuation formula is the classical analytic input. The pole cancellation
   and remainder estimates are derived explicitly.
2. **Uniform coefficient theorem.** Lambda = n A delta belongs to a compact
   positive interval. All Fourier arcs are controlled. No restriction on
   epsilon log(1/delta) is imposed. The rate O(delta^(1-eta)) is additive inside
   the normalized formula, and relative on those compact parameter sets.
3. **All-orders coefficients.** At epsilon = 0, each finite-order truncation has
   a uniform asymptotic remainder. Infinite-series convergence is not claimed.
4. **Inverse charts.** Actual convergence in delta and then E = exp(-1/c) in
   normalized inverse coordinates. Original-U coefficients can depend affinely
   on c; this is not analyticity in c at zero. The physical branch is specified.
5. **Gaussian matching.** A separate local-limit proof handles lambda -> infinity
   while keeping the exact fold location in the exponential factor. The leading
   compact-window profile alone acquires an exp(lambda delta/4) correction.
6. **Cutoff profile.** Epsilon -> 0, delta -> 0, lambda and M delta in compact
   positive windows. The full centering is retained when actions are removed.
7. **Sharp limiting loss.** Fixed lambda, then m -> infinity. The first Palm
   moment is evaluated by a positive endpoint integral, and the second factorial
   moment is proved negligible. This justifies passage from an expected count
   to a probability and yields the displayed prefactor.
8. **Tolerance inversion.** A statement about the limiting profile. There is no
   uniform finite-n error certificate at arbitrarily small target tolerances.

## Scope not covered

Boundary-critical and subcritical coupling paths with no positive fold;
finite-prefix or slowly varying tail universality; general complex Stokes
continuation; arbitrary arithmetic supports; unrestricted transseries
realization; effective finite-n errors at growing cutoffs; worldwide priority.

## Executed checks

43 exact Fraction/SymPy assertions, 24 90-digit normal-form comparisons,
9 coefficient cases, 9 cutoff cases, 6 large-lambda profile values, and
4 first-Palm-moment comparisons. All finite assertions passed. Numerical
quadrature values and plots are not interval-certified. No Lean module
was created, compiled, or claimed to verify these results.

## Particular sign and normalization checks

- Ordinary coefficients u_n, not n! u_n.
- The exact coefficient is (1/n) [t^n] exp(n c Li(t)).
- The U-coefficient contour has no extra exp(-delta s) amplitude.
- The omitted-tail compensator produces the positive argument a_m in g_m(a_m).
- The Landau convention is fixed by exp(z log z + x z).
- The first Gaussian profile correction is +1/(24 lambda).
- The first fold-value term is -delta/4, yielding a positive matching factor.
- The cutoff-loss prefactor includes exp(-m/(2 lambda)) and m^(-2).
