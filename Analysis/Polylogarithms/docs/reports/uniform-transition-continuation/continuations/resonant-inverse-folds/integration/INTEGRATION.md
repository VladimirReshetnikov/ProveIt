# Integration proposal

## Placement

Place this entire package, without auxiliary TeX build files, at:

    Analysis/Polylogarithms/docs/reports/resonant-polylogarithm-inversion/

Cross-link it from:

    Analysis/Transseries/docs/series-and-transseries/README.md

Do not merge its named results into the canonical volumes as accepted
without statement-level mathematical review. The existing classical and
fixed-order results should retain their attribution.

## Suggested registry text

> **Resonant Polylogarithm Inversion** studies normalized Taylor remainders
> of `Li_(n+1+epsilon)(exp(-t))` as the order approaches an integer. It proves
> a pole-cancelled order-jet formula, a convergent primary inverse chart,
> and an exact Gamma–zeta critical locus at every positive integer `n`.
> At the nonzero scaled-order resonances `lambda = 2*pi*i*k`, the dilogarithm
> alone is an undetuned fold. The article constructs a convergent two-sheet
> chart, computes the moving critical order, and gives the leading
> coefficient of every exponential sector. Conventional proofs are
> supplied. The accompanying replay has 150 finite exact algebra checks
> and 73 floating-point diagnostics at 180 digits, not interval
> certificates or Lean formalizations. Publication novelty remains subject
> to a broader literature review. Its targeted audit confirms an already
> recorded historical correction and establishes no new false current
> canonical theorem.

## Statement-level review order

1. Verify the definition and sign of the normalized remainder and its
   Gamma/zeta pole cancellation. This determines every later sign.
2. Check the analytic parameter domains, logarithm-sheet convention,
   normal convergence, and the primary compact-uniform implicit-function
   argument. The primary chart excludes all nonzero zeros of A(lambda).
3. Check the two-equation elimination for the core critical locus and
   the first full-tail displacement. Keep core and full formulas separate.
4. Check the two-root contour moments, discriminant factorization, and
   the exceptional n=1 classification.
5. Check the substitution eta=v*r, the analytic square root after dividing
   D by v, and coefficient extraction for the all-action leading law.
6. Replay the finite computations as diagnostics and coefficient checks,
   not substitutes for the preceding analytic proofs.

The machine-readable dependency/status inventory is `RESULT_STATUS.json`.

## Branch and normalization requirements

The target family subtracts the first n analytic Taylor terms. For n>=2,
the raw difference `zeta(n+1)-Li_(n+1)(exp(-t))` has a nonzero linear term
and is not the same inversion problem. Do not omit the subtraction when
copying the theorem.

The primary complex chart is on the logarithmic sheet specified by its
chosen `log A`; when the domain contains zero, normalize `log A(0)=0`.
The headline dilogarithm roots are both near a positive t and on the same
original logarithm branch. They are two roots of one equation, not two
input branch choices.

Exponential sector statements refer to coefficients of an analytic
independent sector variable. A finite algebraic truncation is insufficient
to isolate an exponentially small term. Local square-root branch
interchange is not a Stokes jump.

## Historical source handling

The historical bridge abstract already has a canonical correction.
Use `HISTORICAL_SUPERSESSION_NOTE.md` only as an explicit pointer for
standalone distributions; do not claim a new correction discovery or
silently rewrite preserved archival evidence.

## No remote mutation

The delivery has not committed, uploaded, opened a pull request, or changed
any existing ProveIt file. The suggested location and text are proposals.
