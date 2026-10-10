# Mathematical review record

This record concerns the delivered research continuation, not an external
refereeing or proof-assistant certification of the full ProveIt manuscript.
Separate AI-assisted reviewers rederived the central arguments before final
assembly; the mathematical proofs and replay programs are supplied so that
the conclusions can be independently assessed.

## Reviewed arguments

- **Kernel extrema:** uniqueness and nondegeneracy of the limiting profile;
  uniform envelope convergence; exclusion of escaping maximizers; analytic
  continuation in 1/N; strict first correction; boundary exclusion at finite
  N; exact N=2 gradient and subresultants.
- **Order-averaged extrema:** the inherited a ≥ 1 constant-one input; uniform
  exclusion below the logarithmic cutoff; strict axis comparison above it;
  axis localization and C² convergence; threshold Mellin prefactor and first
  inverse-log correction; displacement sign; the necessary and sufficient
  near-maximizer conditions.
- **Appell/Lerch zeros:** ordered-root motion versus Riesz mesh preservation;
  Laguerre spacing and largest-root estimates; remote factor block and
  passage to the gamma-product limit; gamma logarithmic moment estimate;
  harmonic root distances; the global multiplicity-counting argument and
  the joint-growth constant 1/sqrt(60).
- **Negative orders:** independent exact differentiation for q2, q3, q5;
  beta/eta coefficients; the Mellin one-crossing argument and endpoint
  signs; exact b=1 evaluations and the two q5 kernel roots.
- **Mixed generator:** shift signs; cyclotomic factors and branch convention;
  ordinary convergence at weight two; even samples, odd finite parts,
  the essential pole-times-linear-term contribution, and the t=3
  subtraction constant; consistency of the S14 normalization and tails.

## Revisions made during review

Two malformed TeX fraction commands were repaired. An expectation was made
explicit in a displayed compact-parameter comparison. The Gaussian rational
sampling proof now includes an explicit ordinary-convergence argument, and
the local finite-part sequence was renamed to avoid conflict with the main
Euler constant C_N. The elementary reciprocal-polynomial proof of the two q5
kernel roots was added. These are revisions of this draft, not accusations of
errors in the inherited source.

No theorem-level error was identified in the reviewed final arguments.
That assessment is limited to the arguments listed above and does not imply
an exhaustive audit of all source material or a claim of literature priority.

## Computational corroboration

The delivered replay report records four exact-arithmetic checks and five
optional numerical/symbolic diagnostics. In particular, the S14 certificate
reconstructs exact rational endpoints from the frozen integer vector and
proves an absolute normalized residual bound below 10^−775. An interval
containing zero is not a proof of the conjectural equality.

The standard-library certificate programs use unconditional error checks.
Numerical stationary points, high-precision zero decimals, and quadrature
residuals remain diagnostics with their stated precision and scope.
