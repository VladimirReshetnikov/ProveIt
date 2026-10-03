# Validation record

## Mathematical review performed while preparing this article

The following dependency-sensitive points were checked explicitly:

- The Lagrange coefficient is `(1/n)[t^n] exp(n c A(t))`, not a derivative
  expression with an extra factor of n.
- Truncated coefficients use the original critical coupling. Their probability
  recurrence retains the original zero-count probability, including the tail.
- The dense no-large-action estimate contains a local `1/b` factor. A mere
  tail Chernoff bound would not suffice for all allowed growth rates of b.
- The sparse no-large-action estimate retains a factor of lambda even when
  lambda tends to zero arbitrarily fast.
- The mean-defect center uses the full finite prefix. Only after criticality
  is invoked, and b exceeds the prefix, does it equal a pure Hurwitz-zeta tail.
- The sign and location of the 1-stable law were fixed by its compensated
  Levy integral. The largest-action fluctuation is its reflection.
- The point process and the compensated sum are joint limits, not independent
  random objects.
- Exact centering D and leading scale d differ by logarithmically many b
  widths; they are not interchangeable in a quantile.
- Total variation is not used to infer convergence of unbounded moments.
- The fixed-prefix limit is invisible in the standardized dense cloud but
  remains visible in the sparse compound-Poisson law.
- The exponential coefficient normalizer rho^(-n) is kept exact.
- The limiting analytic endpoint has c=0 and U=0; it is not presented as a
  nonzero critical function.

This is an internal preparation audit, not independent peer review or a
formal verification certificate.

## Exact finite computation

The full `verify.py` run passed 62 exact algebra assertions:

- 36 rational identities comparing the feedback solution and Lagrange formula
  through degree 12 in three models.
- 24 rational identities comparing multiplicity-vector enumeration and the
  same coefficient through degree 8 in those three models.
- 2 symbolic identities for the first two chart coefficients.

## Floating-point diagnostics

The recorded JSON includes coefficient comparisons, genuine triangular
sequences, bounded-intensity sequences, finite-prefix perturbations, cutoff
ratios, the normalized stable CDF, chart reconstructions, and centering shifts.
None uses directed rounding. Numerical integration error estimates are not
rigorous enclosures. The script tests for nonfinite or underflowed probability
values and gives a separate output name for a quick run.

## PDF quality assurance

The final source was compiled in three pdflatex passes. The final log contains
no undefined citations or references and no overfull boxes. The document has
24 A4 pages and embedded Type 1 fonts. Rendered pages were inspected, including
the compact table of contents, principal theorem, local probability proof,
sharp cutoff formulas, numerical tables, and bibliography.

Build artifacts and page-rendering images are intentionally excluded from the
research ZIP.
