# Claims and validation boundaries

## Analytic theorems proved in article.tex

1. Exact invariant Fourier space and exact finite moment identity.
2. Strictly dominant, simple, positive Perron eigenvalue for every phase.
   The nonzero phase argument uses a finite backward-tree zero-set lemma.
   The exceptional phase c=0 is handled separately by an explicit spectrum.
3. Real-analytic Perron data, fixed-order uniform spectral gap, and moment
   asymptotics with uniform exponentially small relative error.
4. Identification with topological pressure using a cylinder-supremum /
   integral inequality, not an assumed general RPF theorem.
5. All-order missing Taylor coefficient, by the exact two-branch equation
   and the periodized-sinc eigenfunction at the atomic phase.
6. Phase-independent determinant and exact finite recurrences.

The finite checks support the algebra but do not prove these universal
statements in place of the written proofs.

## Exact finite certificate used in a proof

The sixth-moment optimization theorem uses rational Sturm calculations and
rational interval evaluations as part of its proof. The scripts verify the
characteristic polynomial directly from the matrix, then eliminate the
stationary eigenvalue. The linear subresultant has nonzero constant
content, so no parameter-dependent factor was silently divided away.
Three of the four stationary-eigenvalue candidates are excluded by the
analytic lower bound rho_3 >= 1/4. The remaining candidate must be the unique
global minimizer by the endpoint comparisons and compactness.

All four cosine root intervals and stationary-eigenvalue enclosures are
recorded in minimum_certificate.json. Decimal endpoints there are parsed
as exact rational numbers, never floating-point numbers.

## External dependence

The statements about Renyi dimensions use the pressure–spectrum identity
in Gohlke–Kesseböhmer–Schindler, Theorem 2.6. They are stated separately from
the self-contained finite-moment results. The identity is not claimed for
all real orders at c=0; only the integer extension used in the article is
justified there directly.

## What is not claimed

- No proof of real-analyticity for all noninteger positive orders.
- No phase-uniform-in-m gap as m tends to infinity.
- No new universal pointwise Fourier decay or unweighted shell asymptotic.
- No priority claim for classical moment matrices or classical recurrences.
- No numerical plot or floating-point optimizer used as a proof.
- No Lean implementation, kernel checking, or independent peer review.
- No guarantee that an equivalent new theorem is absent from all literature.

## Executed checks

- verify_pressure.py: 23 default test groups passed, including m=1..10 base
  spectra and m=2..6 exact Taylor jets through degree 2m+2.
- verify_minimum.py: all exact checks passed, including the fourth-moment
  comparison and sixth-moment local-maximum identity.
- The PDF was compiled with pdfLaTeX via latexmk. No undefined references or
  overfull boxes were present in the final build.
- Every PDF page was rendered and inspected in contact sheets; the cover,
  main coefficient identities, and optimization certificate were additionally
  inspected at larger resolution.
