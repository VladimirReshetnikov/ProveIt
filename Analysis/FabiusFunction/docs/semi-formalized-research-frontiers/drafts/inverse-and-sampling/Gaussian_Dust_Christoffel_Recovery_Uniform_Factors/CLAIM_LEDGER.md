# Claim ledger

All items below have conventional proofs in `article.tex`. None is marked as
independently refereed or proof-assistant verified. The test script supplies
supporting finite algebraic checks only.

| Result | Label / location | Status and boundary |
|---|---|---|
| Exponential bounds and cumulants | `lem:subgaussian`, `lem:cumulants`, Section 2 | Classical formulas, proved and credited |
| Variance-weighted spectral representation | `thm:spectral`, Theorem 3.2 | A representation of the existing identifiability theorem; not a new uniqueness claim |
| Intrinsic maximal Gaussian factor | `prop:intrinsic`, Proposition 3.3 | Proved using bounded background and log-MGF growth |
| Compactification and TV topology | `prop:compact`, Proposition 4.1 | DUSTPAN compactification is prior work; smoothed TV reformulation proved here |
| Complete continuity locus | `thm:continuity`, Theorem 4.2 | Gaussian variance is continuous exactly at s=0 on the full class |
| Rank-free L1 expansion | `thm:dust`, Theorem 5.1 | Explicit remainder; W^(8,1) density sufficient; constants not claimed optimal |
| Leading dust TV asymptotic | `cor:dust`, Section 5 | Requires maximal half-length tending to zero, bounded total variance |
| Exact global minimax risks | `thm:minimax`, Theorem 6.1 | V/2 absolute and V^2/4 squared at every finite sample size; unrestricted rank |
| Exact local limiting minimax risks | `cor:localminimax`, Corollary 6.4 | Shrinking TV neighborhoods, sample size held fixed |
| Positive cumulant ladder | `thm:ladder`, Theorem 7.1 | Exact monotone bias identity and two-sided tail comparison |
| Complete compact-class criterion | `thm:criterion`, Theorem 8.1 | Compactness and smoothing are explicit assumptions |
| Christoffel spectrum recovery | `thm:christoffel`, Theorem 9.2 | Classical variational tool; model-specific tail bound and cumulant representation |
| Exact geometric bias | `thm:geometric`, Theorem 10.1 | Cauchy-determinant specialization; no independent priority claim |
| Bounded-coefficient noise bound | `thm:regularized`, Theorem 11.1 | Deterministic normalized-moment error; explicit lower head scales for tail bound |
| Envelope sampling rates | `thm:statbound`, Corollaries 12.3–12.4 | Attainable upper bounds only, not proved minimax-optimal |
| Pointwise estimator on full class | `thm:pointwise`, Theorem 13.1 | Consistent at each fixed parameter, not uniformly over the full class |
| Ten further research questions | Section 15 | Open proposals, not proved assertions |

## Validation exclusions

- Finite checks do not establish infinite-dimensional convergence.
- The Fourier diagnostic is not TV quadrature or a likelihood experiment.
- No efficiency guarantee is attached to the coefficient-grid minimization.
- The exact Christoffel upper bound is not claimed sharp under the additional
  integer-atom-multiplicity constraint of the uniform-factor model.
- The entire-sample distribution and individual factor spectrum are not
  interchangeable data objects; cumulant conversion is required.
- The fixed background is known exactly. Unrestricted unknown-background
  factorization is not covered.
