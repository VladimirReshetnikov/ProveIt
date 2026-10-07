# Theorem and verification status

Date: 2026-10-07.

**All general mathematical assertions below have human-readable proofs in
`article.tex`. None is accompanied by a newly compiled Lean proof.**
The results are supplied for independent review. “Proved in the manuscript” is
not a claim of independent peer review or exhaustive literature novelty.

| LaTeX label | Assertion | Validation / dependence |
| --- | --- | --- |
| `lem:twomarked` | Two Gowers factors and one L2 factor control a progression average | Fourier base case; complete Cauchy–Schwarz induction |
| `prop:upper` | A non-optimal quadratic symmetric upper bound | Two-marked estimate and exact balanced expansion |
| `thm:partition` | General first-dependent-subset partition asymptotic | Analytic proof with exact centering and a finite Taylor remainder |
| `lem:tripleexpansion` | Triple leading term; higher-slot O(n^-1) error | Analytic partition method |
| `lem:cubegeometry` | First binary-cube dependencies and four-circuit count | Algebraic proof; small finite-field rank checks |
| `prop:Prec` | Exact recurrence for circuit partitions | Elementary bijection; exact computations through dimension four |
| `lem:circlemoments` | Circle local moments | Finite Fourier orthogonality; exact small checks |
| `lem:spikemoments` | Spike rank expansion | Finite expansion and rank-nullity |
| `cor:fieldmoments` | Field triple and four-circuit moments | Rank expansion; exact finite checks |
| `prop:weighted` | Weighted count and norm asymptotics | Partition theorem and local moments; optional high-precision tests |
| `lem:transfer` | Bounded-frequency torus-to-cyclic identities | Signed-radix proof; exact small radix checks |
| `prop:primeweighted` | Weighted examples at every large prime | Explicit Taylor truncation and no-aliasing transfer |
| `lem:rounding` | Indicator rounding with exact size | Written finite-probability proof; no huge rounded set enumerated |
| `thm:field` | Fixed-field indicator examples | Weighted asymptotics and rounding |
| `thm:prime` | Prime-cyclic indicator examples | Transfer, recentering, and rounding |
| `cor:barrier` | No uniform o(u^2) error | Positive limiting ratio from `thm:prime` |
| `thm:universal` | One sequence for all fixed lengths/orders | Diagonal construction; no uniform growing-parameter claim |
| `prop:largerR` | Divisor-sum improvement to the attainable coefficient | Exact Fourier moment counts and divisor grouping |

## Computational record

- 8,916 selected exact finite checks: passed.
- Additional exact recurrence values: P2 = 1, P3 = 6, P4 = 635.
- Optional 90-digit characteristic-function comparisons: passed at
  n = 16, 64, 256, 1024, 4096.
- Numerical tests are not interval-certified.
- Finite tests do not prove the general analytic asymptotic theorem.

## Explicit exclusions

- No new global bound for progression-free subsets of intervals.
- No independent validation of the full OpenAI quasipolynomial Szemerédi proof.
- No new Lean formalization and no rerun of either repository's full audit.
- No claim that the attainable coefficients are globally optimal.
- No exhaustive worldwide priority determination.
