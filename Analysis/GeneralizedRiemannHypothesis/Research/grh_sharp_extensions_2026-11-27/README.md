# Sharp congruence bounds and finite prime sampling

Research package prepared for Vladimir Reshetnikov, 27 November 2026.

## Read first

`report.pdf` is the complete research report. Its editable source is
`report.tex`, with four substantive sections and a bibliography in `sections/`.

The main result is the sharp finite-precision estimate

    length(H_n) <= min(n, a) + (d^2 - 1) min(n, e)

for congruences between two integral representations with full rational
matrix spans. Here `a` is trace-congruence depth and `e` is the smaller
matrix-order containment exponent. This is unconditional algebra, and
the report proves sharpness at every precision. It extends the Article's
maximal-order trace theorem to nonmaximal image orders.

The second result constructs a positive finite grid of prime statistics
recovering central-zero multiplicities under Dirichlet GRH, with error
`O((log N)^3 / N^2)` from `N` underlying ramp samples for fixed-family gap
constants. A prescribed schedule that does not use zero data has the
slightly weaker polylogarithmic factor stated in the report. Every fixed
grid retains the one-sided zero detector.

## Contents

| Path | Purpose |
| --- | --- |
| `report.pdf`, `report.tex`, `sections/` | Complete statements, proofs, source analysis and bibliography |
| `code/verify_order_defect.py` | Exact Smith certificates and small exhaustive kernel counts |
| `data/order_defect_certificates.json` | 27 recorded exact cases; five full finite-level enumerations |
| `code/verify_grid_projection.py` | Independent exact coefficient formulas, analytic diagnostics and prime-side examples |
| `data/grid_projection_results.json` | Full recorded analytic-check results |
| `code/make_figures.py`, `figures/` | Reproducible exact-formula illustrations |
| `formalization_outline.md` | Definitions, lemmas and dependency order for future Lean formalization |
| `provenance/` | Pinned sources, hashes, novelty comparison and review record |
| `SHA256SUMS.txt` | File-integrity manifest for this package |

## Reproduce the computations

Python 3.11 or later is sufficient. The required packages are `sympy`,
`mpmath`, `numpy`, and `matplotlib` (see `requirements.txt`). From this folder:

```sh
python3 code/verify_order_defect.py --output data/order_defect_certificates.json
python3 code/verify_grid_projection.py --output data/grid_projection_results.json
python3 code/make_figures.py
```

The prime-side demonstration enumerates primes and prime powers through
442,413. To omit it while rerunning the other analytic checks, add
`--skip-primes` to the second command. Such a run produces a reduced
results file; use a different output path if preserving the full record.

## Rebuild the PDF

A normal TeX Live or MiKTeX installation with the packages listed in
`report.tex` is sufficient. The figures are already included.

```sh
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

Alternatively use `latexmk -pdf report.tex`. No BibTeX invocation is needed.

## Proof and novelty status

The general results have full mathematical proofs in the report and were
reviewed independently during preparation. The new results are not claimed
to be Lean-verified. Exact finite checks support examples; numerical
frequency checks and prime-statistic values do not prove a theorem about
all zeros or certify a central multiplicity.

The bounds are new relative to the inspected Article and incoming reports.
The report distinguishes them from Carayol trace rigidity, the already
existing Smith formula, and classical cascaded uniform-average filters.
Targeted literature searches did not locate the exact new statements;
global publication priority has not been established.

The analytic result uses RH/GRH for Dirichlet L-functions at the pinned
upstream source. It does not assume or prove arbitrary automorphic GRH.
Effective rounding requires certified gap, count and remainder constants;
the prescribed schedule gives eventual convergence without a known
stopping threshold. Noise estimates distinguish normalized observations
from raw unnormalized ramp sums.

## Pinned upstream sources

- `lsernau/grh-lean`: `72fead102f663d5c7a407964a13dc0cf9d977207`.
- `VladimirReshetnikov/ProveIt`: `22e5c8b7dda558fd9a50b61465483cb4c0433694`.

The report cites exact locations. Upstream proof projects and third-party
papers are referenced rather than redistributed. No repository was modified.
