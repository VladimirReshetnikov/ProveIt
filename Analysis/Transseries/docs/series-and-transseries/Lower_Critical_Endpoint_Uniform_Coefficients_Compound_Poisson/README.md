# The Lower Critical Endpoint of Exponential-Feedback Transseries

**Uniform coefficient asymptotics, deletion of the largest action, Landau cutoff profiles, and the compound-Poisson boundary**

Research manuscript prepared for Vladimir Reshetnikov, 29 September 2026.
The compiled article has 20 A4 pages, including the title page and contents.

## Research target and scope

This continues Question 4 of ProveIt's *Beyond Finite-Action Folds: Critical
Hahn Transseries, Stable Sector Asymptotics, and Sharp Action Budgets* at
repository revision `3d5973524506411392a911470b5ddc35521568ea`. The editorial
note at that question says the upper endpoint had been treated by subsequent
packages, while the lower endpoint remained untreated.

The model is

    U_e(q) = A_e(q exp(U_e(q))),
    A_e(z) = (Li_(2+e)(z) + P(z)) / (zeta(1+e) + P'(1)),

where e > 0 and P is a fixed finite polynomial perturbation preserving
nonnegative action weights. The limit is n -> infinity, e -> 0.

Main results, with proofs in the article:

- A convergent, parameter-uniform critical Hahn chart and its renormalized
  dilogarithmic endpoint (Section 3).
- A relative coefficient equivalent uniform for every joint limit, including
  arbitrarily small e, with an explicit first correction and all fixed orders
  (Sections 4-6).
- Total-variation convergence of the entire conditioned residual process,
  after deleting its largest action, to the unconditioned independent Poisson
  process (Section 7).
- A reflected Landau cutoff window, an asymptotic minimal-action quantile,
  and a Poisson law for residual extremes when n*e diverges (Section 8).
- A discrete compound-Poisson deficit law when n*e remains bounded, and
  matching of the discrete and continuous limits (Sections 9-10).

The nine further-research questions appear in Section 13. The article also
provides a formalization roadmap without claiming any new Lean verification.

This is an unrefereed, model-specific research manuscript. General publication
priority has not been established. The classical Lagrange, singularity-analysis,
and big-jump mechanisms are explicitly credited; no unrestricted transseries,
Borel-summability, or resurgence theorem is claimed.

## Contents

- `article.pdf`: compiled 20-page article.
- `article.tex`: complete LaTeX source with an internal bibliography.
- `coefficient_table.tex`, `landau_table.tex`: generated table rows.
- `verify.py`: exact finite checks and numerical diagnostics.
- `verification_results.json`: recorded full run.
- `make_tables.py`: regenerates the table rows from the recorded JSON.
- `verification_audit.md`: what was checked, limitations, and PDF audit.
- `source_provenance.json`: pinned repository paths and primary references.
- `requirements.txt`: numerical package versions used for the recorded run.
- `build.sh`: rebuilds the tables and PDF, optionally rerunning diagnostics.

## Rebuild

A standard TeX installation providing `latexmk`, `pdflatex`, Latin Modern,
amsmath, amsthm, mathtools, microtype, booktabs, enumitem, hyperref, fancyhdr,
and listings is needed. No bibliography service or external repository files
are needed.

From this directory:

```sh
python -m pip install -r requirements.txt
./build.sh
```

The default build uses the recorded JSON. To repeat the full numerical run:

```sh
./build.sh --verify
```

Equivalently:

```sh
python verify.py --output verification_results.json
python make_tables.py
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

A quicker diagnostic run omits the larger Landau cutoff computations:

```sh
python verify.py --quick --output verification_quick_rerun.json
```

Use a different output filename for a quick run: the main table generator
requires the full `landau` section in `verification_results.json`. The numerical
program needs no network access. The recorded environment was Python 3.13.5,
NumPy 2.3.5, SciPy 1.17.0, and mpmath 1.3.0. Exact finite tests use the standard
library's `fractions.Fraction`; coefficient diagnostics use log-space arithmetic
and do not rely on an extended-range `long double` type.

## Validation boundaries

There were 385 successful exact rational assertions, twelve 55-digit numerical
Hankel-integral checks, and an independent 80-digit coefficient recurrence
comparison. Numerical cutoff examples intentionally include visibly slow
convergence. Floating-point results are diagnostics, not interval certificates,
and finite checks are not proofs of the limit theorems. The mathematical proofs
are in the article.

No repository files have been modified by this delivery.
