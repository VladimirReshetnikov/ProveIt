# Fabius-Rvachev frontier report (30 August 2026)

This archive contains the LaTeX source, compiled PDF, numerical code, exact tables, Monte Carlo validation data, and figures for:

**Flat Parameter Fronts, q-Susceptibility, and Smooth Dynamics: New Frontier Results in the Fabius-Rvachev System**

## Main contents

- `fabius_frontier_report.tex` — complete LaTeX source.
- `fabius_frontier_report.pdf` — compiled 23-page report.
- `code/fabius_q_response_experiments.py` — documented Python program for exact symbolic calculations and numerical checks.
- `data/` — exact rational coefficient tables and Monte Carlo validation tables.
- `figures/` — figures included in the report.
- `NUMERICAL_README.txt` — numerical parameters, methodology, and interpretation.
- `requirements.txt` — Python package requirements.

## Principal results developed in the report

1. Joint smoothness of the normalized geometric-uniform density in both the parameter and spatial variables, together with a continuum of flat but nonanalytic plateau fronts.
2. A linear-response theory at the Fabius parameter `q = 1/2`, including a contractive signed-measure resolvent, exact refinement equations, a marked infinite-sinc product, Bernoulli cumulant jets, Bell-polynomial moment recurrences, and exact rational shifted-Legendre coefficients.
3. A global smooth Schroeder/Koenigs coordinate conjugating Fabius iteration to multiplication by two, with beyond-all-orders inverse-iterate asymptotics.
4. A logarithmic Bottcher-type endpoint height, double-exponential forward-orbit asymptotics, and an exact one-periodic quotient relating the two dynamical coordinates.
5. Explicit conjectures, open problems, and a staged Lean formalization roadmap.

“Repository-novel” in the report means that the result was not found in the active primary exposition, canonical frontier synthesis, or current draft manifest under the audited concepts and equivalent terminology. It is not a claim of absolute priority over the entire mathematical literature.

## Rebuilding the PDF

From the archive root, run:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error fabius_frontier_report.tex
```

The source uses standard TeX Live packages and the Libertinus Type 1 font package.

## Reproducing the numerical layer

Create an environment with Python 3.11 or later, install the requirements, and run:

```bash
python -m pip install -r requirements.txt
python code/fabius_q_response_experiments.py --output-root .
```

The default invocation regenerates the exact CSV files, Monte Carlo validation tables, and figures. The computations use a fixed seed for reproducibility. Command-line options permit changing sample counts, digit truncation, precision, finite-difference step, and output location; see `python code/fabius_q_response_experiments.py --help`.

Exact cumulant, moment, and Legendre calculations use SymPy rational arithmetic. Monte Carlo experiments are validation checks only and are not used as proofs.
