# Resonance Profiles and Sharp Endpoint Laws for Rotating Fabius–Rvachev Distributions

Research article prepared for Vladimir Reshetnikov, 28 September 2026.

## Read the article

`article.pdf` is the compiled article. `article.tex` is the LaTeX driver;
its only external inputs are the two supplied table files in `data/`.

The article develops the directional-cap questions labelled
`conj:diophantine-endpoint` and `conj:liouville` in ProveIt's
*Matrix-Dilated Fabius–Rvachev Laws* report. The exact repository revision,
source path, blob identifier, and literature references are recorded in
`PROVENANCE.json` and in the article.

## Main results

The normalized random variable is

    S_beta = sum_{n>=1} 2 exp(-lambda*n) |cos(pi*(n*alpha+beta))| V_n,
    V_n independent Uniform[0,1], lambda>0.

Theorem 4.1 proves the common leading endpoint law for every irrational
rotation, uniformly in phase. Theorem 6.2 gives a bounded-type refinement in
terms of one explicit truncated resonance profile. Theorems 7.3, 8.1, and 8.2
supply a relative saddle formula, a three-term logarithmic cap expansion,
and a multiplicative inverse-quantile asymptotic. Theorems 9.2 and 9.3 classify
phase-dependent quantile oscillations, including the contrast between almost
every phase and a dense, dimension-zero residual set. Theorem 10.2 constructs
dense Liouville families with superlinear Laplace corrections.

The displayed Diophantine estimate in the repository is proved in a stronger
form. The expectation of a bounded or logarithmic carrier is qualified:
merely excluding exact zero factors is not sufficient. A full all-orders
quasiperiodic expansion is not proved. Sharp Liouville CDF/quantile spikes
are also left for further work; the Liouville theorem here concerns Laplace
transforms. The article gives eight further research directions.

## Build the PDF

A TeX Live installation with pdflatex and the packages named in the preamble
is sufficient. Libertinus is used when available, with Latin Modern as a
fallback. No font files are included in this package.

Run from this directory:

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

The bibliography is embedded in `article.tex`; BibTeX/Biber is not needed.
The supplied tables already allow a build without running Python.

## Reproduce the numerical checks and tables

Python 3.10 or later and mpmath are required. The environment used mpmath
1.3.0. From this directory:

```sh
python -m pip install -r requirements.txt
python verify_endpoints.py --output data --dps 110
```

The program regenerates both CSV files, both LaTeX table files, and
`data/verification_report.json`. Its calculations require no network access.
It writes only the named generated outputs in the selected output directory.
It uses no random sampling and no proof-assistant installation.

The cases include a golden rotation, an engineered phase with one exceptionally
small amplitude, rational shadows for the Liouville construction, kernel
identities, a precision comparison, and a saddle equation solved by bisection.
The engineered phase demonstrates one finite-scale ramp; it does not numerically
establish infinitely many resonances. The rational table does not by itself
construct a single irrational limit.

## Verification boundary

The article supplies ordinary mathematical proofs, not kernel-checked proofs.
It has not been independently peer reviewed. Targeted repository and literature
checks do not certify universal publication priority.

The numerical program reports analytic omitted-tail bounds separately from
rounding error. It uses high precision and a second-precision comparison, not
interval arithmetic. It does not independently compute the exact cap CDF,
so its saddle probability value is an asymptotic approximation rather than a
finite-argument probability certificate. Numerical examples are not used to
prove the infinite-subsequence or almost-everywhere results.

`VALIDATION.json` records the final compilation/render checks performed for
this package. Compilation and visual inspection validate the artifact, not
the correctness of its mathematical theorems.

## Files

- `article.tex`, `article.pdf`: article source and compiled PDF.
- `verify_endpoints.py`, `requirements.txt`: deterministic computation code.
- `data/bounded_type_checks.csv`, `data/rational_resonance_checks.csv`: results.
- `data/bounded_type_table.tex`, `data/rational_table.tex`: article tables.
- `data/verification_report.json`: numerical checks and limitations.
- `PROVENANCE.json`, `VALIDATION.json`: source and artifact-validation records.
