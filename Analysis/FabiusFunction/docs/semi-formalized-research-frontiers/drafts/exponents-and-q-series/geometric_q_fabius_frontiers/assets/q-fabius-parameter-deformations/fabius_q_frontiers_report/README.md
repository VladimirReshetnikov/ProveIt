> **Absorbed into the consolidated volume.**
> This directory is the preserved verification package of a report that is now
> **Part~X** of `geometric_q_fabius_frontiers.tex`, two levels up. The
> report's own `.tex` and `.pdf` were deleted when it was merged; git history
> is the archive, and the volume's Provenance section pins the absorbed
> snapshot by SHA-256. The scripts, data, and figures here are still live —
> the volume includes them from `assets/q-fabius-parameter-deformations/fabius_q_frontiers_report/`. Any build or path
> instruction below describes the original standalone package and no longer
> resolves as written.

# q-Fabius–Rvachev Parameter Frontiers

This reproducibility package accompanies the report

**Parameter-Flow, Gaussian, and Large-Deviation Frontiers for the q-Fabius–Rvachev Family**

prepared on 30 August 2026.

The report studies the centered geometric-uniform series

\[
X_q=(1-q)\sum_{j\ge 0}q^jU_j,\qquad U_j\sim\mathrm{Uniform}[-1,1],\quad 0<q<1.
\]

At `q = 1/2`, its density is the centered Rvachev `up` function and is affinely related to the Fabius function. The new layer developed in the report consists of:

1. an exact parameter-flow probability kernel and tail-shift martingale coupling proving `X_s <=cx X_r` for `0 < r < s < 1`, with a compound-Poisson cocycle interpretation;
2. a `q -> 1` large-deviation principle whose scaled cumulant transform is a logarithmic midpoint integral, together with an all-orders midpoint Euler–Maclaurin expansion and a Lambert-`W_{-1}` support-edge law;
3. a uniform, differentiated, all-orders Edgeworth expansion for the continuous geometric parameter family;
4. central/moderate/large-deviation matching, exact Bernoulli-cumulant formulas, numerical diagnostics, and a list of conjectures and formalization targets.

Novelty claims in the report are explicitly limited to comparison with the live ProveIt Fabius documentation corpus and its draft manifest as inspected on 30 August 2026; they are not unconditional historical-priority claims.

## Files

- `q_fabius_parameter_frontiers.tex` — complete LaTeX source.
- `q_fabius_parameter_frontiers.pdf` — current compiled 22-page A4 report.
- `experiments.py` — documented numerical experiments and figure generation.
- `symbolic_checks.py` — exact SymPy verification of cumulants, rate series, Edgeworth coefficients, the parameter-kernel cocycle, and Euler–Maclaurin operators.
- `requirements.txt` — Python package requirements.
- `data/` — CSV outputs and plain-text numerical/symbolic summaries.
- `figures/` — the four report figures in vector PDF and PNG form.

## Python reproduction

A recent CPython 3 installation is required. The computations were executed with Python 3.13, NumPy 2.3.5, SciPy 1.17.0, Matplotlib 3.10.8, and SymPy 1.14.0.

```bash
python -m venv .venv
source .venv/bin/activate          # Windows PowerShell: .venv\Scripts\Activate.ps1
python -m pip install --upgrade pip
python -m pip install -r requirements.txt

python symbolic_checks.py
python experiments.py
```

A faster smoke test is available:

```bash
python experiments.py --quick
```

The full run used a fixed random seed and takes about 10–20 seconds on a typical modern workstation. It should reproduce convergence slopes close to:

```text
raw midpoint-CGF error                 2.00
midpoint-CGF error after correction    4.00
Gaussian density approximation         1.02
Edgeworth weighted order 1             2.05
Edgeworth weighted order 2             3.07
Edgeworth weighted order 3             4.10
```

The Monte Carlo stop-loss plot is only a diagnostic. The convex-order result is proved exactly in the report by an explicit martingale coupling.

## LaTeX reproduction

A TeX Live installation with the standard packages named in the preamble is sufficient. Run exactly three strict serial passes from this directory.

```bash
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error q_fabius_parameter_frontiers.tex
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error q_fabius_parameter_frontiers.tex
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error q_fabius_parameter_frontiers.tex
```

The figures are already included. Running `experiments.py` regenerates them before compilation.

The current publication artifact was rebuilt on 31 August 2026 from the
1,492-line source. It is a 700,025-byte, 22-page A4 PDF with extractable text
and no encryption. All 33 font rows are embedded and subset; five are
Libertinus rows and eight are Type-3 rows inherited from the four included
Matplotlib vector figures. The standalone figure PDFs contain the same eight
Type-3 rows, so figure-font normalization remains outstanding. The active
20-entry checksum ledger verifies the current package in full.

## Numerical methodology

- The standardized density is obtained by cosine-transform inversion of the infinite sinc product.
- Product truncation occurs only after the largest omitted argument is below `1e-10`; the leading quadratic logarithmic tail is inserted analytically.
- The finite-`q` cumulant transform is evaluated using its exact midpoint-sum identity.
- The Lambert endpoint constant is evaluated from two absolutely convergent integrals.
- Exact rational identities and Taylor coefficients are produced independently by `symbolic_checks.py`.

## Scope and status

The parameter-flow kernel and martingale coupling are elementary exact theorems. The large-deviation, midpoint Euler–Maclaurin, Lambert-boundary, and differentiated Edgeworth results are presented with proof arguments in the report. The later saddlepoint, endpoint-transseries, strictness, metric-contraction, and coefficient-positivity statements are explicitly labeled as conjectures or open problems.
