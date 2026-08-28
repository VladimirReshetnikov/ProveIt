# Dyadic-Comb Interpolation of the Fabius and Rvachev Functions

This archive accompanies the 35-page research report on global Lagrange interpolation of
the Fabius function and the centered Rvachev bump on the uniform dyadic comb.  It contains
the LaTeX source, compiled PDF, exact/high-precision numerical experiments, raw CSV data,
and vector figures.

## Main files

- `fabius_dyadic_interpolation_report.tex` — report source.
- `fabius_dyadic_interpolation_report.pdf` — compiled report.
- `numerical_experiments.py` — self-contained exact dyadic evaluator and all experiment
  implementations.
- `reproduce_all.py` — cross-platform orchestration that rebuilds every dataset and figure.
- `requirements.txt` — Python dependencies.
- `data/` — raw CSV outputs, including per-batch files and merged tables.
- `figures/` — PDF vector figures included by the LaTeX source.
- `SHA256SUMS` — integrity hashes.

## Mathematical/numerical design

Every Fabius value at a dyadic rational is computed as an exact `fractions.Fraction` from
the inverse-power recurrence and bit recursion documented in the report.  Arbitrary
precision (`mpmath`) is used only to evaluate the interpolating polynomial away from its
nodes.  This prevents a low-accuracy Fabius oracle from masquerading as Runge oscillation.

The endpoint-flat Hermite polynomial is never obtained from a confluent Vandermonde solve.
It is factored exactly as

```text
P_N,m(x) = I_x(m+1,m+1) + [x(1-x)]^(m+1) Q_N,m(x),
```

and `Q_N,m` is evaluated by an ordinary barycentric formula on the interior dyadic nodes.
The Rvachev version omits the beta-polynomial bridge.

## Rebuild all data and figures

Create a Python environment and install the two dependencies:

```console
python -m venv .venv
# Windows PowerShell:
.venv\Scripts\Activate.ps1
# POSIX shell:
# source .venv/bin/activate
python -m pip install -r requirements.txt
```

Then run:

```console
python reproduce_all.py
```

The full run includes exact endpoint-derivative calculations through `N=8192` and
high-precision scans through `N=128`.  To preserve existing batch results while rebuilding
missing pieces and all figures:

```console
python reproduce_all.py --skip-existing
```

A fast implementation check is:

```console
python numerical_experiments.py --task smoke
```

## Build the report

A TeX Live installation with `latexmk` is sufficient:

```console
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  fabius_dyadic_interpolation_report.tex
```

The figures are already present as vector PDFs.  No shell escape, external plotting during
LaTeX compilation, or BibTeX run is required.

## Individual experiment examples

```console
python numerical_experiments.py --task fabius --N 64 --m-start 0 --m-end 24 \
  --grid-level 12 --output data/fabius_N64.csv

python numerical_experiments.py --task up --N 64 --m-start 0 --m-end 20 \
  --grid-level 12 --output data/up_N64.csv

python numerical_experiments.py --task lebesgue --N 64 --m-start 0 --m-end 24 \
  --grid-level 11 --output data/lebesgue_N64.csv

python numerical_experiments.py --task derivative --n-min 4 --n-max 13 \
  --output data/endpoint_derivative_defects.csv
```

## Source boundary

The report audits the recursive `*.tex` corpus under
`Analysis/FabiusFunction/docs` in `VladimirReshetnikov/ProveIt`, with the final comparison
made against repository main commit
`3c7f2912a47433264f52ad530cc75adbaa83b764` (2026-08-28).

## Reproducibility caveat

Reported maxima are maxima on complete fine dyadic test grids, not computer-assisted proofs
of the continuum supremum.  The report labels them numerical observations.  The algebraic
factorization and cardinal-mode lower bounds are proved independently of those scans.
