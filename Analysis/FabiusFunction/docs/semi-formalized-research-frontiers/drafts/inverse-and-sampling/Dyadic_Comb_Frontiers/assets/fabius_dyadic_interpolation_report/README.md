# Dyadic-Comb Interpolation of the Fabius and Rvachev Functions

This archive contains the LaTeX source, compiled PDF, exact/high-precision Python experiments, CSV data, and figures for the report.

## Main files

- `fabius_dyadic_interpolation_report.tex` - report source.
- `fabius_dyadic_interpolation_report.pdf` - compiled report.
- `fabius_dyadic_interpolation_experiments.py` - exact dyadic evaluator and interpolation experiments.
- `data/` - numerical tables used in the report.
- `figures/` - vector PDF figures and PNG inspection copies.

## Rebuild the PDF

From this directory, run:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error fabius_dyadic_interpolation_report.tex
```

A standard `pdflatex` run repeated twice also works.

## Run the numerical experiments

Dependencies: Python 3.11 or newer, `mpmath`, `numpy`, and `matplotlib`.

A smaller verification run:

```bash
python fabius_dyadic_interpolation_experiments.py \
  --mode quick --check-level 10 --output-dir reproduced-quick
```

The expensive report-scale scan:

```bash
python fabius_dyadic_interpolation_experiments.py \
  --mode report --check-level 11 --output-dir reproduced-report
```

All Fabius samples and check-grid reference values are first computed as exact rational numbers. The global interpolants are evaluated in high precision because the report proves that the underlying equispaced interpolation operators are exponentially ill-conditioned.

## Interpretation of the CSV data

The reported maximum errors are maxima over a fine dyadic check grid, not interval-certified continuous suprema. `check_level=11` means 2,049 check points in the affine interval `[0,1]`; for Rvachev's function this interval represents `t=2x-1`.

> **Editorial note (2026-08-28):** the report source (.tex) and compiled PDF listed above were removed from this directory after their content was merged into the volume `Dyadic_Comb_Frontiers.tex`; their SHA-256 hashes remain in the volume provenance section, and git history archives the files. This directory keeps only figures, data, and scripts.
