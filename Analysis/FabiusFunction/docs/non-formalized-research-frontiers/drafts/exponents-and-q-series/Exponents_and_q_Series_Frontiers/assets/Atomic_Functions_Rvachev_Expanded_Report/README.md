# Atomic Functions, Rvachev's up-Function, Smooth Cantor Splines, and the Theta Geometry of Derivatives

This archive contains the English reconstruction and expansion of the supplied
Russian Rvachev chapter, together with its compiled PDF and reproducible
numerical experiments.

## Primary files

- `Atomic_Functions_Rvachev_Expanded_Report.tex` — complete LaTeX source.
- `Atomic_Functions_Rvachev_Expanded_Report.pdf` — compiled 35-page report.
- `numerical_experiments.py` — deterministic, extensively commented Python
  experiments and formula checks.

The report distinguishes five provenance levels throughout: source
reconstruction, repository synthesis, inherited frontier baseline, results new
in this revision, and conjectural frontier. Novelty claims are deliberately
relative to the audited repository corpus, not claims of universal priority.

The recursive repository audit is pinned to the immutable ProveIt commit

```text
97940779a83c93c1d6310ccf7d5560c19df6bc87
```

so that later repository consolidation does not silently change the
non-duplication boundary.

## Included numerical outputs

The Python program generates or validates:

- the fixed-point approximation of `h_3` and its central plateau;
- the exact geometric law of local polynomial degree;
- the standardized `Fup_n` central-limit regime;
- the Jacobi-theta symbols and finite derivative Gram spectra;
- exact Toeplitz determinants and the q-binomial Gram--Schmidt factorization.

The corresponding PNG, CSV, and TXT outputs are included in the archive.

## Rebuilding the report

A recent TeX Live installation with `latexmk` is recommended:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  Atomic_Functions_Rvachev_Expanded_Report.tex
```

The source uses Libertinus when installed and falls back to Latin Modern.

## Re-running the experiments

Requirements:

```text
Python 3.10+
NumPy
SciPy
Matplotlib
```

Run:

```bash
python numerical_experiments.py
```

The script uses a fixed random seed and writes all outputs into its own
directory. It raises an exception if any certified numerical identity exceeds
its stated tolerance.

> **Editorial note (2026-08-28):** the report source and compiled PDF listed above (and, where listed, the supplied source scan/OCR) were removed from this directory after their content was merged into the volume `Exponents_and_q_Series_Frontiers.tex`; their SHA-256 hashes remain in the volume provenance list (and in `SHA256SUMS` here where present), and git history archives the files. This directory keeps only figures, data, and scripts.
