# Atomic Functions and Rvachev Up

This package contains the English reconstruction and post-merge expansion of
Rvachev's Russian chapter on atomic functions, prepared in the notation and
house style of the `ProveIt` Fabius-function documentation corpus.

## Contents

- `Atomic_Functions_Rvachev_Report.tex` — complete LaTeX source.
- `Atomic_Functions_Rvachev_Report.pdf` — rendered 37-page report.
- `experiments.py` — deterministic, extensively commented numerical checks and
  figure generation.
- `figures/` — PNG and PDF versions of all generated figures.
- `data/` — CSV diagnostics supporting the numerical statements.
- `CORPUS_AUDIT.md` — pinned repository scope, corpus layers, and
  nonduplication methodology.
- `requirements.txt` — Python dependencies.
- `SHA256SUMS` — checksums for every packaged file except the checksum file
  itself.

## Main post-merge results

The report distinguishes translated source material, established repository
results, results inherited from the attached draft and now present in the
current corpus, genuinely post-merge theorems, and conjectures.  Its three new
proved directions are:

1. the exact q-Gaussian Gram geometry of the normalized derivative tower,
   including a finite q-Pochhammer determinant, Gram-Schmidt pivots, and sharp
   Jacobi-theta Riesz bounds;
2. the explicit distribution and log-Weibull tail of the leading local
   polynomial jet in the separated regime `a > 2`, including divergence of all
   positive moments;
3. a uniform all-orders differentiated Edgeworth expansion for the
   standardized `Fup_n` hierarchy, with exact Bernoulli-cumulant coefficients.

“New” is used only relative to the pinned repository snapshot and the
literature cited in the report; it is not a claim of worldwide historical
priority.

## Rebuilding the figures and data

Python 3.10 or later is recommended.

```bash
python -m pip install -r requirements.txt
python experiments.py
```

The script is deterministic.  It writes all figures to `figures/` and all
numerical diagnostics to `data/`.

## Rebuilding the PDF

A reasonably complete TeX Live installation is sufficient.  Libertinus is
used when available, with the report's fallback handled by the source.

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  Atomic_Functions_Rvachev_Report.tex
```

Two ordinary `pdflatex` passes also work.

> **Editorial note (2026-08-28):** the report source and compiled PDF listed above (and, where listed, the supplied source scan/OCR) were removed from this directory after their content was merged into the volume `Exponents_and_q_Series_Frontiers.tex`; their SHA-256 hashes remain in the volume provenance list (and in `SHA256SUMS` here where present), and git history archives the files. This directory keeps only figures, data, and scripts.
