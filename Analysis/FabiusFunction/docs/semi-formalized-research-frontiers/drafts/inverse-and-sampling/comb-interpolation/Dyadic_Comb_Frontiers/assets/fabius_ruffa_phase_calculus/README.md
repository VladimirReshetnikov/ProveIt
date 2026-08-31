# Bernoulli–Ruffa phase–resolution calculus

This archive accompanies the report **“Bernoulli–Ruffa Phase–Resolution Calculus for Fabius and Rvachev Moment Integrals.”**

## Files

- `fabius_ruffa_phase_calculus.tex` — complete LaTeX source.
- `fabius_ruffa_phase_calculus.pdf` — compiled report.
- `experiments.py` — commented exact-symbolic and independent FFT verification program.
- `moment_table.csv` — exact rational values of the Rvachev moments, the moments of `F'`, and `I_p = ∫_0^1 x^p F(x) dx`, through `p = 14`.
- `numerical_checks.csv` — row-level numerical comparisons for the stable shifted formula, first-alias law, phase cubature, and Thue–Morse phase filters.
- `phase_defect.png` — generated normalized first-defect phase curves.
- `CORPUS_AUDIT.md` — repository snapshot, source-inventory method, and novelty exclusions.

## Reproducing the numerical artifacts

Python 3.10 or later is recommended. Install NumPy, SciPy, SymPy, mpmath, and Matplotlib, then run:

```console
python experiments.py --output-dir . --grid-power 19
```

The exact CSV is produced by SymPy rational arithmetic. The numerical checks reconstruct Rvachev’s `up` density independently from a 50-factor sinc product by inverse FFT on `2^19` points, integrate it to obtain the Fabius CDF, and evaluate the finite sums directly. The FFT is verification only; no numerical observation is used in a proof.

A faster exact-only run is:

```console
python experiments.py --output-dir . --skip-fft
```

## Building the report

A modern LaTeX installation with `latexmk` or `pdflatex` is sufficient. From this directory:

```console
latexmk -pdf fabius_ruffa_phase_calculus.tex
```

The source uses Libertinus when available and falls back to Latin Modern.

> **Editorial note (2026-08-28):** the report source (.tex) and compiled PDF listed above were removed from this directory after their content was merged into the volume `Dyadic_Comb_Frontiers.tex`; their SHA-256 hashes remain in the volume provenance section, and git history archives the files. This directory keeps only figures, data, and scripts.
