# Lagrange–Rvachev Closed-Loop Report

This archive accompanies the report

**Lagrange Cardinal Polynomials and the Rvachev Up-Function: Closing an Exact Finite/Infinite Representation Loop**

prepared on 29 August 2026.

## Main files

- `lagrange_up_loop.tex` — complete LaTeX source.
- `lagrange_up_loop.pdf` — compiled 28-page report.
- `experiments.py` — commented exact-symbolic and numerical experiments.
- `data/` — exact CSV output and the two generated LaTeX table fragments.
- `figures/` — vector PDF figures used in the report.
- `requirements.txt` — Python dependencies.
- `SHA256SUMS` — checksums for the distributed files.

## Reproduce the experiments

From the archive directory, run:

```bash
python experiments.py
```

The defaults reproduce the report data:

```text
--matrix-degree 18
--legendre-order 16
--denominator-degree 8
```

The symbolic calculations use exact SymPy rationals. Floating point is used only for matrix conditioning diagnostics and plots. On the preparation system the full default run took about 11 seconds.

## Rebuild the PDF

After regenerating the data and figures, run:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error lagrange_up_loop.tex
```

The source uses standard TeX Live packages and the Libertinus Type 1 fonts when available, falling back to Latin Modern otherwise.

## Tested environment

- Python 3.13.5
- SymPy 1.14.0
- NumPy 2.3.5
- Matplotlib 3.10.8
- latexmk 4.86
- pdfTeX 1.40.26 / TeX Live 2025 development snapshot

## What the code verifies

The script independently reconstructs moment and reciprocal-moment sequences from Bernoulli cumulants; verifies the quadratic Lagrange-cardinal expansions and Appell–Vandermonde inverse exactly; verifies all Fourier–Legendre/up closures through degree 32; checks the exact top-amplitude formula and top-block dominance through cutoff 16; compares equispaced and Chebyshev–Lobatto conditioning through degree 18; and factors denominator data through degree 8.
