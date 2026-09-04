# Fabius–Rvachev Frontier Report

## Contents

- `fabius_frontier_report.tex` — complete LaTeX source.
- `fabius_frontier_report.pdf` — compiled 22-page report.
- `numerical_experiments.py` — commented, network-free exact/high-precision experiments.
- `generated/` — exact TeX tables and a plain-text numerical summary.
- `figures/` — retained vector sources and the PNG figures used by LaTeX.
- `requirements.txt` — Python packages used by the experiment script.

## Main new theorem chains

The report develops repository-relative frontier results from the exact integer-zero divisor of the Rvachev Fourier product:

1. Laguerre–Pólya classification, derivative real-rootedness, Pólya-frequency normalized moments, shifted Jensen-polynomial hyperbolicity, and strict Turán inequalities.
2. Non-D-finiteness of the Fourier and moment transforms and non-P-recursiveness of the exact even moments.
3. Cartwright classification and exact base-b digital zero counting.
4. A complete-Bernstein/Thorin representation and an explicit generalized gamma-convolution semigroup.
5. An arithmetic heat trace with an exact Mellin/log-periodic skeleton, an exact Jacobi-dual beyond-all-orders remainder, and lower-Lambert-W inversion.
6. An exact modular-dual formula whose exponentially small factor is the partition product into powers of b.

Conjectures and research directions include differential transcendence, strict total positivity, Hermite universality of Jensen polynomials, closed forms for the modular constant, nonintegral-base collision theory, orthogonal-polynomial asymptotics, and Lean formalization.

“New” is used relative to the live ProveIt documentation corpus; the report does not claim literature-wide historical priority.

## Reproduce the numerical material

From this directory:

```bash
python -m pip install -r requirements.txt
python numerical_experiments.py --precision 75 --moments 28
```

The script overwrites the files in `generated/` and `figures/`. It uses exact `sympy.Rational` arithmetic for moment data and arbitrary-precision `mpmath` arithmetic for the heat-trace and modular-dual checks. It has no network dependency.

## Rebuild the PDF

A TeX Live installation with Libertinus is required. Run exactly three serial
passes:

```bash
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error fabius_frontier_report.tex
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error fabius_frontier_report.tex
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error fabius_frontier_report.tex
```

The synchronized 2026-08-31 rebuild is 22 A4 pages. Every page rendered and
contained extractable text. All 18 font rows are embedded and subset, five are
Libertinus, and none is Type 3. The final log has no TeX error, unresolved
reference/citation, rerun request, overfull box, or underfull box. The separate
`ARRIVAL_SHA256SUMS` ledger remains unchanged. The package-local `SHA256SUMS`
ledger was retired repository-wide on 2026-09-01; its final source, PDF, and
experiment-script snapshot remains recoverable from Git history.
