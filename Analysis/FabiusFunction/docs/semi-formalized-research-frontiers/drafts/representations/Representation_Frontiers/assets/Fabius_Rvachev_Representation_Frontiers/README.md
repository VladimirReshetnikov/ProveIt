# Assets for Part I of Representation Frontiers

These files support Part I, *Resolvent, Continued-Fraction, and Transform
Representations of the Fabius–Rvachev System*, in the consolidated volume
[`../../Representation_Frontiers.tex`](../../Representation_Frontiers.tex).
The former standalone TeX/PDF pair was absorbed into that volume and is
available through git history.

## Contents

- `rvachev_frontier_experiments.py` — commented, reproducible exact/numerical experiments.
- `generated_tables.tex` — exact moment and Jacobi-coefficient tables included by the report.
- `corpus_inventory.tex` — audited repository-source ledger included by the report.
- `data/up_even_moments.csv` — exact even moments through order 40.
- `data/up_jacobi_coefficients.csv` — exact Jacobi coefficients through order 40.
- `data/numerical_checks.txt` — high-precision checks of the resolvent and logarithmic-derivative identities.
- `figures/` — PDF and PNG versions of both numerical figures; the consolidated volume embeds the PNG copies to avoid Type-3 fonts from the generated PDFs.
- The former package-file checksum ledger is retired and recoverable from Git
  history.

## Principal new results developed in the report

The report constructs a Cauchy–Stieltjes transform for the Rvachev up-law and derives:

1. moment, hyperbolic-product Laplace, one-sided Fourier–Laplace, and boundary-value representations;
2. an exact logarithmic fixed-point identity and the dyadic equation
   `R'(z)=2(R(2z+1)-R(2z-1))`;
3. an all-order finite Thue–Morse formula for every derivative of `R`;
4. a finite `2^N`-term Thue–Morse logarithmic resolvent whose boundary jump is the finite spline density;
5. exact Laplace/Fourier transforms of the Fabius function, one-sided up-function transforms, and pushforward transforms for the inverse Fabius function;
6. cotangent, tangent, zero-set, digamma, and Hurwitz-zeta representations for logarithmic derivatives of the Fourier image;
7. a trace-class Fredholm determinant model for the infinite Fourier product;
8. the Jacobi/Stieltjes continued fractions of the up-law, exact rational coefficients through order 40, Gaussian-quadrature approximants, and the proved limit `beta_n -> 1/4`;
9. clearly separated conjectures and future directions, including Jacobi monotonicity, the endpoint-sensitive convergence rate, a dyadic Mittag–Leffler expansion, arithmetic questions, and fractional resolvent dynamics.

## Reproducing the numerical artifacts

Requirements:

- Python 3.10 or newer;
- `mpmath`;
- `matplotlib`.

Run from this asset directory, writing into a scratch subdirectory so the
curated package layout remains untouched:

```bash
python3 rvachev_frontier_experiments.py --order 40 --digits 45 \
  --output-dir reproduced
```

Compare the regenerated CSV/text files with `data/`, the generated TeX table
with `generated_tables.tex`, and the regenerated figures with `figures/`.

## Compiling the report

A reasonably complete TeX Live installation is sufficient. From this asset
directory, build the consolidated source with exactly three passes:

```bash
cd ../..
pdflatex -interaction=nonstopmode -halt-on-error Representation_Frontiers.tex
pdflatex -interaction=nonstopmode -halt-on-error Representation_Frontiers.tex
pdflatex -interaction=nonstopmode -halt-on-error Representation_Frontiers.tex
```

> **Editorial note (2026-08-28):** the report source (.tex) and compiled PDF listed above were removed from this directory after their content was merged into the volume `Representation_Frontiers.tex`; their SHA-256 hashes remain in the volume provenance section, and git history archives the files. This directory keeps only figures, data, and scripts.
