# Fabius–Rvachev Representation Frontiers

> **Archived companion bundle.** The former standalone manuscript is now
> consolidated in `../../Representation_Frontiers.tex`, with the rendered
> report at `../../Representation_Frontiers.pdf`. This directory retains its
> supporting computations, data, and figures.

This package accompanied the former 30-page standalone report.

## Contents

- `../../Representation_Frontiers.tex` — current consolidated LaTeX source.
- `../../Representation_Frontiers.pdf` — current rendered consolidated report.
- `rvachev_frontier_experiments.py` — commented, reproducible exact/numerical experiments.
- `generated_tables.tex` — exact moment and Jacobi-coefficient tables included by the report.
- `corpus_inventory.tex` — audited repository-source ledger included by the report.
- `data/up_even_moments.csv` — exact even moments through order 40.
- `data/up_jacobi_coefficients.csv` — exact Jacobi coefficients through order 40.
- `data/numerical_checks.txt` — high-precision checks of the resolvent and logarithmic-derivative identities.
- `figures/` — PDF and PNG versions of both numerical figures.
- `SHA256SUMS` — checksums for the package files.

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

Run from the package root:

```bash
python3 rvachev_frontier_experiments.py --order 40 --digits 45
```

The script writes its output to the current working directory. To preserve the packaged directory layout, either run it in a scratch copy or move the regenerated CSV/text files into `data/` and the figures into `figures/`.

## Compiling the report

A reasonably complete TeX Live installation with the Libertinus Type 1 fonts is
required for the committed artifact. From this archived companion directory,
run exactly three serial passes:

```bash
(cd ../.. && pdflatex -interaction=nonstopmode -halt-on-error Representation_Frontiers.tex)
(cd ../.. && pdflatex -interaction=nonstopmode -halt-on-error Representation_Frontiers.tex)
(cd ../.. && pdflatex -interaction=nonstopmode -halt-on-error Representation_Frontiers.tex)
pdffonts ../../Representation_Frontiers.pdf | grep Libertinus
```

These commands update `../../Representation_Frontiers.pdf`. The retained
root-level and `figures/` copies preserve the former package's numerical
artifacts and provenance.
