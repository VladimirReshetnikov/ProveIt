# Noncommutative Cumulant Frontiers for the Fabius--Rvachev Law

This archive accompanies the LaTeX/PDF research report. It develops a free- and Boolean-probability layer for the dyadic geometric-uniform law whose density is Rvachev's `up` function, then connects that layer to the Fabius function, inverse Fabius representations, Jacobi/Legendre expansions, Bernoulli and Bell polynomials, q-integers, finite sinc products, Thue--Morse spline approximants, and Lambert-W endpoint asymptotics.

## Main files

- `report.tex` -- complete LaTeX source.
- `report.pdf` -- compiled 29-page report.
- `numerical_experiments.py` -- fully commented exact/high-precision computations.
- `results/` -- exact rational certificates, symbolic formulas, CSV tables, Sturm data, and numerical diagnostics.
- `figures/` -- PDF and PNG versions of the generated figures.
- `requirements.txt` -- Python package requirements.

## Principal new results in the report

1. An exact shifted-Hankel certificate proves that the dyadic `up` law is **not freely infinitely divisible**, even though its even free cumulants are exactly positive through `r_120` in the computation.
2. For the geometric-uniform family, an exact degree-30 obstruction polynomial and Sturm isolation prove non-free-infinite-divisibility for
   `0 < q < 0.523498599534498...`, including `q=1/2`.
3. Boolean cumulants are identified with moments of the first associated Jacobi tail, proving strict positivity.
4. Free cumulants are re-expanded in Jacobi increments with nonnegative integer coefficients through `r_16`, motivating a general positivity conjecture.
5. Cumulants of finite dyadic sinc-product approximants are exact polynomials in `Q=4^{-N}`, yielding finite q-binomial/Richardson extraction formulas.
6. Endpoint data motivate Boolean-renewal and free-transform-radius conjectures tied to the Lambert-W saddle structure already developed in the repository.

Novelty is claimed relative to the audited repository corpus and the literature search described in the report, not as a formal worldwide priority claim.

## Reproducing the computations

Run the three stages as **separate Python processes**. This bounds memory during the largest symbolic Jacobi expansion.

```bash
python3 numerical_experiments.py --task jacobi \
  --output-dir results --jacobi-order 8

python3 numerical_experiments.py --task finite \
  --output-dir results --finite-order 6

python3 numerical_experiments.py --task analysis \
  --output-dir results --figure-dir figures \
  --exact-order 60 --endpoint-order 200 --hankel-max 10
```

The exact certificate stages use Python `Fraction` and SymPy rational/integer arithmetic. Decimal values are printed only after the exact calculation. The threshold hierarchy and endpoint tables use `mpmath` at explicit high precision.

## Compiling the report

From the archive directory:

```bash
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

A modern TeX Live installation with the packages named in the preamble is sufficient.
