# Inverse Fabius compositional iterates: nowhere analyticity

This archive contains the complete source and rendered report proving that, for every integer `n >= 1`, the `n`-fold compositional iterate of the inverse Fabius function is real analytic at no point of `[0,1]`.

## Main results

Let `F:[0,1] -> [0,1]` be the bounded Fabius function, `I=F^{-1}`, `G_n=F^{\circ n}`, and `K_n=I^{\circ n}=G_n^{-1}`.

The report proves:

1. Every forward iterate `G_n` is nowhere real analytic, via the exact derivative atlas, a Faà di Bruno partition-defect estimate, and a finite orbit-spine asymptotic.
2. Local formal power-series convergence is invariant under inversion of smooth germs with nonzero derivative. Therefore the Taylor series of `K_n` has radius zero on a co-countable dense subset of `(0,1)`.
3. No `K_n` is analytic at any interior point, by the analytic inverse-function theorem.
4. At either endpoint, `K_n` is not Hölder continuous of any positive order. More precisely,

   `-log K_n(y) ~ (2 log 2)^(1-2^(-n)) (log(1/y))^(2^(-n))` as `y -> 0+`,

   with the reflected formula at `1`.
5. At the fixed center `1/2`, the Taylor series is the affine polynomial

   `K_n(1/2+h) ~ 1/2 + 2^(-n) h`,

   but it does not represent the function on any neighborhood.

The report also records conjectures and future directions involving tied orbit spines, weighted Bell/partition polynomials, nested Lambert-W endpoint phases, Legendre approximation, general q-atomic functions, and Lean formalization.

## Files

- `inverse_fabius_iterates_nowhere_analytic.tex` — complete LaTeX source.
- `inverse_fabius_iterates_nowhere_analytic.pdf` — rendered 23-page report.
- `numerical_experiments.py` — fully commented deterministic numerical checks.
- `figures/` — figures embedded in the report.
- `numerical_output/spine_diagnostic.csv` — forward and inverse Taylor diagnostics through order 22.
- `numerical_output/numerical_metadata.txt` — run parameters, orbit data, and the formal-reversion residual.
- `requirements.txt` — Python package dependencies.
- `SHA256SUMS.txt` — checksums for archive contents other than the checksum file itself.

No numerical experiment is used as a premise of the proof.

## Rebuild the PDF

A recent TeX Live installation with `latexmk` is sufficient:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  inverse_fabius_iterates_nowhere_analytic.tex
```

The source expects the included `figures/` directory to remain beside the `.tex` file.

## Reproduce the numerical diagnostics

Install the dependencies, then run:

```bash
python -m pip install -r requirements.txt
python numerical_experiments.py \
  --output-dir numerical_output \
  --x0 0.437123456789 \
  --iterate-count 4 \
  --max-order 22
```

For the archived run, the maximum coefficient residual in the formal identity
`G_4(K_4(y_0+w)) = y_0+w` through order 22 is approximately `1.8991135e-65` at 160 decimal digits of working precision.
