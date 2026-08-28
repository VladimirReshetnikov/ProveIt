# Fractional integral calculus for the Fabius--Rvachev system

> **Archived companion bundle.** The former standalone manuscript is now
> consolidated in `../../Integration_and_Transform_Frontiers.tex`, with the
> rendered report at `../../Integration_and_Transform_Frontiers.pdf`. This
> directory retains its supporting computations and figures.

This bundle contains the numerical verification script, generated results,
and figures for the former standalone report

> **Fractional Integral Calculus and Complex-Order Transform Hierarchies for
> the Fabius--Rvachev System**

The repository audit is pinned to ProveIt commit
`3adc011108796355f1a874a5036f28098408d370`.

## Build the article

A recent TeX Live installation is sufficient:

```bash
(cd ../.. && pdflatex -interaction=nonstopmode -halt-on-error Integration_and_Transform_Frontiers.tex)
(cd ../.. && pdflatex -interaction=nonstopmode -halt-on-error Integration_and_Transform_Frontiers.tex)
(cd ../.. && pdflatex -interaction=nonstopmode -halt-on-error Integration_and_Transform_Frontiers.tex)
```

These commands update `../../Integration_and_Transform_Frontiers.pdf`.

## Regenerate numerical experiments

The script requires Python 3.10 or newer with NumPy, SciPy, and Matplotlib:

```bash
python -m pip install -r requirements.txt
python numerical_experiments.py
```

The supplied outputs were generated with Python 3.13.5, NumPy 2.3.5,
SciPy 1.17.0, and Matplotlib 3.10.8.

It reconstructs Rvachev's up-function from the infinite sinc product, derives
monotone interpolants for the Fabius function and its inverse, computes exact
rational moments independently, and evaluates fractional-Laplacian profiles
with a nonperiodic singular-integral quadrature. It regenerates:

- `numerical_results.json`
- `numerical_results.txt`
- `numerical_results.tex`
- `caputo_endpoint_ratio.png`
- `riesz_fractional_profiles.png`

No random sampling is used.

## Proof-status convention

“New” in the article means not located in the recursively audited repository
corpus at the pinned commit. It is not a universal publication-priority claim.
Theorems are proved in the article; conjectural statements and numerical
observations are explicitly labelled.
