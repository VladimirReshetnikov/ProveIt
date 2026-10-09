# Optimal simplex products for projection-body volume

The manuscript is `optimal_simplex_products.pdf` (11 pages). Its source is
`main.tex` together with `body.tex` and the package's shared
`../common/preamble.tex`.

## Main results

For the normalized projection-body volume of an affine image of a product
of simplices, the unique optimal exponential factor dimension is 13.
The manuscript gives the exact optimum in every dimension by comparing
only two balanced products. From dimension 100 onward, the maximizing
factor dimensions follow an exact rule modulo 13. It proves a sharp
uniform gap to every other dimension multiset, an exact recurrence,
the full asymptotic expansion relative to a simplex, and the optimum
at a prescribed number of factors or facets.

The restriction to simplex products is essential. The manuscript does not
claim to determine the maximum over arbitrary convex bodies. The geometric
input is proved again in full, with credit to the original sources. The
specific optimization results appear to refine the inspected source;
the article does not claim a settled priority determination.

## Build

Run these commands in this directory:

```sh
pdflatex -interaction=nonstopmode -halt-on-error -jobname=optimal_simplex_products main.tex
pdflatex -interaction=nonstopmode -halt-on-error -jobname=optimal_simplex_products main.tex
```

The supplied PDF was built with pdfTeX from TeX Live 2023. The final build
had no undefined references, citations, or overfull/underfull box warnings.

## Verification

See `verification/README.md`. The main exact dynamic program checks
dimensions 1 through 300. A separate implementation checks the best and
runner-up rational values through dimension 260. Both agree with the
proved formulas, and the latter confirms the sharp gap on its entire
tested range. The finite checks supplement the proofs; they do not
establish an unbounded claim by extrapolation.
