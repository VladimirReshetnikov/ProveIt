# The sharp localization barrier for positive Dirichlet zero filters

Research note, 27 November 2026. Read `sharp_global_filters.pdf`; its complete source is `sharp_global_filters.tex`.

## Results and status

- Assuming Dirichlet GRH, the coefficient in ProveIt's open full-spectrum filter question improves from `2*pi*d/Q_*` to `pi*d/Q_*`, for every fixed conjugation-closed multiset of primitive Dirichlet characters.
- At the critical coefficient, entire division and sector Phragmen–Lindelof imply polynomial rigidity. A moment series gives the strict degree cutoff. The exact supremum and endpoint attainment are established for products of zeta, beta, and the quadratic character modulo 5. The new upper bound is not claimed to be the sharp supremum for arbitrary signed canonical kernels.
- The article's underlying RH/GRH theorem is used as a hypothesis. The vendored project was inspected but not rebuilt. No new Lean verification or comprehensive priority search was carried out. The claimed novelty is relative to the inspected article and its explicit open problem.

## Reproduce

With a standard TeX Live installation (`amsmath`, `amsthm`, `lmodern`, `xurl`, etc.):

```
pdflatex -halt-on-error -interaction=nonstopmode sharp_global_filters.tex
pdflatex -halt-on-error -interaction=nonstopmode sharp_global_filters.tex
pdflatex -halt-on-error -interaction=nonstopmode sharp_global_filters.tex
```

Optional numerical illustration (Python 3 and mpmath):

```
python verify_examples.py > checks.json
```

`checks.json` shows how the logarithmic dyadic slopes of the positive moment-series summands approach the exact predicted power. Numerical checks are not part of the proof. All endpoint classifications are analytic; they do not depend on zero computations.

## Repository provenance

- `Analysis/GeneralizedRiemannHypothesis/Article/sections/fil.tex`, blob `ee4a2a3294242cdb7594a09c5b47b350aad5c2fa`, specifically labels `fil:thm:global`, `fil:cor:endpoint`, and `fil:sec:open`.
- Vendored upstream `lsernau/grh-lean` commit `72fead102f663d5c7a407964a13dc0cf9d977207`; `src/Statements.lean` and `src/Main.lean` inspected.
- The note gives references and precise conventions for the canonical kernel, multiplicity, central zeros, and exponent.
