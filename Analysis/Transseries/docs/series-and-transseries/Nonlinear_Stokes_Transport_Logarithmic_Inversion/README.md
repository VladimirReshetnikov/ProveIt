# Nonlinear Stokes Transport under Logarithmic Inversion

**Convergent sector expansions, exact-core resurgence, real reconstruction,
and curvature-shifted fold scaling**

Research report prepared for Vladimir Reshetnikov, 29 September 2026.

## Read the article

`article.pdf` is the 24-page article. `article.tex` is its editable source.
The source uses the included `figures/fold_scaling.pdf`; extract the whole
archive before rebuilding.

The article proves explicit results about analytic inversion and finite
exponential perturbations. Its main components are:

1. A contour-based inverse-transport theorem with every mixed coefficient,
   absolute sector convergence, a quantitative tail, and a weighted countable
   analytic extension.
2. An exact logarithmic-core reduction for a finite-pole Euler model, with an
   explicit Borel kernel verifying the hypotheses of established resurgent
   and summable implicit-function theorems.
3. Exact finite Stokes transitions, a positive asymptotic arithmetic-averaging
   defect, and sequential recovery of primitive amplitudes that accounts for
   nonlinear resonances.
4. Uniform outer Lambert resummation, curvature corrections to the real fold,
   an asymptotically sharp convergence-radius estimate, and a shifted inner
   square-root limit.

Section 10 proposes ten further projects. The appendices give a notation and
logical-dependency guide and an alternative formula for the real averaging
bias in forward derivatives.

## Mathematical status

These are conventional mathematical proofs, not Lean-checked proofs. No Lean
code or successful Lean build is claimed. The article clearly credits
Lagrange inversion, general resurgence/summability closure, and the classical
Lambert branch point. It does not claim to resolve a named, community-wide
open conjecture or to establish priority for every refinement. The proposed
contributions are explicit quantitative and model-specific results, whose
independent novelty still needs assessment.

The exact complex amplitude radius is not determined: the article proves
`R_g = exp(-1) + O(g^-2)` and bounds it above by the real fold, not equality
with that fold for every large finite `g`. Arithmetic averaging is not being
identified with general Ecalle median summation. The countable analytic
extension is not a countable-action resurgence theorem.

## Reproduce

The supplied outputs were generated with Python 3.13.5, SymPy 1.14.0, mpmath
1.3.0, matplotlib, and pdfLaTeX. A recent TeX Live installation with the
packages in the article preamble is needed. In a Python environment:

```sh
python -m pip install -r requirements.txt
sh build.sh
```

Or execute the individual stages:

```sh
python verify.py --out results
python make_figure.py
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

The build script changes to its own directory. The individual commands should
be run in the extracted article directory. No network connection is needed
after dependencies are installed. The scripts read no external datasets and
modify only generated local output files.

## Verification

`verify.py` performs exact generic checks of the first four inverse-sector
formulas, an independent polynomial residual test through amplitude degree
nine, generation of six exact core coefficients, checks of the displayed
first four core coefficients, and a symbolic fold critical-value check.
Its numerical tests use 100 decimal digits and compare actual lateral roots
with the expansions and analytic error formulas. The figure uses 60 decimal
digits for its 363 computed points.

The analytic bounds are proved in the article. Their numerical evaluations
are **not directed-rounding interval certificates**; floating-point tests
are corroboration, not proofs. `results/verification.json` and the matching
text report contain the executed outputs.

## Files

- `article.tex`, `article.pdf`: source and rendered article.
- `verify.py`, `make_figure.py`: symbolic/numerical checks and figure generation.
- `build.sh`, `requirements.txt`: build instructions and Python dependencies.
- `results/verification.json`, `results/verification.txt`: actual test results.
- `figures/fold_scaling.pdf`, `.png`, `.csv`: figure and its raw numerical data.
- `SOURCES.md`: repository snapshot and primary-source provenance.
- `QA_REPORT.md`: build and inspection record.
- `SHA256SUMS.txt`: checksums for the packaged files other than itself.

No external repository was modified. No external source corpus or font files
are included.
