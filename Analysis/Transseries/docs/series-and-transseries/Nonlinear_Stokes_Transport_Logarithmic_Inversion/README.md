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

Since the editorial amendments below, `build.sh` no longer overwrites the
recorded outputs: it writes fresh verification results to `build/results/`, a
fresh figure to `build/figures/`, and its LaTeX pass logs and auxiliary files to
`build/`, typesets the article from the recorded figure, and replaces only
`article.pdf`. Set `PYTHON` to choose the interpreter. The individual commands
above still overwrite `results/` and `figures/` (figure bytes are not
reproducible); run them on a copy to compare.

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
- The delivered checksum ledger was verified in full on filing (batch 46) and
  not kept; the delivered archive remains in the repository history (see
  `docs/incoming/README.md`, batch 46 row).

No external repository was modified. No external source corpus or font files
are included.

## Editorial amendments (ProveIt, 2026-09-29)

Made in place after filing (batch 46 of `docs/incoming/README.md`). The author's
text is otherwise unchanged; every change to the article source is preceded by a
`% ed. (2026-09-29)` comment, and no label was renamed or theorem renumbered.

- `article.tex`: six visible "Editorial note (ProveIt, 2026-09-29)" blocks. In the
  provenance subsection: the current locations of the consolidated volume
  (`../Transseries_And_Inversion/`) and of the four named Lean modules
  (`TransseriesFlat.lean` is now in `Analysis/Transseries/Lean/Transseries/`; the
  other three remain in `Analysis/FabiusFunction/Lean/FabiusFunction/`). After the
  proof of `thm:transport`: its one-action instance `thm:stokes` in
  `../Inverse_Harmonic_Stokes_Transport/`, and its restatement in core coordinates
  in `../Resonance_Block_Summation_Transseries/` (`thm:inverse`). After the
  tree-coefficient paragraph: the same coefficients in
  `../Support_Controlled_Reversion_One_Exponential/` (`thm:cayley`) and
  `../Action_Accumulation_Nonlinear_Inversion/` (`thm:tree`). After `thm:core`: it
  is a model answer to the reversion package's question "Analytic subclasses stable
  under exact-core inversion", uncited. After the proof of `thm:radius`: the
  uncited overlap with `../Critical_Transseries_Moving_Fold/` (`thm:atlas`,
  `thm:actions`), not compared constant by constant. After the research question
  "Countably many resurgent input poles": the resonance-block package answers its
  forward half for sine-product Borel kernels; the resurgent half stays open. The
  repository bibliography entry gained the current location; the pinned URL is
  kept.
- `article.pdf`: rebuilt from the amended source with `latexmk -pdf`; 25 pages (the
  delivered PDF had 24; `QA_REPORT.md` describes the delivered build), no errors,
  undefined references, multiply defined labels or duplicate destinations, and no
  Type 3 fonts.
- `figures/fold_scaling.pdf`: regenerated by the amended `make_figure.py` with
  TrueType (Type 42) fonts; the delivered figure embedded Type 3 fonts. The data are
  unchanged: the regenerated `fold_scaling.csv` equals the filed LF file byte for
  byte. `fold_scaling.png` is the delivered file.
- `make_figure.py`: Type 42 fonts, and the CSV is written with LF line endings.
- `verify.py`: writes LF on every platform. A rerun on a copy (SymPy 1.14.0,
  mpmath 1.3.0, matplotlib 3.10.8) reproduced `results/verification.json` and
  `results/verification.txt` byte for byte.
- `build.sh`: redirected to `build/` as described under "Reproduce"; tested on a
  copy, where the recorded `results/` and `figures/` stayed untouched.
- `SOURCES.md`: a note giving the README's current location.
- This README: the paragraph on `build.sh`, and the checksum-ledger entry.
