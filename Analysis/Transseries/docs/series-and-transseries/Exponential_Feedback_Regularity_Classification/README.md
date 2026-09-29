# A sharp regularity classification for countable exponential-feedback transseries

Research draft prepared for Vladimir Reshetnikov, 29 September 2026.

## Main model

U(q) = sum_{j>=1} q^j exp(lambda_j U(q)), with lambda_j >= 0.

The article derives an exact convergence criterion, an exact factorial-normalized
Gevrey type identity, logarithmic coefficient asymptotics and concentration for
regularly varying slopes, a Borel-growth obstruction, and a uniform left-sector
analytic construction. It also transfers the Gevrey-class criterion to formal
compositional inverses.

## Contents

- `article.tex`: self-contained LaTeX source, including bibliography.
- `article.pdf`: compiled article.
- `code/verify.py`: exact coefficient recurrence, independent partition checks,
  and floating-point evaluations of proved coefficient bounds.
- `data/quadratic_coefficients.csv`: exact coefficients through degree 120.
- `data/quadratic_envelopes.csv`: floating-point large-order bound diagnostics.
- `data/verification.json`: results of the executed exact checks.
- `requirements.txt`: dependencies used only by the numerical envelope tables.
- `SOURCES.md`: source/provenance notes and exact snapshot identification.

## Reproduce

Use a Python 3.10+ environment and a reasonably recent TeX Live installation.

```sh
python -m pip install -r requirements.txt
python code/verify.py --order 120
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

The exact arithmetic part uses only the Python standard library. The envelope
calculations additionally use NumPy and SciPy. They are not interval arithmetic.
The LaTeX file requires standard mathematical/text packages and no external
figures or bibliography database. Two runs resolve references and the contents.

## Verification and limits

The quadratic coefficients through degree 120 were computed exactly. Twelve
quadratic coefficients were checked by an independent partition formula; twelve
zero-slope coefficients and twelve linear-slope coefficients were also checked
against separate formulas. All 36 comparisons passed.

The asymptotic and analytic results are conventional proofs in the article, not
Lean-verified results. Numerical checks do not establish the asymptotic theorems.
The entire Borel transform is NOT claimed Borel-Laplace summable on the positive
ray; the article proves that it is not. The left-sector construction proves
Poincare asymptotics, not a uniform Gevrey remainder estimate or a directional
Borel-summation theorem. The reversion theorem transfers class membership, not
the sharp numerical type.

The exact classification is the proposed contribution of this AI-assisted
research draft. Global novelty and publication priority have not been certified.
The article does not claim to resolve a named longstanding conjecture. Independent
mathematical review and further literature comparison are recommended.

No files or branches in the ProveIt repository were modified.

## Editorial amendments (ProveIt, 2026-09-29)

The package was filed in batch 45 (see `docs/incoming/README.md`). The
following changes were made after filing; everything else is as delivered.

- `article.tex`: an unnumbered "Editorial note (ProveIt, 2026-09-29)"
  environment was added to the preamble. The quoted directory of the canonical
  volume in Section 1 now gives its current location,
  `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`,
  and an editorial note records the pre-split path of the pinned snapshot; the
  bibliography entry `repo` gains the same current path (its pinned link is
  unchanged). Editorial notes were added after the end of Section 3 (the
  missing local limit and multiplicative asymptotic) and after six of the
  further-research questions, naming the later packages of this series that
  answer them and how far: directional summability (the negative-ray,
  natural-boundaries and sectorial-summability packages), beyond logarithmic
  coefficient asymptotics (the finite-core, microscopic-condensation and
  Poisson-layer packages), the near-linear transition (the near-linear
  package), exact type under compositional inversion (the weighted-type
  package; the finite-core package and the two batch-49 quadratic-inverse
  packages for multiplicative inverse laws), amplitudes (partly, the
  near-linear, critical Hahn and natural-boundaries packages) and uniform
  Gevrey remainders (the sectorial-summability package; the negative-ray
  package for the quadratic inverse). Every change is marked in the source by
  a `% ed. (2026-09-29)` comment. No label, theorem or number changed.
- `article.pdf`: rebuilt from the amended source.
- `SOURCES.md`: the relevant path now gives the current location and records
  the pre-split path of the pinned snapshot.
- `code/verify.py`: the default `--order` is now 120, the order of the recorded
  run, so a bare run no longer overwrites the degree-120 tables with shorter
  ones; the CSV and JSON writers emit LF line endings on every platform. A
  bare rerun on a copy reproduced the three filed `data/` files byte for byte.
