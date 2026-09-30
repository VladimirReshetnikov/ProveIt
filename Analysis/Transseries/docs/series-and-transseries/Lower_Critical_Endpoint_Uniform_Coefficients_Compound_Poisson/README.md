# The Lower Critical Endpoint of Exponential-Feedback Transseries

**Uniform coefficient asymptotics, deletion of the largest action, Landau cutoff profiles, and the compound-Poisson boundary**

Research manuscript prepared for Vladimir Reshetnikov, 29 September 2026.
The compiled article has 21 A4 pages (20 as delivered), including the title page and contents.

## Research target and scope

This continues Question 4 of ProveIt's *Beyond Finite-Action Folds: Critical
Hahn Transseries, Stable Sector Asymptotics, and Sharp Action Budgets* at
repository revision `3d5973524506411392a911470b5ddc35521568ea`. The editorial
note at that question says the upper endpoint had been treated by subsequent
packages, while the lower endpoint remained untreated.

The model is

    U_e(q) = A_e(q exp(U_e(q))),
    A_e(z) = (Li_(2+e)(z) + P(z)) / (zeta(1+e) + P'(1)),

where e > 0 and P is a fixed finite polynomial perturbation preserving
nonnegative action weights. The limit is n -> infinity, e -> 0.

Main results, with proofs in the article:

- A convergent, parameter-uniform critical Hahn chart and its renormalized
  dilogarithmic endpoint (Section 3).
- A relative coefficient equivalent uniform for every joint limit, including
  arbitrarily small e, with an explicit first correction and all fixed orders
  (Sections 4-6).
- Total-variation convergence of the entire conditioned residual process,
  after deleting its largest action, to the unconditioned independent Poisson
  process (Section 7).
- A reflected Landau cutoff window, an asymptotic minimal-action quantile,
  and a Poisson law for residual extremes when n*e diverges (Section 8).
- A discrete compound-Poisson deficit law when n*e remains bounded, and
  matching of the discrete and continuous limits (Sections 9-10).

The nine further-research questions appear in Section 13. The article also
provides a formalization roadmap without claiming any new Lean verification.

This is an unrefereed, model-specific research manuscript. General publication
priority has not been established. The classical Lagrange, singularity-analysis,
and big-jump mechanisms are explicitly credited; no unrestricted transseries,
Borel-summability, or resurgence theorem is claimed.

## Contents

- `article.pdf`: compiled 20-page article.
- `article.tex`: complete LaTeX source with an internal bibliography.
- `coefficient_table.tex`, `landau_table.tex`: generated table rows.
- `verify.py`: exact finite checks and numerical diagnostics.
- `verification_results.json`: recorded full run.
- `make_tables.py`: regenerates the table rows from the recorded JSON.
- `verification_audit.md`: what was checked, limitations, and PDF audit.
- `source_provenance.json`: pinned repository paths and primary references.
- `requirements.txt`: numerical package versions used for the recorded run.
- `build.sh`: rebuilds the PDF; `--tables` regenerates the table rows first,
  `--verify` reruns the diagnostics into `build/rerun_results.json`.

## Rebuild

A standard TeX installation providing `latexmk`, `pdflatex`, Latin Modern,
amsmath, amsthm, mathtools, microtype, booktabs, enumitem, hyperref, fancyhdr,
and listings is needed. No bibliography service or external repository files
are needed.

From this directory:

```sh
python -m pip install -r requirements.txt
./build.sh
```

The default build uses the filed tables. To repeat the full numerical run
(written to `build/rerun_results.json`, which leaves the record unchanged):

```sh
./build.sh --verify
```

Equivalently:

```sh
python verify.py
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

`python make_tables.py` (or `./build.sh --tables`) regenerates the two table
files from the recorded `verification_results.json`. Replacing the record
itself requires `python verify.py --output verification_results.json
--overwrite-recorded`.

A quicker diagnostic run omits the larger Landau cutoff computations:

```sh
python verify.py --quick --output verification_quick_rerun.json
```

Use a different output filename for a quick run: the main table generator
requires the full `landau` section in `verification_results.json`. (The
commands above were changed on filing; see the amendments below.) The numerical
program needs no network access. The recorded environment was Python 3.13.5,
NumPy 2.3.5, SciPy 1.17.0, and mpmath 1.3.0. Exact finite tests use the standard
library's `fractions.Fraction`; coefficient diagnostics use log-space arithmetic
and do not rely on an extended-range `long double` type.

## Validation boundaries

There were 385 successful exact rational assertions, twelve 55-digit numerical
Hankel-integral checks, and an independent 80-digit coefficient recurrence
comparison. Numerical cutoff examples intentionally include visibly slow
convergence. Floating-point results are diagnostics, not interval certificates,
and finite checks are not proofs of the limit theorems. The mathematical proofs
are in the article.

No repository files have been modified by this delivery.

## Editorial amendments (ProveIt, 2026-09-29)

The package was filed in batch 52 (see `docs/incoming/README.md`). The
following changes were made on 2026-09-29; everything else is as delivered.

- `article.tex`: an unnumbered `ednote` environment (the article's remarks
  share the theorem counter, so its numbering is unchanged) and four visible
  "Editorial note (ProveIt, 2026-09-29)" paragraphs, each preceded by a
  `% ed. (2026-09-29)` comment:
  - end of Section 1.2 (scope): the same question is Question 10 of
    `../Confluent_Critical_Transseries_Exponent_Two_Boundary/` (coupling
    `1/zeta(alpha)`, the case `P = 0`) and Question 8 of
    `../Logarithmic_Critical_Endpoint_Lambert_Charts/`, answered here on the
    critical path; the interior-fold side is
    `../Lower_Critical_Endpoint_Landau_Transseries/` (batch 51); the
    subcritical side stays open;
  - after Theorem 4.1 (`thm:uniform`): its leading term is the critical Hahn
    article's `eq:critical-leading` (`thm:phases`) with `a = 1`,
    `beta_c = c_eps`, `B = K_eps`, proved here uniformly as `alpha -> 1`;
    and the independent batch-52 package
    `../Lower_Critical_Endpoint_Cauchy_Cutoff_Condensation/` proves the same
    coefficient law (without an error rate) and the same cutoff law. One
    theorem with two independent proofs: `B/d_n -> 1`, `eps B/b_n -> 1`,
    `D_n = B + eps B log(1/eps) + (1-gamma) b_n + o(b_n)`, its stable
    variable is `Z + 1 - gamma`; it also proves the joint limit of the
    extremes with the cloud that Theorem 8.6 disclaims; Corollary 6.2
    reproduces its recorded exact-recurrence ratios to three or four digits
    (checked on filing);
  - at research question 8: for `P = 0` the unnormalized model is treated
    in `../Lower_Critical_Endpoint_Landau_Transseries/` (interior fold at
    `delta = -log(1 - e^(-1/c))`, Landau profile at `lambda = n c delta`),
    without the matching asked for here;
  - Appendix (reproduction): the new output location, LF writers and
    `build.sh` behaviour.
  The title page no longer creates a PDF page anchor (`pageanchor=false`
  around it), which removes the delivered build's duplicate destination
  `page.1`. No label was renamed or removed.
- `article.pdf`: rebuilt from the amended source with `latexmk -pdf`
  (21 pages; the delivered PDF had 20; no errors, undefined references,
  multiply defined labels, duplicate destinations or overfull boxes).
  Line numbers of `article.tex` after line 26 differ from the delivered
  file. `verification_audit.md` (20 pages) describes the delivered build.
- `verify.py`: the default `--output` is `build/rerun_results.json` beside
  the program (as delivered, `verification_results.json` in the working
  directory, i.e. the record when run from here); writing the recorded file
  requires `--overwrite-recorded`; the JSON is written LF on every platform
  (as delivered, CRLF on Windows).
- `make_tables.py`: writes LF on every platform (as delivered, CRLF on
  Windows). It still writes the two filed table inputs, from the recorded
  JSON.
- `build.sh`: no longer runs `make_tables.py` on every build (only with
  `--tables`); `--verify` writes `build/rerun_results.json` instead of the
  record; `PYTHON` selects the interpreter (bare `python` by default).
- Rerun on a copy (Windows, Python 3.13.5, NumPy 2.3.5, SciPy 1.17.0,
  mpmath 1.3.0, default output): 385 exact assertions passed; the JSON is
  LF and equals the record except for last-digit floating differences
  (relative at most 4.4e-11); `make_tables.py` reproduced both table files
  byte for byte.
