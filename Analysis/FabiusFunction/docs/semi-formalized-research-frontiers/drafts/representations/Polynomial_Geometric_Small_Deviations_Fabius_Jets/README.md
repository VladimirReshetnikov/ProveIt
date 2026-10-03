# Polynomial–Geometric Small Deviations

**A corrected Fabius-jet conjecture, all-order Lambert asymptotics, and inverse quantiles**

Research manuscript prepared for Vladimir Reshetnikov, 29 September 2026.

## Main result

For independent U_n uniform on [0,1], let

    S = sum_{n>=1} n^m exp(-lambda*n) U_n,  m>=0, lambda>0,
    p=m+1,  x=R^p exp(-lambda*R),  R>p/lambda.

The manuscript proves a full fixed-order relative expansion for P(S<=x),
with real-analytic periodic coefficients. Its leading factor is

    exp(-lambda*R^2/2 + (lambda/2+p)*R - Psi_lambda(R))
    / (2*pi*R)^(p/2).

The leading periodic correction Psi_lambda is independent of m. The paper
gives a convergent product, a Gamma–zeta Fourier formula, a closed first
coefficient, and a finite algorithm for every coefficient.

In L=log(1/x), the expansion includes the previously omitted term

    ((m+1)^2 * log(lambda)/lambda) * log(L).

This disproves the precise conjecture `conj:jet-small-ball` in the inspected
ProveIt source whenever lambda != 1. The exceptional case lambda=1 is
handled separately. (Editorial, 2026-09-29: the report now carries an
editorial note under the conjecture marking it false for lambda != 1; and for
m = 0, q = 1/2 the term is already part of a machine-checked Lean theorem,
see "Editorial amendments" below.) Additional proved results give a comparison law for
all weight multipliers exp(eta_n) with eta_n -> 0, a harmonic-tail scaling
law, and inverse-quantile error transport.

## Contents

- `article.pdf`: the compiled article (24 pages as delivered; 25 pages after the editorial rebuild of 2026-09-29).
- `article.tex`: self-contained LaTeX source, including the bibliography.
- `build.sh`: three-pass PDF build script.
- `code/verify.py`: deterministic symbolic and numerical diagnostics.
- `requirements.txt`: the exact Python package versions used for the recorded run.
- `results/periodic.csv`: boundary-product versus Fourier checks.
- `results/asymptotics.csv`: independent inversion versus A_1 and A_2.
- `results/comparison.csv`: the harmonic perturbation check.
- `results/verification.json`: environment and test summary.
- `results/run.txt`: complete recorded diagnostic output (the captured standard output of the recorded run).

## Build the PDF

Use a TeX distribution with pdflatex, Latin Modern, amsmath, amsthm,
mathtools, microtype, geometry, hyperref, cleveref, booktabs, and fancyhdr.
No external figures or bibliography database are required.

```sh
sh build.sh
```

The distributed PDF compiled without LaTeX warnings or overfull boxes.
Representative title, theorem, proof, table, and bibliography pages were
rendered and visually inspected.

## Reproduce the diagnostics

The recorded run used Python 3.13.5. A fresh virtual environment is recommended.

```sh
python -m pip install -r requirements.txt
mkdir -p rerun
python code/verify.py --output rerun > rerun/run.txt
```

(Editorial, 2026-09-29: the delivered recipe was `python code/verify.py
--output results`, which rewrote the recorded `results/` and left
`results/run.txt` stale. The program's default output is now `rerun/` beside
`code/`, and it refuses to write into `results/` unless given
`--overwrite-recorded`. On Windows use `py` instead of `python`, or
`uv run --no-project --with mpmath==1.3.0 --with numpy==2.3.5 --with
scipy==1.17.0 --with sympy==1.14.0 python code/verify.py`.)

No network calls or random sampling occur in the program. The script checks
exact symbolic identities; evaluates product and Fourier expressions with
at least 60 decimal digits plus guard digits; and independently evaluates
a scaled Bromwich integral by double-precision adaptive quadrature.
It repeats the contour calculation at two cutoffs.

Recorded results:

- First-coefficient symbolic identity: passed.
- Gamma moment valuation identities through j=10: passed.
- Maximum product/Fourier discrepancy at nine test points: 6.64e-74.
- Maximum normalized probability change between contour cutoffs: 8.67e-15.
- First- and second-order asymptotic tests: see the full CSV.

These are diagnostic computations, NOT interval-arithmetic certificates.
Quadrature estimates do not bound all roundoff or truncated-product error.
The general mathematical results rely on the proofs in the article.

## Source provenance

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned commit:

    aab173a7ccdd48add72191d68ce6b0c12ffd72fe

Source file:

    Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/
    representations/common_digit_fabius_zonoids_frontier_report/
    common_digit_fabius_zonoids.tex

(The three display lines above constitute a single repository path.)

Target labels: `conj:jet-small-ball`, `eq:small-ball-conjecture`.
Inspected source range: 1690–1840.
Returned blob SHA: `dabfc501dfe952d826001703a087b47424568581`.

The article includes the source locator, a claim-by-claim audit, and primary
literature references. It distinguishes the corrected repository conjecture
from classical small-deviation rates and existing Mellin–Fourier methods,
including a related 2026 preprint on the base-three uniform-series density.

## Status

This package contains conventional mathematical proofs and reproducible
computational checks. It contains no new Lean formalization and makes no
claim of an exhaustive global-priority determination. The all-order theorem
is a fixed-order statement; optimal truncation, Gevrey bounds, uniform
singular parameter limits, and certified numerical quantiles are proposed
research questions rather than claimed completed results.

## Editorial amendments (ProveIt, 2026-09-29)

Filed on 2026-09-29 (batch 50 of `docs/incoming/`; see `docs/incoming/README.md`)
beside the report whose conjecture it corrects. The report's conjecture
`conj:jet-small-ball` was marked false for lambda != 1 by an editorial note in
the report, in a commit of its own before this package was filed. The
following changes were made to the package; every change to the article
source is preceded by a `% ed. (2026-09-29)` comment, the visible additions
are labelled "Editorial note (ProveIt, 2026-09-29)", and no label was renamed.

- `article.tex`:
  - an unnumbered `ednote` environment (no numbering shifts);
  - an editorial note at the end of Section 1.3 ("Relation to existing
    literature"): the case m = 0, q = 1/2 was already machine-checked when the
    conjecture was stated, so its Fabius case was already contradicted by a Lean
    theorem, which the article does not cite; the report now carries the
    refutation note;
  - an editorial note at the end of Section 3 (after "The dyadic case") naming the
    machine-checked counterparts at (m, lambda) = (0, log 2), all in
    `Analysis/FabiusFunction/Lean/FabiusFunction/`:
    `Fabius.log_fabius_sub_sharpLambertMain_hasAsymptoticExpansion`
    (`FabiusFullAsymptoticExpansion.lean`; main term `fabiusSharpLambertMain`
    in the exact phase `lambda 2^(-lambda) = x`),
    `Fabius.log_fabius_sub_explicitCorrectedWikipediaMain_isBigO`
    (`FabiusSharpAsymptotic.lean`; its elementary main term
    `fabiusWikipediaElementaryMain` contains `(log log 2/log 2) log L`, with
    error `O(1/L)`), `fabiusFirstSaddleCorrection` (= `A_1` at m = 0, with the
    periodic function of opposite sign), and
    `hasSum_negativeLaplacePsi_gammaZeta_fourierSeries`,
    `negativeLaplacePsiFourierCoeff_ne_zero` (`PeriodicFourier.lean`); the
    canonical volume states them as `eq:sharp-main-lambda` and
    `eq:all-orders-log`;
  - an editorial note in Section 12 ("Formalization boundaries") pointing to
    those modules;
  - the reproduction command in Section 11.1 now writes to `rerun/`;
  - a bibliography entry `ed:fabiuslean` for the Lean corpus and the volume.
- `article.pdf`: rebuilt with three pdfLaTeX passes (25 pages, was 24; no
  errors, undefined references, multiply defined labels or duplicate
  destinations; every font Type 1).
- `code/verify.py`: CSV rows, `verification.json` and standard output are
  written with LF on every platform; the default output directory is `rerun/`
  beside `code/`, and writing into the recorded `results/` requires
  `--overwrite-recorded`. A rerun on a copy reproduced `results/periodic.csv`
  byte for byte and every other recorded file up to the last digits of
  double-precision diagnostics (contour integral, as delivered); the recorded
  `results/` are unchanged.
- `README.md`: this section, the notes in "Main result", "Contents" and
  "Reproduce the diagnostics".

On filing, the three CSV tables under `results/` were normalized from CRLF to
LF; every other file was filed byte for byte as delivered.
