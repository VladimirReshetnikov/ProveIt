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
handled separately. Additional proved results give a comparison law for
all weight multipliers exp(eta_n) with eta_n -> 0, a harmonic-tail scaling
law, and inverse-quantile error transport.

## Contents

- `article.pdf`: the compiled 24-page article.
- `article.tex`: self-contained LaTeX source, including the bibliography.
- `build.sh`: three-pass PDF build script.
- `code/verify.py`: deterministic symbolic and numerical diagnostics.
- `requirements.txt`: the exact Python package versions used for the recorded run.
- `results/periodic.csv`: boundary-product versus Fourier checks.
- `results/asymptotics.csv`: independent inversion versus A_1 and A_2.
- `results/comparison.csv`: the harmonic perturbation check.
- `results/verification.json`: environment and test summary.
- `results/run.txt`: complete recorded diagnostic output.

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
python code/verify.py --output results
```

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
