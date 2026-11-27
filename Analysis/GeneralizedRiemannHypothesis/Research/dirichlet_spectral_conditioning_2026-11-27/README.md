# Sharp conditional gamma limits for reciprocal completed L-functions

**A four-fifths transition, a spectral bridge, and a median-height law**  
Research extension of the supplied ProveIt materials, 27 November 2026.

Start with **`report.pdf`**. The complete proof is in `report.tex` and
`sections/*.tex`; the PDF and TeX have the same mathematical content.

## Main result

Let the positive zero ordinates of zeta, or of a fixed primitive real
Dirichlet L-function, be `gamma_j`, with multiplicity. Introduce independent
`Gamma(shape=theta, rate=1)` variables `G_j` and the random sum

`X = sum_j G_j / gamma_j^2`.

Choose the exact saddle height `u` from

`x = theta sum_j 1 / (gamma_j^2 + u^2)`.

Condition on `X <= x`, with `x -> 0`. For the scaled vector
`(u^2 G_j / gamma_j^2)_{gamma_j <= h}`, comparison with independent
unit-rate shape-theta gamma variables has a sharp threshold at

`h_*(u) = (u^4 / log u)^(1/5)`.

At `h = c h_*`, the total-variation distance tends to

`2 Phi(c^(5/2) sqrt(theta/(50 pi))) - 1`.

The distance tends to zero below this scale and to one above it, in the
ratio senses `h/h_* -> 0` and `h/h_* -> infinity`. Here `Phi` is the
standard normal CDF and total variation lies in `[0,1]`.

The report also proves the general regularly varying spectrum theorem,
the joint spectral Brownian-bridge and exponential-slack limit, a separate
larger threshold for independence with the correct unequal rates, a
degree-independent count normalization, and a normal law for the height
carrying half the sum with the necessary Catalan-constant centering.

The probability theorem is unconditional under its stated spectral
assumptions. RH/Dirichlet GRH identifies the arithmetic random law with
the reciprocal of the appropriate completed function. These are theorems
about introduced random weights, not claims that zeta zeros are random.

## Status and novelty

- Complete analytical proofs are included. No new Lean formalization is
  claimed or included.
- The source analysis pins ProveIt commit
  `2a9f8e3ee74a1824d57546f0b1b4f1cef5df93d6` and distinguishes actual
  exported Mathlib RH/Dirichlet GRH statements from broader GRH claims.
- The exact growing-block transitions were not located in the supplied
  article or targeted literature search. Publication priority against
  all existing literature is not established. Classical gamma-series,
  exponential-tilting, and conditional-bridge ideas are credited.
- The review notes record separate model-assisted mathematical and code
  reviews. They are not external peer review or proof-assistant certificates.
- The vendored Lean source was inspected and matched by Git blob hashes;
  no fresh full build or kernel replay was performed in this work.

## Contents

| Path | Contents |
| --- | --- |
| `report.pdf` | Complete research manuscript |
| `report.tex`, `sections/*.tex` | All manuscript sources and bibliography |
| `code/build_report.sh` | PDF build command |
| `code/verify_and_illustrate.py` | Reproducible constants, simulations, and plots |
| `code/requirements.txt` | Versions used for the recorded numerical run |
| `data/verification.json` | Constants, roots, estimates, and finite-size differences |
| `figures/*.pdf`, `figures/*.png` | Three standalone figures in both formats |
| `evidence/*.md` | Source audit and independent review notes |
| `evidence/numerical_run.log` | Recorded numerical run output |
| `provenance/*.json` | Source and incoming-archive identifiers |
| `SHA256SUMS.txt` | SHA-256 checksums of the packaged files |

## Rebuild the manuscript

Requirements: a TeX distribution with `pdflatex`, `latexmk`, and the
standard packages listed in `report.tex` (including `lmodern`, `microtype`,
`mathtools`, `booktabs`, `fancyhdr`, `xurl`, and `hyperref`).

From the unpacked package directory:

```bash
bash code/build_report.sh
```

The supplied figures are sufficient to compile. No simulation, network
connection, or external source checkout is needed to rebuild the PDF.

## Reproduce the numerical artifacts

The recorded environment used Python 3.12.14. In an environment with the
dependencies from `code/requirements.txt`, run:

```bash
python3 code/verify_and_illustrate.py --draws 50000
```

This uses seed `20261127` and rewrites the JSON and six figure files.
The run involves many random samples and can take a few minutes depending
on hardware. Floating-point and plotting-library differences can change
last digits or file bytes. The analytic proof does not depend on a
particular numerical output.

The simulations have deliberately limited meanings:

1. High-precision quadrature checks integral constants; root finding checks
   deterministic median-center equations. These are not interval proofs.
2. Exact exponential-tilt rejection samples the conditional **finite** model
   `gamma_j=j`, `1<=j<=4096`, `theta=1`. It does not sample the full
   reciprocal-xi distribution. Finite-saddle correlations remain visible.
3. A separate likelihood experiment estimates TV between **independent**
   product-exponential distributions on synthetic ordinates
   `2*pi*j/W(j/e)`. Those ordinates have the required counting asymptotic
   but are not actual zeta zeros. It does not directly sample the
   conditioned law. Finite-size deviations from the asymptotic curve are
   larger than Monte Carlo standard errors in some rows.

## Source locations

The supplied sources are available at the pinned commit:

- [Vendored Lean development](https://github.com/VladimirReshetnikov/ProveIt/tree/2a9f8e3ee74a1824d57546f0b1b4f1cef5df93d6/Analysis/GeneralizedRiemannHypothesis/vendor/grh-lean)
- [Article](https://github.com/VladimirReshetnikov/ProveIt/tree/2a9f8e3ee74a1824d57546f0b1b4f1cef5df93d6/Analysis/GeneralizedRiemannHypothesis/Article)

The immediate article input is `ana:sec:smalldev`, especially
`ana:thm:gammasum` and `ana:thm:smalldev`. The manuscript contains a
bibliography and an explicit comparison with the related literature.
The archive does not duplicate the large upstream Lean tree.

