# Compensated positive kernels for polylogarithms

**Subcritical zero geometry, a sharp critical Euler constant, and exact generalized Stieltjes order at every depth**

Research continuation prepared for ProveIt, 9 October 2026 (America/Los_Angeles). The standalone article has 25 pages. Repository baseline: `a0a90ef31877f98be437191c48b46f02d5456867`.

## Mathematical contribution

The article proves the two conjectures labeled `conj:subcritical` and `conj:constant` in `real_order_threshold.tex`. A compensated positive measure proves angular uniqueness and slit-plane nonvanishing below the finite signed-measure threshold, and extends strict normalized-radius increase to all positive `a,b` with `a+b <= 1`. Combined with the previously proved supercritical case, angular uniqueness and slit-plane nonvanishing hold for every positive pair.

A beta likelihood-ratio argument proves strict decrease of `-Im F_(a,w-a)(i rho)` in `a` at fixed total weight `w > 0`, for `0 < rho <= 1`. It proves the optimal uniform critical Euler constant `pi/4 + log(2)/2`. Positive transport supplies Euler bounds at every positive pair and independent affine strides. At strict depth `d`, the normalized function has exact generalized Stieltjes order `d`, and `c_(n+d) n!/(alpha)_n` is a positive Hausdorff moment sequence exactly for `alpha >= d`.

These are written mathematical proofs, not claims of independent refereeing or proof-assistant formalization. Novelty is assessed against the inspected project material, not by an exhaustive worldwide priority search. The S6 period identity and the general supercritical normalized-radius conjecture remain open here.

## Contents

| File or directory | Purpose |
|---|---|
| `article.tex`, `article.pdf` | Standalone source and compiled 25-page article; all proofs and further questions |
| `code/certify.py`, `data/exact_certificates.json` | Standard-library exact rational verifier and frozen certificates |
| `code/diagnostics.py`, `code/symbolic_checks.py` | Optional independent floating-point and symbolic checks |
| `data/angular_proposals.json` | Rational endpoints; accepted only by a separate exact sign check |
| `CLAIM_STATUS.json`, `CORRECTIONS.md`, `PROVENANCE.json` | Claim scope, audit cautions, source identity and limitations |
| `integration/` | Editorial insertion fragment and integration instructions |
| `MANIFEST.sha256`, `code/verify_integrity.py` | Package byte-integrity check, not mathematical verification |

## Exact replay

From this directory, with ordinary Python 3.10 or later:

```sh
python code/verify_integrity.py
python code/certify.py --check
```

Do not use Python's `-O` option: the verifier intentionally requires assertion checks. The exact verifier needs no third-party packages, network access, CAS, or trigonometric library. It checks 3,915 integer-root inequalities, nine Gaussian enclosures of width below `3.187e-58`, twelve subcritical angular sign brackets, 728 positive finite differences, 96 positive Hankel determinants, and 288 affine Euler-coefficient inequalities. Its recorded results are regenerated, not merely read and trusted.

The twelve angular brackets have cosine width `5e-12`. Uniqueness is supplied by the analytic theorem. Their rational endpoint proposals may originate from numerical root finding, but no proposal is accepted without exact rational signs and an explicit series remainder.

## Optional diagnostics

Install the packages listed in `requirements-diagnostics.txt`, then run:

```sh
python code/diagnostics.py
python code/symbolic_checks.py
python code/certify.py
```

The first command rewrites numerical diagnostics and rational bracket proposals. The final command independently verifies the new proposals and writes a new exact certificate. For a byte-for-byte replay of the frozen certificate, run `certify.py --check` before regenerating proposals. Different numerical-library versions may propose different valid brackets.

The recorded independent 128-node generalized Gauss--Laguerre quadrature differs from the Euler centers by at most approximately `3.109e-15`. This is an observed floating-point discrepancy, **not** a certified quadrature-error theorem. All six fixed-weight diagnostic grids show the predicted decrease. Seven separate symbolic rational identities pass. The proofs do not infer global statements from these finite tests.

## Rebuilding the PDF

With `pdflatex` and the packages named in the preamble installed:

```sh
python code/build_article.py
```

The builder runs three LaTeX passes in a temporary directory and copies back only the PDF. A rebuilt PDF can have different metadata bytes, so the original byte manifest is not expected to validate a modified or rebuilt package. The source is standalone: no external bibliography file, image, or custom font file is needed.

## Integration

Suggested destination:

`Analysis/Polylogarithms/docs/reports/compensated-polylogarithms/`

Read `integration/README.md` and `CORRECTIONS.md` before insertion. Preserve the old finite signed-measure threshold and the old critical atom. Below threshold, the new positive measure has infinite mass, so its moments must remain compensated. Do not promote the new higher-depth angular-count conjecture to a theorem, or interpret exact Stieltjes order as arithmetic period independence.

No upstream files or branches were modified in preparing this package.
