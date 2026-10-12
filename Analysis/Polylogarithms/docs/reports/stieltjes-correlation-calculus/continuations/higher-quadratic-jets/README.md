# Higher Quadratic Spectral Jets

**Harmonic–Stieltjes factorization defects, polylogarithmic second derivatives,
and exact mass collisions — 11 October 2026**

A 27-page research continuation for Vladimir Reshetnikov's ProveIt programme,
with self-contained proofs and reproducible independent checks.

## Reading artifact

`ProveIt_Higher_Quadratic_Jets_2026-10-11.pdf` is the compiled article.
`ProveIt_Higher_Quadratic_Jets_2026-10-11.tex` is a standalone source: it does
not require the modular section files to compile. The editable modular source
is `preamble.tex`, `sections/*.tex`, and `references.tex`; `verification/build.py`
assembles the standalone source from those files before building.

## Main results

The article proves an all-order factorization-defect formula, with explicit
harmonic coefficients and Stieltjes contact terms; a complete universal
higher-order vanishing classification; and the finite-part conversion at
noninteger-weight resonances. It evaluates every negative-integer second
spectral jet using a finite polylogarithm/order-derivative/integral family,
constructs a Gamma-normalized all-order mass-antiderivative ladder, and gives
the second derivative of a two-mass spectrum with every polynomial subtraction
and every collision coefficient explicit. It also provides a Gamma–dilogarithm
primitive for an ordinary convergent logarithmic-square family.

Theorem numbers and source-question mapping are in `integration/INTEGRATION.md`.
No minimality of the added integral coordinate, numerical period independence,
or resolution of the Gaussian S6/S8 conjectures is claimed.

## Replay

Python 3.10 or newer is required. The tested environment and source provenance
are in `PROVENANCE.json`.

```sh
python -m pip install -r requirements.txt
python verification/verify_manifest.py
python verification/check_exact.py
python verification/check_numeric.py --part factorization --output data/numerical_factorization.json
python verification/check_numeric.py --part fourier --output data/numerical_fourier.json
python verification/check_numeric.py --part collision --output data/numerical_collision.json
```

The three executed numerical suites contain 19 + 24 + 20 = **63 comparisons**
at 50 decimal working digits. The exact suite contains **834 assertions** and
**five rejected mutation controls**. Results are retained in `data/`.
Use alternate `--output` paths to preserve the delivered receipts. Replaying
will alter receipt timestamps or timings; manifest checking is intended for
the delivered unmodified bytes.

These numerical routines are diagnostics, not interval-certified evaluators.
They use precision-dependent generous truncations and ordinary quadrature.
The independent routes have explicitly stated parameter domains; large orders
or parameters close to a series boundary may require additional numerical
analysis. The proofs establish the all-index claims.

## Build and review

Install a LaTeX distribution with `pdflatex` (or `lualatex`), Latin Modern,
AMS packages, `mathrsfs`, `microtype`, and `hyperref`.

```sh
python verification/build.py
python -m pip install -r requirements-review.txt
python verification/review_pdf.py --render-directory review
```

The build uses three serial passes. The delivered final pass had no LaTeX
warnings, overfull boxes, or unresolved references. Every page was rendered
and reviewed in contact sheets; selected formula pages were inspected at
full resolution. `data/pdf_review.json` records the delivered PDF hash and
review scope. A new build may have different PDF metadata and needs its own
review; old hash receipts do not review a changed PDF.

## Source and integration status

Repository metadata anchor: `73f18ef013d5b74eafc883efb2c15210642df12a`.
The matching-title predecessor TeX was read from the user's Library. Its hash
is recorded; its byte identity with the incoming ZIP was not established.
The six incoming archive interiors were **not** inspected. No comprehensive
novelty or repository-wide correctness audit is claimed.

A suitable additive destination is
`Analysis/Polylogarithms/docs/reports/higher-quadratic-jets/`.
No remote repository files were modified. Historical sources should be
preserved, and the predecessor's correct first-jet parity theorem should not
be overwritten with the distinct higher-order classification.
