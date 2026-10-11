# Unequal-Twist Stieltjes Jets

**Monodromy Obstructions, Convergent Harmonic Expansions, Gamma Convolutions,
and Multishift Zeta Finite Parts**

Research continuation prepared for Vladimir Reshetnikov's ProveIt programme,
10 October 2026, with ChatGPT.

## Reading and integration

`article.pdf` is the 19-page standalone article; `article.tex` is its complete,
self-contained LaTeX source, including the bibliography. The four-page
`integration/addendum-preview.pdf` previews the additive canonical fragment
`integration/07-unequal-twist-jets.tex`. No repository files were changed.

The targeted repository source anchor is commit
`b1df802799851c62a860570c3ac78ee31b9f5c04`. See `SOURCE_AUDIT.md` and
`source-provenance.json` for the actual reading scope, input Git blob identifiers,
and limitations. In particular, the incoming ZIP directory was inventoried,
but its binary archive contents were not exhaustively audited.

## Main results

The article proves a precise finite functional closure classification: a
product of distinct shifted integer rational powers decorated with logarithms
belongs to the finite constant-coefficient span of single-shift integer-order
jets exactly when it is rational or only one shift is active. The proof passes
from eventual Fourier-sequence equality to an analytic identity and then uses
monodromy. This is not a numerical period-independence theorem or a resolution
of isolated S6/S8 values.

A convergent expansion supplies the positive counterpart. Every finite mixed
twist convolution has a one-centre expansion, entire in its order parameters,
with explicit Pochhammer, harmonic and Stirling coefficients. Finite Fourier
heads repair arbitrary real nonintegral shifts across frequency intervals.
Further consequences include ordinary rational-grid log-Gamma convolutions;
unilateral multishift Lerch identities and every ordinary primitive; an
all-index Hurwitz-jet formula and lower-degree recursion for logarithmic
sharp-cutoff constants; Gamma antiderivatives; all transverse spectral-ray
jets; and a pole-aware cyclotomic Stieltjes filter.

The source-count discrepancy in the editorial ledger is flagged for
synchronization. No new mathematical error was found in the targeted canonical
chapters. The safeguards against lost contact terms, phases, zero-order
Pochhammer derivatives and pole logarithms are not accusations that those
chapters made these mistakes. No global literature-priority claim is made.

## Reproduction

Python 3.10 or later is required. The recorded environment uses Python 3.13,
SymPy 1.14.0 and mpmath 1.3.0; precise patch versions are in the reports.

```bash
python -m pip install -r requirements.txt
python scripts/check_package.py
python scripts/verify.py --part all --dps 65
python scripts/verify_extended.py --dps 65
# Full rerun at both recorded working precisions:
python scripts/replay_all.py
```

The executed suites pass **824 finite exact assertions** (779 core plus 45
supplemental) and **96 numerical comparisons at each of 65 and 85 working
decimal digits** (38 spectral, 28 scalar, 4 ordinary Gamma integrals and 26
supplemental). JSON reports preserve individual residuals. The largest recorded
scaled residual in either complete numerical run is about `6.85e-45`; test
tolerances range from `1e-34` to `1e-38`. Working precision is not an accuracy
guarantee: some residuals are limited by fixed finite series or contour
truncations, and none is an interval certificate.

The numerical root-of-unity order-jet evaluator uses an Euler-transformed
series with 150 extra working digits for its internal finite differences.
A direct numerical finite-difference call near integral polylogarithm order
was unstable and is not used in the delivered root-of-unity tests. The
scalar cutoff comparisons use an independently assembled Euler--Maclaurin
tail, not the mixed Hurwitz expansion under test. Ordinary Gamma integrals
are checked by quadrature against half-grid positive-order zeta jets.

To build the PDFs, install pdfLaTeX through TeX Live or MiKTeX with the standard
packages named in the source, then run:

```bash
python scripts/build.py
```

The builder makes three passes in temporary directories, rejects overfull
boxes and unresolved references, and records its logs in `validation/build/`.
It does not perform visual review. The delivered PDFs were rendered and
reviewed separately; the receipt is `validation/pdf-review.json`. A rebuild
changes artifacts and may change binary metadata. Old hash and visual-review
receipts do not automatically apply to a rebuilt PDF.

`SHA256SUMS` checks integrity, not mathematical correctness. Replaying scripts
or rebuilding files changes the relevant receipts; regenerate the manifest
only after deliberately accepting the new artifacts.

## Scope and status

Full ordinary mathematical proofs are provided. Finite checks do not replace
the analytic proofs; neither the article nor the addendum is proof-assistant
formalized or independently peer reviewed. The precise theorem status and
integration dependencies are in `THEOREM_LEDGER.md` and `integration/INTEGRATION.md`.
Eight further research directions are developed in Section 12 of the article.
