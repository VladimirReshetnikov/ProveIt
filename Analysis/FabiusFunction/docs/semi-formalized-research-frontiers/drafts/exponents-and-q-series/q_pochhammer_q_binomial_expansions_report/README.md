# Local, Boundary, and Reciprocal Expansions of q-Analogues

This package contains a standalone, audited companion report on local and
boundary expansions of q-Pochhammer symbols, Gaussian coefficients, and
related q-analogues.

## Package contents

- `q_analog_expansions_report.tex` — normalized report source (2,917 lines).
- `q_analog_expansions_report.pdf` — validated 39-page report.
- `q_expansion_experiments.py` — exact-symbolic and high-precision numerical
  checks (408 lines).
- `numerical_results.txt` — byte-reproduced output from the bundled program
  (44 lines).
- `pdf_preflight.json` — machine-readable PDF/build validation summary.
- `MANIFEST.sha256` — immutable five-entry arrival ledger.
- `SHA256SUMS.txt` — authoritative seven-entry ledger for the current package,
  excluding the ledger itself and including the arrival ledger.

The extracted package contained no figures, so there are no figure sources or
raster/vector assets to regenerate.

## Provenance and ledgers

Before normalization, every entry in the extracted `MANIFEST.sha256` was
verified against the arrival bytes (5/5). The manifest is preserved
byte-for-byte as historical provenance; its SHA-256 digest is
`17307793f182da4757f0344da4d7aec57b4f92fb8483005e92ea7b3c244a18cb`.
Because the report and README were subsequently audited and normalized, the
arrival manifest is deliberately not a current-file ledger.

Use the separate current ledger for the live package:

```sh
sha256sum -c SHA256SUMS.txt
```

## Mathematical status boundary

The report was checked against the live Lean source and the existing
`q_pochhammer_q_binomial_monograph` on 2026-08-30.

- Lean presently covers the finite algebra/evaluation layer: Pascal recursion,
  symmetry, the denominator-free factorial relation, the finite q-binomial
  theorem, evaluation at q=1, and finite base reversal.
- The existing monograph already contains the Gaussian Bernoulli expansion and
  centering, the q=0 rectangular-partition formulas, reciprocity, cyclotomic
  factorization, the q-Lucas value at roots of unity, and the value at q=-1.
  Their appearances here are baseline or rederivations, not novelty claims.
- General logarithmic/Bell jets, the first derivative at q=-1, higher
  cyclotomic jets, infinite-product and q-gamma asymptotics, radial
  root-of-unity coefficients, hypergeometric operator deformations, and
  double-scaling formulas have no exact live Lean counterpart located by this
  audit. A result described as “proved here” is a paper proof only.
- “Companion-only” means absent from the inspected monograph; it makes no claim
  of worldwide priority.
- Uniform resonant scaling, higher cyclotomic jets, resurgence, certified
  remainder control, and formal verification remain open or proposed. The
  cyclic-gamma statement is an informal research target, not a theorem-grade
  conjecture until its domain, branches, normalization, and remainder are
  fixed.

The audit also made analytic domains explicit. Infinite-product logarithms use
the branch obtained by continuation from the stated base point; q-exponential
log formulas assume real `0 < q < 1`, `|h*x| < 1`, and continuation from
`x = 0`. The basic hypergeometric operator statement excludes singular
denominator parameters and any vanishing shifted-factorial denominator. Its
operator expansion is coefficientwise/asymptotic, not a finite identity in the
deformation parameter.

## Reproducing the computation

The recorded check was safely replayed offline with Python, SymPy, and mpmath:

```sh
UV_OFFLINE=1 uv run --offline --with sympy --with mpmath \
  python q_expansion_experiments.py
```

The replay was byte-identical to `numerical_results.txt`, whose SHA-256 digest
is `a2052f71be8ca67e6728c522377d34284dc03691cdc1376b0f5cf053ec5099eb`.
The exact q=1 and q=-1 suites each cover all 230 pairs `0 <= k <= n <= 20`.
Additional adversarial spot checks covered the q=-1 derivative, both
q-exponential series through cubic order, the q-difference series, a basic
hypergeometric coefficient, eta and negative-eta cases, and a theta-Poisson
case; all passed.

## Rebuilding the PDF

The source uses the repository's exact canonical primary preamble: `article`,
A4 paper, 27 mm margins, and Libertinus text fonts. From a clean directory, the
frozen final source was compiled with exactly three strict serial passes:

```sh
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error q_analog_expansions_report.tex
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error q_analog_expansions_report.tex
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error q_analog_expansions_report.tex
```

All three passes succeeded. The third pass had zero LaTeX/package warnings,
undefined references or citations, rerun requests, duplicate labels or
destinations, overfull boxes, underfull boxes, and fatal errors.

## PDF validation

- 39 pages; all pages and all Media/Crop/Bleed/Trim/Art boxes are A4
  (595.276 by 841.89 points), with zero rotation.
- All 23 font records are embedded and subset; four are Libertinus text-font
  records. Canonical Computer Modern math is intentional. There are no Type 3
  or Latin Modern fonts.
- `pdftotext -layout` extraction succeeds (2,511 lines, 147,482 bytes) and
  preserves the provenance/status boundary, public names, formulas, and
  references.
- The PDF contains no raster images and is not encrypted or scan-only.
- Focused visual inspection of pages 1, 17--19, and 39 covers the title,
  complete first jet, new denominator-free ring theorem and Lean crosswalk,
  following chapter boundary, formula map, and bibliography; no clipping,
  overlap, corruption, or malformed glyphs was found. Programmatic geometry
  and text checks cover all 39 pages.

See `pdf_preflight.json` for the compact machine-readable record.

## Lean crosswalk

The value half of the report's complete first-jet theorem at `q = -1` is now
formalized in the stronger setting of an arbitrary commutative ring.  The
even-row/odd-column zero follows from reciprocal symmetry in
`FabiusFunction.QBinomialReciprocity`; the other three parity values and the
paired even- and odd-length finite q-Pochhammer product identities live in
`FabiusFunction.GaussianBinomialAtNegOne`, whose induction reuses that zero
theorem.  The focused Lake target has been compiled successfully.

The first-derivative formulas and the resulting characteristic-zero
simple-root theorem are not yet formalized.  The report's manuscript proof is
not a substitute for those remaining Lean declarations.

## Baseline source

The report is a self-contained companion to:

`Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/exponents-and-q-series/q_pochhammer_q_binomial_monograph/q_pochhammer_q_binomial_monograph.tex`

in the `VladimirReshetnikov/ProveIt` repository, live source inspected on
2026-08-30.
