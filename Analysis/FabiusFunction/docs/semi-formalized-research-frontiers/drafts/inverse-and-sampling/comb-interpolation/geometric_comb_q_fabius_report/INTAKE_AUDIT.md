# Intake audit: geometric-comb q/Fabius report

Audit date: 2026-08-30

## Scope and arrival provenance

The intake lease covered only this package directory. No group README,
`MANIFEST`, Git/index state, Lean source, incoming ZIP, or neighboring package
was changed.

No source ZIP attributable to this package was present in the audited
workspace. No archive hash is therefore asserted. The delivered
`SHA256SUMS.txt` was checked successfully against all 16 entries before any
payload edit and was then preserved byte for byte as
`ARRIVAL_SHA256SUMS.txt` (SHA-256
`7fd96e3a02cdb05e1660fa1bece7bc02872a8eecc5f0c37725537276cf0b6b99`).
That ledger excludes itself, so the arrival directory contained 17 regular
files.

The report identifies source snapshot
`e5175d5eb78d66f4e31db3bc506541b9bae12c57` (2026-08-30). It is an ancestor
of intake head `ffcdbdac47246bd553f272bd1ceac441f8dd4f0c`. A path-restricted
`git diff --exit-code` found no change between those commits in the eight Lean
files containing the declarations listed below. No Lean file was edited or
rebuilt during intake.

## Mathematical and Lean-status audit

In the manuscript, “theorem,” “proposition,” “lemma,” and “corollary” mean
proved in the manuscript, not automatically checked by Lean. The following
finite inputs have direct declarations in the unchanged Lean source:

| Lean declaration | Defining source at intake head |
|---|---|
| `finite_qBinomial_theorem` | `FiniteQBinomialCore.lean:556` |
| `gaussianBinomial_reciprocity` | `QBinomialReciprocity.lean:129` |
| `completeHomogeneousEvalOn_geometric_range` | `GeometricLagrangeCompleteHomogeneous.lean:42` |
| `geometricLagrangeWeight_eq_qBinomial` | `GeometricLagrangeQBinomial.lean:316` |
| `geometricLagrangeQMoment_eq_residual_qBinomial` | `GeometricLagrangeQMoments.lean:446` |
| `sum_abs_geometricLagrangeWeight_eq_qPochhammer_ratio` | `GeometricLagrangeQMoments.lean:714` |
| `halfMoment_eq_fabius_formula` | `AnalyticMoments.lean:444` |
| `integral_eval_rvachevDeconvolvedPolynomial_add_mul_rvachev` | `RvachevMomentAppell.lean:407` |
| `normalized_sum_Ioo_rvachevDeconvolvedPolynomial_mul_shifted_rvachevUp` | `RvachevPolynomialSynthesis.lean:181` |

No one-to-one Lean declaration was found for the report-specific iterated
`D_q`/divided-difference theorem, Gaussian Newton basis pair,
arbitrary-evaluation residual, analytic infinite-Newton convergence theorem,
boundary-layer or global Lebesgue asymptotics, Newton--Jackson quadrature,
Fabius residue/fixed-jet/gap bounds, or Gaussian--Appell cardinal,
biorthogonality, and right-inverse packaging. These retain manuscript-proof
status only. Rvachev fixed-radius polynomial synthesis is, by contrast,
directly formalized by the declaration above; the intake text now says so.

The two-sided Fabius gap asymptotic, second-order Lebesgue expansion, and
Hermite saddle displacement remain conjectures in both layers. Growing-order
Hermite anchoring remains an open problem. The final appendix status ledger
includes all three conjectures explicitly.

The hostile read-through made these material scope repairs:

- Analytic Hermite convergence now assumes a centered disk `|z| < R_0` with
  `R_0 > c`, exactly as required by the proof.
- The numerical search and CSV fields are described as a maximum on the
  persistent top gap, not as an independently certified finite-degree global
  maximum.
- The Rvachev-loop norm identity is asserted only on `[-1,1]`, where the
  compact-support reduction used in the proof applies.
- Novelty language is limited to the explicitly inspected source baseline;
  the report makes neither an exhaustive repository nonduplication claim nor
  an unrestricted priority claim.
- The appendix status ledger now distinguishes the directly formalized
  Rvachev synthesis from manuscript-only packaging and records the Hermite
  saddle conjecture.

## Source normalization and numerical replay

The final TeX uses the canonical primary-report setup: A4 paper, 27 mm
margins, 11 pt one-sided book layout, T1/UTF-8 input, Libertinus with a
documented Latin Modern fallback, microtype, and Unicode hyperlinks with
`hypertexnames=false`.

The numerical replay used Python 3.13.14 and the 12 exact package pins in
`requirements.txt`. Exact identities use `fractions.Fraction`; floating point
is confined to positive Lebesgue sums, one-dimensional top-gap optimization,
and plotting. Two consecutive runs in the pinned environment reproduced all
11 generated data/figure artifacts byte for byte. Console output was:

```text
All exact identity checks passed.
Endpoint Lebesgue limit: 8.25598793577825006554414084943
Global asymptotic prefactor: 1.75421915716734780836138830414
```

The Fabius interpolation CSV and exact identity transcript also reproduce
their arrival bytes. Besides semantic header repairs, the only arrival/final
Lebesgue-data differences are in the `n=17` floating optimizer row:
`delta x_top_gap_max = +7.3454402560457766e-09`,
`delta n(1-x_top_gap_max) = -1.2487248435277820e-07`,
`delta log10 maximum = -7.1054273576010019e-15`, and
`delta asymptotic ratio = -1.3211653993039363e-14`. Exact fields are unchanged.
`NUMERICAL_REPLAY.txt` records the pins, command, comparison, and all 11
generated-artifact hashes.

Matplotlib was forced to the noninteractive Agg backend; PDF/PS font type 42
and fixed PDF/PNG metadata were set. The four regenerated standalone PDFs are
single-page vector plots. Across them there are nine font rows, all
embedded/subset CID TrueType, with zero Type 3 fonts and zero raster objects.

## Frozen build and PDF preflight

The final source was frozen at 3,575 lines with SHA-256
`37e71ad371673a8c301d1b2f23e516cf34b904fb98f22e18448e4dedfe939c08`.
The experiment script is 637 lines with SHA-256
`5f70dfb4dbba3af018f5be1abb09b7521c906658317d12bbed20b07cae56d365`.

Starting from a clean auxiliary state, the frozen TeX received exactly three
strict, serial invocations of:

```text
pdflatex -halt-on-error -file-line-error -interaction=nonstopmode geometric_comb_q_fabius_report.tex
```

All three exited successfully. The third-pass log has zero LaTeX warnings,
package warnings, undefined-reference hits, rerun requests, overfull boxes,
underfull boxes, and fatal errors. No further TeX pass was run.

The final PDF title is “Geometric-Comb Interpolation, Gaussian Pascal
Transforms, and the Fabius–Rvachev Boundary Layer.” It is 68 pages and
818,043 bytes, with SHA-256
`bcd2559f1e6f4be608c291c6ef5de48108c3b0d78139ecf1a5672942d72d9b92`.
Poppler 22.02.0 opened, inspected, extracted, and rendered it successfully.

- All 68 pages are 595.276 by 841.89 pt A4 with rotation zero; all seven
  reported page-box families were checked on every page, with zero deviations.
- All 31 PDF font rows are embedded and subset. Four are Libertinus rows,
  nine are the embedded CID TrueType plot fonts, and none is Type 3.
- `pdftotext -layout` produced 181,173 bytes, 3,324 lines, and 68 page records;
  it found no literal `??` marker and includes the Hermite status row.
- `pdfimages -list` found zero raster objects in the report PDF; its four plots
  remain vector content.
- All 68 pages rendered at 110 dpi to 910 by 1287 pixel JPEGs. Contact-sheet
  inspection of pages 1--17, 18--34, 35--51, and 52--68, plus full-size review
  of the archive/status/bibliography tail, found no clipping, overlap,
  malformed glyph, blank-content loss, or illegible plot/table.
- The PDF is unencrypted, has no form, JavaScript, or parser “suspects,” and
  reports PDF version 1.5.

Machine-readable details are in `pdf_preflight.json`. After validation, all
LaTeX auxiliaries were removed. The final package contains 21 regular files;
the exhaustive `SHA256SUMS.txt` has 20 entries and excludes only itself.
