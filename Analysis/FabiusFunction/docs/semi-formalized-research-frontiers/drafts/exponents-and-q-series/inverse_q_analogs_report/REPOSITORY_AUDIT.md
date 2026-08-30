# Repository audit

Audit date: 2026-08-30.

## Intake and provenance

- Recovered archive:
  `drafts/incoming/inverse_q_analogs_report.zip`.
- Outer size: 894,405 bytes.
- Outer SHA-256:
  `471ee715022df77f2c5f45b86c213e50e980478eee1a6fc48dd91556cdaeb627`.
- Archive integrity: pass.
- Path audit: 19 entries under one wrapper, 17 regular payload files, no
  traversal, absolute path, drive path, symlink, or conflict marker.
- Submitted checksum ledger: none.
- Repository-created arrival ledger: 17 rows, verified 17/17 against the
  recovered archive before any normalization or editorial change.

`ARRIVAL_SHA256SUMS.txt` is intentionally historical. It records arrival bytes
and is not expected to verify after the audited source, script, figures, and PDF
were normalized.

## Formal-corpus boundary

The live Lean corpus supplies selected foundations rather than this report's
inverse theory. Relevant exact declarations include:

- `Fabius.finiteQPochhammerIn`, `Fabius.finiteQPochhammerIn_add`,
  `Fabius.gaussianBinomial`, and `Fabius.finite_qBinomial_theorem` in
  `FabiusFunction.FiniteQBinomialCore`;
- `Fabius.finiteQPochhammerIn_base_reversal` and its unit-valued strengthening
  in `FabiusFunction.QPochhammerElementaryIdentities`, with the nonzero
  argument/base boundary stated in the report;
- `Fabius.qPochhammerInf`, `Fabius.tendsto_finiteQPochhammerIn`, and
  `Fabius.qPochhammerInf_pos` in `FabiusFunction.LimitConditionNumber`;
- `Fabius.complexQPochhammerInf`,
  `Fabius.multipliable_one_sub_mul_pow_complex`,
  `Fabius.hasProd_complexQPochhammerInf`, and
  `Fabius.tendsto_finiteQPochhammerIn_complex` in
  `FabiusFunction.RvachevPochhammerFactorization`;
- the norm-bounded logarithmic/product bridge in
  `FabiusFunction.EulerLogTransform`, evaluated Gaussian positivity in
  `FabiusFunction.GeneralQConditionNumber`, the value at one in
  `FabiusFunction.GaussianBinomialAtOne`, and the rational positive-base bridge
  in `FabiusFunction.GeometricLagrangeQMoments`.

These declarations do not prove coefficientwise positivity, strict
monotonicity in the base, inverse branches, critical-value discriminants,
Maxwell collisions, monodromy, q-special-function inverses, or inverse
asymptotics. No report-specific labelled inverse/branch/discriminant/asymptotic
result has an exact public Lean counterpart. The source monograph's 184-row
ledger independently records 35 exact, 24 partial, 122 without counterparts,
and 3 interface-only rows.

## Hostile mathematical review

The central finite-product branch atlas, discriminant factorization, principal
infinite-product inverse, Gaussian reversion, and q-gamma/q-beta branch
arguments had no further mathematical blocker. The following overstatements
were repaired in the retained TeX:

1. The nonnegative-order inverse now excludes the infinite-order limit from
   its attained target range; the negative-argument analogue also calls its
   terminal value an unattained limit.
2. The safeguarded-Newton result now assumes twice continuous differentiability
   and a derivative bounded away from zero, accepts Newton only in the middle
   half of the bracket, proves a three-quarter width contraction, and reserves
   quadratic convergence for the accepted local Newton regime.
3. The naive near-unit-base product cost now includes both the tolerance
   logarithm and the additional logarithm of the reciprocal base gap.
4. Radical non-solvability is conditional on the proved symmetric-monodromy
   hypotheses; the uniform generic-Galois statement remains conjectural.
5. The q-Bessel/q-Airy sentence is limited to standard parameter regimes, the
   conclusion no longer implies bibliographic novelty, and the order-six sheet
   identification is explicitly high-precision numerical evidence rather than
   interval certification.

The exact order-five collision polynomial proves existence and uniqueness of
the positive collision parameter. Identification of the colliding sheets at
orders five and six remains numerical, as labelled. No worldwide priority is
asserted.

## Computational replay

The script was replayed without network access under CPython 3.13.14 with
`mpmath` 1.3.0, `sympy` 1.14.0, `numpy` 2.3.5, and `matplotlib` 3.10.8.

- Seven data/text outputs: 7/7 byte-identical to arrival before repository
  normalization; five CSVs are stored and regenerated with LF endings.
- Five plot PDFs: plotted content reproduced; their bytes were intentionally
  changed by the archival PDF-font setting.
- Regenerated plot fonts: embedded/subset CID TrueType, no Type 3.
- Reported order-five collision root:
  `0.84015337830837665866293643188913294310139258365832`.
- Numerical output is evidence only and is not presented as interval proof.

## Document normalization and validation

The book-style arrival was mechanically mapped to the shared canonical article
style: A4 paper, 27 mm margins, the canonical visual/theorem/macro/listing
block, and Libertinus prose. Parts and the three-level mathematical hierarchy
were preserved as article sections/subsections/subsubsections. Appendix anchors
were made unique, and the five figures use ordinary article floats.

The frozen TeX was built from a clean auxiliary state with exactly three strict
serial `pdflatex` passes. The resulting PDF is 51 A4 pages, all rotation zero.
Its final log is free of errors, warnings, unresolved references/citations,
rerun requests, duplicate anchors, and overfull/underfull boxes. All 34 font
rows are embedded and subset, including six Libertinus rows; there are no Type
3 or Latin Modern fonts. All pages and all five figures were visually checked.
