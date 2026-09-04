# Canonical source integrity and retained-PDF validation

This receipt records two distinct audit surfaces for the canonical inverse
Fabius synthesis: the current source closure and the last fully reviewed PDF
artifact.  Because the source changed after that PDF was rendered, the hashes
below are **not** asserted to form a synchronized source/PDF pair.

## Artifact identity

| Item | Size | SHA-256 |
| --- | ---: | --- |
| `inverse_fabius_theory.tex` | 293 lines; 11,514 bytes | `92fab1fae38bbcf86a45b51bfe7ff34e2801361df9d2f3d6aa3de4dc966eaa3c` |
| `SOURCE_CLOSURE.sha256` | Exhaustive purpose-specific record of 23 permanent build inputs | `aedf007c2cd150b1f83de6d8996b4bf31e267b3dbcec2d5cd4720f5d92122bdb` |
| `inverse_fabius_theory.pdf` | 134 A4 pages; 2,027,726 bytes | `22bc68d855ad04dde9654e9fbd20b3ba7f05a33e3c5df0e5b80bb8991c94b41d` |

The first two rows identify the current source surface. The third is a
historical artifact receipt. A fresh three-pass render is required
before those surfaces may again be described as a publication pair.

The 23-input source closure consists of:

- the master `inverse_fabius_theory.tex`;
- the shared `../../../../fabius-notation.tex`;
- all nine chapter inputs:
  `chapters/00_scope_and_platform.tex`,
  `chapters/01_analyticity_and_elementarity.tex`,
  `chapters/02_inverse_iterates.tex`,
  `chapters/03_inverse_germs_and_deconvolution.tex`,
  `chapters/04_endpoint_all_orders.tex`,
  `chapters/05_dyadic_self_sampling.tex`,
  `chapters/06_computability.tex`,
  `chapters/07_certification_and_provenance.tex`, and
  `chapters/09_references.tex`;
- the three generated TeX inputs
  `assets/self-sampling/generated/appell_polynomials.tex`,
  `assets/self-sampling/generated/harmonic_tail_table.tex`, and
  `assets/self-sampling/generated/quadrature_table_display.tex`; and
- the nine publication PNG figures
  `assets/inverse-germs/figures/quarter_quantile_richardson.png`,
  `assets/endpoint/wright-omega/figures/carrier_comparison.png`,
  `assets/endpoint/wright-omega/figures/scaled_residuals.png`,
  `assets/endpoint/all-orders/figures/endpoint_error_plot.png`,
  `assets/endpoint/dyadic-completion/figures/psi_periodic.png`,
  `assets/endpoint/dyadic-completion/figures/dyadic_tail_convergence.png`,
  `assets/self-sampling/figures/defect_profiles.png`,
  `assets/self-sampling/figures/quadrature_weights.png`, and
  `assets/self-sampling/figures/appell_roots.png`.

## Retained PDF build convergence

At the retained PDF checkpoint, exactly three guarded serial pdfLaTeX passes
were run.  Every pass returned zero; the independently hashed input closure for
that build was identical before and after each pass, and no TeX/Lean/Lake work
interleaved with them.  These passes were not rerun after the current master and
shared-notation edits.

| Pass | Produced pages |
| ---: | ---: |
| 1 | 127 |
| 2 | 134 |
| 3 | 134 |

The final log census is:

- fatal or emergency diagnostics: 0;
- undefined-control diagnostics: 0;
- undefined-reference diagnostics: 0;
- multiply-defined diagnostics: 0;
- actionable rerun diagnostics: 0;
- duplicate diagnostics: 0; and
- overfull horizontal or vertical boxes: 0.

The stable 134-page count on the final two passes is recorded here without
claiming byte identity between intermediate pass artifacts.

## PDF structural and visual checks

- Page format and count: 134 of 134 pages are A4 and 134 of 134 have rotation
  zero.
- Text extraction: all 134 of 134 pages are nonblank.
- Page-box census: all 670 of 670 Media, Crop, Bleed, Trim, and Art boxes have
  the exact A4 geometry.
- Fonts: all 31 reported Type-1 font entries were embedded and subsetted; six
  entries were Libertinus; no Type-3 font was present.
- A fresh targeted visual inspection covered physical pages 1, 36, 65, 100,
  110, 132, and 134, including the Appell material and chapter-07 provenance.
  Every inspected page was clean.

## Package integrity and cleanliness

- No canonical `.aux`, `.log`, `.out`, or `.toc` file, guarded-pass/render
  temporary, or shallow generated sidecar remains in the package.
- The current canonical asset tree contains 55 files. Its former 63-row asset
  checkpoint included eight historical ledger payloads that are now retired.
- The former 90-row root ledger and 63-row asset ledger are retired and
  recoverable from Git; the latter had SHA-256
  `b274fe39cde808c34e82789136af51616e9177f424763b3eec153bc18e10fa3c`.
  Their workflows no longer generate either root or asset `SHA256SUMS` files.
- The purpose-specific 23-input `SOURCE_CLOSURE.sha256` record remains current.
- Python byte-code caches and other transient files are not publication
  payloads.

The retired package-ledger receipts, current purpose-specific source-closure
record, and PDF hash serve different purposes. Historical receipt validity and
current source integrity must not be mistaken for source/PDF synchronization.
