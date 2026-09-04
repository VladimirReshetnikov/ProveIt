# Canonical source integrity and publication validation

This receipt records the historical synchronized `b899` publication and two
older audit surfaces: the unregenerated purpose-specific closure ledger and the
preceding 134-page PDF. Every record remains valid only for its named source
checkpoint and is not a merged-current publication gate.

## Artifact identity

| Item | Size | SHA-256 |
| --- | ---: | --- |
| `inverse_fabius_theory.tex` | 293 lines; 11,514 bytes | `92fab1fae38bbcf86a45b51bfe7ff34e2801361df9d2f3d6aa3de4dc966eaa3c` |
| historical `b899` recursive TeX closure | 17 files; 10,682 lines; 431,748 bytes | `6e4e6fde424fd5046467b1f1cec0c19b6c10eb681fae4ba7cc53e14b6a5bf61e` |
| `inverse_fabius_theory.pdf` | 137 A4 pages; 2,045,486 bytes | `cee0de894656562fbdb75d6304055fc03fae06203985119419e465a5cd213995` |
| historical `SOURCE_CLOSURE.sha256` | Pre-overlay purpose-specific record of 23 build inputs | `aedf007c2cd150b1f83de6d8996b4bf31e267b3dbcec2d5cd4720f5d92122bdb` |
| current regenerated `SOURCE_CLOSURE.sha256` | 23 lexical source-closure entries; all passed | `76ac9fd6fadbf8291fe186a111330d098c2ed12ceda67aa32031d424ba67d611` |
| historical `inverse_fabius_theory.pdf` | 134 A4 pages; 2,027,726 bytes | `22bc68d855ad04dde9654e9fbd20b3ba7f05a33e3c5df0e5b80bb8991c94b41d` |

The first three rows form the historical synchronized `b899` receipt. The
fourth row records the older closure-ledger file identity; the fifth records
the regenerated 23-entry lexical source closure, not a PDF-parity gate. The
sixth row is the preceding historical PDF checkpoint. The historical rows do
not form a current source/PDF pair.

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

## Historical `b899` PDF build convergence

Exactly three serial halt-on-error passes were run from absent sidecars:

| Pass | Produced pages | PDF bytes |
| ---: | ---: | ---: |
| 1 | 132 | 1,983,313 |
| 2 | 137 | 2,045,485 |
| 3 | 137 | 2,045,486 |

Required final-log error, undefined-control, reference/citation, multiply
defined, duplicate-destination, missing-file, and rerun gates all close at zero.
The log has no vertical box and only two nonblocking horizontal boxes, 2.42 and
2.45 pt. All 137 pages are A4 at rotation zero, render successfully, and
contain nonblank extracted text. All 31 font rows are embedded and subset, six
are Libertinus, and none is Type 3. Metadata passed. Targeted visual inspection
covered physical pages 1, 61, 124, 135, and 137; every sampled page was clean.
Generated sidecars and temporary audit files were removed, and the forbidden
checksum-basename search passed.

## Historical retained-PDF build convergence

Exactly three guarded serial pdfLaTeX passes were run for the current source.
Every pass returned zero; the source graph was frozen for the run and no
TeX/Lean/Lake work interleaved with it.

| Pass | Produced pages |
| ---: | ---: |
| 1 | 132 |
| 2 | 137 |
| 3 | 137 |

The final log census is:

- fatal or emergency diagnostics: 0;
- undefined-control diagnostics: 0;
- undefined-reference diagnostics: 0;
- multiply-defined diagnostics: 0;
- actionable rerun diagnostics: 0;
- duplicate diagnostics: 0; and
- overfull horizontal or vertical boxes: 0.

The stable 137-page count on the final two passes is recorded here without
claiming byte identity between intermediate pass artifacts.

## PDF structural and visual checks

- Page format and count: 137 of 137 pages are A4 and 137 of 137 have rotation
  zero.
- PDF metadata: PDF 1.5 and unencrypted.
- Fonts: every reported font was embedded and subsetted, Libertinus was
  present, and no Type-3 font was present.
- The accepted visual gate was clean.

## Package integrity and cleanliness

- No canonical `.aux`, `.log`, `.out`, or `.toc` file, guarded-pass/render
  temporary, or shallow generated sidecar remains in the package.
- The current canonical asset tree contains 55 files. Its former 63-row asset
  checkpoint included eight historical ledger payloads that are now retired.
- The former 90-row root ledger and 63-row asset ledger are retired and
  recoverable from Git; the latter had SHA-256
  `b274fe39cde808c34e82789136af51616e9177f424763b3eec153bc18e10fa3c`.
  Their workflows no longer generate either root or asset `SHA256SUMS` files.
- The purpose-specific 23-input `SOURCE_CLOSURE.sha256` record remains a
  historical pre-overlay receipt and is not the current closure.
- Python byte-code caches and other transient files are not publication
  payloads.

The measured 17-file closure digest and 137-page PDF hash identify the current
synchronized `b899` publication. The `SOURCE_CLOSURE.sha256` file hash and
134-page PDF hash identify separate historical checkpoints; neither is a live
current-publication gate. Retired package-ledger receipts remain recoverable
from Git and are not live validation artifacts.
