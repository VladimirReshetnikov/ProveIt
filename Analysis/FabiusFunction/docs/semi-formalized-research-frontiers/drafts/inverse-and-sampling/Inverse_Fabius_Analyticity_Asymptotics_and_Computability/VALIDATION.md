# Canonical source integrity and publication validation

This record separates the accepted current inverse source/PDF receipt in the
[authoritative register](../../MANIFEST.md#current-post-merge-publication-receipts)
from the historical publication and purpose-specific closure checkpoints below.
The closure generator is maintained independently and is not a package-wide or
PDF checksum gate.

## Artifact identity

| Item | Size | SHA-256 |
| --- | ---: | --- |
| `inverse_fabius_theory.tex` | 293 lines; 11,514 bytes | `92fab1fae38bbcf86a45b51bfe7ff34e2801361df9d2f3d6aa3de4dc966eaa3c` |
| historical ordered 14-file TeX graph | 10,909 lines; 438,542 bytes | `24bdab6491f5ca84fbb9e716f92c7923e8961b6acbc793d9aa5e0faa68852444` |
| historical first-merge `SOURCE_CLOSURE.sha256` | Purpose-specific source-only record of 23 inputs | `e07cb51f4fe072cd79a014cc891cb8cede62880593d7659b17da9377a21099bc` |
| historical 137-page PDF | 137 A4 pages; 2,045,463 bytes | `ca403c74e2b46923ce9ac1eda547ab1bcb5e71039b35c8ee394acdd2014c4f8e` |
| historical final build log | 1,569 lines; 64,081 bytes | `d4aa25579c958e11c59d914c74dfca331fc2bbccf7bba4715dcd18fa050e771f` |
| historical incoming `b899` recursive TeX closure | 17 files; 10,682 lines; 431,748 bytes | `6e4e6fde424fd5046467b1f1cec0c19b6c10eb681fae4ba7cc53e14b6a5bf61e` |
| historical incoming `b899` PDF | 137 A4 pages; 2,045,486 bytes | `cee0de894656562fbdb75d6304055fc03fae06203985119419e465a5cd213995` |
| historical closure-file identity | Pre-overlay purpose-specific record | `aedf007c2cd150b1f83de6d8996b4bf31e267b3dbcec2d5cd4720f5d92122bdb` |
| historical earlier PDF | 134 A4 pages; 2,027,726 bytes | `22bc68d855ad04dde9654e9fbd20b3ba7f05a33e3c5df0e5b80bb8991c94b41d` |

Each historical source/PDF tuple is scoped to its named checkpoint. The
purpose-specific 23-input record is regenerated separately for merged inputs;
its generated file and checker are authoritative for that narrow scope.
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

## Historical incoming `b899` PDF build convergence

Exactly three serial halt-on-error passes from absent sidecars produced
132/137/137 pages and 1,983,313/2,045,485/2,045,486 bytes. The required
log, reference/rerun, metadata, all-page A4/rotation/render/text, font, visual,
cleanup, and forbidden-basename gates passed. All 31 font rows were embedded
and subset, six were Libertinus, none was Type 3, and the only box diagnostics
were nonblocking 2.42 and 2.45 pt horizontal boxes.

## Historical first-merge PDF build convergence

Exactly three guarded serial pdfLaTeX passes were run for that source snapshot.
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

- The historical final log is pinned above; no transient pass/render file is
  a publication payload.
- The canonical asset tree contains 55 retained files. Its former 63-row asset
  checkpoint included eight historical ledger payloads that are now retired.
- The former 90-row root ledger and 63-row asset ledger are retired and
  recoverable from Git; the latter had SHA-256
  `b274fe39cde808c34e82789136af51616e9177f424763b3eec153bc18e10fa3c`.
  Their workflows no longer generate either root or asset `SHA256SUMS` files.
- The purpose-specific 23-input `SOURCE_CLOSURE.sha256` record is generated
  and checked independently for the merged inputs and has no whole-package or
  PDF-parity role; earlier digests above remain provenance only.
- Python byte-code caches and other transient files are not publication
  payloads.

The accepted current inverse source/PDF receipt is recorded in the
authoritative register linked above. All earlier 134- and 137-page tuples and
closure-file identities remain explicit history; retired package-ledger
receipts remain Git-recoverable and are not live validation artifacts.
