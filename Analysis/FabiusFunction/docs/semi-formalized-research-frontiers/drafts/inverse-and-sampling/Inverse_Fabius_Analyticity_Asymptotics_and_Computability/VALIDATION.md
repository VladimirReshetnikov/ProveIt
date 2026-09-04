# Historical first-merge source and PDF validation

This receipt records the accepted first-merge build of the canonical inverse
Fabius synthesis. Later source changes make the tuple historical; the accepted
current source/PDF receipt is in the [authoritative receipt
register](../../MANIFEST.md#current-post-merge-publication-receipts). The live
23-input closure has also been regenerated. The
14-file aggregate pins the TeX graph used by that historical build, while the
recorded first-merge 23-input closure digest identifies the corresponding
source-only snapshot that also accounted for generated inputs and publication
figures.

## Artifact identity

| Item | Size | SHA-256 |
| --- | ---: | --- |
| `inverse_fabius_theory.tex` | 293 lines; 11,514 bytes | `92fab1fae38bbcf86a45b51bfe7ff34e2801361df9d2f3d6aa3de4dc966eaa3c` |
| ordered 14-file TeX graph | 10,909 lines; 438,542 bytes | `24bdab6491f5ca84fbb9e716f92c7923e8961b6acbc793d9aa5e0faa68852444` |
| first-merge `SOURCE_CLOSURE.sha256` | Purpose-specific source-only record of 23 permanent inputs | `e07cb51f4fe072cd79a014cc891cb8cede62880593d7659b17da9377a21099bc` |
| `inverse_fabius_theory.pdf` | 137 A4 pages; 2,045,463 bytes | `ca403c74e2b46923ce9ac1eda547ab1bcb5e71039b35c8ee394acdd2014c4f8e` |
| final build log | 1,569 lines; 64,081 bytes | `d4aa25579c958e11c59d914c74dfca331fc2bbccf7bba4715dcd18fa050e771f` |

The root and aggregate identify the source of the historically accepted PDF.
The 23-input closure included the first-merge changes to chapters 03, 06, and 07 and had a
narrow source-integrity role; it is not a whole-package or PDF checksum gate.

The live purpose-specific ledger has been regenerated for the current 23
inputs. Its SHA-256 is
`76ac9fd6fadbf8291fe186a111330d098c2ed12ceda67aa32031d424ba67d611`,
and `python -B audit/build_source_closure.py --check` passes. This purpose-
specific source-only receipt has no PDF-parity role.

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

## Historical accepted PDF build convergence

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

- The final log is pinned above; transient guarded-pass/render files are not
  publication payloads.
- The canonical asset tree contains 55 retained files. Its former 63-row asset
  checkpoint included eight historical ledger payloads that are now retired.
- The former 90-row root ledger and 63-row asset ledger are retired and
  recoverable from Git; the latter had SHA-256
  `b274fe39cde808c34e82789136af51616e9177f424763b3eec153bc18e10fa3c`.
  Their workflows no longer generate either root or asset `SHA256SUMS` files.
- The live purpose-specific 23-input `SOURCE_CLOSURE.sha256` record has digest
  `76ac9fd6fadbf8291fe186a111330d098c2ed12ceda67aa32031d424ba67d611`
  and has no whole-package or PDF-parity role; the first-merge digest in the
  historical artifact table remains provenance only.
- Python byte-code caches and other transient files are not publication
  payloads.

The aggregate source hash and PDF/log hashes form the accepted historical
first-merge build receipt. The source-closure hash is complementary historical
source-only evidence. The regenerated live closure is a current source-only
receipt; the current PDF receipt is recorded separately in the authoritative
register linked above.

## Earlier receipt (history)

The preceding accepted checkpoint produced 127/134/134 pages. Its 134-page,
2,027,726-byte PDF had SHA-256
`22bc68d855ad04dde9654e9fbd20b3ba7f05a33e3c5df0e5b80bb8991c94b41d`,
and the later source-only 23-input closure digest was
`418f6f93e5b40ec2fa441cc6379a21c9587f2b6e6c50f7863c75595c062e606c`.
Those values remain explicit historical provenance and precede the later
first-merge receipt above; both tuples are now historical.
