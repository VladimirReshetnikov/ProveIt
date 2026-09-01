# Canonical publication validation

This receipt certifies the final source/PDF pair for the canonical inverse
Fabius synthesis.  The certification applies only to the exact hashes below.

## Artifact identity

| Item | Size | SHA-256 |
| --- | ---: | --- |
| `inverse_fabius_theory.tex` | 296 lines; 11,625 bytes | `7b8cea5ff685db3bb676e08f8e3b3c6586a7702f8bf3a85298fb9ced00054d25` |
| Exhaustive 23-input source closure | 23 permanent build inputs | `775c993b8e94c67b90e884e095daba7542140966863319206d8e6eb5fc23715b` |
| `inverse_fabius_theory.pdf` | 134 A4 pages; 2,027,672 bytes | `a530b433392effd3a7941764c19b4c2dae3b35832ab569e9d6b630358646ede3` |

The 23-input closure consists of:

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

## Guarded build convergence

Exactly three guarded serial passes were run:

| Pass | Produced pages |
| ---: | ---: |
| 1 | 127 |
| 2 | 134 |
| 3 | 134 |

The final log census is:

- fatal diagnostics: 0;
- undefined diagnostics: 0;
- actionable rerun diagnostics: 0;
- duplicate diagnostics: 0; and
- overfull boxes: 0.

The stable 134-page count on the final two passes is recorded here without
claiming byte identity between intermediate pass artifacts.

## PDF structural and visual checks

- Page format and count: 134 of 134 pages are A4.
- Text extraction: text was present and inspectable on 134 of 134 pages.
- Page-box census: 670 of 670 expected boxes were present.
- Fonts: all 31 reported Type-1 font entries were embedded and subsetted; six
  entries were Libertinus; no Type-3 font was present.
- Targeted visual inspection covered pages 1, 36, 65, 100, 110, 132, and 134.
  Every inspected page was clean.

## Package integrity and cleanliness

- No TeX auxiliary or build-temporary file remains in the package.
- Root `SHA256SUMS` contains exactly 87 rows, one for every permanent package
  file except the self-referential ledger itself.
- The root ledger includes the nested `assets/SHA256SUMS` as a permanent file.
  That 63-row asset ledger remains byte-identical, with SHA-256
  `b274fe39cde808c34e82789136af51616e9177f424763b3eec153bc18e10fa3c`.
- Python byte-code caches and other transient files are excluded from the root
  ledger and are not publication payloads.

The root ledger, source-closure hash, and PDF hash serve different purposes:
the root ledger inventories the complete permanent package, the closure hash
identifies exactly what entered the TeX build, and the PDF hash identifies the
reviewed publication artifact.
