# Provenance ledger

The canonical volume absorbs the following six source packages.  The paths
below are historical paths relative to their former sibling layout under
`exponents-and-q-series/`.  The exact normalized source tree is pinned by
[`audit/SOURCE_REVISION`](audit/SOURCE_REVISION), and repository history
preserves every retired path.

| Source package | Canonical role |
| --- | --- |
| `inverse_q_analog_functions_report/` | Branchwise narrative, parameter selection, real and complex branch atlases, numerical continuation. |
| `inverse_q_analog_jet_atlas/` | Universal inverse jets, Bell-polynomial organization, mixed derivatives, Lagrange-Good inversion, coefficient atlases. |
| `inverse_q_analogs_extended_report/` | Corrected special regimes, certification arguments, radial inverses, and Fabius-Rvachev recovery material. |
| `inverse_q_analogs_report/` | Discriminant and remote-branch analyses, interval and continuation certificates, early conjecture register. |
| `inverse_q_analogs_report-2/` | Independent branch synthesis, reciprocal regimes, compact coefficient tables, algorithmic cross-checks. |
| `q_pochhammer_q_binomial_expansions_report/` | Canonical forward expansion engine for finite and infinite products, Gaussian and multinomial coefficients, roots of unity, and q-special functions. |

## Intake archive provenance

All six packages arrived on 2026-08-30.  These hashes identify the submitted
archive bytes, before repository normalization or later editorial changes.

| Historical package | Delivered archive | Outer SHA-256 |
| --- | --- | --- |
| `inverse_q_analog_jet_atlas/` | `inverse_q_analog_jet_atlas_2026-08-30.zip` | `9c9a0353eb355e6defb87845c4a2a79d85c537fe5a6c38c5473f9d3d56448ead` |
| `inverse_q_analog_functions_report/` | `inverse_q_analog_functions_report.zip` | `19cc7da37f71ddbbc0c46b91c55c23059a1e305500260bd0a306394f4c21f4de` |
| `inverse_q_analogs_extended_report/` | `inverse_q_analogs_all_parameters_report.zip` | `0263542a7a6a50459eeb0359015b4086245e7311528e80e3875657529825669f` |
| `inverse_q_analogs_report-2/` | `inverse_q_analogs_report_bundle.zip` | `82ab1dc2cbdd4e69d638cfc045d9ca331e8152e1faeba763732fa9231578b875` |
| `inverse_q_analogs_report/` | `inverse_q_analogs_report.zip` | `471ee715022df77f2c5f45b86c213e50e980478eee1a6fc48dd91556cdaeb627` |
| `q_pochhammer_q_binomial_expansions_report/` | `q_pochhammer_q_binomial_expansions_report.zip` | `e8c6e5be4512abc0bacfd904e3f0027b35fd5e47e916a6ad11cc76b2893b3a07` |

The archive hashes identify delivery bytes.  `theorem_concordance.csv`
records normalized result-level provenance, `assets/ASSET_DISPOSITION.csv`
records path-level disposition, and `audit/SOURCE_REVISION` pins the immutable
pre-retirement Git tree used by the source extractor.

The source packages were independently delivered reports, not a linear series
of editions.  Shared titles or formulas therefore do not imply ancestry.  The
concordance records semantic provenance per result rather than selecting a
single package wholesale.

## Post-retirement audit reconciliation

The later integration commit `53c431137` replayed seven audit-only sidecars
from an older branch into the already retired paths
`inverse_q_analogs_report/` and
`q_pochhammer_q_binomial_expansions_report/`.  They contained no new theorem
statement, proof, TeX source, PDF, experiment program, figure, or numerical
payload.  Their nonduplicative evidence was reviewed and is preserved here;
the redundant sidecars were then retired again so that the canonical package
remains the sole live inverse-q document.

For `inverse_q_analogs_report/`, the sidecars confirm that the original
17-file delivery matched the archive hash already recorded above, and that a
later normalized edition passed three strict serial pdfLaTeX runs, a complete
51-page visual inspection, and deterministic replay of all seven textual data
outputs.  That edition had TeX SHA-256
`de375ee059e0ee9485286aea13e917363854d610b5ff77672001828fa663699b`
and PDF SHA-256
`1ef95365aa42fc5426dc7f7533096ecdc9605479fa1eb6c2b8757fc25e086fdb`.
Its repaired endpoint, safeguarded-Newton, near-unit truncation-cost, and
conditional-radicals statements are represented in the source concordance and
the corrected canonical proofs.  The exact reship
`Fabius_Rvachev_Frontier_Report_2026-08-30-E.zip`, with outer SHA-256
`174bf733156cd874cf4f9321c6ab71ca44f311856cc01dc158ddf83dc00cf813`,
was byte-identical to the filed package after documented line-ending
normalization and introduced no additional mathematical content.

For `q_pochhammer_q_binomial_expansions_report/`, the sidecars confirm a
seven-file normalized ledger, exact replay of the retained 44-line numerical
output, three clean serial pdfLaTeX passes, and visual inspection of the
39-page report.  The validated source had SHA-256
`2d3d47cb82ebeea01d43858599e78ddff3d0c97ac62cbe4f09e3ad7314eb4aee`
and its PDF had SHA-256
`88f8e5b4272a949a0521561d2328eb8312167726fbad5c80088ee017921463c5`.
The retained program and numerical output already live in the canonical
asset tree.  Git commit `53c431137` remains the byte-level archive for all
seven sidecars summarized in this section.

For that reason the consolidation lives in the neutral
`inverse_q_analogs_and_series/` directory.  Although the extended report has
the broadest pre-existing asset layout, promoting it in place would falsely
suggest that the other five packages were merely earlier editions.  They are
peer inputs, and several of their strongest results are absent from the
extended report.

## Source-result inventory

`audit/extract_source_results.py` inventories every theorem-style source
environment from the pinned pre-retirement Git revision.  The six inventoried
snapshots contain 260 such environments:

| Kind | Count |
| --- | ---: |
| theorem | 131 |
| proposition | 28 |
| lemma | 2 |
| corollary | 16 |
| conjecture | 32 |
| problem | 9 |
| research problem | 19 |
| principle | 4 |
| definition | 9 |
| algorithm | 5 |
| computational result | 1 |
| example | 4 |

The generated `theorem_concordance.csv` retains source package, path, line,
label, result kind, title, enclosing chapter and section, and whether a proof
environment followed the statement.  Editorial columns then record the
canonical label, proof status, Lean counterpart when one exists, and the
reason for merging, correcting, retaining, or retiring the source item.

## Non-TeX asset audit and migration

At the pinned pre-retirement revision, the six packages contained 65 tracked
non-TeX files totalling 5,832,780 bytes:
six Python experiment programs, two requirements files, six READMEs, six
checksum ledgers, six generated report PDFs, twenty generated figures, and
nineteen generated data or audit files.  Four additional untracked files in
the forward-expansion package are ordinary `.aux`, `.log`, `.out`, and `.toc`
build intermediates.

Every entry in all six source checksum ledgers matched its corresponding file
at that revision.  SHA-256 comparison found no byte-identical pair among the
69 tracked and untracked non-TeX files.  Similar names therefore did not
license deletion:
for example, the three scripts named `inverse_q_analogs_experiments.py`, the
two PDFs named `inverse_q_analogs_report.pdf`, and the two
`qgamma_inverse_branches.pdf` figures all have different contents.

Only two source packages themselves recorded an immutable repository snapshot:

- `inverse_q_analog_jet_atlas/` records
  `1cea73234a363ddbc392816f6babb5a57920e984`;
- `inverse_q_analogs_extended_report/` records
  `23b19a515ceb44a513b1ec56aeb5c9e99dda5952`.

Both names resolve to commits in the repository.  The other four packages
recorded no immutable source commit, so their build statements are preserved
as historical package claims, not promoted to current validation evidence.
Independently, this consolidation pins the normalized sources of all six
packages at
`6fe9fb8f50e1b8a9a800fa0e8ef6f688f5bb5838`, the value stored in
`audit/SOURCE_REVISION` and verified as an ancestor of the retirement commit.

Unique scripts, captured outputs, tables, and figures were migrated under
`assets/` when they support a retained theorem, conjecture, or reproducible
calculation.  The completed 77-row disposition ledger retains 39 files---six
programs, 19 CSV/TXT outputs, and 14 vector figures---and retires 38
superseded narratives, duplicate previews, package metadata files, generated
LaTeX fragments, and build products.  All 33 retained non-script payloads
match their historical source bytes.  The six programs were rerun serially;
[`assets/VALIDATION.md`](assets/VALIDATION.md) records exact-output parity and
the one disclosed last-digit runtime drift, while `assets/SHA256SUMS` fixes
the post-migration bytes.

All tracked superseded material remains recoverable from Git history.  The
only untracked files removed with the old directories were four disposable
TeX build intermediates (`.aux`, `.log`, `.out`, and `.toc`) already recorded
as retirements in the asset-disposition audit.

## Scope boundaries with neighboring volumes

This consolidation is canonical for branch-specified inverse maps, singular
inverse regimes, certification, and the six-package concordance above.  The
separate `q_pochhammer_q_binomial_monograph/` remains the broad reference for
forward q-algebra, combinatorics, summation, and arithmetic; forward results
are repeated here only when an inverse proof needs them.

`Cyclotomic_q_Fabius_Rvachev_Frontier/` remains a separate natural-boundary
and blow-up volume.  Its radial root-of-unity layer overlaps Chapters 3 and 6,
but its condensation, Gould--Hopper, polyharmonic, and natural-boundary
programs are broader than inverse-q branch theory.  Likewise,
`Exponents_and_q_Series_Frontiers/` owns the geometric-uniform/Fabius
deformation and signed/reciprocal parameter-orbit program, and
`inverse-and-sampling/geometric_comb_q_fabius_report/` owns the detailed
interpolation and stability theory behind the short geometric-comb application
in Chapter 6.  These explicit boundaries prevent the six-source concordance
from being misread as a claim to have absorbed those broader volumes.
