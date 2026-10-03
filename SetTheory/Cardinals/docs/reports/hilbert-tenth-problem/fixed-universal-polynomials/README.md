# Fixed Universal Polynomials

**A literal Grill instance, exact degree laws, native witness fibers and positive-index restoration**

This is a research report dated 3 October 2026, built from five manuscripts:
"Research Reports" 23 (revision 1), 24, 25, 33 and 34 of one AI-assisted
research pipeline, all of batch 82 (cluster M3). Author lines: "Research report
23" ("Revision 1 with the exact degree theorem"), "Research report 24",
"Research report 25", and "Mathematical research report" for Reports 33 and 34.
All five build on the Hilbert's-tenth programme's own research artifacts in
this repository, at pinned commits.

| Source | Report | Batch 82 | Archive (arrival `db37d18c8`) | Pin | Placed | Printed as |
|---|---|---|---|---|---|---|
| 11 | 23, revision 1 | 11 | `Fixed_Universal_Grill_Polynomial_Package (1).zip` (15,508,226 B; 23-page PDF) | `2d887f0fa` | `2f58ab4e9` | Part I, Sections 23.1–23.15 (base) |
| 14 | 24 | 14 | `Native_Grill_Exact_Degree_Laws_Package.zip` (552,226 B; 15 pp.) | `2d887f0fa` | `2f58ab4e9` | Part II, Sections 24.1–24.11 |
| 07 | 25 | 07 | `Entire_Native_Witness_Fiber_Package.zip` (531,631 B; 19 pp.) | `ad634b2d1` | `2f58ab4e9` | Part III, Sections 25.1–25.13 |
| 10 | 33 | 10 | `Failure_of_Positive_Index_Restoration_Package.zip` (703,207 B; 17 pp.) | `2dde7850f`; context `93ad43375` | `2f58ab4e9` | Part IV, Sections 33.1–33.10, 33.A, 33.B |
| 05 | 34 | 05 | `Counterexample_Height_Expansions_and_Rotation_Discrepancy_Package.zip` (591,664 B; 17 pp.) | `2dde7850f`; transfer appendix `9fa99be93` | `2f58ab4e9` | Part IV, Sections 34.1–34.9, 34.A, 34.B |
| — | 23, original edition | 12 | `Fixed_Universal_Grill_Polynomial_Package.zip` (15,390,453 B; 19 pp.) | `2d887f0fa` | not staged | superseded by source 11 |

Every result, proof, remark, question and limitation of the five manuscripts
is printed. Text marked **[write]** in the article was written at the merge.
The report is AI-assisted and unrefereed. **It is not formalized, and the
programme has reviewed only parts of it** (see below). The language theorem of
Part I is conditional on pinned imports; Parts III and IV inherit pinned
native-source theorems as they state.

**Editions.** Archive 12 is the original edition of Report 23 and archive 11
its revision 1. `11-grill-poly-REVISION.md` anchors the SHA-256 of archive 12
(`467e2b4795fd484b73d94c6a006a84652fea772f1b0f870cac1a1f5d1445bf9b`, measured
equal) and of its PDF, LaTeX source and inventory. Revision 1 changes no gate,
coefficient, witness or comparison: its 177 `reproducibility/` files are
byte-identical to the original's. It replaces the propagated upper bound
71,731,007 by the exact degree 69,339,973 (Section 23.13) and keeps the
original's QA as `qa/v0-*`. Nothing of archive 12 is staged; its open question
"Can the true degree be determined?" is answered by Section 23.13.

## Files

```
README.md     this guide (it replaces source 11's delivery README, which survives in the arrival archive)
article.tex   the report: standalone LaTeX, one bibliography per source at the end of its Part
article.pdf   the compiled report, 102 pages (unnumbered title page; contents pages 1-5; front
              matter 6-11; Part I 12-34; Part II 35-50; Part III 51-68; Part IV 69-101)
```

The other 269 files are the five sources' audit and provenance notes (root),
code (`code/`) and recorded data (`data/`), byte-identical to the delivery,
each name prefixed by its source:

Source 11 (Report 23 rev. 1): 34 audit, proof and provenance notes, 58 code files, 64 data files.

```
11-grill-poly-PORTABILITY.md
11-grill-poly-README.md
11-grill-poly-REVISION.md
11-grill-poly-arithmetic-FULL_COMPOSITION_PROOF.md
11-grill-poly-arithmetic-README.md
11-grill-poly-arithmetic-input_PROOF.md
11-grill-poly-arithmetic-native_history_proof.md
11-grill-poly-arithmetic-review_complete_report.md
11-grill-poly-arithmetic-review_grill_program.md
11-grill-poly-circuit-audit-AUDIT.md
11-grill-poly-circuit-audit-README.md
11-grill-poly-circuit-audit-sources-grill_tag_native_composed205.md
11-grill-poly-circuit-audit-sources-grill_tag_native_phase_residual206.md
11-grill-poly-exact-degree-DEGREE_PROOF.md
11-grill-poly-exact-degree-PORTABILITY.md
11-grill-poly-exact-degree-README.md
11-grill-poly-exact-degree-frozen-README.md
11-grill-poly-exact-degree-independent-review-INDEPENDENT_LEADING_PROOF.md
11-grill-poly-input-audit-AUDIT.md
11-grill-poly-input-audit-README.md
11-grill-poly-input-audit-normalization-AUDIT.md
11-grill-poly-input-audit-reviewed_semantic_contract.md
11-grill-poly-input-audit-sources-grill_tag_exact_width_loader.md
11-grill-poly-input-audit-sources-native_binary_dyadic_duration_recoder.md
11-grill-poly-input-audit-sources-neary_woods_explicit_universal_tm.md
11-grill-poly-input-audit-sources-review_grill_tag_exact_width_loader.md
11-grill-poly-input-research-FINDINGS.md
11-grill-poly-input-research-literal-README.md
11-grill-poly-input-research-literal-RESOURCE_PLAN.md
11-grill-poly-input-research-literal-REVIEW_LITERAL_TABLES.md
11-grill-poly-input-research-literal-upstream_recoder_duration.md
11-grill-poly-input-research-literal-upstream_u15_proof.md
11-grill-poly-qa-article-math-review.md
11-grill-poly-qa-v0-article-math-review.md
code/11-grill-poly-arithmetic-compact_dag.py
code/11-grill-poly-arithmetic-compact_dag.py.txt
code/11-grill-poly-arithmetic-compose_universal.py
code/11-grill-poly-arithmetic-compose_universal.py.txt
code/11-grill-poly-arithmetic-emit_grill_program.py
code/11-grill-poly-arithmetic-emit_grill_program.py.txt
code/11-grill-poly-arithmetic-input_loaders.py
code/11-grill-poly-arithmetic-input_loaders.py.txt
code/11-grill-poly-arithmetic-input_verify.py
code/11-grill-poly-arithmetic-input_verify.py.txt
code/11-grill-poly-arithmetic-native_backend_check.py
code/11-grill-poly-arithmetic-native_backend_check.py.txt
code/11-grill-poly-arithmetic-native_check.py
code/11-grill-poly-arithmetic-native_check.py.txt
code/11-grill-poly-arithmetic-native_history.py
code/11-grill-poly-arithmetic-native_history.py.txt
code/11-grill-poly-arithmetic-review_complete_dag.py
code/11-grill-poly-arithmetic-review_complete_dag.py.txt
code/11-grill-poly-arithmetic-review_complete_leading.py
code/11-grill-poly-arithmetic-review_complete_leading.py.txt
code/11-grill-poly-arithmetic-review_grill_program.py
code/11-grill-poly-arithmetic-review_grill_program.py.txt
code/11-grill-poly-build.sh
code/11-grill-poly-circuit-audit-check_exact_source.py
code/11-grill-poly-circuit-audit-check_exact_source.py.txt
code/11-grill-poly-circuit-audit-check_interfaces.py
code/11-grill-poly-circuit-audit-check_interfaces.py.txt
code/11-grill-poly-exact-degree-check_degree.py
code/11-grill-poly-exact-degree-check_degree.py.txt
code/11-grill-poly-exact-degree-check_leading.py
code/11-grill-poly-exact-degree-independent-review-check_leading.py.txt
code/11-grill-poly-exact-degree-replay.py
code/11-grill-poly-exact-degree-test_integrity.py
code/11-grill-poly-input-audit-independent_outer_checks.py
code/11-grill-poly-input-audit-independent_outer_checks.py.txt
code/11-grill-poly-input-audit-normalization-check_normalization.py
code/11-grill-poly-input-audit-normalization-check_normalization.py.txt
code/11-grill-poly-input-research-literal-build_literal.py
code/11-grill-poly-input-research-literal-build_literal.py.txt
code/11-grill-poly-input-research-literal-check_literal.py
code/11-grill-poly-input-research-literal-check_literal.py.txt
code/11-grill-poly-input-research-literal-resource_estimate.py.txt
code/11-grill-poly-input-research-literal-resource_source_grill_tag_native_composed205.py.txt
code/11-grill-poly-input-research-literal-resource_source_grill_tag_native_phase_residual206.py.txt
code/11-grill-poly-input-research-literal-resource_source_grill_tag_native_phase_sharing.py.txt
code/11-grill-poly-input-research-literal-resource_source_grill_tag_native_weak_cone.py.txt
code/11-grill-poly-input-research-literal-resource_source_grill_tag_native_word_closure.py.txt
code/11-grill-poly-input-research-literal-resource_source_pcp_affine_slope_class_history.py.txt
code/11-grill-poly-input-research-literal-resource_source_pcp_uniform_affine_pair_history.py.txt
code/11-grill-poly-input-research-literal-resource_source_pcp_uniform_affine_pair_units.py.txt
code/11-grill-poly-input-research-literal-review_literal_tables.py
code/11-grill-poly-input-research-literal-review_literal_tables.py.txt
code/11-grill-poly-input-research-literal-upstream_u15_builder.py.txt
code/11-grill-poly-input-research-own_macro_checks.py
code/11-grill-poly-input-research-own_macro_checks.py.txt
code/11-grill-poly-replay.py
code/11-grill-poly-test_integrity.py
code/11-grill-poly-verify_release.py
data/11-grill-poly-PROVENANCE.json
data/11-grill-poly-arithmetic-emission_result.json
data/11-grill-poly-arithmetic-grill_program.json
data/11-grill-poly-arithmetic-input_provenance.json
data/11-grill-poly-arithmetic-input_source_pin.json
data/11-grill-poly-arithmetic-input_validation.json
data/11-grill-poly-arithmetic-native_backend_small_0.bin
data/11-grill-poly-arithmetic-native_backend_small_0.json
data/11-grill-poly-arithmetic-native_backend_small_1.bin
data/11-grill-poly-arithmetic-native_backend_small_1.json
data/11-grill-poly-arithmetic-native_backend_small_2.bin
data/11-grill-poly-arithmetic-native_backend_small_2.json
data/11-grill-poly-arithmetic-native_backend_small_3.bin
data/11-grill-poly-arithmetic-native_backend_small_3.json
data/11-grill-poly-arithmetic-native_backend_small_result.json
data/11-grill-poly-arithmetic-native_check_result.json
data/11-grill-poly-arithmetic-native_receipt_fixtures.json
data/11-grill-poly-arithmetic-native_unit_kernel.json
data/11-grill-poly-arithmetic-review_complete_dag.json
data/11-grill-poly-arithmetic-review_complete_dag.log
data/11-grill-poly-arithmetic-review_complete_dag.normal.json
data/11-grill-poly-arithmetic-review_complete_dag.optimized.log
data/11-grill-poly-arithmetic-review_complete_leading.json
data/11-grill-poly-arithmetic-review_complete_leading.log
data/11-grill-poly-arithmetic-review_complete_manifest.json
data/11-grill-poly-arithmetic-review_complete_structure.json
data/11-grill-poly-arithmetic-review_complete_structure.log
data/11-grill-poly-arithmetic-review_grill_derived.json
data/11-grill-poly-arithmetic-review_grill_manifest.json
data/11-grill-poly-arithmetic-review_grill_program.json
data/11-grill-poly-arithmetic-universal.json
data/11-grill-poly-circuit-audit-MANIFEST.json
data/11-grill-poly-circuit-audit-exact-normal.json
data/11-grill-poly-circuit-audit-final-resources.txt
data/11-grill-poly-circuit-audit-interfaces-normal.json
data/11-grill-poly-circuit-audit-optimized-resources.txt
data/11-grill-poly-circuit-audit-phase_sharing_connector_pin.json
data/11-grill-poly-circuit-audit-pins.json
data/11-grill-poly-circuit-audit-source_connector_pins.json
data/11-grill-poly-exact-degree-MANIFEST.json
data/11-grill-poly-exact-degree-PROVENANCE.json
data/11-grill-poly-exact-degree-QA_RECEIPT.json
data/11-grill-poly-exact-degree-check_degree.log
data/11-grill-poly-exact-degree-check_degree_optimized.log
data/11-grill-poly-exact-degree-degree_certificate.json
data/11-grill-poly-exact-degree-degree_certificate_optimized.json
data/11-grill-poly-exact-degree-independent-review-check_leading.log
data/11-grill-poly-exact-degree-independent-review-check_leading_optimized.log
data/11-grill-poly-input-audit-MANIFEST.json
data/11-grill-poly-input-audit-independent_outer_checks.json
data/11-grill-poly-input-audit-normalization-check_normalization.json
data/11-grill-poly-input-audit-source_pins.json
data/11-grill-poly-input-research-literal-literal_checks.json
data/11-grill-poly-input-research-literal-literal_tables.json
data/11-grill-poly-input-research-literal-resource_geometry.json
data/11-grill-poly-input-research-literal-review_literal_tables_result.json
data/11-grill-poly-input-research-literal-source_manifest.json
data/11-grill-poly-input-research-own_macro_checks.json
data/11-grill-poly-qa-article-render-qa.json
data/11-grill-poly-qa-exact-degree-extension-qa.json
data/11-grill-poly-qa-portable-integrity-normal.json
data/11-grill-poly-qa-portable-integrity-optimized.json
data/11-grill-poly-qa-portable-replay-receipt.json
data/11-grill-poly-qa-v0-article-render-qa.json
```

Source 14 (Report 24): 3 audit, proof and provenance notes, 13 code files, 12 data files.

```
14-degree-laws-README.md
14-degree-laws-qa-MATH_REVIEW.md
14-degree-laws-research-GENERAL_DEGREE_THEOREM.md
code/14-degree-laws-build.sh
code/14-degree-laws-checks-check_diagonal_expansion.py
code/14-degree-laws-checks-check_loader_degrees.py
code/14-degree-laws-checks-check_native_law.py
code/14-degree-laws-checks-review_extensions.py
code/14-degree-laws-research-check_diagonal_expansion.py.txt
code/14-degree-laws-research-check_loader_degrees.py.txt
code/14-degree-laws-research-check_native_law.py.txt
code/14-degree-laws-research-review_extensions.py.txt
code/14-degree-laws-test_integrity.py
code/14-degree-laws-test_release_integrity.py
code/14-degree-laws-verify.py
code/14-degree-laws-verify_release.py
data/14-degree-laws-INPUT_PINS.json
data/14-degree-laws-PROVENANCE.json
data/14-degree-laws-QA_RECEIPT.json
data/14-degree-laws-certificates-diagonal_expansion_certificate.json
data/14-degree-laws-certificates-diagonal_expansion_certificate_optimized.json
data/14-degree-laws-certificates-extension_review_certificate.json
data/14-degree-laws-certificates-independent_certificate.json
data/14-degree-laws-certificates-independent_certificate_optimized.json
data/14-degree-laws-certificates-loader_degree_certificate.json
data/14-degree-laws-qa-RELEASE_QA.json
data/14-degree-laws-qa-RENDER_QA.json
data/14-degree-laws-research-MANIFEST.json
```

Source 07 (Report 25): 17 audit, proof and provenance notes, 12 code files, 12 data files.

```
07-native-fiber-proofs-canonical-transport-SUMMARY.md
07-native-fiber-proofs-entire-fiber-CLASSIFICATION-REVIEW.md
07-native-fiber-proofs-entire-fiber-COUNT-REVIEW.md
07-native-fiber-proofs-entire-fiber-DEPENDENCY-AUDIT.md
07-native-fiber-proofs-entire-fiber-README.md
07-native-fiber-proofs-entire-fiber-REVIEW.md
07-native-fiber-proofs-entire-fiber-THEOREM.md
07-native-fiber-proofs-second-term-CHECKS.md
07-native-fiber-proofs-second-term-INDEPENDENT-COUNT-REVIEW.md
07-native-fiber-proofs-second-term-README.md
07-native-fiber-proofs-second-term-THEOREM.md
07-native-fiber-proofs-total-bitlength-CHECKS.md
07-native-fiber-proofs-total-bitlength-INDEPENDENT-REVIEW.md
07-native-fiber-proofs-total-bitlength-README.md
07-native-fiber-proofs-total-bitlength-THEOREM.md
07-native-fiber-report25-math-review.md
07-native-fiber-source-PELL_RELAXED_AUXILIARY_PROOF.md
code/07-native-fiber-audit_dependency.py
code/07-native-fiber-build.sh
code/07-native-fiber-check_entire_fiber.py
code/07-native-fiber-check_privacy.py
code/07-native-fiber-check_provenance.py
code/07-native-fiber-check_second_term.py
code/07-native-fiber-check_total_bitlength.py
code/07-native-fiber-check_total_bitlength_review.py
code/07-native-fiber-release_checks.py
code/07-native-fiber-replay.py
code/07-native-fiber-verify_release.py
code/07-native-fiber-write_manifest.py
data/07-native-fiber-CHECK-RECEIPT.json
data/07-native-fiber-DEPENDENCY-RECEIPT.json
data/07-native-fiber-SECOND-TERM-RECEIPT.json
data/07-native-fiber-TOTAL-BITLENGTH-RECEIPT.json
data/07-native-fiber-delivery-provenance.json
data/07-native-fiber-provenance-entire-fiber-original-MANIFEST.json
data/07-native-fiber-provenance-report22-original-release-manifest.json
data/07-native-fiber-report25-qa.json
data/07-native-fiber-source-native_blocks.json
data/07-native-fiber-source-pins.json
data/07-native-fiber-source-provenance.json
data/07-native-fiber-source-relaxed-provenance.json
```

Source 10 (Report 33): 12 audit, proof and provenance notes, 6 code files, 15 data files.

```
10-index-restore-repro-README.md
10-index-restore-repro-evidence-BOOTSTRAP-INDEPENDENT-REVIEW.md
10-index-restore-repro-evidence-FULL-SIGNED-COUNTEREXAMPLE.md
10-index-restore-repro-evidence-INDEPENDENT-AUDIT.md
10-index-restore-repro-evidence-KERNEL-INDEPENDENT-REVIEW.md
10-index-restore-repro-evidence-RAW-POSITIVE-REDUCTION.md
10-index-restore-repro-evidence-provisional_bootstrap.snapshot.md
10-index-restore-repro-evidence-provisional_negative_kernel.snapshot.md
10-index-restore-supplements-README.md
10-index-restore-supplements-evidence-GENERALIZED-COMPILER-SUPPLEMENT.md
10-index-restore-supplements-evidence-GENERALIZED-SUPPLEMENT-AUDIT.md
10-index-restore-supplements-evidence-INDEPENDENT-REVIEW.md
code/10-index-restore-build_pdf.sh
code/10-index-restore-repro-checks.py
code/10-index-restore-repro-verify.py
code/10-index-restore-supplements-checks.py
code/10-index-restore-supplements-verify.py
code/10-index-restore-verify_package.py
data/10-index-restore-QA.json
data/10-index-restore-context-source_manifest.json
data/10-index-restore-repro-CHECKS.json
data/10-index-restore-repro-REPLAY.json
data/10-index-restore-repro-evidence-bounded-check-results.json
data/10-index-restore-repro-evidence-prime-certificate.json
data/10-index-restore-repro-evidence-provenance.json
data/10-index-restore-repro-source_manifest.json
data/10-index-restore-supplements-CHECKS.json
data/10-index-restore-supplements-REPLAY.json
data/10-index-restore-supplements-additional_source_manifest.json
data/10-index-restore-supplements-evidence-audit_results.json
data/10-index-restore-supplements-evidence-historical-generalized-exponent-checks.json
data/10-index-restore-supplements-evidence-provenance.json
data/10-index-restore-supplements-source_manifest.json
```

Source 05 (Report 34): 7 audit, proof and provenance notes, 2 code files, 2 data files.

```
05-signed19-heights-evidence-ALL-ORDERS-HEIGHT-CHECK.md
05-signed19-heights-evidence-ALL-ORDERS-SUPPLEMENT.md
05-signed19-heights-evidence-HEIGHT-ASYMPTOTICS-CHECK.md
05-signed19-heights-evidence-INDEPENDENT-FULL-AUDIT.md
05-signed19-heights-evidence-PROOF-PACKET.md
05-signed19-heights-evidence-TRANSFER-PROOF.md
05-signed19-heights-evidence-rotation-counting-audit.md
code/05-signed19-heights-build_pdf.sh
code/05-signed19-heights-verify_package.py
data/05-signed19-heights-PROVENANCE.json
data/05-signed19-heights-QA.json
```

## Delivery names and shipped names

Every shipped file is a delivered file with the delivery directory flattened
into its name. The rule per source (delivery directory, relative to the
package root, -> name prefix; `.py`, `.sh` and `.py.txt` files go to `code/`,
JSON, logs, `.bin` and `.txt` data to `data/`, markdown to the root):

| Source | Delivery directory | Shipped prefix |
|---|---|---|
| 11 | `universal-grill-report23-v1/` (root files) | `11-grill-poly-` (its `README.md` was staged as this directory's `README.md` and is replaced by this guide) |
| 11 | `article/` | `code/11-grill-poly-build.sh`; `report23.tex` is `article.tex`, rewritten by the merge |
| 11 | `exact-degree/`, `exact-degree/frozen/`, `exact-degree/replay_code/` | `11-grill-poly-exact-degree-` (the frozen `README.md` is `11-grill-poly-exact-degree-frozen-README.md`) |
| 11 | `exact-degree/frozen/independent-review/` | `11-grill-poly-exact-degree-independent-review-` |
| 11 | `qa/` | `11-grill-poly-qa-` |
| 11 | `reproducibility/` | `11-grill-poly-` (so `11-grill-poly-README.md` is the delivered `reproducibility/README.md`) |
| 11 | `reproducibility/frozen/<d>/` and `reproducibility/replay_code/<d>/`, for `<d>` = `arithmetic`, `circuit-audit`, `circuit-audit/sources`, `input-audit`, `input-audit/normalization`, `input-audit/sources`, `input-research`, `input-research/literal` | `11-grill-poly-<d with / as ->-` |
| 14 | `native-degree-law-report24/`, its `article/` and `reproducibility/` | `14-degree-laws-` |
| 14 | `qa/`, `reproducibility/certificates/`, `reproducibility/checks/`, `reproducibility/research/` | `14-degree-laws-qa-`, `-certificates-`, `-checks-`, `-research-` |
| 07 | `entire-native-fiber-report25/` | `07-native-fiber-` |
| 07 | `proofs/<d>/`, `provenance/`, `source/` | `07-native-fiber-proofs-<d>-`, `-provenance-`, `-source-` |
| 10 | `Research_Report33/`, `context/`, `repro/`, `repro/evidence/`, `supplements/`, `supplements/evidence/` | `10-index-restore-`, `-context-`, `-repro-`, `-repro-evidence-`, `-supplements-`, `-supplements-evidence-` |
| 05 | `Research_Report34/`, `evidence/` | `05-signed19-heights-`, `05-signed19-heights-evidence-` |

In source 11 the frozen original of a script and its portable executable
version both appear in `code/`: the inert original keeps the delivered
`.py.txt` name (for example `code/11-grill-poly-arithmetic-compact_dag.py.txt`,
from `reproducibility/frozen/arithmetic/`) and the executable is the `.py`
(from `reproducibility/replay_code/arithmetic/`). The `.py.txt` names must not
be changed back: the delivered `reproducibility/replay.py` (shipped as
`code/11-grill-poly-replay.py`, line 73) rejects any `.py` under `frozen/`, and
the inventories pin the `.py.txt` names. Source 14 has the same convention
(`code/14-degree-laws-research-*.py.txt` are its inert originals).

**Delivered text that uses delivery names.** Every shipped audit, proof note,
provenance record, manifest and script names files by their delivery paths
(for example `reproducibility/frozen/arithmetic/universal.dag`,
`repro/evidence/FULL-SIGNED-COUNTEREXAMPLE.md`, `context/Research_Report25.tex`,
`PROVENANCE.json`). Use the table above to find them. Several name files that
are not shipped here: the release inventories and checksum ledgers, the PDFs,
the heavy files of source 11, the byte copies of research-tree files, source
05's context copies of Reports 25 and 33, and the third-party paper copies
(next section).

## Not shipped

All of these survive in the arrival commit `db37d18c8` and can be extracted
with `git show "db37d18c8:docs/incoming/<archive>" > x.zip` (the archives were
retired from `docs/incoming/` by the placement commit).

| Source | Not shipped |
|---|---|
| 11 | 24 byte copies of research-tree files (below); 12 in-archive byte copies (shipped once); 13 third-party files; 7 inventories and checksum ledgers; 2 heavy regenerable files; the PDF |
| 14 | 1 byte copy of a research-tree file; 14 byte copies of source 11's files (shipped once, under `11-grill-poly-`); 4 ledgers; manuscript, delivery README, PDF |
| 07 | 4 byte copies of research-tree files; 4 ledgers; manuscript, delivery README, PDF |
| 10 | 38 byte copies of research-tree files; 5 in-archive byte copies; 4 ledgers; manuscript, delivery README, PDF |
| 05 | 6 byte copies of research-tree files; 2 byte copies of source 10's evidence (shipped once, under `10-index-restore-repro-evidence-`); `context/Research_Report25.tex` and `context/Research_Report33.tex` (byte-identical to the manuscripts printed as Parts III and IV); 2 ledgers; manuscript, delivery README, PDF |

**Third-party papers.** Archive 11 contained copies of T. Neary and D. Woods,
*Four small universal Turing machines*, Fundamenta Informaticae 91 (2009),
123–144, and J. Cocke and M. Minsky, *Universality of Tag Systems with P=2*,
Journal of the ACM 11 (1964), 15–20: under
`reproducibility/frozen/input-audit/sources/` the files
`NearyWoods-FI09-primary.pdf`, `nearywoods-primary.txt`, `neary-page112.png`,
`neary-page121.png`, `cocke-minsky-1964.pdf`, `cocke-minsky-1964.txt` and
`cm-page5.png`, and under `reproducibility/frozen/input-research/` the files
`cm-page4.png`, `cm-page5.png`, `cocke-minsky-1964.pdf`,
`literal/neary-woods-2009.pdf`, `literal/neary-woods-2009.txt` and
`literal/u15-table16-page.png`. Their redistribution is not established, so
they are not redistributed here; Part I's bibliography cites both papers with
the URLs the source gives. The sealed verifiers of source 11 pin them, so they
are needed only to rerun those verifiers, from an extraction of the archive.

**Byte copies of research-tree files.** 73 members of the five archives are
byte copies of 51 distinct files of `Computability/HilbertTenthProblem/Papers/`.
Every one was compared with the current file at this write and is
byte-identical; no pinned file has changed since its pin. They are cited by
path:

Source 11 (Report 23 rev. 1), 24 members:

| Archive member | Repository file (under `Computability/HilbertTenthProblem/Papers/`) |
|---|---|
| `reproducibility/frozen/arithmetic/input_recoder130_receipt.json` | `research-wip/native-stream-queue/native_binary_input_dilation130.json` |
| `reproducibility/frozen/arithmetic/review_grill_bridge_pinned.md` | `research-wip/native-stream-queue/grill_tag_halt_bridge.md` |
| `reproducibility/frozen/circuit-audit/sources/grill_tag_native_composed205.json` | `research-wip/native-stream-queue/grill_tag_native_composed205.json` |
| `reproducibility/frozen/circuit-audit/sources/grill_tag_native_composed205.py.txt` | `research-wip/native-stream-queue/grill_tag_native_composed205.py` |
| `reproducibility/frozen/circuit-audit/sources/grill_tag_native_phase_residual206.py.txt` | `research-wip/native-stream-queue/grill_tag_native_phase_residual206.py` |
| `reproducibility/frozen/circuit-audit/sources/grill_tag_native_phase_sharing.md` | `research-wip/native-stream-queue/grill_tag_native_phase_sharing.md` |
| `reproducibility/frozen/circuit-audit/sources/grill_tag_native_phase_sharing.py.txt` | `research-wip/native-stream-queue/grill_tag_native_phase_sharing.py` |
| `reproducibility/frozen/circuit-audit/sources/grill_tag_native_word_closure.py.txt` | `research-wip/native-stream-queue/grill_tag_native_word_closure.py` |
| `reproducibility/frozen/circuit-audit/sources/native_binary_input_dilation130.json` | `research-wip/native-stream-queue/native_binary_input_dilation130.json` |
| `reproducibility/frozen/circuit-audit/sources/pcp_affine_slope_class_history.md` | `research-wip/native-stream-queue/pcp_affine_slope_class_history.md` |
| `reproducibility/frozen/circuit-audit/sources/pcp_affine_slope_class_history.py.txt` | `research-wip/native-stream-queue/pcp_affine_slope_class_history.py` |
| `reproducibility/frozen/circuit-audit/sources/pcp_uniform_affine_pair_units.md` | `research-wip/native-stream-queue/pcp_uniform_affine_pair_units.md` |
| `reproducibility/frozen/input-audit/sources/gpcp_fixed_program_input_bridge.md` | `research-wip/native-stream-queue/gpcp_fixed_program_input_bridge.md` |
| `reproducibility/frozen/input-audit/sources/gpcp_fixed_program_input_bridge.py.txt` | `research-wip/native-stream-queue/gpcp_fixed_program_input_bridge.py` |
| `reproducibility/frozen/input-audit/sources/grill_tag_halt_bridge.md` | `research-wip/native-stream-queue/grill_tag_halt_bridge.md` |
| `reproducibility/frozen/input-audit/sources/grill_tag_native_weak_cone.md` | `research-wip/native-stream-queue/grill_tag_native_weak_cone.md` |
| `reproducibility/frozen/input-audit/sources/grill_tag_native_word_closure.md` | `research-wip/native-stream-queue/grill_tag_native_word_closure.md` |
| `reproducibility/frozen/input-audit/sources/group_linked_binary_geometry47.md` | `research-wip/native-stream-queue/group_linked_binary_geometry47.md` |
| `reproducibility/frozen/input-audit/sources/native_binary_input_dilation129.md` | `research-wip/native-stream-queue/native_binary_input_dilation129.md` |
| `reproducibility/frozen/input-audit/sources/native_binary_input_dilation130.md` | `research-wip/native-stream-queue/native_binary_input_dilation130.md` |
| `reproducibility/frozen/input-audit/sources/native_binary_input_dilation132.md` | `research-wip/native-stream-queue/native_binary_input_dilation132.md` |
| `reproducibility/frozen/input-audit/sources/native_binary_masked_selection63.md` | `research-wip/native-stream-queue/native_binary_masked_selection63.md` |
| `reproducibility/frozen/input-audit/sources/native_binary_recoder_factored128.md` | `research-wip/native-stream-queue/native_binary_recoder_factored128.md` |
| `reproducibility/frozen/input-audit/sources/review_native_binary_recoder_factored128.md` | `research-wip/native-stream-queue/review_native_binary_recoder_factored128.md` |

Source 14 (Report 24), 1 members:

| Archive member | Repository file (under `Computability/HilbertTenthProblem/Papers/`) |
|---|---|
| `reproducibility/data/input_recoder130_receipt.json` | `research-wip/native-stream-queue/native_binary_input_dilation130.json` |

Source 07 (Report 25), 4 members:

| Archive member | Repository file (under `Computability/HilbertTenthProblem/Papers/`) |
|---|---|
| `source/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md` | `1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md` |
| `source/EXPLORATION_ODD_INDEX_PELL_SIGNS.md` | `1980/EXPLORATION_ODD_INDEX_PELL_SIGNS.md` |
| `source/native_binary_masked_selection63.md` | `research-wip/native-stream-queue/native_binary_masked_selection63.md` |
| `source/native_controller_binary_selector56.md` | `research-wip/native-stream-queue/native_controller_binary_selector56.md` |

Source 10 (Report 33), 38 members:

| Archive member | Repository file (under `Computability/HilbertTenthProblem/Papers/`) |
|---|---|
| `context/review_complete74_nonlinear_index_bootstrap.md` | `research-wip/native-stream-queue/review_complete74_nonlinear_index_bootstrap.md` |
| `repro/sources/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md` | `1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md` |
| `repro/sources/FIXED_RAW_UNIVERSAL_76_PROOF.md` | `1980/FIXED_RAW_UNIVERSAL_76_PROOF.md` |
| `repro/sources/HALF_PARAMETER_PELL_92_PROOF.md` | `1980/HALF_PARAMETER_PELL_92_PROOF.md` |
| `repro/sources/PELL_RELAXED_AUXILIARY_PROOF.md` | `1980/PELL_RELAXED_AUXILIARY_PROOF.md` |
| `repro/sources/complete74_factored_first_norm.json` | `research-wip/native-stream-queue/complete74_factored_first_norm.json` |
| `repro/sources/complete74_nonlinear_index_projection_scout.json` | `research-wip/native-stream-queue/complete74_nonlinear_index_projection_scout.json` |
| `repro/sources/complete74_nonlinear_index_projection_scout.md` | `research-wip/native-stream-queue/complete74_nonlinear_index_projection_scout.md` |
| `repro/sources/complete75_asymmetric_scale_tradeoffs.md` | `research-wip/native-stream-queue/complete75_asymmetric_scale_tradeoffs.md` |
| `repro/sources/complete75_half_binomial_compiler.md` | `research-wip/native-stream-queue/complete75_half_binomial_compiler.md` |
| `repro/sources/complete75_half_binomial_compiler.py` | `research-wip/native-stream-queue/complete75_half_binomial_compiler.py` |
| `repro/sources/complete75_signed_projection_elimination101.md` | `research-wip/native-stream-queue/complete75_signed_projection_elimination101.md` |
| `repro/sources/explore_fixed_raw_universal_76.py` | `verification/explore_fixed_raw_universal_76.py` |
| `repro/sources/explore_fixed_raw_universal_77.py` | `verification/explore_fixed_raw_universal_77.py` |
| `repro/sources/explore_fixed_raw_universal_78.py` | `verification/explore_fixed_raw_universal_78.py` |
| `repro/sources/pell_kernel_half_binomial42.md` | `research-wip/native-stream-queue/pell_kernel_half_binomial42.md` |
| `repro/sources/review_complete74_nonlinear_index_projection.md` | `research-wip/native-stream-queue/review_complete74_nonlinear_index_projection.md` |
| `supplements/sources/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md` | `1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md` |
| `supplements/sources/FIXED_RAW_UNIVERSAL_76_PROOF.md` | `1980/FIXED_RAW_UNIVERSAL_76_PROOF.md` |
| `supplements/sources/HALF_PARAMETER_PELL_92_PROOF.md` | `1980/HALF_PARAMETER_PELL_92_PROOF.md` |
| `supplements/sources/PELL_RELAXED_AUXILIARY_PROOF.md` | `1980/PELL_RELAXED_AUXILIARY_PROOF.md` |
| `supplements/sources/complete74_factored_first_norm.json` | `research-wip/native-stream-queue/complete74_factored_first_norm.json` |
| `supplements/sources/complete74_factored_first_norm.py` | `research-wip/native-stream-queue/complete74_factored_first_norm.py` |
| `supplements/sources/complete74_nonlinear_index_projection_scout.json` | `research-wip/native-stream-queue/complete74_nonlinear_index_projection_scout.json` |
| `supplements/sources/complete74_nonlinear_index_projection_scout.md` | `research-wip/native-stream-queue/complete74_nonlinear_index_projection_scout.md` |
| `supplements/sources/complete74_nonlinear_index_projection_scout.py` | `research-wip/native-stream-queue/complete74_nonlinear_index_projection_scout.py` |
| `supplements/sources/complete75_asymmetric_scale_tradeoffs.md` | `research-wip/native-stream-queue/complete75_asymmetric_scale_tradeoffs.md` |
| `supplements/sources/complete75_half_binomial.py` | `research-wip/native-stream-queue/complete75_half_binomial.py` |
| `supplements/sources/complete75_half_binomial_compiler.md` | `research-wip/native-stream-queue/complete75_half_binomial_compiler.md` |
| `supplements/sources/complete75_half_binomial_compiler.py` | `research-wip/native-stream-queue/complete75_half_binomial_compiler.py` |
| `supplements/sources/complete75_positive_elimination.py` | `research-wip/native-stream-queue/complete75_positive_elimination.py` |
| `supplements/sources/complete75_signed_projection_elimination101.md` | `research-wip/native-stream-queue/complete75_signed_projection_elimination101.md` |
| `supplements/sources/explore_fixed_raw_universal_76.py` | `verification/explore_fixed_raw_universal_76.py` |
| `supplements/sources/explore_fixed_raw_universal_77.py` | `verification/explore_fixed_raw_universal_77.py` |
| `supplements/sources/explore_fixed_raw_universal_78.py` | `verification/explore_fixed_raw_universal_78.py` |
| `supplements/sources/explore_fixed_raw_universal_80.py` | `verification/explore_fixed_raw_universal_80.py` |
| `supplements/sources/pell_kernel_half_binomial42.md` | `research-wip/native-stream-queue/pell_kernel_half_binomial42.md` |
| `supplements/sources/review_complete74_nonlinear_index_projection.md` | `research-wip/native-stream-queue/review_complete74_nonlinear_index_projection.md` |

Source 05 (Report 34), 6 members:

| Archive member | Repository file (under `Computability/HilbertTenthProblem/Papers/`) |
|---|---|
| `sources/complete74_asymmetric_scale_transfer.json` | `research-wip/native-stream-queue/complete74_asymmetric_scale_transfer.json` |
| `sources/complete74_asymmetric_scale_transfer.md` | `research-wip/native-stream-queue/complete74_asymmetric_scale_transfer.md` |
| `sources/complete74_equation_orientation_census.json` | `research-wip/native-stream-queue/complete74_equation_orientation_census.json` |
| `sources/complete74_equation_orientation_census.md` | `research-wip/native-stream-queue/complete74_equation_orientation_census.md` |
| `sources/complete74_factored_first_norm.json` | `research-wip/native-stream-queue/complete74_factored_first_norm.json` |
| `sources/review_complete74_equation_orientation_census.md` | `research-wip/native-stream-queue/review_complete74_equation_orientation_census.md` |

Two near-copies are shipped because they differ from the research-tree file:
`11-grill-poly-input-audit-sources-neary_woods_explicit_universal_tm.md`
differs from `native-stream-queue/neary_woods_explicit_universal_tm.md` only in
one path-sanitized command line (line 323), and
`07-native-fiber-source-PELL_RELAXED_AUXILIARY_PROOF.md` differs from
`Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md` only by one added final newline.

## Reconstructing the excluded data

Two deterministic outputs of source 11's generators are not stored here:

- `reproducibility/frozen/arithmetic/universal.dag`: the complete
  3,600,546-gate arithmetic DAG, 61,209,290 bytes, SHA-256
  `a07c1ba41e3a18fafd05c19b8ac39211b0475e30ed8a08ddf43c45a9f5f440f2`;
- `reproducibility/frozen/arithmetic/grill_program.u32`: the literal
  397,488-entry run table, 1,589,952 bytes, SHA-256
  `fa658fcdfe1dae2be3a8e2bf97bd613db59558949ea23ca03f549b77201dad01`.

**Rebuild them from the shipped code** (Python 3.10 or newer, standard library
only). The scripts import the Unix-only module `resource`; on Linux run them
with `python3`, and on Windows use a Python environment that provides a no-op
`resource` module (the placement used a virtual environment with a stub whose
`setrlimit` does nothing and whose `getrusage` reports the peak working set).
From the repository root, with `D` this directory and `W` a fresh scratch
directory outside the repository:

```sh
D=SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/fixed-universal-polynomials
W=$(mktemp -d); mkdir -p "$W/arithmetic" "$W/input-research/literal"
for f in compact_dag compose_universal emit_grill_program input_loaders native_history; do
  cp "$D/code/11-grill-poly-arithmetic-$f.py" "$W/arithmetic/$f.py"
done
cp "$D/data/11-grill-poly-arithmetic-native_unit_kernel.json" "$W/arithmetic/native_unit_kernel.json"
cp Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_binary_input_dilation130.json \
   "$W/arithmetic/input_recoder130_receipt.json"
cp "$D/data/11-grill-poly-input-research-literal-literal_tables.json" "$W/input-research/literal/literal_tables.json"
(cd "$W/arithmetic" && python3 -B emit_grill_program.py && python3 -B compose_universal.py --size 397488)
sha256sum "$W/arithmetic/grill_program.u32" "$W/arithmetic/universal.dag"
```

The recoder receipt `input_recoder130_receipt.json` is a byte copy of the
research-tree file named in the `cp` line. The two scripts also write
`grill_program.json`, `universal.json` and `emission_result.json` into `$W`;
those contain timings and paths and differ from the shipped, SHA-pinned
`data/11-grill-poly-arithmetic-*.json`, which must not be replaced. The recipe
writes nothing into this directory. Measured: 11 s on this machine at this
write (Windows 11, Python 3.14.4, with the stub), both outputs byte-identical
to the digests above; the placement measured 25 s idle and 93 s on a loaded
machine, with 118 MB peak memory, and a delete-and-rebuild test in a
delivery-layout copy after which `verify_release.py` passed.

**Or extract them from the arrival archive** (SHA-256
`e7baac1f3cf2c519d40ffc336424ba28c4d44d81a0ec9ed8f0b1812a8ed00405`):

```sh
git show "db37d18c8:docs/incoming/Fixed_Universal_Grill_Polynomial_Package (1).zip" > r23v1.zip
unzip -j r23v1.zip \
  "universal-grill-report23-v1/reproducibility/frozen/arithmetic/universal.dag" \
  "universal-grill-report23-v1/reproducibility/frozen/arithmetic/grill_program.u32" -d <scratch>
```

(tested at this write: both files have the digests above). The same archive
holds the third-party files, the research-tree byte copies and the sealed
inventories.

## Rerunning the delivered suites

The delivered verifiers check sealed inventories of the delivery layout, so
they report a file-set mismatch in this directory. Rerun them in a scratch
extraction of the arrival archive, never here:

```sh
git show "db37d18c8:docs/incoming/<archive>.zip" > x.zip && unzip x.zip -d <scratch>
```

Commands (from each delivery README) and the results of the placement's reruns
on such copies (Python 3.14.4, Windows 11):

| Source | Command, in the extracted package root | Result at placement |
|---|---|---|
| 11 | `python3 -B verify_release.py` (Linux, or the `resource` stub) | PASS, 6 s (217 files) |
| 11 | `python3 -B exact-degree/replay.py` | PASS, 57 s; exact degree 69,339,973; residues 3 (mod 17) and 53,942,795 (mod 10^9+7) |
| 11 | `python3 -B verify_release.py --replay` (15 replay steps) | all 15 steps PASS when run one at a time, about 381 s in total |
| 11 | `python3 -B reproducibility/test_integrity.py`, `python3 -B exact-degree/test_integrity.py` | PASS (23 s, 5 s) |
| 14 | `python -B verify_release.py` (and `-O`), `--integrity-only`, `test_release_integrity.py`, `reproducibility/test_integrity.py` | all PASS, natively on Windows |
| 14 | `python -B verify_release.py --universal --source-dir <extracted source 11>/reproducibility/frozen/arithmetic` | PASS, 29 s; needs source 11's `universal.dag` |
| 07 | `python3 -B verify_release.py`; `python3 -B replay.py --output <new directory outside the package>` | PASS (1 s; 98 s, normal and optimized) |
| 10 | `python3 -I -B verify_package.py --replay` (and `-O`) | PASS (14 s; 10 s) |
| 05 | `python3 verify_package.py` (and `-O`) | PASS, 1 s each: an identity gate only, no mathematical checker by design |

Not rerun: the PDF builds, source 11's optimized replay. Do not run source
07's `write_manifest.py` (it reseals the release) or the `--write` modes of its
checkers (they regenerate receipts). Source 05's `--build` and `build_pdf.sh`
need an external build directory. Passing these suites supports the
implementations, not the unbounded theorems.

## Labels and numbering

Every label carries the prefix `fup:`. The delivered labels are kept with
their delivered names after a sub-prefix: source 11 `fup:gp:` (27), source 14
`fup:dl:` (46), source 07 `fup:nf:` (63), source 10 `fup:ir:` (77) and source 05
`fup:hc:` (61), 274 in all. The write added 12: eight front-matter labels
`fup:fm:*` and the four Part labels `fup:part:gp`, `fup:part:dl`, `fup:part:nf`,
`fup:part:ir`; 286 in total. Bibliography keys carry the same sub-prefixes.

Numbers carry the Report number: Section *k*, statement *k.m*, equation (*k*)
and Appendix X of Report NN are Section NN.*k*, statement NN.*k.m*, equation
(NN.*k*) and Section NN.X here. For example Theorem 13.1 of Report 23 (the
exact degree) is Theorem 23.13.1, and Theorem 2.1 of Report 25 is Theorem
25.2.1. Tables are numbered consecutively through the report. Only macro names
changed, never renderings: Report 24's `\sha` and `\fname` are `\shasmall` and
`\fnameB`; Report 33's `\MF` and `\MFS` are `\MFnat` and `\MFsrc`; Report 34's
`\MF`, which means the paid mask, is `\MFsrc`.

## What is claimed and what is not

- **Part I (Report 23 rev. 1).** One literal 397,488-phase Grill program and
  one complete polynomial circuit: ordinary positive input `x`, five program
  parameters fixed for each represented c.e. set, 797,135 positive witnesses,
  3,600,546 operations (803,517 M + 2,797,029 A), 86 residuals inside one
  integer-unit finalizer. The language theorem (Theorem 23.1.1) is
  **conditional** on pinned full native-history, binary-recoder and
  finite-input U15 universality theorems, and applies only to the explicit
  valid parameter slices; the title states universality before this
  qualifier. The exact total degree 69,339,973 (Theorem 23.13.1) is
  unconditional algebra on the unchanged circuit. Not claimed: a new MRDP
  theorem, optimality, a materialized full Pell witness or universal accepting
  run, bit complexity.
- **Part II (Report 24).** For every nonempty run table of the native Grill
  template, exact degrees 63N−4 (unit), 12N+10 (largest residual) and 87N+16
  (native polynomial), N = 2m+g+5; residual gluing; recoder and loader maxima;
  fresh-input degrees. Not claimed: universality, semantic correctness of
  arbitrary loaders, minimal degree.
- **Part III (Report 25).** The entire positive fiber of the twenty-two
  coordinate native component at fixed ports (seventeen forced, five
  parametrized by two Pell indices) and the two-term height law with a
  ζ(1/2) second term, conditional on pinned native soundness and completeness.
  Not claimed: minimality, finite-fold MRDP, a numerical witness.
- **Part IV (Reports 33, 34).** The complete74 signed19 child has infinitely
  many positive zeros with restored index R < 0 at every positive input, for
  every actual compiler export (Report 33), so its proposed positive
  restoration fails; raw29 and positive21 remain open. Report 34 counts one
  canonical family of these zeros: N(B) ~ κ log log B with a power saving, an
  exact rotation discrepancy, the falsity of a bounded smooth second term
  (Kesten), and an equivalence of the finer law with an unresolved
  discrepancy estimate. Not claimed: an operation bound, a machine-specific
  false acceptance, a materialized child witness, a result about the whole
  signed19 fiber.

## Relation to the research tree, its reviews and other reports

The five sources import or cite files of
`Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/`
(and `Papers/1980/`) at their pins. Section 0.4 of the article records the
overlaps: the norm cancellation behind the exact degrees is identity (4) of
the tree's `gpcp_shared_selectors774.md` (`ee507599f`), uncited by Reports 23
and 24; Report 24's method is that of the tree's PCP law 58N+28
(`pcp_affine_slope_class_history.md`); Report 23's Grill and native sections
re-state and re-certify the tree's halt bridge and composed native history,
with attribution; Report 33's input-index dichotomy is proved independently in
`complete74_negative_index_refinement.md` (`813c1cff4`), which goes further;
Report 33's bounded-window reduction imports the tree's bootstrap
(`93ad43375`) and says so. New relative to the tree: the literal Grill program
and its exact degree, the laws of Part II, the native-fiber classification and
counting, the signed19 counterexample and the canonical-family counting.

**Reviews by the programme** (after arrival):
`native-stream-queue/review_incoming_matrix_grill.md` (commit `32da04296`)
reviews both editions of Report 23, Report 24 and Report 32 as data, checks the
DAG independently and recomputes 87N+16 = 69,339,973; it calls Part I a useful
numerical Grill milestone, not an operation improvement.
`native-stream-queue/review_incoming_negative_index_fibers.md` (commit
`0055e1c4d`) reviews Reports 33, 25 and 22: no gap in Report 33's construction
(the programme's README now calls the signed19 candidate refuted), Report 25's
classification consistent, its second-term and bit-length theorems not
certified there. **Report 34 has not been reviewed.** Report 23 is not an
operation record: the tree's universal polynomials by other routes have 85
operations (exact degree 175, `109aaca15`) and 86 operations (exact degree 131,
`55d248dc5`).

**Formal status.** Placement beside the Lean development of
`Computability/HilbertTenthProblem` confers no formal status. No statement of
this report is formalized; no source contains or cites Lean or Rocq code.

**Other reports.** Report 22, the predecessor of Report 25 (archive
`Canonical_Histories_and_Infinite_Fibers_Package.zip`, batch 82 cluster M2), was
placed by `7d2b1b245` as source 23 of `../signal-machine-collision-certificates`,
in its Part VIII (labels `smc:ch:`); its
fixed-scale native infinitude is a corollary of Theorem 25.2.1. Report 32, a
fixed universal matrix semigroup from the same batch, is Part V of
`../group-theoretic-substrates`. Part I bears on, without answering, the
instantiation questions `ste:ta:q:instantiate`
(`../stochastic-and-thermal-exactness`), `pwh:oc:q:numerical`
(`../polynomial-witness-histories`), the explicitness boundary of
`lbh:qd:sec:universal` (`../liveness-beyond-halting`) and the remark near
`smc:cg:sec:barrier`: it is a conditional literal circuit with exact degree,
not an expanded polynomial.

## Other discrepancies and hazards

- **Stale upper-bound prose, kept byte for byte.** `11-grill-poly-arithmetic-README.md`
  line 12 says "Formal degree upper bound: 71,731,007; no exact-degree claim",
  and the delivered `reproducibility/README.md` (shipped as
  `11-grill-poly-README.md`) still describes 71,731,007 as an upper bound
  only, as does the manifest field `degree_upper`; revision 1 explains in
  `11-grill-poly-REVISION.md` why these frozen bytes are unchanged. Section
  23.13 proves the exact degree 69,339,973; the upper bound stays valid.
- **Unix-only code.** Source 11's checkers and generators import `resource`
  (for example `code/11-grill-poly-arithmetic-compact_dag.py`, line 11); its
  delivery states Linux. Sources 14, 07, 10 and 05 run natively on Windows.
- **Source 14's optional regression** reads source 11's `universal.dag`;
  rebuild or extract it first.
- **Files shared with Report 22.** `data/07-native-fiber-source-native_blocks.json`,
  `data/07-native-fiber-source-provenance.json` and
  `data/07-native-fiber-provenance-report22-original-release-manifest.json`
  are byte-identical to files in Report 22's archive; they are shipped once,
  here.
- Source 05's `data/05-signed19-heights-PROVENANCE.json` records its own path
  normalizations of the analytic notes; source 11's
  `11-grill-poly-PORTABILITY.md` and `data/11-grill-poly-PROVENANCE.json`
  record its portability transformations.
- No delivered text file contains a CR byte; the four
  `data/11-grill-poly-arithmetic-native_backend_small_*.bin` fixtures contain
  NUL bytes and are binary to git.

## Building the PDF

Copy `article.tex` to a scratch directory and run

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

(pdfLaTeX; standard packages only). At this write the build had no errors, no
undefined references or citations, no multiply defined labels, no duplicate
PDF destinations and no overfull boxes; it gives 102 pages.
