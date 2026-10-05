# Airy Amplitudes for Relaxed Trees, Compacted Trees and Finite-Language Automata (OEIS A082161 and relatives)

**Positive amplitudes and expansions to every fixed order, binary and every fixed arity k ≥ 3**

This research report was built on 2 October 2026 from six manuscripts of batch 77, all
dated 2 October 2026. The author line is empty in sources 62, 15, 29 and 48 and reads
"Research report" in sources 18 and 66; no tool or person is named. Each source calls
itself an independently checked research report and disclaims publication and peer review.

On 5 October 2026 (batch 102) three bundle reports, Reports 100, 101 and 103, all dated
2 October 2026, were added as **Part V**. They prove the binary theorems of Parts I, II and
IV a second time, by a different route, and add a few new results (listed below). The
author line of Reports 100 and 101, on the title page and in the PDF metadata, is
"Research prepared for private review"; that of Report 103 is "Research prepared for
Vladimir", and Report 103's bibliography calls Report 100 a "companion research report
prepared for private review". No tool or person is named.

| Source | Batch-77 manuscript | Archive (main file) | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 62 | 62 | `relaxed-binary-trees-reproducibility.zip` (`article/relaxed-binary-trees.tex`, 1,221 lines, 23-page PDF) | none | `34f1acd4b` | Part I, Sections 1–15 (the base) |
| 15 | 15 | `compacted-binary-trees-reproducibility.zip` (`article/compacted-binary-trees.tex`, 1,274 lines, 21 pp.) | none (records a repository search at `89daa64f`) | `34f1acd4b` | Part II, Sections 16–29, and Appendix A |
| 18 | 18 | `fixed-arity-airy-package.zip` (`report/fixed-arity-airy-expansions.tex`, 515 lines, 12 pp.) | none | `34f1acd4b` | Part III, Sections 30–37 |
| 66 | 66 | `ternary-airy-amplitudes-result.zip` (`report/ternary-airy-amplitudes.tex`, 656 lines, 14 pp.) | none | `34f1acd4b` | Part III, ternary section, Sections 38–46 |
| 29 | 29 | `larger-alphabet-automata-report.zip` (`article/larger-alphabet-automata.tex`, 344 lines, 6 pp.) | none (its search receipt refers to `4b874cea0`) | `34f1acd4b` (handed over from cluster P4) | Part III, comparison section, Sections 47–52 |
| 48 | 48 | `oeis-dfa-finite-language-report.zip` (`article/dfa-finite-languages.tex`, 967 lines, 16 pp.) | `a68b926cf` (overlap receipt) | `aa7345800` (cluster P2) | Part IV, Sections 53–65 |
| Report 100 | batch 102 | `A082161_Positive_Airy_Amplitude_and_All_Orders_Source.zip` (`Relaxed_Tree_Amplitude_Source/relaxed_tree_amplitude.tex`, 992 lines, 24 pp.) | `4b874cea0` (repository collision check) | `6ab1f1979` | Part V, Sections 67–79 |
| Report 101 | batch 102 | `A254789_Positive_Airy_Amplitude_and_All_Orders_Source.zip` (`compacted_tree_amplitude/compacted_tree_amplitude.tex`, 693 lines, 19 pp.) | none (embeds Report 100) | `6ab1f1979` | Part V, Sections 80–91 |
| Report 103 | batch 102 | `A331120_Minimal_Binary_Automata_All_Orders_Source.zip` (`minimal_dfa_amplitude/minimal_dfa_amplitude.tex`, 927 lines, 23 pp.) | none (embeds Report 100) | `6ab1f1979` | Part V, Sections 92–104 |

All six batch-77 archives arrived in commit `096ee7b87` and survive there
(`git show 096ee7b87:docs/incoming/<archive>`). The three commits named in the Pin column
for them are ancestors of both placement commits; none is a continuation pin. The three
batch-102 archives arrived in commit `60f54ea06` and survive there. Report 100's pin
`4b874cea0` (recorded in `data/102-100-relaxed-PROVENANCE.json`) is the collision check of
its bounded repository search, an ancestor of `34f1acd4b`; Reports 101 and 103 each embed
Report 100's PDF and source archive byte for byte (verified at the write: SHA-256
`4684736e…` and `72e79141…`) and name no repository path. None of the three knew of
Parts I–IV.

The six manuscripts are one family. Relaxed trees, compacted trees and minimal
deterministic automata accepting finite languages satisfy one triangular recurrence
family indexed by the arity k (source 18's Section 2). At k = 2 the three counts are
A082161 (source 62), A254789 (source 15) and A331120 (source 48); for every fixed k ≥ 3
source 18 treats all three, source 66 is its k = 3 case and base proof, and source 29
proves the order-of-growth comparison that 18 and 66 upgrade.

Every result, proof, remark, question and limitation of the six manuscripts is printed,
with three kinds of material printed once. (1) Source 15's appendix "Self-contained Jacobi
estimates" is Appendix A; source 48's appendix is the same text with one word changed and
is not reprinted. (2) Source 48's Sections 3–8 and 10 follow source 15 line by line; the
five passages that are word for word source 15's (the definitions and Jacobi lemma of its
Section 3, the finite-memory lemma, the formal-equation paragraph, the bootstrap of
Section 8.2 and the rational-field paragraph) are replaced by pointers, and every display
in which the automaton differs is printed. (3) The positive completed-run comparison is
stated once as a theorem, source 29's (its earliest form); sources 18 and 66 use it as a
proof step, kept with a pointer. Source 66's two theorems are kept, marked as the k = 3
case of source 18's, because the proof after them is the base proof 18 generalizes. Part 0
of the article ("Where the merge had to choose") gives the reasons.

Part V prints Reports 100, 101 and 103 in full, each opening with its abstract, with two
exceptions: the Sections 3 of Reports 101 and 103 restate Report 100's definitions and
summarize its proofs; those restatements are replaced by pointers (the lemma and the
proposition they cite are kept, each line traced to Report 100). Reports 101 and 103 run
the same signed-memory argument with different coefficients; they paraphrase each other
and both are printed. Section 66 of the article (Part V's guide) gives the provenance, a
table mapping every result to its counterpart in Parts I, II, IV, a notation table and the
assembly choices; Section 105 is Part V's register of open and answered questions.

**Status: AI-assisted, unrefereed, not formalized.** No Lean or Rocq declaration exists for
any statement of this report.

## Files

```
article.tex   the merged report, standalone LaTeX with an internal bibliography (source 62's
              delivered article/relaxed-binary-trees.tex, rewritten as the merged text)
article.pdf   the compiled report, 175 pages
README.md     this guide (replaces source 62's delivered README.md)
```

Source 62 (Part I), from `relaxed-binary-trees-reproducibility.zip` (wrapper `relaxed-binary-trees/`):

```
62-relaxed-verif-README.md                                         <- verification/README.md
62-relaxed-verif-mathematical-review.md                            <- verification/mathematical-review.md
62-relaxed-verif-transcription-signoff.md                          <- verification/transcription-signoff.md
code/62-relaxed-article-build_pdf.sh                               <- article/build_pdf.sh
code/62-relaxed-coefficients.py                                    <- coefficients.py
code/62-relaxed-exact_recurrence.py                                <- exact_recurrence.py
code/62-relaxed-forward_evidence.py                                <- forward_evidence.py
code/62-relaxed-frozen_quasimode.py                                <- frozen_quasimode.py
code/62-relaxed-inverse_checks.py                                  <- inverse_checks.py
code/62-relaxed-make_manifest.py                                   <- make_manifest.py
code/62-relaxed-replay.py                                          <- replay.py
code/62-relaxed-verif-check_formal_independent.py                  <- verification/check_formal_independent.py
code/62-relaxed-verif-check_frozen_and_spectrum.py                 <- verification/check_frozen_and_spectrum.py
code/62-relaxed-verif-run_checks.py                                <- verification/run_checks.py
data/62-relaxed-fix-expected.json                                  <- fixtures/expected.json
data/62-relaxed-output-coefficients.json                           <- output/coefficients.json
data/62-relaxed-output-coefficients.stdout.log                     <- output/coefficients.stdout.log
data/62-relaxed-output-exact_recurrence.json                       <- output/exact_recurrence.json
data/62-relaxed-output-final-clean-replay.json                     <- output/final-clean-replay.json
data/62-relaxed-output-forward_evidence.json                       <- output/forward_evidence.json
data/62-relaxed-output-forward_evidence.stdout.log                 <- output/forward_evidence.stdout.log
data/62-relaxed-output-frozen_quasimode.json                       <- output/frozen_quasimode.json
data/62-relaxed-output-frozen_quasimode.stdout.log                 <- output/frozen_quasimode.stdout.log
data/62-relaxed-output-inverse_checks.json                         <- output/inverse_checks.json
data/62-relaxed-output-manifest-extension.json                     <- output/manifest-extension.json
data/62-relaxed-output-replay_results.json                         <- output/replay_results.json
data/62-relaxed-output-verif-check_formal_independent.stdout.log   <- output/verification/check_formal_independent.stdout.log
data/62-relaxed-output-verif-check_frozen_and_spectrum.stdout.log  <- output/verification/check_frozen_and_spectrum.stdout.log
data/62-relaxed-output-verif-verification-results.json             <- output/verification/verification-results.json
data/62-relaxed-requirements.txt                                   <- requirements.txt
data/62-relaxed-verif-expected-check_formal_independent.json       <- verification/expected/check_formal_independent.json
data/62-relaxed-verif-expected-check_frozen_and_spectrum.json      <- verification/expected/check_frozen_and_spectrum.json
```

Source 15 (Part II and the Appendix), from `compacted-binary-trees-reproducibility.zip` (wrapper `compacted-binary-trees/`):

```
15-compacted-audits-independent-amplitude-audit.md               <- audits/independent-amplitude-audit.md
15-compacted-audits-independent-comparison-audit.md              <- audits/independent-comparison-audit.md
15-compacted-audits-independent-integrated-tex-audit.md          <- audits/independent-integrated-tex-audit.md
15-compacted-audits-independent-inverse-audit.md                 <- audits/independent-inverse-audit.md
15-compacted-src-amplitude-allorders-candidate.md                <- source-proofs/amplitude-allorders-candidate.md
15-compacted-src-comparison-supplement.md                        <- source-proofs/comparison-supplement.md
15-compacted-src-inverse-supplement.md                           <- source-proofs/inverse-supplement.md
15-compacted-src-literature-and-provenance.md                    <- source-proofs/literature-and-provenance.md
15-compacted-src-positive-kernel-verification.md                 <- source-proofs/positive-kernel-verification.md
15-compacted-src-shared-jacobi-lemmas.md                         <- source-proofs/shared-jacobi-lemmas.md
code/15-compacted-checks-audit_compacted_coefficients.py         <- checks/audit_compacted_coefficients.py
code/15-compacted-checks-check_delay_operator.py                 <- checks/check_delay_operator.py
code/15-compacted-checks-check_forward.py                        <- checks/check_forward.py
code/15-compacted-checks-check_shared_jacobi.py                  <- checks/check_shared_jacobi.py
code/15-compacted-checks-formal_compacted.py                     <- checks/formal_compacted.py
code/15-compacted-checks-inverse_check.py                        <- checks/inverse_check.py
code/15-compacted-checks-verify_positive_kernel.py               <- checks/verify_positive_kernel.py
code/15-compacted-replay.py                                      <- replay.py
data/15-compacted-fix-audit_compacted_coefficients_results.json  <- fixtures/audit_compacted_coefficients_results.json
data/15-compacted-fix-delay-operator-check.json                  <- fixtures/delay-operator-check.json
data/15-compacted-fix-formal-coefficients.json                   <- fixtures/formal-coefficients.json
data/15-compacted-fix-forward-check.json                         <- fixtures/forward-check.json
data/15-compacted-fix-inverse_check.json                         <- fixtures/inverse_check.json
data/15-compacted-fix-verify_positive_kernel_results.json        <- fixtures/verify_positive_kernel_results.json
data/15-compacted-output-delay_operator.json                     <- output/delay_operator.json
data/15-compacted-output-delay_operator.stdout.log               <- output/delay_operator.stdout.log
data/15-compacted-output-exact_forward_evidence.json             <- output/exact_forward_evidence.json
data/15-compacted-output-exact_forward_evidence.stdout.log       <- output/exact_forward_evidence.stdout.log
data/15-compacted-output-final-clean-replay.json                 <- output/final-clean-replay.json
data/15-compacted-output-final-visual-review.json                <- output/final-visual-review.json
data/15-compacted-output-formal_coefficients.json                <- output/formal_coefficients.json
data/15-compacted-output-formal_coefficients.stdout.log          <- output/formal_coefficients.stdout.log
data/15-compacted-output-manifest-final.log                      <- output/manifest-final.log
data/15-compacted-output-mathematical.clean.log                  <- output/mathematical.clean.log
data/15-compacted-output-pdf.clean.log                           <- output/pdf.clean.log
data/15-compacted-output-replay-results.json                     <- output/replay-results.json
data/15-compacted-requirements-lock.txt                          <- requirements-lock.txt
data/15-compacted-requirements.txt                               <- requirements.txt
```

Source 18 (Part III, Sections 30-37), from `fixed-arity-airy-package.zip` (wrapper `fixed-arity-airy-release/`):

```
18-arity-REPRODUCIBILITY.md                         <- REPRODUCIBILITY.md
18-arity-algebra-audit.md                           <- algebra-audit.md
18-arity-all-orders-proof.md                        <- all-orders-proof.md
18-arity-canc-ind-analytic-audit.md                 <- cancellation/independent-audit/analytic-audit.md
18-arity-canc-ind-verdict.md                        <- cancellation/independent-audit/verdict.md
18-arity-canc-proof.md                              <- cancellation/proof.md
18-arity-fixed-arity-proof.md                       <- fixed-arity-proof.md
18-arity-ind-allorders-analytic-audit.md            <- independent-all-orders-audit/analytic-audit.md
18-arity-ind-allorders-verdict.md                   <- independent-all-orders-audit/verdict.md
18-arity-ind-analytic-analytic-audit.md             <- independent-analytic-audit/analytic-audit.md
18-arity-ind-analytic-verdict.md                    <- independent-analytic-audit/verdict.md
18-arity-report-integrated-mathematical-review.md   <- report/integrated-mathematical-review.md
18-arity-report-visual-quality-review.md            <- report/visual-quality-review.md
18-arity-signed-general-signed-all-orders.md        <- signed-extensions/general-signed-all-orders.md
18-arity-signed-ind-analytic-audit.md               <- signed-extensions/independent-audit/analytic-audit.md
18-arity-signed-ind-verdict.md                      <- signed-extensions/independent-audit/verdict.md
code/18-arity-canc-check_cancellation.py            <- cancellation/check_cancellation.py
code/18-arity-canc-ind-check_independent.py         <- cancellation/independent-audit/check_independent.py
code/18-arity-check_exact.py                        <- check_exact.py
code/18-arity-check_first_correction.py             <- check_first_correction.py
code/18-arity-coef-derive_c2.py                     <- coefficients/derive_c2.py
code/18-arity-ind-allorders-check_independent.py    <- independent-all-orders-audit/check_independent.py
code/18-arity-replay.sh                             <- replay.sh
code/18-arity-signed-check_seeds_runs.py            <- signed-extensions/check_seeds_runs.py
code/18-arity-signed-ind-check_independent.py       <- signed-extensions/independent-audit/check_independent.py
data/18-arity-canc-check-output.txt                 <- cancellation/check-output.txt
data/18-arity-canc-ind-independent-output.json      <- cancellation/independent-audit/independent-output.json
data/18-arity-coef-c2-output.txt                    <- coefficients/c2-output.txt
data/18-arity-ind-allorders-independent-output.txt  <- independent-all-orders-audit/independent-output.txt
data/18-arity-signed-ind-independent-output.json    <- signed-extensions/independent-audit/independent-output.json
```

Source 66 (Part III, ternary section, Sections 38-46), from `ternary-airy-amplitudes-result.zip` (wrapper `ternary-airy-amplitudes-result/`):

```
66-ternary-REPRODUCIBILITY.md                                <- REPRODUCIBILITY.md
66-ternary-all-orders-reduction.md                           <- all-orders-reduction.md
66-ternary-allorders-audit-audit.md                          <- all-orders-audit/audit.md
66-ternary-amplitude-proof-candidate.md                      <- amplitude-proof-candidate.md
66-ternary-audit-frozen_ternary_boundary_audit.md            <- audit/frozen_ternary_boundary_audit.md
66-ternary-audit-singular_form_boundary_addendum.md          <- audit/singular_form_boundary_addendum.md
66-ternary-dfa-audit-verdict.md                              <- dfa-transfer-audit/verdict.md
66-ternary-dfa-ratio-transfer.md                             <- dfa-ratio-transfer.md
66-ternary-ind-gap-leading-amplitude-verdict.md              <- independent-gap-audit/leading-amplitude-verdict.md
66-ternary-ind-gap-reviewed-leading-proof.md                 <- independent-gap-audit/reviewed-leading-proof.md
66-ternary-ind-gap-singular-airy-audit.md                    <- independent-gap-audit/singular-airy-audit.md
66-ternary-inverse-audit-inverse-verdict.md                  <- inverse-audit/inverse-verdict.md
66-ternary-repaired-high-path-tail.md                        <- repaired-high-path-tail.md
66-ternary-report-integrated-review.md                       <- report/integrated-review.md
66-ternary-report-visual-quality-review.md                   <- report/visual-quality-review.md
code/66-ternary-allorders-audit-check_coefficients.py        <- all-orders-audit/check_coefficients.py
code/66-ternary-audit-verify_frozen_ternary.py               <- audit/verify_frozen_ternary.py
code/66-ternary-check_quasimode.py                           <- check_quasimode.py
code/66-ternary-dfa-audit-check_transfer.py                  <- dfa-transfer-audit/check_transfer.py
code/66-ternary-exact_blocks.py                              <- exact_blocks.py
code/66-ternary-formal_recursion.py                          <- formal_recursion.py
code/66-ternary-inverse-audit-check_inverse.py               <- inverse-audit/check_inverse.py
code/66-ternary-replay.sh                                    <- replay.sh
data/66-ternary-allorders-audit-coefficients.json            <- all-orders-audit/coefficients.json
data/66-ternary-allorders-audit-scalar-endpoint-checks.json  <- all-orders-audit/scalar-endpoint-checks.json
data/66-ternary-dfa-audit-exact-checks.json                  <- dfa-transfer-audit/exact-checks.json
data/66-ternary-exact-block-checks.json                      <- exact-block-checks.json
data/66-ternary-formal-recursion-checks.json                 <- formal-recursion-checks.json
data/66-ternary-inverse-audit-numerical-checks.json          <- inverse-audit/numerical-checks.json
data/66-ternary-quasimode-checks.json                        <- quasimode-checks.json
```

Source 29 (Part III, comparison section, Sections 47-52), from `larger-alphabet-automata-report.zip` (wrapper `larger-alphabet-automata-report/`):

```
29-alphabet-review-independent-renewal-audit.md         <- review/independent-renewal-audit.md
29-alphabet-review-integrated-review.md                 <- review/integrated-review.md
29-alphabet-sources-literature.md                       <- sources/literature.md
code/29-alphabet-check_inverse_and_boundary.py          <- code/check_inverse_and_boundary.py
code/29-alphabet-exact_checks.py                        <- code/exact_checks.py
code/29-alphabet-run_all.py                             <- run_all.py
code/29-alphabet-verify.py                              <- code/verify.py
data/29-alphabet-expected-exact_checks.json             <- expected/exact_checks.json
data/29-alphabet-expected-inverse-boundary-checks.json  <- expected/inverse-boundary-checks.json
data/29-alphabet-expected-verification.json             <- expected/verification.json
data/29-alphabet-review-visual-qa.json                  <- review/visual-qa.json
```

Source 48 (Part IV), from `oeis-dfa-finite-language-report.zip` (wrapper `dfa-finite-languages/`):

```
48-dfa-independent-delay-audit.md               <- review/independent-delay-audit.md
48-dfa-integrated-review.md                     <- review/integrated-review.md
48-dfa-literature-status.md                     <- sources/literature-status.md
code/48-dfa-check_exact.py                      <- code/check_exact.py
code/48-dfa-check_inverse.py                    <- code/check_inverse.py
code/48-dfa-formal_dfa.py                       <- code/formal_dfa.py
code/48-dfa-independent_coefficient_audit.py    <- code/independent_coefficient_audit.py
code/48-dfa-run_all.py                          <- run_all.py
data/48-dfa-A331120.seq                         <- sources/A331120.seq
data/48-dfa-canonical-source-scan.json          <- sources/canonical-source-scan.json
data/48-dfa-duplicate-check.json                <- sources/duplicate-check.json
data/48-dfa-exact-checks.json                   <- expected/exact-checks.json
data/48-dfa-formal-coefficients.json            <- expected/formal-coefficients.json
data/48-dfa-independent-coefficient-audit.json  <- expected/independent-coefficient-audit.json
data/48-dfa-inverse-checks.json                 <- expected/inverse-checks.json
data/48-dfa-producer-replay.json                <- review/producer-replay.json
data/48-dfa-requirements.txt                    <- requirements.txt
data/48-dfa-visual-qa.json                      <- review/visual-qa.json
```

Report 100 (Part V), from `A082161_Positive_Airy_Amplitude_and_All_Orders_Source.zip` (wrapper `Relaxed_Tree_Amplitude_Source/`):

```
102-100-relaxed-checks-README.md                                 <- checks/README.md
102-100-relaxed-checks-diagnostics-README.md                     <- checks/diagnostics/README.md
102-100-relaxed-numerics-README.md                               <- numerics/README.md
code/102-100-relaxed-checks-formal_engine.py                     <- checks/formal_engine.py
code/102-100-relaxed-checks-negative_tests.py                    <- checks/negative_tests.py
code/102-100-relaxed-checks-verify.py                            <- checks/verify.py
code/102-100-relaxed-numerics-analyze_numerics.py                <- numerics/analyze_numerics.py
code/102-100-relaxed-numerics-check_dp.py                        <- numerics/check_dp.py
code/102-100-relaxed-numerics-check_jacobi.py                    <- numerics/check_jacobi.py
code/102-100-relaxed-numerics-compute_canonical_amplitude.py     <- numerics/compute_canonical_amplitude.py
code/102-100-relaxed-replay.sh                                   <- replay.sh
data/102-100-relaxed-PROVENANCE.json                             <- PROVENANCE.json
data/102-100-relaxed-RELEASE_VALIDATION.json                     <- RELEASE_VALIDATION.json
data/102-100-relaxed-checks-data-endpoint_9.json                 <- checks/data/endpoint_9.json
data/102-100-relaxed-checks-data-formal_9.json                   <- checks/data/formal_9.json
data/102-100-relaxed-checks-diagnostics-exact_dp_3000.json       <- checks/diagnostics/exact_dp_3000.json
data/102-100-relaxed-checks-diagnostics-numerical_analysis.json  <- checks/diagnostics/numerical_analysis.json
data/102-100-relaxed-checks-logs-exact_normal.log                <- checks/logs/exact_normal.log
data/102-100-relaxed-checks-logs-exact_optimized.log             <- checks/logs/exact_optimized.log
data/102-100-relaxed-checks-logs-negative_normal.log             <- checks/logs/negative_normal.log
data/102-100-relaxed-checks-logs-negative_optimized.log          <- checks/logs/negative_optimized.log
data/102-100-relaxed-checks-logs-run_records.json                <- checks/logs/run_records.json
data/102-100-relaxed-checks-provenance-source_hashes.json        <- checks/provenance/source_hashes.json
data/102-100-relaxed-checks-requirements.txt                     <- checks/requirements.txt
data/102-100-relaxed-numerics-check_jacobi.txt                   <- numerics/check_jacobi.txt
data/102-100-relaxed-numerics-compute_canonical_amplitude.txt    <- numerics/compute_canonical_amplitude.txt
```

Report 101 (Part V), from `A254789_Positive_Airy_Amplitude_and_All_Orders_Source.zip` (wrapper `compacted_tree_amplitude/`):

```
102-101-compacted-VERIFICATION.md                                   <- VERIFICATION.md
102-101-compacted-checks-formal-README.md                           <- checks/formal/README.md
102-101-compacted-numerics-README.md                                <- numerics/README.md
code/102-101-compacted-checks-verify_compacted.py                   <- checks/verify_compacted.py
code/102-101-compacted-numerics-compute_canonical_amplitude.py      <- numerics/compute_canonical_amplitude.py
code/102-101-compacted-replay.sh                                    <- replay.sh
code/102-101-compacted-verify_release.py                            <- verify_release.py
data/102-101-compacted-PROVENANCE.json                              <- PROVENANCE.json
data/102-101-compacted-checks-formal-provenance-source_hashes.json  <- checks/formal/provenance/source_hashes.json
data/102-101-compacted-numerics-compute_canonical_amplitude.txt     <- numerics/compute_canonical_amplitude.txt
```

Report 103 (Part V), from `A331120_Minimal_Binary_Automata_All_Orders_Source.zip` (wrapper `minimal_dfa_amplitude/`):

```
102-103-dfa-checks-README.md                         <- checks/README.md
102-103-dfa-numerics-README.md                       <- numerics/README.md
code/102-103-dfa-checks-formal_engine.py             <- checks/formal_engine.py
code/102-103-dfa-checks-negative_tests.py            <- checks/negative_tests.py
code/102-103-dfa-checks-replay.sh                    <- checks/replay.sh
code/102-103-dfa-checks-verify.py                    <- checks/verify.py
code/102-103-dfa-numerics-diagonal_diagnostics.py    <- numerics/diagonal_diagnostics.py
code/102-103-dfa-replay.sh                           <- replay.sh
data/102-103-dfa-PROVENANCE.json                     <- PROVENANCE.json
data/102-103-dfa-RELEASE_VALIDATION.json             <- RELEASE_VALIDATION.json
data/102-103-dfa-checks-data-dependencies.json       <- checks/data/dependencies.json
data/102-103-dfa-checks-data-endpoint_7.json         <- checks/data/endpoint_7.json
data/102-103-dfa-checks-data-exact.json              <- checks/data/exact.json
data/102-103-dfa-checks-data-formal_7.json           <- checks/data/formal_7.json
data/102-103-dfa-checks-data-inverse.json            <- checks/data/inverse.json
data/102-103-dfa-checks-logs-exact_normal.log        <- checks/logs/exact_normal.log
data/102-103-dfa-checks-logs-exact_optimized.log     <- checks/logs/exact_optimized.log
data/102-103-dfa-checks-logs-negative_normal.log     <- checks/logs/negative_normal.log
data/102-103-dfa-checks-logs-negative_optimized.log  <- checks/logs/negative_optimized.log
data/102-103-dfa-checks-logs-run_records.json        <- checks/logs/run_records.json
data/102-103-dfa-numerics-diagonal_diagnostics.txt   <- numerics/diagonal_diagnostics.txt
```

The 57 Part V files (255,432 bytes) were staged by `6ab1f1979` byte-identical to the
delivery; the eight delivered `.log` files were force-added. **Not shipped** (all survive in
`60f54ea06`): the three manuscripts and PDFs, the three delivery READMEs and `build.sh`
scripts, the ledgers (`SHA256SUMS` of 100 and 103, verified 33/33 and 29/29; 101's
`MANIFEST.json`, checked by its `verify_release.py`) and the manifests `checks/manifest.json`
(100, 103) and `checks/formal/manifest.json` (101); the copies of Report 100's PDF and
source archive in the `dependencies/` directories of 101 and 103; ten files of 101's
`checks/formal/` that are byte copies of Report 100's `checks/` (`verify.py`,
`formal_engine.py`, `negative_tests.py`, `requirements.txt`, `data/*`, `diagnostics/*`);
Report 100's in-package copies `checks/data/formal_9_linear_solver.json` (= `formal_9.json`)
and `numerics/endpoint_9.json` (= `checks/data/endpoint_9.json`); and 103's
`checks/requirements.txt` (= Report 100's, `sympy==1.14.0`). No heavy regenerable file was
excluded; the largest shipped Part V file is `data/102-100-relaxed-checks-diagnostics-exact_dp_3000.json`
(59,915 bytes of decimal diagnostics, regenerable by `numerics/check_dp.py`).

All 159 batch-77 files other than `article.tex`, `article.pdf` and `README.md` are byte-identical
to the delivered members (verified at placement). `article.tex` is source 62's delivered
article rewritten as the merged text; source 62's delivered `README.md` (a guide to its
reproducibility package) is replaced by this file and survives in `096ee7b87`.

**Not shipped** (all survive in `096ee7b87`): the six PDFs; the six checksum ledgers
(`SHA256SUMS`, verified at placement and retired: 62 21/21, 15 33/33, 18 35/35, 66 34/34,
29 16/16, 48 22/22); the manuscripts, delivery READMEs and build scripts of the five merge
members (62's build script is shipped as `code/62-relaxed-article-build_pdf.sh`); twelve
empty `output/*.stderr.log` files of sources 15 (7) and 62 (5); byte-identical copies
(15's `output/` receipts equal to its `fixtures/`, 15's `output/shared_jacobi.{json,stdout.log}`
equal to 62's `verification/expected/check_frozen_and_spectrum.json` and
`output/verification/check_frozen_and_spectrum.stdout.log`, 62's `output/*.stdout.log`
equal to the JSON of the same run and its `output/verification/*.json` equal to
`verification/expected/*.json`, 18's `cancellation/relaxed_low_stages.py` equal to
`coefficients/derive_c2.py`); 15's `dependencies/relaxed/` (three earlier versions of
source 62's article, review and Section 12, superseded by the shipped 62 files); and
29's `sources/overlap.json` (114,187 bytes of raw repository-search receipts at commit
`4b874cea0`: its searches for the A-numbers and topic phrases found nothing on this
enumeration problem, only unrelated hits). No heavy regenerable file of this report was
excluded, so there is no reconstruction step; the delivered archives are fetched with
`git show 096ee7b87:docs/incoming/<archive> > <scratch>/<archive>`.

## Labels and numbering

Every label carries the prefix `air:`, with sub-prefixes `air:rb:` (Part I, 25 labels),
`air:cb:` (Part II, 86), `air:ka:` (Part III, source 18, 33), `air:t3:` (source 66, 40),
`air:ka:al:` (source 29, 26), `air:dfa:` (Part IV, 48), `air:app:jacobi` (1), Part labels
`air:part:` (5) and guide labels `air:guide:` (9): **273 labels**, all distinct. The
delivered `article.tex` (source 62) had 26 unprefixed labels, all section labels; 25 are kept
with the prefix and the label of its References section, merged into the bibliography, is
dropped. Of the 249 labels of the six manuscripts, 221 are printed with the prefix; the
others are 62's `references` and the 27 labels of source 48's word-for-word passages, whose
references point to Part II's identical labels. The write added 52 labels: section labels
for sources 15, 18, 66, 29 and 48 (36), two displays in Part IV's bootstrap pointer, nine
guide and five Part labels.

Part V (5 October 2026) added 290 labels, for **563** in all, none of the 273 earlier labels
lost or renumbered (checked against the build of the committed text): `air:jp:rb:` (Report
100, 93), `air:jp:cb:` (Report 101, 80), `air:jp:dfa:` (Report 103, 98), `air:part:jp`, and
18 labels of Part V's own Sections 66 and 105 (`air:jp:sec:`, `air:jp:rem:`, `air:jp:cor:`,
`air:jp:q:`). Of the reports' 275 labels, 269 are printed with the prefix; the six display
labels of the restatements replaced by pointers (101's `eq:S`, `eq:R`; 103's `eq:A`, `eq:S`,
`eq:j`, `eq:T`) were unreferenced and are not printed. The first sections of Reports 100 and
101 had no label and received `sec:result`. Report 100's Section k is Section k + 66,
Report 101's k + 79, Report 103's k + 91; Section 66 is Part V's guide and Section 105 its
question register. Notes added then are marked **[write, 5 October 2026, batch 102]**.

Sections are numbered through the report: source 62's Section k is Section k; source 15's
is k + 15; source 18's k + 29; source 66's k + 37; source 29's k + 46; source 48's k + 52.
Theorems keep their position in their section (source 15's Theorem 1.1 is Theorem 16.1).
Equations are numbered within sections; source 62's tagged equations (F1)–(F36), (G1)–(G5)
and (I1)–(I19) keep their tags. Notes added by the merge are marked
**[write, 2 October 2026]**.

## Notation

No symbol of any source was renamed: each Part keeps its source's letters. Part 0 of the
article has a normalization dictionary and a table of letters with several meanings.
The readings most likely to mislead:

- **The Airy zero.** z = −2.338107410459767… in Parts I, II, IV and source 29; written a
  (or a₁) in Part III. In Parts I, II and IV, a := 2^{−1/3} z is *not* the zero. Part III's
  λ = a/B with B = (2/q)^{1/3} is, at k = 2, exactly Parts I, II, IV's a.
- **γ.** The amplitude in Parts I and IV (γ_c, γ_r in Part II); in Part III γ = 3(kq/2)^{1/3} a
  is the (negative) coefficient of n^{1/3}, and the amplitudes are A_k^R, A_k^C, A_k^B
  (C_R, C_B in source 66). Source 29's C_k = 2k^k/q^q is a growth constant, not an amplitude.
- **k.** The arity only in Part III. In Parts I, II, IV it is an order index or a run length.
- **Index n.** Internal nodes for trees, transient states for automata (one extra rejecting
  sink); source 29 also counts total states N = n + 1.
- **c and b in Part IV.** c_{n,m} = b_{n,m}/2^m is the normalized automaton array, not
  Part II's compacted count; b is used three ways there, as in the source.
- **Part III at k = 2.** Its general c₁, c₂ reduce exactly to Part I's (F3) at k = 2
  (checked symbolically at the write), but Part III claims only k ≥ 3, and at k = 2 the
  compacted and automaton powers are n^{3/4} and n^{7/8}, not n.
- **Part V** has its own conventions (article Section 66.3). There a (or a₁) *is* the Airy
  zero, κ = ϰ = 2^{2/3} a is twice the a of Parts I, II, IV, time is halved (n = N/2,
  ε = n^{−1/3}), S_n is a diagonal symmetrizer (not the Jacobi matrix), λ_n ≈ 4 (not 2), and
  the scalar coefficients are σ_m = 2 s_m. Report 101 writes b_j (logarithmic) and d_j
  (multiplicative); Report 103 writes d_j (logarithmic) and c_j (multiplicative).

## What is claimed

- **Part I (source 62).** For relaxed binary trees (A082161), a_n = γ n! 4^n e^{3z n^{1/3}} n
  (1 + Σ c_k n^{−k/3} + O_M(n^{−(M+1)/3})) for every M, γ > 0, c_k ∈ ℚ[z]; logarithmic
  corrections 53z²/90, 44z/27, 141/140 − 1304z³/42525; c₁, c₂, c₃ explicit; Lambert-W
  inverses and discrete threshold brackets.
- **Part II (source 15).** For compacted binary trees (A254789), the same with n^{3/4},
  amplitude γ_c > 0 and corrections 53z²/90, 271z/216, 393/1120 − 1304z³/42525; exact
  positive four-state, three-state and renewal models with their symmetry obstructions;
  log(c_n/r_n) = log(γ_c/γ_r) − ¼ log n − (3z/8) n^{−2/3} − (21/32) n^{−1} + O(n^{−4/3})
  (the n^{−1/3} term cancels; uses Part I); inverses.
- **Part III (sources 18, 66, 29).** For every fixed k ≥ 3, positive amplitudes and every
  fixed order for relaxed, compacted and automaton counts, scale (n!)^q (k^k/q^q)^n
  e^{γ n^{1/3}} n^{(2k−1)/3} (automata with 2^n), common c₁, c₂; first model-dependent
  defects (q/k)^k/(k−2) · n^{−(k−2)} and half of it, eventual decrease of both normalized
  ratios; the cancellation identity with coefficient −q^q/k^k; an inverse. Source 66 adds
  at k = 3 the explicit c₃ and 𝔰₃…𝔰₆, the weight bound 1 ≤ ω ≤ 3/2 and a bridge-tail route
  to the automaton amplitude. Source 29 adds the explicit comparison
  P_{k,n} ≤ B_n/(2^{n−1}R_n) ≤ 1 with P_{k,n} = ∏_{j=2}^n (1 − 1/(2j^{k−1})), uniform in
  k ≥ 3 and n ≥ 1, P_k ≥ (2√2/π) sin(π/√2), a uniform finite-level approximation, a
  Θ-only inverse enclosure and the boundary obstruction that 66 and 18 resolve.
- **Part IV (source 48).** For finite binary languages (A331120), b_n = γ n! 8^n e^{3z n^{1/3}}
  n^{7/8} (1 + Σ 𝔠_k n^{−k/3} + O_M) with γ > 0, corrections 53z²/90, 623z/432,
  3497/4480 − 1304z³/42525; a nonnegative renewal representation; a selected smooth inverse.
- **Part V (Reports 100, 101, 103).** Second routes to the theorems of Parts I, II and IV
  (even-time two-step Jacobi product, killed lazy-walk smoothing, three-lag signed memory).
  New: Report 100's Lemma 72.1, a proof that the relaxed amplitude is positive from the exact
  recurrence alone, without the Elvey Price–Fang–Wallner lower bound every earlier Part
  uses (checked at intake; Remark 66.1 applies it to Part I and recovers the relaxed Θ
  theorem); the endpoint law φ_n(0) = √2 n^{−1/2}(1 + O(n^{−2/3})), sharper than Part I's
  O(N^{−1/3}); a telescoping series for the projection constant; relaxed b₄ = −422z²/1215,
  b₅, b₆ and r_n/(4n r_{n−1}) through n^{−3}; compacted b₄ = −2053z²/9720, b₅, b₆ (proved by
  Report 101; formal in Report 100) and, by Corollary 66.3, c_n/(4n c_{n−1}) through n^{−3};
  automaton d₄ = −5429z²/19440, c₄, σ₇, b_n/(8n b_{n−1}) through n^{−7/3} and the explicit
  X^{−1/3} term of the inverse. Proved at the write: Remarks 66.1 (positivity in Part I),
  66.2 (σ_m = 2 s_m for every m, ℓ_j = h_j) and Corollary 66.3 (Report 100's compacted
  formal expansions are genuine).

## What is not claimed

- No amplitude is evaluated or enclosed. 166.9506 and 166.9515 (Part I), 173.12105
  (Part II) and Part IV's normalized ratios are evidence; Part III gives no values.
- Every expansion is a Poincaré expansion to each fixed order: no convergence, Gevrey bound,
  optimal truncation, exponentially small term or transseries, and no canonical real
  interpolation of an integer sequence.
- Part III is not uniform in k and proves only eventual decrease of the ratios.
- Inverses keep smooth-model inverses, interpolation inverses and integer thresholds apart;
  unspecified constants give eventual statements, not certified finite thresholds.
- The growth orders are due to Elvey Price, Fang and Wallner (JCTA 2021; AofA 2020) and to
  Ghosh Dastidar and Wallner (AofA 2024), whose lower bounds supply positivity; the sources'
  literature and repository checks are bounded searches, not priority claims.
- Sources 18 and 66 state that the high-path lemma of Ghosh Dastidar–Wallner (Lemma 14 of
  arXiv v1, Lemma 15 published) uses a false pointwise bound U ≤ q. The inequality does fail
  near the boundary for the coefficient as the sources define it, but the printed text of
  the paper was **not** checked; neither source uses the bound.
- Part V: no amplitude is enclosed. 166.9520924395 and the extrapolation 166.9520895742200
  (relaxed), 173.1267049959 and 173.1267048501473 (compacted) and 76.438 (automata,
  G⁽⁴⁾₃₀₀₀ = 76.4383234197) are uncertified evidence. Reports 101 and 103 still take
  positivity from published lower bounds (compacted; for 103 with the comparison
  b_n ≥ 2^{n−1} c_n); whether Lemma 72.1's argument can replace them is open (Question V.5).
  Report 103's remark that the transformed arrays printed on pp. 11:6–11:7 of the AofA 2020
  paper give 5/4 instead of 3/2 at one entry when read uniformly was **not** checked against
  the paper (Question V.4); Report 103 says it is not a claim that the published theorem is
  false. The two-step Jacobi estimates are partly sketched (min–max bounds, Taylor
  envelopes; Question V.8). Every non-claim of the three reports is kept in the article.

## Relation to other reports and to formal developments

- No earlier repository report treats any of these sequences; this report is the first.
  The repository searches recorded by sources 15, 29 and 48 were right when made, and
  notes in the Parts say so. So was Report 100's "no duplicate relaxed-amplitude result in
  the inspected repository snapshot" at `4b874cea0` (its Section 13, article Section 79); it
  is stale now, since Part I (placed `34f1acd4b`) proves the same theorem, and a dated note
  says so.
- `../a213863-tree-child-networks` (batch 77) proves the same polynomial–Airy identity
  L(PF + QF′) = (P″ + 2(cx + ℓ)Q′ + cQ)F + (2P′ + Q″)F′ with general c, ℓ, and uses the
  same zero-limit projection bootstrap, for tree-child networks. The two reports neither
  cite nor depend on each other. Its Parts III–IV (bundle Reports 104 and 102, same
  delivery series as Part V's Reports 100, 101, 103; written in `7e85b5a0c`) share the
  lemma family, including the restart positivity comparison of Report 100's Lemma 72.1;
  Report 102's "companion relaxed-tree article", which it does not need, is presumably
  Report 100. The reports stay separate.
- `SetTheory/Cardinals/docs/reports/automata-and-formal-languages/accessible-and-strong-automata`
  (batch 77) counts accessible and strongly connected automata in the Korshunov–Liskovets
  regime of inverse-power corrections: no stretched exponential, no shared lemma.
- `../a290268-unbounded-deficits` has an Airy law of a different kind (an additive fold),
  unrelated.
- Every inverse section is an instance of `p0:thm:lambert-core`,
  `p0:thm:perturbed-inversion` and `p0:thm:staircase` of the transseries volume
  (`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`); no
  novelty is claimed for the inversion mechanics.
- **Formal status.** Placement in the collection confers no formal status, and no formal
  development continues this report. The only related Lean declarations are
  `Fabius.staircase_ceil` and `Fabius.staircase_separation`
  (`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`), which formalize
  the general rounding step of `p0:thm:staircase` and nothing specific to this report.

## Building the PDF

From a scratch copy of `article.tex` (pdfLaTeX, MiKTeX or TeX Live; no `\input` files, no
BibTeX):

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The build of 5 October 2026 has 0 errors, 0 warnings (no undefined references or
citations, no multiply defined labels, no duplicate destinations) and 0 overfull boxes,
and gives 175 pages: title, abstract and contents pp. 1–7, Part 0 (guide) pp. 8–16,
Part I pp. 16–38, Part II pp. 38–55, Part III pp. 55–88, Part IV pp. 88–99, Part V
pp. 99–171 (guide Section 66 pp. 99–105, Report 100 pp. 105–129, Report 101 pp. 129–146,
Report 103 pp. 146–169, Section 105 pp. 169–171), Appendix A pp. 171–174, references
pp. 174–175. (The build of 2 October 2026, before Part V, had 98 pages.) The contents use a
2em number box for Sections 66–105 (`\airwidertoc`), since 100–105 have three digits.

## Rerunning the programs

The shipped programs keep their bytes and their delivered internal paths: they import
siblings and read `fixtures/`, `expected/`, `output/` and the ledger `SHA256SUMS` by their
delivered names, and several replays verify that ledger first (it is not shipped). Rerun
from the delivered layout, in a scratch directory, never in this directory:

```sh
git show 096ee7b87:"docs/incoming/<archive>.zip" > /tmp/air.zip
mkdir /tmp/air && cd /tmp/air && unzip -q ../air.zip && cd <wrapper>
```

| Source | Archive / wrapper | Command (Python 3 with SymPy 1.14, mpmath; 62 and 15 also NumPy, SciPy) |
|---|---|---|
| 62 | `relaxed-binary-trees-reproducibility` / `relaxed-binary-trees` | `python replay.py --max-n 20000` (verifies the ledger, runs five checks, compares with `fixtures/expected.json`); then `python verification/run_checks.py` |
| 15 | `compacted-binary-trees-reproducibility` / `compacted-binary-trees` | `python replay.py` (`--manifest-only` checks the ledger only) |
| 18 | `fixed-arity-airy-package` / `fixed-arity-airy-release` | `bash replay.sh` (checks run on copies under `output/replay-*`; `--pdf` also rebuilds the member manuscript) |
| 66 | `ternary-airy-amplitudes-result` / `ternary-airy-amplitudes-result` | the seven Python steps of `replay.sh`, run one by one (the script ends by rebuilding the manuscript with TeX and `pdftotext`, and checks no ledger) |
| 29 | `larger-alphabet-automata-report` / `larger-alphabet-automata-report` | `python3 run_all.py` |
| 48 | `oeis-dfa-finite-language-report` / `dfa-finite-languages` | `python run_all.py` (asserts the ledger; writes `output/checks/`) |

Part V's three archives are fetched the same way from `60f54ea06`:

| Source | Archive / wrapper | Command (Python 3 with SymPy 1.14.0; numerics also mpmath, NumPy, SciPy) |
|---|---|---|
| Report 100 | `A082161_Positive_Airy_Amplitude_and_All_Orders_Source` / `Relaxed_Tree_Amplitude_Source` | `bash replay.sh` (in `checks/`: `verify.py` and `negative_tests.py`, each normally and under `python -O`); optional `numerics/` scripts as its README says (`python check_dp.py 3000` writes `numerics/exact_dp_3000.json`) |
| Report 101 | `A254789_Positive_Airy_Amplitude_and_All_Orders_Source` / `compacted_tree_amplitude` | `python verify_release.py` (ledger `MANIFEST.json`), then `bash replay.sh` (`checks/verify_compacted.py`, its `--negative` cases, and the formal suite in `checks/formal/`) |
| Report 103 | `A331120_Minimal_Binary_Automata_All_Orders_Source` / `minimal_dfa_amplitude` | `bash replay.sh` (runs `checks/replay.sh`); optional `python3 numerics/diagonal_diagnostics.py` |

These suites check the unshipped manifests (`checks/manifest.json`, `checks/formal/manifest.json`,
`MANIFEST.json`) and, for 101 and 103, the `dependencies/` copies of Report 100's PDF and
archive, all by delivered names, so they run only in the delivered layout. Unlike the
batch-77 suites they are fail-closed and *meant* to be run under `python -O` as well. Report
103's `checks/replay.sh` deletes and rewrites `checks/logs/` (and its success record
`run_records.json`); never run it beside the shipped logs.

To run a shipped copy instead, copy it to a scratch directory under its delivered name
(the tables above give every name) together with the files it reads. Hazards:

- Do not run the batch-77 programs with `python -O`: their checks are assertions, and
  source 62's programs reject optimized mode explicitly. (Part V's suites raise explicit
  exceptions and are run under `-O` by their own replay scripts.)
- On Windows, Python writes CRLF: compare regenerated JSON and text with the shipped
  receipts after stripping CR (`diff --strip-trailing-cr`), or by parsed JSON.
- Source 62's `replay.py` replaces earlier files under `output/`; its own README suggests
  `--output-dir output/run-2`. Source 48's `code/formal_dfa.py` writes
  `formal-coefficients.json` beside itself; run it from a copy.
- Six JSON files of source 48 (`data/48-dfa-canonical-source-scan.json`,
  `-exact-checks.json`, `-formal-coefficients.json`, `-inverse-checks.json`,
  `-producer-replay.json`, `-visual-qa.json`) lack a final newline, as delivered.

**Reruns at intake** (copies, `PYTHONUTF8=1`, a 170-second cap per step, on a heavily
loaded machine): source 62, all five checks and its verification suite pass (identical or
float last digits; its forward run gives raw ratio 187.01754328008786 at n = 20000, where
the article prints 187.01754328008607, a float difference under the fixture tolerance
10⁻⁷); source 15, the positive-kernel, shared-Jacobi, delay-operator and inverse checks pass
and the formal coefficient run passed in a longer attempt (about 4 minutes), while its
independent coefficient audit and the exact forward run to n = 2500 did not finish within
the cap; source 18, every check passes except `derive_c2.py` (over the cap; its c₂ is
reproduced by the independent audit); source 66, all seven Python steps pass; source 29,
`run_all.py` passes in 7 s; source 48, `check_exact.py` and `check_inverse.py` reproduce
their receipts, `formal_dfa.py` reproduced s₂…s₅ before the cap, and its independent
coefficient audit did not finish. Independent checks at intake: the initial terms of
every sequence in Part 0's table from the recurrences; 62's (F3) from (F2); 18's c₁, c₂ at
k = 2 and k = 3 against 62's and 66's (zero difference); 15's ratio corollary as the
difference of the two (F2)-type expansions; amplitude extrapolations from exact counts to
n = 900 (γ_r ≈ 166.9508, γ_c ≈ 173.1263, against the published fits 166.95209 and 173.12670);
18's k = 3 defects 8/27, 4/27 and cancellation −4/27 numerically; 66's c₃ by the rate of
the corrected differences; 48's 𝔠₂ symbolically and 𝔠₃ to about 0.2 % by an exact recurrence
to n = 500. None of these numbers is an enclosure.

**Part V reruns** (5 October 2026, copies of the delivered layout, Python 3.14.4, SymPy
1.14.0, `PYTHONUTF8=1`, one at a time on a loaded machine): ledgers 100 33/33 and 103 29/29,
101's `verify_release.py` PASS; Report 100's `checks/verify.py` PASS (325 s here, 40 s
recorded) and `negative_tests.py` PASS with 53 rejections, output equal to the delivered
logs up to the Python-version line, the elapsed time and CR line ends; Report 101's
`verify_compacted.py` PASS and `--negative` PASS (10 rejections), 12 s (its `checks/formal/`
suite is byte-identical to Report 100's and was not rerun); Report 103's `checks/verify.py`
PASS (372 s) and `negative_tests.py` PASS (269 s), equal to the delivered logs up to the
Python-version line. The `-O` reruns and the optional n = 3000 numerics were not repeated
(the delivered logs record them). Independent checks at intake and write: exact counts to
n = 1000 reproduce Report 100's ratio residuals at n = 500 and 1000 and Report 103's
G₁₀₀₀ = 102.077189105… (printed …106, last-digit rounding) and G⁽⁴⁾₁₀₀₀ = 76.4392078929; a
SymPy recomputation at the write confirms every conversion between printed coefficients
(b ↦ ratio for all three models, b ↦ d for 101, d ↦ c for 103 including c₄, agreement of
b₁…b₃ and d₁…d₃ with Parts I, II, IV, and σ_m = 2 s_m for m = 3…6), difference zero.

The shipped logs and `data/102-103-dfa-checks-data-exact.json`, like source 62's and 15's
fixtures and `data/48-dfa-A331120.seq`, contain initial terms of OEIS A082161, A254789 and
A331120 (computed from the recurrences, and matching the OEIS); OEIS data are licensed
CC BY-SA 4.0.

## Delivered files that use delivery names or name unshipped files

- Source 18's proof notes cite a producer workspace: `18-arity-fixed-arity-proof.md` names
  `/workspace/shared/ternary-airy-amplitude-research/amplitude-proof-candidate.md` and
  `independent-gap-audit/leading-amplitude-verdict.md` as its base proof and approval; these
  are source 66's files, shipped as `66-ternary-amplitude-proof-candidate.md` (SHA-256
  `18cdbc4e…`, the hash 18's `18-arity-ind-analytic-analytic-audit.md` pins) and
  `66-ternary-ind-gap-leading-amplitude-verdict.md`. `18-arity-all-orders-proof.md` names
  `/workspace/shared/root-fixed-arity-recursion/check_general.py` (not shipped) and
  `18-arity-canc-proof.md` names two `/workspace/shared/fixed-arity-airy-research/` notes
  (shipped as `18-arity-all-orders-proof.md` and `18-arity-signed-general-signed-all-orders.md`).
  The hash lists in `18-arity-canc-ind-verdict.md` and `18-arity-signed-ind-analytic-audit.md`
  use delivered relative paths; `cancellation/relaxed_low_stages.py` there is the unshipped
  copy of `code/18-arity-coef-derive_c2.py`.
- `29-alphabet-review-independent-renewal-audit.md` audits
  `/workspace/shared/larger-alphabet-automata-research/proof.md`, and
  `66-ternary-dfa-audit-verdict.md` lists `../larger-alphabet-automata-research/proof.md`
  among its inputs: source 29's research proof of its comparison theorem (Theorem 47.1
  here), not shipped. `29-alphabet-sources-literature.md` refers to `overlap.json` (not shipped).
- `15-compacted-src-amplitude-allorders-candidate.md` and
  `66-ternary-amplitude-proof-candidate.md` keep "candidate" in their names although they are
  the approved proofs (the delivered READMEs explain this). Source 15's delivered TeX said
  `bash build_pdf.sh` where its README said `bash article/build_pdf.sh`; neither is shipped.
- `62-relaxed-verif-README.md`, `18-arity-REPRODUCIBILITY.md` and
  `66-ternary-REPRODUCIBILITY.md` describe the delivered package layouts, PDFs and ledgers.
  `48-dfa-literature-status.md` refers to `duplicate-check.json` and
  `canonical-source-scan.json` (shipped as `data/48-dfa-duplicate-check.json` and
  `data/48-dfa-canonical-source-scan.json`); `data/48-dfa-producer-replay.json` records
  `manifest_files: 21`, written before the ledger's final entry (the ledger has 22).
- Every audit, review and receipt refers to its source's delivered paths (`output/…`,
  `fixtures/…`, `expected/…`, `verification/…`); the tables above map them to the shipped
  names.
- Part V: the shipped READMEs and `102-101-compacted-VERIFICATION.md` describe the
  delivered layouts (`checks/`, `numerics/`, `checks/formal/`, `dependencies/`) and name the
  unshipped manifests, ledgers, PDFs and build scripts. `102-101-compacted-checks-formal-README.md`
  describes a `checks/formal/` suite whose programs and data are shipped once, under Report
  100's prefix (`code/102-100-relaxed-checks-*`, `data/102-100-relaxed-checks-data-*`).
  `102-101-compacted-numerics-README.md` points to `checks/formal/diagnostics` (Report 100's
  `checks/diagnostics/`, shipped as `data/102-100-relaxed-checks-diagnostics-*`).
  `data/102-103-dfa-checks-data-dependencies.json` pins the two unshipped `dependencies/`
  files by SHA-256. `102-100-relaxed-checks-diagnostics-README.md` explains that
  `exact_dp_3000.json` is a legacy name for decimal diagnostics, not an integer archive. The
  provenance and run-record JSON files record delivered paths and Python 3.12 environments;
  the two `run_records.json` files (Reports 100 and 103) also record the producer's
  interpreter path under `/opt/codex/…`, a path of the producing environment, not of this
  repository.

## Other discrepancies

- Source 48's text says cutoff errors are exponentially small "in N^{1/8}" where source 15's
  identical sentence has N^{1/4}; both hold for the cutoff χ(j/N^{1/2}), and the article
  notes it.
- Source 62's bibliography lacks Ghosh Dastidar–Wallner (cited by 15, 18, 66, 29, 48); the
  merged bibliography has it, and Part I's higher-arity question now points to Part III.
- Source 48 does not say that its Sections 3–8 and appendix follow source 15; the article
  supplies the attribution (Part IV, Section 55).
- Reports 101 and 103 call Report 100 a "private companion" supplied unchanged with them;
  here it is printed as Sections 67–79, and the dependency copies are not shipped.
  Report 101's text says the companion's JSON certificates are "included"; they are Report
  100's, shipped once.
- Report 100 states its compacted expansion only as a formal ansatz and its compacted
  inverse only conditionally; Report 101 and Part II prove both, and dated notes in Part V
  say so (Corollary 66.3).
- Report 103's table prints G₁₀₀₀ = 102.077189106; the exact value is 102.077189105…
  (rounding of the last digit), noted in the article.
