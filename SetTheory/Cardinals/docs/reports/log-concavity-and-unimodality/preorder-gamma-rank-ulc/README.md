# Rank Ultra-Log-Concavity of Preorder Gamma and Directed Support Polynomials at the Actual Degree

**Degree four, independent role activities, small covers and universal-sink clouds**

This is a research report dated 1 October 2026, built from eleven
manuscripts delivered in eighteen archives of ProveIt's batch 73 (arrival
commit `f8c3a392a`, placement commit `8f5c53106`). It answers Research
question 96 (`mr:q:gamma`) of
[`preorder-root-polytopes`](../../enumerative-combinatorics/preorder-root-polytopes):
is the gamma polynomial of every finite preorder ultra-log-concave after
normalization by its *actual* degree?

| Source | Batch-73 archive(s) | Archive name(s) | Manuscript (pages as delivered) | Pin | Placed | Printed as |
|---|---|---|---|---|---|---|
| 25 | 25 | `preorder-gamma-degree-three-package` | *Rank ultra log concavity for preorder gamma polynomials of degree at most three* (14) | `d5e863bba` | `8f5c53106` | Part I, Section 2 |
| 16 (base) | 16, 17, 18, 19 | `preorder-degree-four-part-4-of-4` … `part-1-of-4` | *Degree four preorder support polynomials* (17) | `d5e863bba` | `8f5c53106` | Part I, Section 3 (its Section 3 and Appendix A are source 20, printed in Part II) |
| 23 | 23 | `template26-structural-supplement` | *A smaller proof of the last Newton gap for template 26* (6) | none | `8f5c53106` | Part I, Section 4 (second route) |
| 20 | 20 | `role-cover-package` | *Real stable monomers under a two by two role cover* (9) | none | `8f5c53106` | Part II, Section (a later step) |
| 12 | 12 (handed over by cluster C1) | `three-core-rayleigh-result` | *Coefficientwise Rayleigh inequalities for a three vertex shore* (6) | none | `8f5c53106` | Part II, Section (a later step) |
| 11 | 11 (handed over by cluster C1) | `physical-cover-three-result` | *Rank ultra log concavity under a three vertex physical cover* (5) | none | `8f5c53106` | Part II, Section (a later step) |
| 15 | 15 (handed over by cluster C1) | `bipartite-and-pendant-support-result` | *Lorentzian and real stable directed support polynomials* (6) | none | `8f5c53106` | Part II, Section (a later step) |
| 22 | 22 | `independent-role-degree-three-package` | *Independently weighted preorder support polynomials of actual degree at most three* (21) | none | `8f5c53106` | Part II, Section (a later step) |
| 14 | 14 | `universal-sink-last-gap-package` | *Sharp final coefficient bounds for directed cores with universal sinks* (4) | none | `8f5c53106` | Part III, Section (a later step) |
| 10 | 10 | `universal-sink-all-degrees-package` | *Rank ultra log concavity for four vertex cores with universal sinks* (5) | none | `8f5c53106` | Part III, Section (a later step) |
| 34 | 34 | `universal-sink-five-core-package` | *Rank five ultra log concavity for five vertex cores with universal sinks* (6) | none | `8f5c53106` | Part III, Section (a later step) |
| 06 | 07 (part 1, carries the manuscript), 06 (part 2) | `universal-sink-five-core-boundary-package-part-1`, `-part-2` | *The rank four boundary for five vertex cores with universal sinks* (7) | none | `8f5c53106` | Part III, Section (a later step) |
| — | 31 | `weighted-degree-three-package` | *Vertex-weighted preorder support polynomials of actual degree at most three* (17) | none | not staged | superseded by 22; its theorem is Corollary (a later step) (the case `u = v`) |
| — | 13 | `universal-sink-degree-four-package` | *Weighted degree four rank ultra log concavity for universal sink extensions* (5) | none | not staged | superseded by 10; one remark in Part III |

Sources are numbered by their batch-73 manuscript numbers; a package
delivered in several archives takes its lowest number. "Pin" is the ProveIt
commit a manuscript cites (`d5e863bba`, "Write batch 70 (4/5)", for
`preorder-root-polytopes`); the other manuscripts cite no ProveIt commit,
and every other 40-digit hexadecimal string in the packages is a SHA-256
of a package file.

**Status.** AI-assisted, unrefereed, not formalized. The title pages of
sources 11, 12, 15, 16, 20, 22 and 25 read "Research manuscript prepared for
Vladimir Reshetnikov" and their PDF metadata "Research manuscript prepared
with OpenAI" (the visible title pages do not mention OpenAI); sources 06,
10, 14 and 34 read "Research note"; source 23 has no author line. The
degree-three and degree-four theorems of Part I, source 22's main theorem,
source 12's boundary theorem (and through it source 11's theorem), and the
first interior inequalities of sources 10, 34 and 06 are
**computer-assisted**: their proofs include exact finite certificate
computations shipped here. The other theorems have ordinary proofs. No
statement is formalized in Lean or Rocq, and no source claims
literature-wide priority.

The report has three Parts: **Part I**, unit activities on finite preorders
through actual degree four (sources 25, 16, 23); **Part II**, independent
role activities and small covers (sources 20, 12, 11, 15, 22); **Part III**,
universal-sink clouds over an arbitrary directed core (sources 14, 10, 34,
06). Every result, proof, example, remark, limitation and research question
of every source is printed. A result proved by several sources is printed
once, with the other proofs kept as marked second routes or, where the
proof is the same, replaced by a pointer (Appendix A.3 of the article lists
every such choice). Results that `preorder-root-polytopes` or
`matching-rank-normalization` already prove are cited by label.

## Files

The listing matches the directory. Every file except `article.tex`,
`article.pdf`, `README.md` and the derived container
`data/34-five-core-certificate-data.tar.xz` is a delivered file, byte for
byte, renamed to `NN-slug-` followed by its delivered path with `/`
replaced by `-` and long directory names abbreviated (for example
`independent-audit/` → `ia-`, `four-attachment/` → `a4-`; source 16's
`reproducibility/sources/preorder-gamma-degree4/` is dropped). Code is in
`code/`, recorded outputs, certificates and receipts in `data/`, audit and
proof-note Markdown at the top. The second column gives each file's
delivered path inside its package (for source 16 inside the assembled
four-part package, for source 06 inside the assembled two-part package).

```
article.tex        the report (pdfLaTeX), standalone, internal bibliography
article.pdf        the compiled report, 40 pages (title page and contents, then the three Parts and Appendix A)
README.md          this guide
```

```
06-five-core-boundary-FIVE_TAILS_FINITE_SINKS.md                                       source 06 (archive 07), Part III: `FIVE_TAILS_FINITE_SINKS.md`
06-five-core-boundary-FOUR_ACTIVE_TAILS.md                                             source 06 (archive 07), Part III: `FOUR_ACTIVE_TAILS.md`
06-five-core-boundary-audits-INDEPENDENT_CERTIFICATE_AUDIT.md                          source 06 (archive 07), Part III: `audits/INDEPENDENT_CERTIFICATE_AUDIT.md`
10-sink-all-degrees-audit-mathematical-and-exact-audit.md                              source 10, Part III: `audit/mathematical-and-exact-audit.md`
10-sink-all-degrees-proof-notes-ACTUAL_DEGREE_CLOSURE.md                               source 10, Part III: `proof-notes/ACTUAL_DEGREE_CLOSURE.md`
11-physical-cover-audits-assembly-audit.md                                             source 11, Part II: `audits/assembly-audit.md`
11-physical-cover-audits-integrated-paper-audit.md                                     source 11, Part II: `audits/integrated-paper-audit.md`
11-physical-cover-proof-notes-PHYSICAL_COVER_THREE_ULC.md                              source 11, Part II: `proof-notes/PHYSICAL_COVER_THREE_ULC.md`
11-physical-cover-proof-notes-STRICTNESS_COROLLARIES.md                                source 11, Part II: `proof-notes/STRICTNESS_COROLLARIES.md`
12-three-core-rayleigh-audits-boundary-audit.md                                        source 12, Part II: `audits/boundary-audit.md`
12-three-core-rayleigh-audits-core-rayleigh-audit.md                                   source 12, Part II: `audits/core-rayleigh-audit.md`
12-three-core-rayleigh-audits-four-core-audit.md                                       source 12, Part II: `audits/four-core-audit.md`
12-three-core-rayleigh-audits-integrated-paper-audit.md                                source 12, Part II: `audits/integrated-paper-audit.md`
12-three-core-rayleigh-proof-notes-COEFFICIENTWISE_BOUNDARY_LEMMA.md                   source 12, Part II: `proof-notes/COEFFICIENTWISE_BOUNDARY_LEMMA.md`
12-three-core-rayleigh-proof-notes-CORE_RAYLEIGH_COROLLARY.md                          source 12, Part II: `proof-notes/CORE_RAYLEIGH_COROLLARY.md`
12-three-core-rayleigh-proof-notes-FOUR_CORE_COEFFICIENT_OBSTRUCTION.md                source 12, Part II: `proof-notes/FOUR_CORE_COEFFICIENT_OBSTRUCTION.md`
14-sink-last-gap-audit-mathematical-audit.md                                           source 14, Part III: `audit/mathematical-audit.md`
14-sink-last-gap-proof-notes-UNIVERSAL_SINK_LAST_GAP.md                                source 14, Part III: `proof-notes/UNIVERSAL_SINK_LAST_GAP.md`
15-pendant-support-audits-bipartition-audit.md                                         source 15, Part II: `audits/bipartition-audit.md`
15-pendant-support-audits-integrated-paper-audit.md                                    source 15, Part II: `audits/integrated-paper-audit.md`
15-pendant-support-audits-pendant-audit.md                                             source 15, Part II: `audits/pendant-audit.md`
15-pendant-support-proof-notes-BIPARTITE_ORIENTATION_LEMMA.md                          source 15, Part II: `proof-notes/BIPARTITE_ORIENTATION_LEMMA.md`
15-pendant-support-proof-notes-PENDANT_HEAD_HPP_CRITERION.md                           source 15, Part II: `proof-notes/PENDANT_HEAD_HPP_CRITERION.md`
16-degree-four-EXTERIOR_LORENTZIAN_INDEPENDENT_AUDIT.md                                source 16 (archive 17), Part I: `reproducibility/sources/preorder-gamma-degree4/EXTERIOR_LORENTZIAN_INDEPENDENT_AUDIT.md`
16-degree-four-EXTERIOR_LORENTZIAN_LEMMA.md                                            source 16 (archive 17), Part I: `reproducibility/sources/preorder-gamma-degree4/EXTERIOR_LORENTZIAN_LEMMA.md`
16-degree-four-README.md                                                               source 16 (archive 19), Part I: `reproducibility/README.md`
16-degree-four-RESULT.md                                                               source 16 (archive 17), Part I: `reproducibility/sources/preorder-gamma-degree4/RESULT.md`
16-degree-four-a2-README.md                                                            source 16 (archive 17), Part I: `reproducibility/sources/preorder-gamma-degree4/two-attachment/README.md`
16-degree-four-a3-README.md                                                            source 16 (archive 19), Part I: `reproducibility/sources/preorder-gamma-degree4/three-attachment/README.md`
16-degree-four-a4-INTEGER_CERTIFICATE_METHOD.md                                        source 16 (archive 19), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/INTEGER_CERTIFICATE_METHOD.md`
16-degree-four-api-AUDIT.md                                                            source 16 (archive 18), Part I: `reproducibility/sources/preorder-gamma-degree4/audit-positivity-independent/AUDIT.md`
16-degree-four-bc-BALANCED_LAST_GAP_PROOF.md                                           source 16 (archive 19), Part I: `reproducibility/sources/balanced-core-gamma-research/BALANCED_LAST_GAP_PROOF.md`
16-degree-four-bc-ia-BALANCED_INDEPENDENT_AUDIT.md                                     source 16, Part I: `reproducibility/sources/balanced-core-gamma-research/independent-audit/BALANCED_INDEPENDENT_AUDIT.md`
16-degree-four-bc-ic-ELEMENTARY_STABILITY_OPERATORS.md                                 source 16, Part I: `reproducibility/sources/balanced-core-gamma-research/incomplete-core/ELEMENTARY_STABILITY_OPERATORS.md`
16-degree-four-bc-ic-MERGE_BY_DIFFERENTIATION.md                                       source 16 (archive 18), Part I: `reproducibility/sources/balanced-core-gamma-research/incomplete-core/MERGE_BY_DIFFERENTIATION.md`
16-degree-four-bc-ic-ia-ELEMENTARY_STABILITY_OPERATORS_INDEPENDENT_AUDIT.md            source 16 (archive 19), Part I: `reproducibility/sources/balanced-core-gamma-research/incomplete-core/independent-audit/ELEMENTARY_STABILITY_OPERATORS_INDEPENDENT_AUDIT.md`
16-degree-four-bc-uc-DELETION_AVERAGE_LEMMA.md                                         source 16 (archive 18), Part I: `reproducibility/sources/balanced-core-gamma-research/unbalanced-core/DELETION_AVERAGE_LEMMA.md`
16-degree-four-bc-uc-UNBALANCED_LAST_GAP_PROOF.md                                      source 16 (archive 18), Part I: `reproducibility/sources/balanced-core-gamma-research/unbalanced-core/UNBALANCED_LAST_GAP_PROOF.md`
16-degree-four-bc-uc-ia-OUTWARD_STAR_INDEPENDENT_AUDIT.md                              source 16 (archive 17), Part I: `reproducibility/sources/balanced-core-gamma-research/unbalanced-core/independent-audit/OUTWARD_STAR_INDEPENDENT_AUDIT.md`
16-degree-four-ia-INDEPENDENT_AUDIT.md                                                 source 16 (archive 18), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/INDEPENDENT_AUDIT.md`
16-degree-four-ia-a2-KERNEL_COVERAGE_AUDIT.md                                          source 16, Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/two-attachment/KERNEL_COVERAGE_AUDIT.md`
16-degree-four-ia-a3-AUDIT.md                                                          source 16, Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/three-attachment/AUDIT.md`
16-degree-four-ia-a3-KERNEL_COVERAGE_AUDIT.md                                          source 16 (archive 17), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/three-attachment/KERNEL_COVERAGE_AUDIT.md`
16-degree-four-ia-a3-POSITIVITY_AUDIT.md                                               source 16, Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/three-attachment/POSITIVITY_AUDIT.md`
16-degree-four-ia-a4-FACE_ORBIT_AUDIT.md                                               source 16 (archive 18), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/FACE_ORBIT_AUDIT.md`
16-degree-four-ia-a4-GLOBAL_BINOMIAL_SQUARE_AUDIT.md                                   source 16 (archive 18), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/GLOBAL_BINOMIAL_SQUARE_AUDIT.md`
16-degree-four-ia-a4-KERNEL_COVERAGE_AUDIT.md                                          source 16, Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/KERNEL_COVERAGE_AUDIT.md`
16-degree-four-ia-a4-MEDIUM_CHECKPOINT1_AUDIT.md                                       source 16, Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/MEDIUM_CHECKPOINT1_AUDIT.md`
16-degree-four-ia-a4-REPRODUCE_A4.md                                                   source 16 (archive 17), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/REPRODUCE_A4.md`
16-degree-four-ia-a4-SMALL_TEMPLATE_POSITIVITY_AUDIT.md                                source 16 (archive 18), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/SMALL_TEMPLATE_POSITIVITY_AUDIT.md`
20-role-cover-final-audit-INDEPENDENT_REVIEW.md                                        source 20, Part II: `final-audit/INDEPENDENT_REVIEW.md`
20-role-cover-proofs-BALANCED_REAL_ROOTEDNESS_PROOF.md                                 source 20, Part II: `proofs/BALANCED_REAL_ROOTEDNESS_PROOF.md`
20-role-cover-proofs-ia-BALANCED_REAL_ROOTEDNESS_INDEPENDENT_AUDIT.md                  source 20, Part II: `proofs/independent-audit/BALANCED_REAL_ROOTEDNESS_INDEPENDENT_AUDIT.md`
20-role-cover-proofs-ia-FREE_PRODUCT_COROLLARY_AUDIT.md                                source 20, Part II: `proofs/independent-audit/FREE_PRODUCT_COROLLARY_AUDIT.md`
20-role-cover-proofs-ic-DISJOINT_CORE_EDGES_REAL_ROOTEDNESS.md                         source 20, Part II: `proofs/incomplete-core/DISJOINT_CORE_EDGES_REAL_ROOTEDNESS.md`
20-role-cover-proofs-ic-ONE_MISSING_EDGE_REAL_ROOTEDNESS.md                            source 20, Part II: `proofs/incomplete-core/ONE_MISSING_EDGE_REAL_ROOTEDNESS.md`
20-role-cover-proofs-ic-STAR_CORE_REAL_ROOTEDNESS.md                                   source 20, Part II: `proofs/incomplete-core/STAR_CORE_REAL_ROOTEDNESS.md`
20-role-cover-proofs-ic-TWO_BY_TWO_ROLE_COVER_THEOREM.md                               source 20, Part II: `proofs/incomplete-core/TWO_BY_TWO_ROLE_COVER_THEOREM.md`
20-role-cover-proofs-ic-ia-DISJOINT_CORE_EDGES_INDEPENDENT_AUDIT.md                    source 20, Part II: `proofs/incomplete-core/independent-audit/DISJOINT_CORE_EDGES_INDEPENDENT_AUDIT.md`
20-role-cover-proofs-ic-ia-ONE_MISSING_EDGE_INDEPENDENT_AUDIT.md                       source 20, Part II: `proofs/incomplete-core/independent-audit/ONE_MISSING_EDGE_INDEPENDENT_AUDIT.md`
20-role-cover-proofs-ic-ia-STAR_CORE_INDEPENDENT_AUDIT.md                              source 20, Part II: `proofs/incomplete-core/independent-audit/STAR_CORE_INDEPENDENT_AUDIT.md`
20-role-cover-proofs-ic-ia-TWO_BY_TWO_ROLE_COVER_INDEPENDENT_AUDIT.md                  source 20, Part II: `proofs/incomplete-core/independent-audit/TWO_BY_TWO_ROLE_COVER_INDEPENDENT_AUDIT.md`
22-independent-role-proofs-A2_ALL_ROLE_ULC.md                                          source 22, Part II: `proofs/A2_ALL_ROLE_ULC.md`
22-independent-role-proofs-A2_MIXED_ROLE_ULC.md                                        source 22, Part II: `proofs/A2_MIXED_ROLE_ULC.md`
22-independent-role-proofs-A2_SAME_SIGN_MOMENT_CONE.md                                 source 22, Part II: `proofs/A2_SAME_SIGN_MOMENT_CONE.md`
22-independent-role-proofs-ARTICULATION_RANK_ONE_RR.md                                 source 22, Part II: `proofs/ARTICULATION_RANK_ONE_RR.md`
22-independent-role-proofs-BOUNDARY_REDUCTIONS.md                                      source 22, Part II: `proofs/BOUNDARY_REDUCTIONS.md`
22-independent-role-proofs-FIVE_VERTEX_DELETION_AND_GLUING.md                          source 22, Part II: `proofs/FIVE_VERTEX_DELETION_AND_GLUING.md`
22-independent-role-proofs-GENERAL_EXTREMAL_BLOCK_REDUCTION.md                         source 22, Part II: `proofs/GENERAL_EXTREMAL_BLOCK_REDUCTION.md`
22-independent-role-proofs-INDEPENDENT_ROLE_WEIGHTED_DEGREE3_THEOREM.md                source 22, Part II: `proofs/INDEPENDENT_ROLE_WEIGHTED_DEGREE3_THEOREM.md`
22-independent-role-proofs-MIXED_THREE_CORE_RR.md                                      source 22, Part II: `proofs/MIXED_THREE_CORE_RR.md`
22-independent-role-proofs-ONE_TAIL_HPP_ROLE_COVER.md                                  source 22, Part II: `proofs/ONE_TAIL_HPP_ROLE_COVER.md`
22-independent-role-proofs-ROLE_MATCHING_RANK_THREE_COROLLARY.md                       source 22, Part II: `proofs/ROLE_MATCHING_RANK_THREE_COROLLARY.md`
22-independent-role-proofs-ROLE_TOTAL_PREORDER_DEGREE3.md                              source 22, Part II: `proofs/ROLE_TOTAL_PREORDER_DEGREE3.md`
22-independent-role-proofs-SAME_ORIENTATION_THREE_CORE_RAYLEIGH.md                     source 22, Part II: `proofs/SAME_ORIENTATION_THREE_CORE_RAYLEIGH.md`
22-independent-role-proofs-SIDE1565_HPP_FINAL_CASE.md                                  source 22, Part II: `proofs/SIDE1565_HPP_FINAL_CASE.md`
22-independent-role-proofs-SIX_VERTEX_ROLE_ULC.md                                      source 22, Part II: `proofs/SIX_VERTEX_ROLE_ULC.md`
22-independent-role-proofs-ZERO_ROLE_ACTIVITY_FILTERING.md                             source 22, Part II: `proofs/ZERO_ROLE_ACTIVITY_FILTERING.md`
22-independent-role-proofs-gallai-edmonds-GALLAI_EDMONDS_REDUCTION.md                  source 22, Part II: `proofs/gallai-edmonds/GALLAI_EDMONDS_REDUCTION.md`
22-independent-role-proofs-gallai-edmonds-STRUCTURAL_AUDIT.md                          source 22, Part II: `proofs/gallai-edmonds/STRUCTURAL_AUDIT.md`
23-template26-sources-ia-st26-DELETION_MIXTURE_INDEPENDENT_AUDIT.md                    source 23, Part I: `sources/preorder-gamma-degree4-independent-audit/structural-template26/DELETION_MIXTURE_INDEPENDENT_AUDIT.md`
23-template26-sources-ia-st26-TEMPLATE26_ASSEMBLY_INDEPENDENT_AUDIT.md                 source 23, Part I: `sources/preorder-gamma-degree4-independent-audit/structural-template26/TEMPLATE26_ASSEMBLY_INDEPENDENT_AUDIT.md`
23-template26-sources-st26-TEMPLATE26_LAST_GAP_PROOF.md                                source 23, Part I: `sources/preorder-gamma-degree4/structural-template26/TEMPLATE26_LAST_GAP_PROOF.md`
23-template26-sources-st26-pc-DELETION_MIXTURE_LEMMA.md                                source 23, Part I: `sources/preorder-gamma-degree4/structural-template26/pair-compatibility/DELETION_MIXTURE_LEMMA.md`
23-template26-sources-wpg-VERTEX_WEIGHTED_DEGREE3_THEOREM.md                           source 23, Part I: `sources/weighted-preorder-gamma/VERTEX_WEIGHTED_DEGREE3_THEOREM.md`
34-five-core-ORDINARY_PROOFS.md                                                        source 34, Part III: `ORDINARY_PROOFS.md`
34-five-core-audits-CERTIFICATE_AUDIT.md                                               source 34, Part III: `audits/CERTIFICATE_AUDIT.md`
code/06-five-core-boundary-discovery-bounded_moment_cubic.py                           source 06 (archive 07), Part III: `discovery/bounded_moment_cubic.py`
code/06-five-core-boundary-discovery-certify_four_active.py                            source 06 (archive 07), Part III: `discovery/certify_four_active.py`
code/06-five-core-boundary-discovery-explicit_last.py                                  source 06 (archive 07), Part III: `discovery/explicit_last.py`
code/06-five-core-boundary-discovery-orbits_four_active.cpp                            source 06 (archive 07), Part III: `discovery/orbits_four_active.cpp`
code/06-five-core-boundary-discovery-pack_certificates.py                              source 06 (archive 07), Part III: `discovery/pack_certificates.py`
code/06-five-core-boundary-discovery-packed_cubic.py                                   source 06 (archive 07), Part III: `discovery/packed_cubic.py`
code/06-five-core-boundary-discovery-parallel_precise_bounded.py                       source 06 (archive 07), Part III: `discovery/parallel_precise_bounded.py`
code/06-five-core-boundary-proof-check-check.py                                        source 06 (archive 07), Part III: `proof-check/check.py`
code/06-five-core-boundary-proof-check-check_ordinary_lemmas.py                        source 06 (archive 07), Part III: `proof-check/check_ordinary_lemmas.py`
code/06-five-core-boundary-verify.py                                                   source 06 (archive 07), Part III: `verify.py`
code/10-sink-all-degrees-checker-check.py                                              source 10, Part III: `checker/check.py`
code/10-sink-all-degrees-discovery-core_kernel.py                                      source 10, Part III: `discovery/core_kernel.py`
code/10-sink-all-degrees-discovery-precise_sos.py                                      source 10, Part III: `discovery/precise_sos.py`
code/10-sink-all-degrees-discovery-run_cloud_cubic.py                                  source 10, Part III: `discovery/run_cloud_cubic.py`
code/10-sink-all-degrees-verify.py                                                     source 10, Part III: `verify.py`
code/11-physical-cover-independent-check_assembly.py                                   source 11, Part II: `reproducibility/independent/check_assembly.py`
code/11-physical-cover-producer-check_internal_assembly.py                             source 11, Part II: `reproducibility/producer/check_internal_assembly.py`
code/11-physical-cover-verify.py                                                       source 11, Part II: `verify.py`
code/12-three-core-rayleigh-independent-boundary-independent_boundary_check.py         source 12, Part II: `reproducibility/independent-boundary/independent_boundary_check.py`
code/12-three-core-rayleigh-independent-four-core-independent_check.py                 source 12, Part II: `reproducibility/independent-four-core/independent_check.py`
code/12-three-core-rayleigh-producer-boundary-universal_boundary_check.py              source 12, Part II: `reproducibility/producer-boundary/universal_boundary_check.py`
code/12-three-core-rayleigh-producer-four-core-check_four_core_obstruction.py          source 12, Part II: `reproducibility/producer-four-core/check_four_core_obstruction.py`
code/12-three-core-rayleigh-verify.py                                                  source 12, Part II: `verify.py`
code/14-sink-last-gap-checker-independent-audit.py                                     source 14, Part III: `checker/independent/audit.py`
code/14-sink-last-gap-checker-producer-verify_universal_sink.py                        source 14, Part III: `checker/producer/verify_universal_sink.py`
code/14-sink-last-gap-verify.py                                                        source 14, Part III: `verify.py`
code/15-pendant-support-independent-bipartite-audit_bipartition.py                     source 15, Part II: `reproducibility/independent-bipartite/audit_bipartition.py`
code/15-pendant-support-independent-pendant-check_pendant_seed.py                      source 15, Part II: `reproducibility/independent-pendant/check_pendant_seed.py`
code/15-pendant-support-producer-check_bipartite_orientation.py                        source 15, Part II: `reproducibility/producer/check_bipartite_orientation.py`
code/15-pendant-support-producer-check_pendant_head_examples.py                        source 15, Part II: `reproducibility/producer/check_pendant_head_examples.py`
code/15-pendant-support-verify.py                                                      source 15, Part II: `verify.py`
code/16-degree-four-a2-enumerate.cpp                                                   source 16, Part I: `reproducibility/sources/preorder-gamma-degree4/two-attachment/enumerate.cpp`
code/16-degree-four-a2-verify_quartic_certificates.py                                  source 16, Part I: `reproducibility/sources/preorder-gamma-degree4/two-attachment/verify_quartic_certificates.py`
code/16-degree-four-a3-canonical.inc                                                   source 16 (archive 19), Part I: `reproducibility/sources/preorder-gamma-degree4/three-attachment/canonical.inc`
code/16-degree-four-a3-enumerate.cpp                                                   source 16 (archive 19), Part I: `reproducibility/sources/preorder-gamma-degree4/three-attachment/enumerate.cpp`
code/16-degree-four-a3-verify_certificates.py                                          source 16, Part I: `reproducibility/sources/preorder-gamma-degree4/three-attachment/verify_certificates.py`
code/16-degree-four-a4-coreE_pruned.py                                                 source 16 (archive 19), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_coreE_pruned.py`
code/16-degree-four-a4-coreE_screen.py                                                 source 16 (archive 18), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_coreE_screen.py`
code/16-degree-four-a4-coreE_shifted_gmp.py                                            source 16 (archive 19), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_coreE_shifted_gmp.py`
code/16-degree-four-a4-core_corrections.cpp                                            source 16 (archive 19), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/core_corrections.cpp`
code/16-degree-four-a4-enumerate_gap3_weighted_zeros.py                                source 16 (archive 17), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/enumerate_gap3_weighted_zeros.py`
code/16-degree-four-a4-exact_bareiss_remaining.cpp                                     source 16, Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/exact_bareiss_remaining.cpp`
code/16-degree-four-a4-generate_templates.py                                           source 16 (archive 18), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/generate_templates.py`
code/16-degree-four-a4-global_integer_sextic_shifted_gmp.py                            source 16 (archive 19), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_sextic_shifted_gmp.py`
code/16-degree-four-a4-integer_sos_common.py                                           source 16 (archive 18), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/integer_sos_common.py`
code/16-degree-four-a4-polynomials.cpp                                                 source 16 (archive 18), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/polynomials.cpp`
code/16-degree-four-a4-verify_global_integer_sextic_lifted.py                          source 16 (archive 18), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/verify_global_integer_sextic_lifted.py`
code/16-degree-four-a4-warm_integer_master.py                                          source 16, Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/warm_integer_master.py`
code/16-degree-four-api-audit.py                                                       source 16 (archive 18), Part I: `reproducibility/sources/preorder-gamma-degree4/audit-positivity-independent/audit.py`
code/16-degree-four-bc-ia-check_balanced.cpp                                           source 16 (archive 17), Part I: `reproducibility/sources/balanced-core-gamma-research/independent-audit/check_balanced.cpp`
code/16-degree-four-bc-ia-producer_verify_bounds.py                                    source 16 (archive 17), Part I: `reproducibility/sources/balanced-core-gamma-research/independent-audit/producer_verify_bounds.py`
code/16-degree-four-bc-ia-producer_verify_decomposition.py                             source 16, Part I: `reproducibility/sources/balanced-core-gamma-research/independent-audit/producer_verify_decomposition.py`
code/16-degree-four-bc-ic-verify_incomplete_kernels.py                                 source 16 (archive 18), Part I: `reproducibility/sources/balanced-core-gamma-research/incomplete-core/verify_incomplete_kernels.py`
code/16-degree-four-bc-ic-verify_matching_squares.py                                   source 16 (archive 18), Part I: `reproducibility/sources/balanced-core-gamma-research/incomplete-core/verify_matching_squares.py`
code/16-degree-four-bc-ic-verify_rayleigh_squares.py                                   source 16 (archive 19), Part I: `reproducibility/sources/balanced-core-gamma-research/incomplete-core/verify_rayleigh_squares.py`
code/16-degree-four-exhaust10_canonical.cpp                                            source 16 (archive 18), Part I: `reproducibility/sources/preorder-gamma-degree4/exhaust10_canonical.cpp`
code/16-degree-four-ia-a2-prepare_representatives.py                                   source 16 (archive 17), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/two-attachment/prepare_representatives.py`
code/16-degree-four-ia-a2-recount_a2.cpp                                               source 16 (archive 19), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/two-attachment/recount_a2.cpp`
code/16-degree-four-ia-a3-audit_positivity.py                                          source 16 (archive 18), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/three-attachment/audit_positivity.py`
code/16-degree-four-ia-a3-prepare.py                                                   source 16 (archive 17), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/three-attachment/prepare.py`
code/16-degree-four-ia-a3-recount.cpp                                                  source 16, Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/three-attachment/recount.cpp`
code/16-degree-four-ia-a4-audit_core_correction.py                                     source 16 (archive 17), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/audit_core_correction.py`
code/16-degree-four-ia-a4-audit_face_orbits.py                                         source 16 (archive 18), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/audit_face_orbits.py`
code/16-degree-four-ia-a4-audit_global_binomial_squares.py                             source 16, Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/audit_global_binomial_squares.py`
code/16-degree-four-ia-a4-audit_global_core_correction.py                              source 16, Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/audit_global_core_correction.py`
code/16-degree-four-ia-a4-audit_population_batch.py                                    source 16 (archive 17), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/audit_population_batch.py`
code/16-degree-four-ia-a4-audit_small_faces.py                                         source 16 (archive 19), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/audit_small_faces.py`
code/16-degree-four-ia-a4-prepare.py                                                   source 16 (archive 19), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/prepare.py`
code/16-degree-four-ia-a4-recount.cpp                                                  source 16 (archive 19), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/recount.cpp`
code/16-degree-four-ia-a4-refresh_progress.py                                          source 16 (archive 18), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/refresh_progress.py`
code/16-degree-four-ia-a4-refresh_replay_inputs.py                                     source 16, Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/refresh_replay_inputs.py`
code/16-degree-four-ia-audit_certificate.py                                            source 16 (archive 18), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/audit_certificate.py`
code/16-degree-four-ia-recount_hall.cpp                                                source 16 (archive 18), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/recount_hall.cpp`
code/16-degree-four-pendant10_canonical.cpp                                            source 16 (archive 19), Part I: `reproducibility/sources/preorder-gamma-degree4/pendant10_canonical.cpp`
code/16-degree-four-verify.py                                                          source 16 (archive 18), Part I: `reproducibility/verify.py`
code/16-degree-four-verify_pendant_certificate.py                                      source 16, Part I: `reproducibility/sources/preorder-gamma-degree4/verify_pendant_certificate.py`
code/20-role-cover-proofs-ia-check_disjoint_monomer.cpp                                source 20, Part II: `proofs/independent-audit/check_disjoint_monomer.cpp`
code/20-role-cover-proofs-ia-check_full_monomer.cpp                                    source 20, Part II: `proofs/independent-audit/check_full_monomer.cpp`
code/20-role-cover-proofs-ia-check_missing_edge_monomer.cpp                            source 20, Part II: `proofs/independent-audit/check_missing_edge_monomer.cpp`
code/20-role-cover-proofs-ia-check_star_monomer.cpp                                    source 20, Part II: `proofs/independent-audit/check_star_monomer.cpp`
code/20-role-cover-proofs-ic-ia-check_disjoint_rayleigh_aggregate.py                   source 20, Part II: `proofs/incomplete-core/independent-audit/check_disjoint_rayleigh_aggregate.py`
code/20-role-cover-proofs-ic-ia-check_rayleigh_aggregate.py                            source 20, Part II: `proofs/incomplete-core/independent-audit/check_rayleigh_aggregate.py`
code/20-role-cover-verify.py                                                           source 20, Part II: `verify.py`
code/22-independent-role-proofs-final-rayleigh-verify_side1565_rayleigh.py             source 22, Part II: `proofs/final-rayleigh/verify_side1565_rayleigh.py`
code/22-independent-role-verify.py                                                     source 22, Part II: `verify.py`
code/23-template26-sources-ia-st26-audit_deletion_mixture.py                           source 23, Part I: `sources/preorder-gamma-degree4-independent-audit/structural-template26/audit_deletion_mixture.py`
code/23-template26-sources-ia-st26-audit_template26_assembly.py                        source 23, Part I: `sources/preorder-gamma-degree4-independent-audit/structural-template26/audit_template26_assembly.py`
code/23-template26-verify.py                                                           source 23, Part I: `verify.py`
code/25-degree-three-code-a1-audit_independent.cpp                                     source 25, Part I: `code/one-attachment/audit_independent.cpp`
code/25-degree-three-code-a1-certify.cpp                                               source 25, Part I: `code/one-attachment/certify.cpp`
code/25-degree-three-code-a1-verify.py                                                 source 25, Part I: `code/one-attachment/verify.py`
code/25-degree-three-code-a2-generate.py                                               source 25, Part I: `code/two-attachment/generate.py`
code/25-degree-three-code-a2-independent_audit.py                                      source 25, Part I: `code/two-attachment/independent_audit.py`
code/25-degree-three-code-a2-verify_gap2_certificates.py                               source 25, Part I: `code/two-attachment/verify_gap2_certificates.py`
code/25-degree-three-code-a2-verify_hall.cpp                                           source 25, Part I: `code/two-attachment/verify_hall.cpp`
code/25-degree-three-code-a2-verify_independent.py                                     source 25, Part I: `code/two-attachment/verify_independent.py`
code/25-degree-three-code-audit_cover3.py                                              source 25, Part I: `code/audit_cover3.py`
code/25-degree-three-code-core_templates.py                                            source 25, Part I: `code/core_templates.py`
code/25-degree-three-code-cover3.py                                                    source 25, Part I: `code/cover3.py`
code/25-degree-three-code-export_cover3.py                                             source 25, Part I: `code/export_cover3.py`
code/25-degree-three-code-layered.py                                                   source 25, Part I: `code/layered.py`
code/25-degree-three-code-minimum-certify_min_size.cpp                                 source 25, Part I: `code/minimum/certify_min_size.cpp`
code/25-degree-three-code-minimum-ia-audit.py                                          source 25, Part I: `code/minimum/independent-audit/audit.py`
code/25-degree-three-code-minimum-scan_a2.py                                           source 25, Part I: `code/minimum/scan_a2.py`
code/25-degree-three-code-minimum-scan_minimum.py                                      source 25, Part I: `code/minimum/scan_minimum.py`
code/25-degree-three-code-minimum-verify_15_supports.py                                source 25, Part I: `code/minimum/verify_15_supports.py`
code/25-degree-three-code-small-check-exhaust.cpp                                      source 25, Part I: `code/small-check/exhaust.cpp`
code/25-degree-three-code-small-check-exhaust7.cpp                                     source 25, Part I: `code/small-check/exhaust7.cpp`
code/25-degree-three-code-small-check-independent_verify.py                            source 25, Part I: `code/small-check/independent_verify.py`
code/25-degree-three-code-verify_cover3_compact.py                                     source 25, Part I: `code/verify_cover3_compact.py`
code/25-degree-three-code-verify_cover3_sdp_complete.py                                source 25, Part I: `code/verify_cover3_sdp_complete.py`
code/25-degree-three-code-verify_cover3_sos.py                                         source 25, Part I: `code/verify_cover3_sos.py`
code/25-degree-three-code-verify_layered.py                                            source 25, Part I: `code/verify_layered.py`
code/25-degree-three-verify_all.py                                                     source 25, Part I: `verify_all.py`
code/34-five-core-discovery-discover.py                                                source 34, Part III: `discovery/discover.py`
code/34-five-core-discovery-kernel.py                                                  source 34, Part III: `discovery/kernel.py`
code/34-five-core-discovery-orbits.cpp                                                 source 34, Part III: `discovery/orbits.cpp`
code/34-five-core-discovery-pair_tools.py                                              source 34, Part III: `discovery/pair_tools.py`
code/34-five-core-discovery-poly.py                                                    source 34, Part III: `discovery/poly.py`
code/34-five-core-proof-check-check.py                                                 source 34, Part III: `proof-check/check.py`
code/34-five-core-proof-check-check_strengthening_counterexample.py                    source 34, Part III: `proof-check/check_strengthening_counterexample.py`
code/34-five-core-verify.py                                                            source 34, Part III: `verify.py`
data/06-five-core-boundary-audits-article-certificate-approval.json                    source 06 (archive 07), Part III: `audits/article-certificate-approval.json`
data/06-five-core-boundary-audits-article-ordinary-scope-approval.json                 source 06 (archive 07), Part III: `audits/article-ordinary-scope-approval.json`
data/06-five-core-boundary-audits-compressed-certificate-parts.json                    source 06 (archive 07), Part III: `audits/compressed-certificate-parts.json`
data/06-five-core-boundary-audits-four-active-certificate-manifest.json                source 06 (archive 07), Part III: `audits/four-active-certificate-manifest.json`
data/06-five-core-boundary-audits-four-active-compression.json                         source 06 (archive 07), Part III: `audits/four-active-compression.json`
data/06-five-core-boundary-audits-four-active-receipt.json                             source 06 (archive 07), Part III: `audits/four-active-receipt.json`
data/06-five-core-boundary-audits-four-sink-receipt.json                               source 06 (archive 07), Part III: `audits/four-sink-receipt.json`
data/06-five-core-boundary-audits-ordinary-scope-approval.json                         source 06 (archive 07), Part III: `audits/ordinary-scope-approval.json`
data/06-five-core-boundary-audits-verification-receipt.json                            source 06 (archive 07), Part III: `audits/verification-receipt.json`
data/06-five-core-boundary-catalogs-four_active_cores.txt                              source 06 (archive 07), Part III: `catalogs/four_active_cores.txt`
data/06-five-core-boundary-four-active-certificates.tar.xz                             source 06 (archive 07), Part III: `four-active-certificates.tar.xz`
data/06-five-core-boundary-qa-visual-review.json                                       source 06 (archive 07), Part III: `qa/visual-review.json`
data/10-sink-all-degrees-audit-article-approval.json                                   source 10, Part III: `audit/article-approval.json`
data/10-sink-all-degrees-audit-independent-original-receipt.json                       source 10, Part III: `audit/independent-original-receipt.json`
data/10-sink-all-degrees-audit-producer-fresh-replay.json                              source 10, Part III: `audit/producer-fresh-replay.json`
data/10-sink-all-degrees-certificate-data-catalog.json                                 source 10, Part III: `certificate-data/catalog.json`
data/10-sink-all-degrees-certificate-data-certificate_0.json                           source 10, Part III: `certificate-data/certificate_0.json`
data/10-sink-all-degrees-certificate-data-certificate_1.json                           source 10, Part III: `certificate-data/certificate_1.json`
data/10-sink-all-degrees-certificate-data-certificate_10.json                          source 10, Part III: `certificate-data/certificate_10.json`
data/10-sink-all-degrees-certificate-data-certificate_100.json                         source 10, Part III: `certificate-data/certificate_100.json`
data/10-sink-all-degrees-certificate-data-certificate_101.json                         source 10, Part III: `certificate-data/certificate_101.json`
data/10-sink-all-degrees-certificate-data-certificate_102.json                         source 10, Part III: `certificate-data/certificate_102.json`
data/10-sink-all-degrees-certificate-data-certificate_103.json                         source 10, Part III: `certificate-data/certificate_103.json`
data/10-sink-all-degrees-certificate-data-certificate_104.json                         source 10, Part III: `certificate-data/certificate_104.json`
data/10-sink-all-degrees-certificate-data-certificate_105.json                         source 10, Part III: `certificate-data/certificate_105.json`
data/10-sink-all-degrees-certificate-data-certificate_106.json                         source 10, Part III: `certificate-data/certificate_106.json`
data/10-sink-all-degrees-certificate-data-certificate_107.json                         source 10, Part III: `certificate-data/certificate_107.json`
data/10-sink-all-degrees-certificate-data-certificate_108.json                         source 10, Part III: `certificate-data/certificate_108.json`
data/10-sink-all-degrees-certificate-data-certificate_109.json                         source 10, Part III: `certificate-data/certificate_109.json`
data/10-sink-all-degrees-certificate-data-certificate_11.json                          source 10, Part III: `certificate-data/certificate_11.json`
data/10-sink-all-degrees-certificate-data-certificate_110.json                         source 10, Part III: `certificate-data/certificate_110.json`
data/10-sink-all-degrees-certificate-data-certificate_111.json                         source 10, Part III: `certificate-data/certificate_111.json`
data/10-sink-all-degrees-certificate-data-certificate_112.json                         source 10, Part III: `certificate-data/certificate_112.json`
data/10-sink-all-degrees-certificate-data-certificate_113.json                         source 10, Part III: `certificate-data/certificate_113.json`
data/10-sink-all-degrees-certificate-data-certificate_114.json                         source 10, Part III: `certificate-data/certificate_114.json`
data/10-sink-all-degrees-certificate-data-certificate_115.json                         source 10, Part III: `certificate-data/certificate_115.json`
data/10-sink-all-degrees-certificate-data-certificate_116.json                         source 10, Part III: `certificate-data/certificate_116.json`
data/10-sink-all-degrees-certificate-data-certificate_117.json                         source 10, Part III: `certificate-data/certificate_117.json`
data/10-sink-all-degrees-certificate-data-certificate_118.json                         source 10, Part III: `certificate-data/certificate_118.json`
data/10-sink-all-degrees-certificate-data-certificate_119.json                         source 10, Part III: `certificate-data/certificate_119.json`
data/10-sink-all-degrees-certificate-data-certificate_12.json                          source 10, Part III: `certificate-data/certificate_12.json`
data/10-sink-all-degrees-certificate-data-certificate_120.json                         source 10, Part III: `certificate-data/certificate_120.json`
data/10-sink-all-degrees-certificate-data-certificate_121.json                         source 10, Part III: `certificate-data/certificate_121.json`
data/10-sink-all-degrees-certificate-data-certificate_122.json                         source 10, Part III: `certificate-data/certificate_122.json`
data/10-sink-all-degrees-certificate-data-certificate_123.json                         source 10, Part III: `certificate-data/certificate_123.json`
data/10-sink-all-degrees-certificate-data-certificate_124.json                         source 10, Part III: `certificate-data/certificate_124.json`
data/10-sink-all-degrees-certificate-data-certificate_125.json                         source 10, Part III: `certificate-data/certificate_125.json`
data/10-sink-all-degrees-certificate-data-certificate_126.json                         source 10, Part III: `certificate-data/certificate_126.json`
data/10-sink-all-degrees-certificate-data-certificate_127.json                         source 10, Part III: `certificate-data/certificate_127.json`
data/10-sink-all-degrees-certificate-data-certificate_128.json                         source 10, Part III: `certificate-data/certificate_128.json`
data/10-sink-all-degrees-certificate-data-certificate_129.json                         source 10, Part III: `certificate-data/certificate_129.json`
data/10-sink-all-degrees-certificate-data-certificate_13.json                          source 10, Part III: `certificate-data/certificate_13.json`
data/10-sink-all-degrees-certificate-data-certificate_130.json                         source 10, Part III: `certificate-data/certificate_130.json`
data/10-sink-all-degrees-certificate-data-certificate_131.json                         source 10, Part III: `certificate-data/certificate_131.json`
data/10-sink-all-degrees-certificate-data-certificate_132.json                         source 10, Part III: `certificate-data/certificate_132.json`
data/10-sink-all-degrees-certificate-data-certificate_133.json                         source 10, Part III: `certificate-data/certificate_133.json`
data/10-sink-all-degrees-certificate-data-certificate_134.json                         source 10, Part III: `certificate-data/certificate_134.json`
data/10-sink-all-degrees-certificate-data-certificate_135.json                         source 10, Part III: `certificate-data/certificate_135.json`
data/10-sink-all-degrees-certificate-data-certificate_136.json                         source 10, Part III: `certificate-data/certificate_136.json`
data/10-sink-all-degrees-certificate-data-certificate_137.json                         source 10, Part III: `certificate-data/certificate_137.json`
data/10-sink-all-degrees-certificate-data-certificate_138.json                         source 10, Part III: `certificate-data/certificate_138.json`
data/10-sink-all-degrees-certificate-data-certificate_139.json                         source 10, Part III: `certificate-data/certificate_139.json`
data/10-sink-all-degrees-certificate-data-certificate_14.json                          source 10, Part III: `certificate-data/certificate_14.json`
data/10-sink-all-degrees-certificate-data-certificate_140.json                         source 10, Part III: `certificate-data/certificate_140.json`
data/10-sink-all-degrees-certificate-data-certificate_141.json                         source 10, Part III: `certificate-data/certificate_141.json`
data/10-sink-all-degrees-certificate-data-certificate_142.json                         source 10, Part III: `certificate-data/certificate_142.json`
data/10-sink-all-degrees-certificate-data-certificate_143.json                         source 10, Part III: `certificate-data/certificate_143.json`
data/10-sink-all-degrees-certificate-data-certificate_144.json                         source 10, Part III: `certificate-data/certificate_144.json`
data/10-sink-all-degrees-certificate-data-certificate_145.json                         source 10, Part III: `certificate-data/certificate_145.json`
data/10-sink-all-degrees-certificate-data-certificate_146.json                         source 10, Part III: `certificate-data/certificate_146.json`
data/10-sink-all-degrees-certificate-data-certificate_147.json                         source 10, Part III: `certificate-data/certificate_147.json`
data/10-sink-all-degrees-certificate-data-certificate_148.json                         source 10, Part III: `certificate-data/certificate_148.json`
data/10-sink-all-degrees-certificate-data-certificate_149.json                         source 10, Part III: `certificate-data/certificate_149.json`
data/10-sink-all-degrees-certificate-data-certificate_15.json                          source 10, Part III: `certificate-data/certificate_15.json`
data/10-sink-all-degrees-certificate-data-certificate_150.json                         source 10, Part III: `certificate-data/certificate_150.json`
data/10-sink-all-degrees-certificate-data-certificate_151.json                         source 10, Part III: `certificate-data/certificate_151.json`
data/10-sink-all-degrees-certificate-data-certificate_152.json                         source 10, Part III: `certificate-data/certificate_152.json`
data/10-sink-all-degrees-certificate-data-certificate_153.json                         source 10, Part III: `certificate-data/certificate_153.json`
data/10-sink-all-degrees-certificate-data-certificate_154.json                         source 10, Part III: `certificate-data/certificate_154.json`
data/10-sink-all-degrees-certificate-data-certificate_155.json                         source 10, Part III: `certificate-data/certificate_155.json`
data/10-sink-all-degrees-certificate-data-certificate_156.json                         source 10, Part III: `certificate-data/certificate_156.json`
data/10-sink-all-degrees-certificate-data-certificate_157.json                         source 10, Part III: `certificate-data/certificate_157.json`
data/10-sink-all-degrees-certificate-data-certificate_158.json                         source 10, Part III: `certificate-data/certificate_158.json`
data/10-sink-all-degrees-certificate-data-certificate_159.json                         source 10, Part III: `certificate-data/certificate_159.json`
data/10-sink-all-degrees-certificate-data-certificate_16.json                          source 10, Part III: `certificate-data/certificate_16.json`
data/10-sink-all-degrees-certificate-data-certificate_160.json                         source 10, Part III: `certificate-data/certificate_160.json`
data/10-sink-all-degrees-certificate-data-certificate_161.json                         source 10, Part III: `certificate-data/certificate_161.json`
data/10-sink-all-degrees-certificate-data-certificate_162.json                         source 10, Part III: `certificate-data/certificate_162.json`
data/10-sink-all-degrees-certificate-data-certificate_163.json                         source 10, Part III: `certificate-data/certificate_163.json`
data/10-sink-all-degrees-certificate-data-certificate_164.json                         source 10, Part III: `certificate-data/certificate_164.json`
data/10-sink-all-degrees-certificate-data-certificate_165.json                         source 10, Part III: `certificate-data/certificate_165.json`
data/10-sink-all-degrees-certificate-data-certificate_166.json                         source 10, Part III: `certificate-data/certificate_166.json`
data/10-sink-all-degrees-certificate-data-certificate_167.json                         source 10, Part III: `certificate-data/certificate_167.json`
data/10-sink-all-degrees-certificate-data-certificate_168.json                         source 10, Part III: `certificate-data/certificate_168.json`
data/10-sink-all-degrees-certificate-data-certificate_169.json                         source 10, Part III: `certificate-data/certificate_169.json`
data/10-sink-all-degrees-certificate-data-certificate_17.json                          source 10, Part III: `certificate-data/certificate_17.json`
data/10-sink-all-degrees-certificate-data-certificate_170.json                         source 10, Part III: `certificate-data/certificate_170.json`
data/10-sink-all-degrees-certificate-data-certificate_171.json                         source 10, Part III: `certificate-data/certificate_171.json`
data/10-sink-all-degrees-certificate-data-certificate_172.json                         source 10, Part III: `certificate-data/certificate_172.json`
data/10-sink-all-degrees-certificate-data-certificate_173.json                         source 10, Part III: `certificate-data/certificate_173.json`
data/10-sink-all-degrees-certificate-data-certificate_174.json                         source 10, Part III: `certificate-data/certificate_174.json`
data/10-sink-all-degrees-certificate-data-certificate_175.json                         source 10, Part III: `certificate-data/certificate_175.json`
data/10-sink-all-degrees-certificate-data-certificate_176.json                         source 10, Part III: `certificate-data/certificate_176.json`
data/10-sink-all-degrees-certificate-data-certificate_177.json                         source 10, Part III: `certificate-data/certificate_177.json`
data/10-sink-all-degrees-certificate-data-certificate_178.json                         source 10, Part III: `certificate-data/certificate_178.json`
data/10-sink-all-degrees-certificate-data-certificate_179.json                         source 10, Part III: `certificate-data/certificate_179.json`
data/10-sink-all-degrees-certificate-data-certificate_18.json                          source 10, Part III: `certificate-data/certificate_18.json`
data/10-sink-all-degrees-certificate-data-certificate_180.json                         source 10, Part III: `certificate-data/certificate_180.json`
data/10-sink-all-degrees-certificate-data-certificate_181.json                         source 10, Part III: `certificate-data/certificate_181.json`
data/10-sink-all-degrees-certificate-data-certificate_182.json                         source 10, Part III: `certificate-data/certificate_182.json`
data/10-sink-all-degrees-certificate-data-certificate_183.json                         source 10, Part III: `certificate-data/certificate_183.json`
data/10-sink-all-degrees-certificate-data-certificate_184.json                         source 10, Part III: `certificate-data/certificate_184.json`
data/10-sink-all-degrees-certificate-data-certificate_185.json                         source 10, Part III: `certificate-data/certificate_185.json`
data/10-sink-all-degrees-certificate-data-certificate_186.json                         source 10, Part III: `certificate-data/certificate_186.json`
data/10-sink-all-degrees-certificate-data-certificate_187.json                         source 10, Part III: `certificate-data/certificate_187.json`
data/10-sink-all-degrees-certificate-data-certificate_188.json                         source 10, Part III: `certificate-data/certificate_188.json`
data/10-sink-all-degrees-certificate-data-certificate_189.json                         source 10, Part III: `certificate-data/certificate_189.json`
data/10-sink-all-degrees-certificate-data-certificate_19.json                          source 10, Part III: `certificate-data/certificate_19.json`
data/10-sink-all-degrees-certificate-data-certificate_190.json                         source 10, Part III: `certificate-data/certificate_190.json`
data/10-sink-all-degrees-certificate-data-certificate_191.json                         source 10, Part III: `certificate-data/certificate_191.json`
data/10-sink-all-degrees-certificate-data-certificate_192.json                         source 10, Part III: `certificate-data/certificate_192.json`
data/10-sink-all-degrees-certificate-data-certificate_193.json                         source 10, Part III: `certificate-data/certificate_193.json`
data/10-sink-all-degrees-certificate-data-certificate_194.json                         source 10, Part III: `certificate-data/certificate_194.json`
data/10-sink-all-degrees-certificate-data-certificate_195.json                         source 10, Part III: `certificate-data/certificate_195.json`
data/10-sink-all-degrees-certificate-data-certificate_196.json                         source 10, Part III: `certificate-data/certificate_196.json`
data/10-sink-all-degrees-certificate-data-certificate_197.json                         source 10, Part III: `certificate-data/certificate_197.json`
data/10-sink-all-degrees-certificate-data-certificate_198.json                         source 10, Part III: `certificate-data/certificate_198.json`
data/10-sink-all-degrees-certificate-data-certificate_199.json                         source 10, Part III: `certificate-data/certificate_199.json`
data/10-sink-all-degrees-certificate-data-certificate_2.json                           source 10, Part III: `certificate-data/certificate_2.json`
data/10-sink-all-degrees-certificate-data-certificate_20.json                          source 10, Part III: `certificate-data/certificate_20.json`
data/10-sink-all-degrees-certificate-data-certificate_200.json                         source 10, Part III: `certificate-data/certificate_200.json`
data/10-sink-all-degrees-certificate-data-certificate_201.json                         source 10, Part III: `certificate-data/certificate_201.json`
data/10-sink-all-degrees-certificate-data-certificate_202.json                         source 10, Part III: `certificate-data/certificate_202.json`
data/10-sink-all-degrees-certificate-data-certificate_203.json                         source 10, Part III: `certificate-data/certificate_203.json`
data/10-sink-all-degrees-certificate-data-certificate_204.json                         source 10, Part III: `certificate-data/certificate_204.json`
data/10-sink-all-degrees-certificate-data-certificate_205.json                         source 10, Part III: `certificate-data/certificate_205.json`
data/10-sink-all-degrees-certificate-data-certificate_206.json                         source 10, Part III: `certificate-data/certificate_206.json`
data/10-sink-all-degrees-certificate-data-certificate_207.json                         source 10, Part III: `certificate-data/certificate_207.json`
data/10-sink-all-degrees-certificate-data-certificate_208.json                         source 10, Part III: `certificate-data/certificate_208.json`
data/10-sink-all-degrees-certificate-data-certificate_209.json                         source 10, Part III: `certificate-data/certificate_209.json`
data/10-sink-all-degrees-certificate-data-certificate_21.json                          source 10, Part III: `certificate-data/certificate_21.json`
data/10-sink-all-degrees-certificate-data-certificate_210.json                         source 10, Part III: `certificate-data/certificate_210.json`
data/10-sink-all-degrees-certificate-data-certificate_211.json                         source 10, Part III: `certificate-data/certificate_211.json`
data/10-sink-all-degrees-certificate-data-certificate_212.json                         source 10, Part III: `certificate-data/certificate_212.json`
data/10-sink-all-degrees-certificate-data-certificate_213.json                         source 10, Part III: `certificate-data/certificate_213.json`
data/10-sink-all-degrees-certificate-data-certificate_214.json                         source 10, Part III: `certificate-data/certificate_214.json`
data/10-sink-all-degrees-certificate-data-certificate_215.json                         source 10, Part III: `certificate-data/certificate_215.json`
data/10-sink-all-degrees-certificate-data-certificate_216.json                         source 10, Part III: `certificate-data/certificate_216.json`
data/10-sink-all-degrees-certificate-data-certificate_217.json                         source 10, Part III: `certificate-data/certificate_217.json`
data/10-sink-all-degrees-certificate-data-certificate_22.json                          source 10, Part III: `certificate-data/certificate_22.json`
data/10-sink-all-degrees-certificate-data-certificate_23.json                          source 10, Part III: `certificate-data/certificate_23.json`
data/10-sink-all-degrees-certificate-data-certificate_24.json                          source 10, Part III: `certificate-data/certificate_24.json`
data/10-sink-all-degrees-certificate-data-certificate_25.json                          source 10, Part III: `certificate-data/certificate_25.json`
data/10-sink-all-degrees-certificate-data-certificate_26.json                          source 10, Part III: `certificate-data/certificate_26.json`
data/10-sink-all-degrees-certificate-data-certificate_27.json                          source 10, Part III: `certificate-data/certificate_27.json`
data/10-sink-all-degrees-certificate-data-certificate_28.json                          source 10, Part III: `certificate-data/certificate_28.json`
data/10-sink-all-degrees-certificate-data-certificate_29.json                          source 10, Part III: `certificate-data/certificate_29.json`
data/10-sink-all-degrees-certificate-data-certificate_3.json                           source 10, Part III: `certificate-data/certificate_3.json`
data/10-sink-all-degrees-certificate-data-certificate_30.json                          source 10, Part III: `certificate-data/certificate_30.json`
data/10-sink-all-degrees-certificate-data-certificate_31.json                          source 10, Part III: `certificate-data/certificate_31.json`
data/10-sink-all-degrees-certificate-data-certificate_32.json                          source 10, Part III: `certificate-data/certificate_32.json`
data/10-sink-all-degrees-certificate-data-certificate_33.json                          source 10, Part III: `certificate-data/certificate_33.json`
data/10-sink-all-degrees-certificate-data-certificate_34.json                          source 10, Part III: `certificate-data/certificate_34.json`
data/10-sink-all-degrees-certificate-data-certificate_35.json                          source 10, Part III: `certificate-data/certificate_35.json`
data/10-sink-all-degrees-certificate-data-certificate_36.json                          source 10, Part III: `certificate-data/certificate_36.json`
data/10-sink-all-degrees-certificate-data-certificate_37.json                          source 10, Part III: `certificate-data/certificate_37.json`
data/10-sink-all-degrees-certificate-data-certificate_38.json                          source 10, Part III: `certificate-data/certificate_38.json`
data/10-sink-all-degrees-certificate-data-certificate_39.json                          source 10, Part III: `certificate-data/certificate_39.json`
data/10-sink-all-degrees-certificate-data-certificate_4.json                           source 10, Part III: `certificate-data/certificate_4.json`
data/10-sink-all-degrees-certificate-data-certificate_40.json                          source 10, Part III: `certificate-data/certificate_40.json`
data/10-sink-all-degrees-certificate-data-certificate_41.json                          source 10, Part III: `certificate-data/certificate_41.json`
data/10-sink-all-degrees-certificate-data-certificate_42.json                          source 10, Part III: `certificate-data/certificate_42.json`
data/10-sink-all-degrees-certificate-data-certificate_43.json                          source 10, Part III: `certificate-data/certificate_43.json`
data/10-sink-all-degrees-certificate-data-certificate_44.json                          source 10, Part III: `certificate-data/certificate_44.json`
data/10-sink-all-degrees-certificate-data-certificate_45.json                          source 10, Part III: `certificate-data/certificate_45.json`
data/10-sink-all-degrees-certificate-data-certificate_46.json                          source 10, Part III: `certificate-data/certificate_46.json`
data/10-sink-all-degrees-certificate-data-certificate_47.json                          source 10, Part III: `certificate-data/certificate_47.json`
data/10-sink-all-degrees-certificate-data-certificate_48.json                          source 10, Part III: `certificate-data/certificate_48.json`
data/10-sink-all-degrees-certificate-data-certificate_49.json                          source 10, Part III: `certificate-data/certificate_49.json`
data/10-sink-all-degrees-certificate-data-certificate_5.json                           source 10, Part III: `certificate-data/certificate_5.json`
data/10-sink-all-degrees-certificate-data-certificate_50.json                          source 10, Part III: `certificate-data/certificate_50.json`
data/10-sink-all-degrees-certificate-data-certificate_51.json                          source 10, Part III: `certificate-data/certificate_51.json`
data/10-sink-all-degrees-certificate-data-certificate_52.json                          source 10, Part III: `certificate-data/certificate_52.json`
data/10-sink-all-degrees-certificate-data-certificate_53.json                          source 10, Part III: `certificate-data/certificate_53.json`
data/10-sink-all-degrees-certificate-data-certificate_54.json                          source 10, Part III: `certificate-data/certificate_54.json`
data/10-sink-all-degrees-certificate-data-certificate_55.json                          source 10, Part III: `certificate-data/certificate_55.json`
data/10-sink-all-degrees-certificate-data-certificate_56.json                          source 10, Part III: `certificate-data/certificate_56.json`
data/10-sink-all-degrees-certificate-data-certificate_57.json                          source 10, Part III: `certificate-data/certificate_57.json`
data/10-sink-all-degrees-certificate-data-certificate_58.json                          source 10, Part III: `certificate-data/certificate_58.json`
data/10-sink-all-degrees-certificate-data-certificate_59.json                          source 10, Part III: `certificate-data/certificate_59.json`
data/10-sink-all-degrees-certificate-data-certificate_6.json                           source 10, Part III: `certificate-data/certificate_6.json`
data/10-sink-all-degrees-certificate-data-certificate_60.json                          source 10, Part III: `certificate-data/certificate_60.json`
data/10-sink-all-degrees-certificate-data-certificate_61.json                          source 10, Part III: `certificate-data/certificate_61.json`
data/10-sink-all-degrees-certificate-data-certificate_62.json                          source 10, Part III: `certificate-data/certificate_62.json`
data/10-sink-all-degrees-certificate-data-certificate_63.json                          source 10, Part III: `certificate-data/certificate_63.json`
data/10-sink-all-degrees-certificate-data-certificate_64.json                          source 10, Part III: `certificate-data/certificate_64.json`
data/10-sink-all-degrees-certificate-data-certificate_65.json                          source 10, Part III: `certificate-data/certificate_65.json`
data/10-sink-all-degrees-certificate-data-certificate_66.json                          source 10, Part III: `certificate-data/certificate_66.json`
data/10-sink-all-degrees-certificate-data-certificate_67.json                          source 10, Part III: `certificate-data/certificate_67.json`
data/10-sink-all-degrees-certificate-data-certificate_68.json                          source 10, Part III: `certificate-data/certificate_68.json`
data/10-sink-all-degrees-certificate-data-certificate_69.json                          source 10, Part III: `certificate-data/certificate_69.json`
data/10-sink-all-degrees-certificate-data-certificate_7.json                           source 10, Part III: `certificate-data/certificate_7.json`
data/10-sink-all-degrees-certificate-data-certificate_70.json                          source 10, Part III: `certificate-data/certificate_70.json`
data/10-sink-all-degrees-certificate-data-certificate_71.json                          source 10, Part III: `certificate-data/certificate_71.json`
data/10-sink-all-degrees-certificate-data-certificate_72.json                          source 10, Part III: `certificate-data/certificate_72.json`
data/10-sink-all-degrees-certificate-data-certificate_73.json                          source 10, Part III: `certificate-data/certificate_73.json`
data/10-sink-all-degrees-certificate-data-certificate_74.json                          source 10, Part III: `certificate-data/certificate_74.json`
data/10-sink-all-degrees-certificate-data-certificate_75.json                          source 10, Part III: `certificate-data/certificate_75.json`
data/10-sink-all-degrees-certificate-data-certificate_76.json                          source 10, Part III: `certificate-data/certificate_76.json`
data/10-sink-all-degrees-certificate-data-certificate_77.json                          source 10, Part III: `certificate-data/certificate_77.json`
data/10-sink-all-degrees-certificate-data-certificate_78.json                          source 10, Part III: `certificate-data/certificate_78.json`
data/10-sink-all-degrees-certificate-data-certificate_79.json                          source 10, Part III: `certificate-data/certificate_79.json`
data/10-sink-all-degrees-certificate-data-certificate_8.json                           source 10, Part III: `certificate-data/certificate_8.json`
data/10-sink-all-degrees-certificate-data-certificate_80.json                          source 10, Part III: `certificate-data/certificate_80.json`
data/10-sink-all-degrees-certificate-data-certificate_81.json                          source 10, Part III: `certificate-data/certificate_81.json`
data/10-sink-all-degrees-certificate-data-certificate_82.json                          source 10, Part III: `certificate-data/certificate_82.json`
data/10-sink-all-degrees-certificate-data-certificate_83.json                          source 10, Part III: `certificate-data/certificate_83.json`
data/10-sink-all-degrees-certificate-data-certificate_84.json                          source 10, Part III: `certificate-data/certificate_84.json`
data/10-sink-all-degrees-certificate-data-certificate_85.json                          source 10, Part III: `certificate-data/certificate_85.json`
data/10-sink-all-degrees-certificate-data-certificate_86.json                          source 10, Part III: `certificate-data/certificate_86.json`
data/10-sink-all-degrees-certificate-data-certificate_87.json                          source 10, Part III: `certificate-data/certificate_87.json`
data/10-sink-all-degrees-certificate-data-certificate_88.json                          source 10, Part III: `certificate-data/certificate_88.json`
data/10-sink-all-degrees-certificate-data-certificate_89.json                          source 10, Part III: `certificate-data/certificate_89.json`
data/10-sink-all-degrees-certificate-data-certificate_9.json                           source 10, Part III: `certificate-data/certificate_9.json`
data/10-sink-all-degrees-certificate-data-certificate_90.json                          source 10, Part III: `certificate-data/certificate_90.json`
data/10-sink-all-degrees-certificate-data-certificate_91.json                          source 10, Part III: `certificate-data/certificate_91.json`
data/10-sink-all-degrees-certificate-data-certificate_92.json                          source 10, Part III: `certificate-data/certificate_92.json`
data/10-sink-all-degrees-certificate-data-certificate_93.json                          source 10, Part III: `certificate-data/certificate_93.json`
data/10-sink-all-degrees-certificate-data-certificate_94.json                          source 10, Part III: `certificate-data/certificate_94.json`
data/10-sink-all-degrees-certificate-data-certificate_95.json                          source 10, Part III: `certificate-data/certificate_95.json`
data/10-sink-all-degrees-certificate-data-certificate_96.json                          source 10, Part III: `certificate-data/certificate_96.json`
data/10-sink-all-degrees-certificate-data-certificate_97.json                          source 10, Part III: `certificate-data/certificate_97.json`
data/10-sink-all-degrees-certificate-data-certificate_98.json                          source 10, Part III: `certificate-data/certificate_98.json`
data/10-sink-all-degrees-certificate-data-certificate_99.json                          source 10, Part III: `certificate-data/certificate_99.json`
data/10-sink-all-degrees-qa-visual-review.json                                         source 10, Part III: `qa/visual-review.json`
data/11-physical-cover-audits-assembly-approval.json                                   source 11, Part II: `audits/assembly-approval.json`
data/11-physical-cover-audits-integrated-paper-approval.json                           source 11, Part II: `audits/integrated-paper-approval.json`
data/11-physical-cover-dependency-release-replay-approval.json                         source 11, Part II: `dependency/release-replay-approval.json`
data/11-physical-cover-independent-independent_receipt.json                            source 11, Part II: `reproducibility/independent/independent_receipt.json`
data/11-physical-cover-producer-assembly_verification.json                             source 11, Part II: `reproducibility/producer/assembly_verification.json`
data/11-physical-cover-qa-visual-qa.json                                               source 11, Part II: `qa/visual-qa.json`
data/12-three-core-rayleigh-audits-boundary-approval.json                              source 12, Part II: `audits/boundary-approval.json`
data/12-three-core-rayleigh-audits-core-rayleigh-approval.json                         source 12, Part II: `audits/core-rayleigh-approval.json`
data/12-three-core-rayleigh-audits-four-core-approval.json                             source 12, Part II: `audits/four-core-approval.json`
data/12-three-core-rayleigh-audits-integrated-paper-approval.json                      source 12, Part II: `audits/integrated-paper-approval.json`
data/12-three-core-rayleigh-independent-boundary-independent_receipt.json              source 12, Part II: `reproducibility/independent-boundary/independent_receipt.json`
data/12-three-core-rayleigh-independent-four-core-independent_receipt.json             source 12, Part II: `reproducibility/independent-four-core/independent_receipt.json`
data/12-three-core-rayleigh-producer-boundary-universal_boundary_receipt.json          source 12, Part II: `reproducibility/producer-boundary/universal_boundary_receipt.json`
data/12-three-core-rayleigh-producer-four-core-four_core_obstruction_receipt.json      source 12, Part II: `reproducibility/producer-four-core/four_core_obstruction_receipt.json`
data/12-three-core-rayleigh-qa-visual-qa.json                                          source 12, Part II: `qa/visual-qa.json`
data/14-sink-last-gap-audit-article-approval.json                                      source 14, Part III: `audit/article-approval.json`
data/14-sink-last-gap-audit-independent-original-receipt.json                          source 14, Part III: `audit/independent-original-receipt.json`
data/14-sink-last-gap-audit-producer-fresh-replay.json                                 source 14, Part III: `audit/producer-fresh-replay.json`
data/14-sink-last-gap-audit-producer-original-receipt.json                             source 14, Part III: `audit/producer-original-receipt.json`
data/14-sink-last-gap-qa-visual-review.json                                            source 14, Part III: `qa/visual-review.json`
data/15-pendant-support-audits-bipartition-approval.json                               source 15, Part II: `audits/bipartition-approval.json`
data/15-pendant-support-audits-integrated-paper-approval.json                          source 15, Part II: `audits/integrated-paper-approval.json`
data/15-pendant-support-audits-pendant-approval.json                                   source 15, Part II: `audits/pendant-approval.json`
data/15-pendant-support-independent-bipartite-verification.json                        source 15, Part II: `reproducibility/independent-bipartite/verification.json`
data/15-pendant-support-independent-pendant-verification.json                          source 15, Part II: `reproducibility/independent-pendant/verification.json`
data/15-pendant-support-producer-pendant_verification.json                             source 15, Part II: `reproducibility/producer/pendant_verification.json`
data/15-pendant-support-producer-verification.json                                     source 15, Part II: `reproducibility/producer/verification.json`
data/15-pendant-support-qa-visual-qa.json                                              source 15, Part II: `qa/visual-qa.json`
data/15-pendant-support-requirements.txt                                               source 15, Part II: `requirements.txt`
data/16-degree-four-a2-coefficient_certificates.json                                   source 16 (archive 18), Part I: `reproducibility/sources/preorder-gamma-degree4/two-attachment/coefficient_certificates.json`
data/16-degree-four-a2-gap3_unresolved_faces.jsonl                                     source 16 (archive 18), Part I: `reproducibility/sources/preorder-gamma-degree4/two-attachment/gap3_unresolved_faces.jsonl`
data/16-degree-four-a2-quartic_classification.json                                     source 16, Part I: `reproducibility/sources/preorder-gamma-degree4/two-attachment/quartic_classification.json`
data/16-degree-four-a2-quartic_general_sos.jsonl                                       source 16 (archive 18), Part I: `reproducibility/sources/preorder-gamma-degree4/two-attachment/quartic_general_sos.jsonl`
data/16-degree-four-a2-quartic_general_sos_result.json                                 source 16, Part I: `reproducibility/sources/preorder-gamma-degree4/two-attachment/quartic_general_sos_result.json`
data/16-degree-four-a2-quartic_sos_basis.json                                          source 16, Part I: `reproducibility/sources/preorder-gamma-degree4/two-attachment/quartic_sos_basis.json`
data/16-degree-four-a2-quartic_sos_result.json                                         source 16, Part I: `reproducibility/sources/preorder-gamma-degree4/two-attachment/quartic_sos_result.json`
data/16-degree-four-a2-quartic_verification.json                                       source 16 (archive 17), Part I: `reproducibility/sources/preorder-gamma-degree4/two-attachment/quartic_verification.json`
data/16-degree-four-a3-a3_gamma_aliases.json                                           source 16 (archive 19), Part I: `reproducibility/sources/preorder-gamma-degree4/three-attachment/a3_gamma_aliases.json`
data/16-degree-four-a3-coefficient_certificates.json                                   source 16 (archive 17), Part I: `reproducibility/sources/preorder-gamma-degree4/three-attachment/coefficient_certificates.json`
data/16-degree-four-a3-verification.json                                               source 16, Part I: `reproducibility/sources/preorder-gamma-degree4/three-attachment/verification.json`
data/16-degree-four-a4-a4_polynomials.jsonl                                            source 16 (archive 17), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/a4_polynomials.jsonl`
data/16-degree-four-a4-approved_progress.json                                          source 16 (archive 18), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/approved_progress.json`
data/16-degree-four-a4-coreE_screen_36.json                                            source 16 (archive 17), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_coreE_screen_36.json`
data/16-degree-four-a4-coreE_screen_37.json                                            source 16, Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_coreE_screen_37.json`
data/16-degree-four-a4-coreE_shifted_gmp_50.json                                       source 16, Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_coreE_shifted_gmp_50.json`
data/16-degree-four-a4-core_corrections.jsonl                                          source 16, Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/core_corrections.jsonl`
data/16-degree-four-a4-face_orbit_summary.json                                         source 16 (archive 18), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/face_orbit_summary.json`
data/16-degree-four-a4-face_tasks.tsv                                                  source 16 (archive 19), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/face_tasks.tsv`
data/16-degree-four-a4-gap3_weighted_leading_zeros_26.json                             source 16 (archive 18), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/gap3_weighted_leading_zeros_26.json`
data/16-degree-four-a4-global_integer_sextic_lifted_verification.json                  source 16 (archive 19), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_sextic_lifted_verification.json`
data/16-degree-four-a4-gram_za_0.json                                                  source 16 (archive 19), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_gram_zeroaware_0.json`
data/16-degree-four-a4-gram_za_1.json                                                  source 16, Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_gram_zeroaware_1.json`
data/16-degree-four-a4-gram_za_10.json                                                 source 16 (archive 18), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_gram_zeroaware_10.json`
data/16-degree-four-a4-gram_za_11.json                                                 source 16, Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_gram_zeroaware_11.json`
data/16-degree-four-a4-gram_za_13.json                                                 source 16 (archive 17), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_gram_zeroaware_13.json`
data/16-degree-four-a4-gram_za_14.json                                                 source 16, Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_gram_zeroaware_14.json`
data/16-degree-four-a4-gram_za_16.json                                                 source 16, Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_gram_zeroaware_16.json`
data/16-degree-four-a4-gram_za_19.json                                                 source 16, Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_gram_zeroaware_19.json`
data/16-degree-four-a4-gram_za_2.json                                                  source 16 (archive 18), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_gram_zeroaware_2.json`
data/16-degree-four-a4-gram_za_21.json                                                 source 16, Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_gram_zeroaware_21.json`
data/16-degree-four-a4-gram_za_23.json                                                 source 16, Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_gram_zeroaware_23.json`
data/16-degree-four-a4-gram_za_26.json                                                 source 16 (archive 19), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_gram_zeroaware_26.json`
data/16-degree-four-a4-gram_za_28.json                                                 source 16 (archive 17), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_gram_zeroaware_28.json`
data/16-degree-four-a4-gram_za_3.json                                                  source 16 (archive 18), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_gram_zeroaware_3.json`
data/16-degree-four-a4-gram_za_33.json                                                 source 16 (archive 17), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_gram_zeroaware_33.json`
data/16-degree-four-a4-gram_za_34.json                                                 source 16 (archive 17), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_gram_zeroaware_34.json`
data/16-degree-four-a4-gram_za_36.json                                                 source 16, Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_gram_zeroaware_36.json`
data/16-degree-four-a4-gram_za_37.json                                                 source 16 (archive 19), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_gram_zeroaware_37.json`
data/16-degree-four-a4-gram_za_4.json                                                  source 16 (archive 18), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_gram_zeroaware_4.json`
data/16-degree-four-a4-gram_za_50.json                                                 source 16 (archive 19), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_gram_zeroaware_50.json`
data/16-degree-four-a4-gram_za_54.json                                                 source 16 (archive 18), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_gram_zeroaware_54.json`
data/16-degree-four-a4-gram_za_6.json                                                  source 16 (archive 18), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_gram_zeroaware_6.json`
data/16-degree-four-a4-gram_za_8.json                                                  source 16 (archive 17), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_gram_zeroaware_8.json`
data/16-degree-four-a4-gram_za_9.json                                                  source 16 (archive 17), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_gram_zeroaware_9.json`
data/16-degree-four-a4-mf-face_aliases.json                                            source 16 (archive 19), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/medium-faces/face_aliases.json`
data/16-degree-four-a4-mf-selection.json                                               source 16 (archive 17), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/medium-faces/selection.json`
data/16-degree-four-a4-sextic_gmp_11.json                                              source 16 (archive 18), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_sextic_shifted_gmp_11.json`
data/16-degree-four-a4-sextic_gmp_12.json                                              source 16 (archive 19), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_sextic_shifted_gmp_12.json`
data/16-degree-four-a4-sextic_gmp_13.json                                              source 16, Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_sextic_shifted_gmp_13.json`
data/16-degree-four-a4-sextic_gmp_14.json                                              source 16 (archive 19), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_sextic_shifted_gmp_14.json`
data/16-degree-four-a4-sextic_gmp_15.json                                              source 16, Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_sextic_shifted_gmp_15.json`
data/16-degree-four-a4-sextic_gmp_16.json                                              source 16, Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_sextic_shifted_gmp_16.json`
data/16-degree-four-a4-sextic_gmp_2.json                                               source 16, Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_sextic_shifted_gmp_2.json`
data/16-degree-four-a4-sextic_gmp_23.json                                              source 16 (archive 17), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_sextic_shifted_gmp_23.json`
data/16-degree-four-a4-sextic_gmp_24.json                                              source 16 (archive 17), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_sextic_shifted_gmp_24.json`
data/16-degree-four-a4-sextic_gmp_28.json                                              source 16 (archive 18), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_sextic_shifted_gmp_28.json`
data/16-degree-four-a4-sextic_gmp_3.json                                               source 16 (archive 17), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_sextic_shifted_gmp_3.json`
data/16-degree-four-a4-sextic_gmp_30.json                                              source 16 (archive 17), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_sextic_shifted_gmp_30.json`
data/16-degree-four-a4-sextic_gmp_33.json                                              source 16 (archive 18), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_sextic_shifted_gmp_33.json`
data/16-degree-four-a4-sextic_gmp_40.json                                              source 16 (archive 17), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_sextic_shifted_gmp_40.json`
data/16-degree-four-a4-sextic_gmp_46.json                                              source 16 (archive 19), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_sextic_shifted_gmp_46.json`
data/16-degree-four-a4-sextic_gmp_5.json                                               source 16, Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_sextic_shifted_gmp_5.json`
data/16-degree-four-a4-sextic_gmp_54.json                                              source 16, Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_sextic_shifted_gmp_54.json`
data/16-degree-four-a4-sextic_gmp_60.json                                              source 16 (archive 18), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_sextic_shifted_gmp_60.json`
data/16-degree-four-a4-sextic_gmp_7.json                                               source 16 (archive 18), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_sextic_shifted_gmp_7.json`
data/16-degree-four-a4-sextic_gmp_8.json                                               source 16, Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/global_integer_sextic_shifted_gmp_8.json`
data/16-degree-four-a4-sf-certificates.jsonl                                           source 16 (archive 17), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/small-faces/certificates.jsonl`
data/16-degree-four-a4-sf-face_aliases.json                                            source 16 (archive 17), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/small-faces/face_aliases.json`
data/16-degree-four-a4-sf-normalized_faces.jsonl                                       source 16 (archive 18), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/small-faces/normalized_faces.jsonl`
data/16-degree-four-a4-sf-selection.json                                               source 16, Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/small-faces/selection.json`
data/16-degree-four-a4-sf-source_faces.jsonl                                           source 16 (archive 19), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/small-faces/source_faces.jsonl`
data/16-degree-four-a4-templates.json                                                  source 16 (archive 19), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/templates.json`
data/16-degree-four-a4-templates.tsv                                                   source 16 (archive 19), Part I: `reproducibility/sources/preorder-gamma-degree4/four-attachment/templates.tsv`
data/16-degree-four-api-receipt.json                                                   source 16 (archive 19), Part I: `reproducibility/sources/preorder-gamma-degree4/audit-positivity-independent/receipt.json`
data/16-degree-four-audits-article_final_mathematical_audit.json                       source 16, Part I: `audits/article_final_mathematical_audit.json`
data/16-degree-four-bc-ia-F_polynomials.txt                                            source 16 (archive 18), Part I: `reproducibility/sources/balanced-core-gamma-research/independent-audit/F_polynomials.txt`
data/16-degree-four-bc-ia-balanced_last_gap_audit_receipt.json                         source 16 (archive 17), Part I: `reproducibility/sources/balanced-core-gamma-research/independent-audit/balanced_last_gap_audit_receipt.json`
data/16-degree-four-bc-ia-bound_verification.json                                      source 16 (archive 19), Part I: `reproducibility/sources/balanced-core-gamma-research/independent-audit/bound_verification.json`
data/16-degree-four-bc-ia-decomposition_verification.json                              source 16 (archive 18), Part I: `reproducibility/sources/balanced-core-gamma-research/independent-audit/decomposition_verification.json`
data/16-degree-four-bc-ia-independent_verification.json                                source 16 (archive 19), Part I: `reproducibility/sources/balanced-core-gamma-research/independent-audit/independent_verification.json`
data/16-degree-four-bc-ic-ia-elementary_stability_operators_audit_receipt.json         source 16 (archive 18), Part I: `reproducibility/sources/balanced-core-gamma-research/incomplete-core/independent-audit/elementary_stability_operators_audit_receipt.json`
data/16-degree-four-bc-ic-verify_matching_squares.json                                 source 16, Part I: `reproducibility/sources/balanced-core-gamma-research/incomplete-core/verify_matching_squares.json`
data/16-degree-four-bc-ic-verify_rayleigh_squares.json                                 source 16 (archive 18), Part I: `reproducibility/sources/balanced-core-gamma-research/incomplete-core/verify_rayleigh_squares.json`
data/16-degree-four-bc-uc-applicable_star_templates.json                               source 16 (archive 17), Part I: `reproducibility/sources/balanced-core-gamma-research/unbalanced-core/applicable_star_templates.json`
data/16-degree-four-bc-uc-ia-last_gap_audit_receipt.json                               source 16 (archive 18), Part I: `reproducibility/sources/balanced-core-gamma-research/unbalanced-core/independent-audit/last_gap_audit_receipt.json`
data/16-degree-four-examples-failed_coreE_integer_witnesses.json                       source 16 (archive 18), Part I: `reproducibility/examples/failed_coreE_integer_witnesses.json`
data/16-degree-four-examples-fulltype_nonreal_witness.json                             source 16, Part I: `reproducibility/examples/fulltype_nonreal_witness.json`
data/16-degree-four-exterior_lorentzian_audit_receipt.json                             source 16 (archive 19), Part I: `reproducibility/sources/preorder-gamma-degree4/exterior_lorentzian_audit_receipt.json`
data/16-degree-four-ia-a2-kernel_audit.json                                            source 16 (archive 17), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/two-attachment/kernel_audit.json`
data/16-degree-four-ia-a3-kernel_audit.json                                            source 16 (archive 19), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/three-attachment/kernel_audit.json`
data/16-degree-four-ia-a3-positivity_audit.json                                        source 16 (archive 17), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/three-attachment/positivity_audit.json`
data/16-degree-four-ia-a3-preparation.json                                             source 16 (archive 19), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/three-attachment/preparation.json`
data/16-degree-four-ia-a4-approved_replay_inputs.json                                  source 16 (archive 17), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/approved_replay_inputs.json`
data/16-degree-four-ia-a4-article_elementary_operator_transcription_audit.json         source 16 (archive 18), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/article_elementary_operator_transcription_audit.json`
data/16-degree-four-ia-a4-article_scope_audit_provisional.json                         source 16 (archive 18), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/article_scope_audit_provisional.json`
data/16-degree-four-ia-a4-complete_a4_audit_receipt.json                               source 16 (archive 19), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/complete_a4_audit_receipt.json`
data/16-degree-four-ia-a4-face_orbit_audit.json                                        source 16 (archive 19), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/face_orbit_audit.json`
data/16-degree-four-ia-a4-global_binomial_square_audit.json                            source 16 (archive 17), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/global_binomial_square_audit.json`
data/16-degree-four-ia-a4-global_gap2_all_large_receipt.json                           source 16 (archive 19), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/global_gap2_all_large_receipt.json`
data/16-degree-four-ia-a4-global_gap2_templates10_34_receipt.json                      source 16 (archive 17), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/global_gap2_templates10_34_receipt.json`
data/16-degree-four-ia-a4-global_gap2_templates2_10_34_receipt.json                    source 16 (archive 18), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/global_gap2_templates2_10_34_receipt.json`
data/16-degree-four-ia-a4-global_gap3_batch10_receipt.json                             source 16, Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/global_gap3_batch10_receipt.json`
data/16-degree-four-ia-a4-global_gap3_batch1_receipt.json                              source 16 (archive 19), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/global_gap3_batch1_receipt.json`
data/16-degree-four-ia-a4-global_gap3_batch2_receipt.json                              source 16, Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/global_gap3_batch2_receipt.json`
data/16-degree-four-ia-a4-global_gap3_batch3_receipt.json                              source 16 (archive 18), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/global_gap3_batch3_receipt.json`
data/16-degree-four-ia-a4-global_gap3_batch4_receipt.json                              source 16, Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/global_gap3_batch4_receipt.json`
data/16-degree-four-ia-a4-global_gap3_batch5_receipt.json                              source 16 (archive 19), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/global_gap3_batch5_receipt.json`
data/16-degree-four-ia-a4-global_gap3_batch6_receipt.json                              source 16 (archive 17), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/global_gap3_batch6_receipt.json`
data/16-degree-four-ia-a4-global_gap3_batch7_receipt.json                              source 16 (archive 18), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/global_gap3_batch7_receipt.json`
data/16-degree-four-ia-a4-global_gap3_batch8_receipt.json                              source 16 (archive 19), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/global_gap3_batch8_receipt.json`
data/16-degree-four-ia-a4-global_gap3_batch9_receipt.json                              source 16 (archive 19), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/global_gap3_batch9_receipt.json`
data/16-degree-four-ia-a4-global_gap3_coreE_batch1_receipt.json                        source 16 (archive 19), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/global_gap3_coreE_batch1_receipt.json`
data/16-degree-four-ia-a4-global_gap3_coreE_batch2_receipt.json                        source 16, Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/global_gap3_coreE_batch2_receipt.json`
data/16-degree-four-ia-a4-global_gap3_coreE_batch3_receipt.json                        source 16 (archive 17), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/global_gap3_coreE_batch3_receipt.json`
data/16-degree-four-ia-a4-global_gap3_templates5_12_receipt.json                       source 16 (archive 18), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/global_gap3_templates5_12_receipt.json`
data/16-degree-four-ia-a4-incremental_progress.json                                    source 16 (archive 17), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/incremental_progress.json`
data/16-degree-four-ia-a4-kernel_audit.json                                            source 16 (archive 19), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/kernel_audit.json`
data/16-degree-four-ia-a4-medium_checkpoint1_batch_audit.json                          source 16 (archive 19), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/medium_checkpoint1_batch_audit.json`
data/16-degree-four-ia-a4-medium_checkpoint2_batch_audit.json                          source 16 (archive 17), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/medium_checkpoint2_batch_audit.json`
data/16-degree-four-ia-a4-ordinary_global_gap_approvals.json                           source 16 (archive 17), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/ordinary_global_gap_approvals.json`
data/16-degree-four-ia-a4-package_fast_replay_71_coverage.json                         source 16, Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/package_fast_replay_71_coverage.json`
data/16-degree-four-ia-a4-package_fast_replay_71_verification.json                     source 16 (archive 17), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/package_fast_replay_71_verification.json`
data/16-degree-four-ia-a4-package_review_snapshot_path.txt                             source 16 (archive 19), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/package_review_snapshot_path.txt`
data/16-degree-four-ia-a4-package_wrapper_audit_71.json                                source 16 (archive 17), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/package_wrapper_audit_71.json`
data/16-degree-four-ia-a4-package_wrapper_hardening_audit.json                         source 16, Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/package_wrapper_hardening_audit.json`
data/16-degree-four-ia-a4-preparation.json                                             source 16 (archive 18), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/preparation.json`
data/16-degree-four-ia-a4-small_faces_incremental_audit.json                           source 16 (archive 17), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/small_faces_incremental_audit.json`
data/16-degree-four-ia-a4-small_faces_mapping_audit.json                               source 16 (archive 19), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/small_faces_mapping_audit.json`
data/16-degree-four-ia-a4-small_generic_regression_batch_audit.json                    source 16 (archive 18), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/small_generic_regression_batch_audit.json`
data/16-degree-four-ia-a4-template9_core_correction_audit.json                         source 16 (archive 19), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/four-attachment/template9_core_correction_audit.json`
data/16-degree-four-ia-certificate_audit.json                                          source 16 (archive 17), Part I: `reproducibility/sources/preorder-gamma-degree4-independent-audit/certificate_audit.json`
data/16-degree-four-provenance-sextic_gmp_26_weighted.log                              source 16, Part I: `reproducibility/provenance/global_integer_sextic_shifted_gmp_26_weighted.log`
data/16-degree-four-provenance-template26_certificate.json                             source 16 (archive 18), Part I: `reproducibility/provenance/template26_certificate.json`
data/20-role-cover-PACKAGE_VALIDATION.json                                             source 20, Part II: `PACKAGE_VALIDATION.json`
data/20-role-cover-final-audit-independent_verification.json                           source 20, Part II: `final-audit/independent_verification.json`
data/20-role-cover-final-audit-review_receipt.json                                     source 20, Part II: `final-audit/review_receipt.json`
data/20-role-cover-proofs-ia-balanced_real_rootedness_audit_receipt.json               source 20, Part II: `proofs/independent-audit/balanced_real_rootedness_audit_receipt.json`
data/20-role-cover-proofs-ia-check_disjoint_monomer.log                                source 20, Part II: `proofs/independent-audit/check_disjoint_monomer.log`
data/20-role-cover-proofs-ia-check_full_monomer.log                                    source 20, Part II: `proofs/independent-audit/check_full_monomer.log`
data/20-role-cover-proofs-ia-check_missing_edge_monomer.log                            source 20, Part II: `proofs/independent-audit/check_missing_edge_monomer.log`
data/20-role-cover-proofs-ia-check_star_monomer.log                                    source 20, Part II: `proofs/independent-audit/check_star_monomer.log`
data/20-role-cover-proofs-ic-ia-check_disjoint_rayleigh_aggregate.log                  source 20, Part II: `proofs/incomplete-core/independent-audit/check_disjoint_rayleigh_aggregate.log`
data/20-role-cover-proofs-ic-ia-check_rayleigh_aggregate.log                           source 20, Part II: `proofs/incomplete-core/independent-audit/check_rayleigh_aggregate.log`
data/20-role-cover-proofs-ic-ia-disjoint_core_edges_audit_receipt.json                 source 20, Part II: `proofs/incomplete-core/independent-audit/disjoint_core_edges_audit_receipt.json`
data/20-role-cover-proofs-ic-ia-one_missing_edge_audit_receipt.json                    source 20, Part II: `proofs/incomplete-core/independent-audit/one_missing_edge_audit_receipt.json`
data/20-role-cover-proofs-ic-ia-star_core_audit_receipt.json                           source 20, Part II: `proofs/incomplete-core/independent-audit/star_core_audit_receipt.json`
data/20-role-cover-proofs-ic-ia-two_by_two_role_cover_audit_receipt.json               source 20, Part II: `proofs/incomplete-core/independent-audit/two_by_two_role_cover_audit_receipt.json`
data/20-role-cover-verification-receipt.json                                           source 20, Part II: `verification-receipt.json`
data/22-independent-role-audit-approved-pure-role-replay.json                          source 22, Part II: `audit/approved-pure-role-replay.json`
data/22-independent-role-audit-global-mathematical-approval.json                       source 22, Part II: `audit/global-mathematical-approval.json`
data/22-independent-role-audit-math-approval.json                                      source 22, Part II: `audit/math-approval.json`
data/22-independent-role-audit-packager-initial-replay.json                            source 22, Part II: `audit/packager-initial-replay.json`
data/22-independent-role-audit-release-status-text-delta.json                          source 22, Part II: `audit/release-status-text-delta.json`
data/22-independent-role-checker-role-degree-three-audit-package.zip                   source 22, Part II: `checker/role-degree-three-audit-package.zip`
data/22-independent-role-dependency-pins.json                                          source 22, Part II: `dependency-pins.json`
data/22-independent-role-proofs-complete-role-ledger.json                              source 22, Part II: `proofs/complete-role-ledger.json`
data/22-independent-role-proofs-final-rayleigh-README.txt                              source 22, Part II: `proofs/final-rayleigh/README.txt`
data/22-independent-role-proofs-final-rayleigh-explicit-rational-squares.txt           source 22, Part II: `proofs/final-rayleigh/explicit-rational-squares.txt`
data/22-independent-role-proofs-final-rayleigh-side1565_rayleigh_0_9_certificate.json  source 22, Part II: `proofs/final-rayleigh/side1565_rayleigh_0_9_certificate.json`
data/22-independent-role-qa-visual-qa.json                                             source 22, Part II: `qa/visual-qa.json`
data/23-template26-article-visual-qa.json                                              source 23, Part I: `article/visual-qa.json`
data/23-template26-audits-integration_approval.json                                    source 23, Part I: `audits/integration_approval.json`
data/23-template26-sources-ia-st26-deletion_mixture_algebra_receipt.json               source 23, Part I: `sources/preorder-gamma-degree4-independent-audit/structural-template26/deletion_mixture_algebra_receipt.json`
data/23-template26-sources-ia-st26-deletion_mixture_approval_receipt.json              source 23, Part I: `sources/preorder-gamma-degree4-independent-audit/structural-template26/deletion_mixture_approval_receipt.json`
data/23-template26-sources-ia-st26-template26_assembly_algebra_receipt.json            source 23, Part I: `sources/preorder-gamma-degree4-independent-audit/structural-template26/template26_assembly_algebra_receipt.json`
data/23-template26-sources-ia-st26-template26_smaller_proof_approval_receipt.json      source 23, Part I: `sources/preorder-gamma-degree4-independent-audit/structural-template26/template26_smaller_proof_approval_receipt.json`
data/23-template26-sources-st26-pc-distinct_deletion_cross_certificates.json           source 23, Part I: `sources/preorder-gamma-degree4/structural-template26/pair-compatibility/distinct_deletion_cross_certificates.json`
data/23-template26-sources-weighted-vertex-seven-ia-approval_receipt.json              source 23, Part I: `sources/weighted-vertex-seven-independent-audit/approval_receipt.json`
data/25-degree-three-code-a1-audit_pairs.csv                                           source 25, Part I: `code/one-attachment/audit_pairs.csv`
data/25-degree-three-code-a1-quadratic_certificates.csv                                source 25, Part I: `code/one-attachment/quadratic_certificates.csv`
data/25-degree-three-code-a1-verification.json                                         source 25, Part I: `code/one-attachment/verification.json`
data/25-degree-three-code-a2-classification.json                                       source 25, Part I: `code/two-attachment/classification.json`
data/25-degree-three-code-a2-gap2_certificates.json                                    source 25, Part I: `code/two-attachment/gap2_certificates.json`
data/25-degree-three-code-a2-independent_audit.json                                    source 25, Part I: `code/two-attachment/independent_audit.json`
data/25-degree-three-code-a2-independent_verification.json                             source 25, Part I: `code/two-attachment/independent_verification.json`
data/25-degree-three-code-a2-templates.json                                            source 25, Part I: `code/two-attachment/templates.json`
data/25-degree-three-code-core_certificates.json                                       source 25, Part I: `code/core_certificates.json`
data/25-degree-three-code-cover3_sdp_4.json                                            source 25, Part I: `code/cover3_sdp_4.json`
data/25-degree-three-code-cover3_sdp_7_complete.json                                   source 25, Part I: `code/cover3_sdp_7_complete.json`
data/25-degree-three-code-cover3_seventeen_templates.json                              source 25, Part I: `code/cover3_seventeen_templates.json`
data/25-degree-three-code-cover3_sos_12.json                                           source 25, Part I: `code/cover3_sos_12.json`
data/25-degree-three-code-cover3_sos_14.json                                           source 25, Part I: `code/cover3_sos_14.json`
data/25-degree-three-code-cover3_sos_2.json                                            source 25, Part I: `code/cover3_sos_2.json`
data/25-degree-three-code-cover3_sos_4.json                                            source 25, Part I: `code/cover3_sos_4.json`
data/25-degree-three-code-cover3_sos_5.json                                            source 25, Part I: `code/cover3_sos_5.json`
data/25-degree-three-code-cover3_sos_6.json                                            source 25, Part I: `code/cover3_sos_6.json`
data/25-degree-three-code-cover3_sos_7.json                                            source 25, Part I: `code/cover3_sos_7.json`
data/25-degree-three-code-cover3_sos_8.json                                            source 25, Part I: `code/cover3_sos_8.json`
data/25-degree-three-code-layered_certificates.json                                    source 25, Part I: `code/layered_certificates.json`
data/25-degree-three-code-minimum-a1_min_size_pairs.csv                                source 25, Part I: `code/minimum/a1_min_size_pairs.csv`
data/25-degree-three-code-minimum-a2_minimum_scan.json                                 source 25, Part I: `code/minimum/a2_minimum_scan.json`
data/25-degree-three-code-minimum-direct_support_verification.json                     source 25, Part I: `code/minimum/direct_support_verification.json`
data/25-degree-three-code-minimum-ia-receipt.json                                      source 25, Part I: `code/minimum/independent-audit/receipt.json`
data/25-degree-three-code-minimum-minimum_scan.json                                    source 25, Part I: `code/minimum/minimum_scan.json`
data/25-degree-three-code-small-check-gamma_histogram.csv                              source 25, Part I: `code/small-check/gamma_histogram.csv`
data/25-degree-three-code-small-check-gamma_representatives.csv                        source 25, Part I: `code/small-check/gamma_representatives.csv`
data/25-degree-three-code-small-check-independent_verification.json                    source 25, Part I: `code/small-check/independent_verification.json`
data/25-degree-three-code-small-check-results.txt                                      source 25, Part I: `code/small-check/results.txt`
data/25-degree-three-code-small-check-results8.txt                                     source 25, Part I: `code/small-check/results8.txt`
data/25-degree-three-receipts-a3_audit_existing_verifiers.log                          source 25, Part I: `receipts/a3_audit_existing_verifiers.log`
data/25-degree-three-receipts-a3_audit_independent.log                                 source 25, Part I: `receipts/a3_audit_independent.log`
data/25-degree-three-receipts-audit-cover-three.log                                    source 25, Part I: `receipts/audit-cover-three.log`
data/25-degree-three-receipts-audit-minimum-independent.log                            source 25, Part I: `receipts/audit-minimum-independent.log`
data/25-degree-three-receipts-audit-one.log                                            source 25, Part I: `receipts/audit-one.log`
data/25-degree-three-receipts-audit-two.log                                            source 25, Part I: `receipts/audit-two.log`
data/25-degree-three-receipts-compile-minimum-core.log                                 source 25, Part I: `receipts/compile-minimum-core.log`
data/25-degree-three-receipts-compile-one-independent.log                              source 25, Part I: `receipts/compile-one-independent.log`
data/25-degree-three-receipts-compile-one.log                                          source 25, Part I: `receipts/compile-one.log`
data/25-degree-three-receipts-compile-small.log                                        source 25, Part I: `receipts/compile-small.log`
data/25-degree-three-receipts-deliverable_validation.json                              source 25, Part I: `receipts/deliverable_validation.json`
data/25-degree-three-receipts-enumerate-minimum-core.log                               source 25, Part I: `receipts/enumerate-minimum-core.log`
data/25-degree-three-receipts-enumerate-one.log                                        source 25, Part I: `receipts/enumerate-one.log`
data/25-degree-three-receipts-enumerate-small.log                                      source 25, Part I: `receipts/enumerate-small.log`
data/25-degree-three-receipts-one-attachment-audit_counts.log                          source 25, Part I: `receipts/one-attachment-audit_counts.log`
data/25-degree-three-receipts-scan-minimum-one-three.log                               source 25, Part I: `receipts/scan-minimum-one-three.log`
data/25-degree-three-receipts-scan-minimum-two.log                                     source 25, Part I: `receipts/scan-minimum-two.log`
data/25-degree-three-receipts-two-attachment-gap2_verification.log                     source 25, Part I: `receipts/two-attachment-gap2_verification.log`
data/25-degree-three-receipts-two-attachment-independent_audit.log                     source 25, Part I: `receipts/two-attachment-independent_audit.log`
data/25-degree-three-receipts-verification_summary.json                                source 25, Part I: `receipts/verification_summary.json`
data/25-degree-three-receipts-verify-cover-compact.log                                 source 25, Part I: `receipts/verify-cover-compact.log`
data/25-degree-three-receipts-verify-cover-general-squares.log                         source 25, Part I: `receipts/verify-cover-general-squares.log`
data/25-degree-three-receipts-verify-cover-squares.log                                 source 25, Part I: `receipts/verify-cover-squares.log`
data/25-degree-three-receipts-verify-fifteen-supports.log                              source 25, Part I: `receipts/verify-fifteen-supports.log`
data/25-degree-three-receipts-verify-one.log                                           source 25, Part I: `receipts/verify-one.log`
data/25-degree-three-receipts-verify-ordinal-core.log                                  source 25, Part I: `receipts/verify-ordinal-core.log`
data/25-degree-three-receipts-verify-ordinal-layers.log                                source 25, Part I: `receipts/verify-ordinal-layers.log`
data/25-degree-three-receipts-verify-small.log                                         source 25, Part I: `receipts/verify-small.log`
data/25-degree-three-receipts-verify-two-hall.log                                      source 25, Part I: `receipts/verify-two-hall.log`
data/25-degree-three-receipts-verify-two.log                                           source 25, Part I: `receipts/verify-two.log`
data/34-five-core-audits-article-certificate-approval.json                             source 34, Part III: `audits/article-certificate-approval.json`
data/34-five-core-audits-independent-certificate-receipt.json                          source 34, Part III: `audits/independent-certificate-receipt.json`
data/34-five-core-audits-independent-counterexample-review.json                        source 34, Part III: `audits/independent-counterexample-review.json`
data/34-five-core-audits-ordinary-and-scope-approval.json                              source 34, Part III: `audits/ordinary-and-scope-approval.json`
data/34-five-core-audits-primary-literature-check.json                                 source 34, Part III: `audits/primary-literature-check.json`
data/34-five-core-audits-strengthening-counterexample-receipt.json                     source 34, Part III: `audits/strengthening-counterexample-receipt.json`
data/34-five-core-certificate-data.tar.xz                                              source 34, Part III: derived container of delivered `certificate-data/` (9,610 files, byte-identical members; see below)
data/34-five-core-discovery-cores.txt                                                  source 34, Part III: `discovery/cores.txt`
data/34-five-core-qa-visual-review.json                                                source 34, Part III: `qa/visual-review.json`
```

## Labels

Every label carries the prefix `pgr:`: `pgr:sec:…`, `pgr:def:…`,
`pgr:lem:…`, `pgr:thm:…`, `pgr:eq:…` for the common material of Section 1
and Appendix A, and per Part `pgr:u:` (I), `pgr:r:` (II), `pgr:s:` (III)
followed by a source infix and the source's own label: `d3` (25), `d4`
(16), `t26` (23), `rc` (20), `tc` (12), `pc` (11), `ps` (15), `ir` (22),
`lg` (14), `ad` (10), `fc` (34), `fb` (06). For example source 22's
`thm:main` is `pgr:r:ir:thm:main`. The base article (source 16) had 26
labels as staged; the report has 85 labels. Labels of source passages
that are printed once elsewhere or replaced by pointers (the degree lemma
and the first inequality of several sources, source 16's Section 3 and
Appendix A, the duplicated three-squares identity and moment envelope, the
last-gap proofs of sources 10 and 34, source 34's appendix, and the proof of
source 22's one-tail criterion) are not defined; references to them point
to the printed copy.

## What the report claims

### Part I — unit activities on finite preorders through actual degree four

Claimed (labels in parentheses):

- **Degree at most three** (source 25, `pgr:u:d3:thm:main`; computer-assisted):
  every finite preorder whose gamma polynomial has actual degree at most
  three is rank-ULC: `γ1² ≥ 3γ2` and `γ2² ≥ 3γ1γ3` in degree three,
  `γ1² ≥ 4γ2` in degree two. Proof: Gallai–Edmonds reduction to four
  attachment branches; a finite real-rootedness lemma through seven
  vertices (`pgr:u:d3:lem:small`, reproducing a published computation);
  2,050 one-attachment quadratic certificates; 1,084 two-attachment
  templates (448 families, 994 face certificates); seventeen
  three-attachment templates, class 0 by the Röhrle–Ulirsch theorem.
- **Bounded-core normal form at every degree** (`pgr:u:d3:thm:normalform`,
  ordinary): `|K| ≤ 3r − 2a`, `ν(G[K∖A]) = r − a`, at most `2^a − 1`
  exterior types with one orientation per attachment, and the finite
  binomial kernel expansion.
- **Minimum order of a nonreal cubic** (`pgr:u:d3:thm:minimum`,
  computer-assisted bounded scan): every preorder of actual degree three on
  at most fourteen vertices has a real-rooted gamma polynomial; at fifteen
  vertices exactly two isomorphism classes fail (the height-two poset with
  `Γ = 1 + 24z + 162z² + 208z³`, discriminant −2592, and its dual).
- **Ordinal sums** (`pgr:u:d3:thm:ordinal`): `P ⊕ A_m ⊕ Q` with
  `|P| + |Q| = 3`, `m ≥ 3`, and every ordinal sum of antichains of actual
  degree three, have three distinct negative roots (two specializations are
  in the literature, credited there).
- **Degree four** (source 16, `pgr:u:d4:thm:middle`; computer-assisted):
  every finite preorder whose *unweighted* support polynomial has actual
  degree four satisfies `3γ1² ≥ 8γ2`, `4γ2² ≥ 9γ1γ3`, `3γ3² ≥ 8γ2γ4`.
  Proof: the normal form at `r = 4`, finite branches `a = 0..3` by exact
  certificates, and 76 canonical four-attachment templates covered by 50
  global binomial-square identities (15,408 square orbits) and ordinary
  theorems; 39,367 face tasks discharged.
- Ordinary tools of source 16: the **exterior-only Lorentzian
  construction** (`pgr:u:d4:thm:exterior`, normalized by the cover order
  `r`, not the actual degree) and the **outward-star last gap**
  (`pgr:u:d4:thm:star`, unit activities).
- **Template 26, second route** (source 23, `pgr:u:t26:thm:main`;
  certificate-assisted): `3γ3² ≥ 8γ2γ4` for every integer population of
  template 26, by `Γ = Q⁺ + tR`, a deletion-mixture lemma with ten exact
  quartic identities (196 squares, 846 remainder terms), the vertex-weighted
  degree-three theorem (Part II, `pgr:r:ir:cor:vertex`) and Wagner's
  rank-three Rayleigh theorem.

Not claimed (Part I): any weighted (non-unit) statement in degree four;
real-rootedness (it fails in degree three, and source 16 exhibits a 29-vertex
nonreal quartic `1 + 40t + 510t² + 2380t³ + 2704t⁴`); degree five or more;
that the first inequality or the degree-two case is new (they are
`preorder-root-polytopes`' `mr:thm:first` and `mr:cor:preorderfirst`); that
the exterior theorem gives actual-degree normalization below full cover
rank; a certificate-free proof of template 26; a minimal-size statement
beyond degree three; a Lean formalization or a global priority claim.
Source 25's finite lemma through seven vertices reproduces a published
computation and is not claimed as a new size range.

### Part II

Written in the next step of this intake.

### Part III

Written in the next step of this intake.

## Research questions of `preorder-root-polytopes`

| Question | Where | Answered by | How |
|---|---|---|---|
| Research question 96, `mr:q:gamma` | Part XII | sources 25, 16 (unit activities), 22 (independent activities); 11, 15, 20 and Part III in families | yes for unit activities through actual degree four and for independent role activities through degree three; open from degree five (unit) and degree four (weighted) in general; "a first unproved target is degree three" is proved |
| "Gamma log-concavity beyond height two" (the paragraphs of its sources 06 and 09, sections `lor:sec:oldquestions` and `mat:sec:oldquestions`) | — | same | answered for unit activities through actual degree four: no counterexample of degree at most four exists, so a minimal counterexample, if any, has degree at least five; real-rootedness does fail, and source 25 determines its least order in degree three (fifteen vertices) |
| `mr:q:certificates` | Part XII | sources 16, 23 | bears on it: binomial-square certificates at scale (source 16), a smaller route for the largest one (source 23) |
| `mrn:w:sb:thm:main` of `matching-rank-normalization` | its Part I | source 20 | generalized to directed relations with overlapping role covers |
| source 15's open question (two tail and three head roles) | Part II | — | stays open; the case of at most two head roles is source 20's theorem, and the case where the tail set lies inside the head set is source 11's corollary |

The reciprocal notes in `preorder-root-polytopes` and
`matching-rank-normalization` are written in separate commits.

## Relation to neighbouring reports and formal projects

- [`preorder-root-polytopes`](../../enumerative-combinatorics/preorder-root-polytopes)
  defines the preorder gamma polynomial (`gam:thm:main`), proves the first
  inequality for directed relations (`mr:thm:first`), the degree-two case
  (`mr:cor:preorderfirst`) and bipartite rank three (`mr:thm:rankthree`,
  `lc:cor:rankthree`), and asks the question answered here. Its theorems are
  cited by label; sources 16 and 25 cite it at `d5e863bba`.
- [`matching-rank-normalization`](../matching-rank-normalization) treats the
  bipartite matching-support polynomial normalized by the matching number.
  Its rank-five corollary (`mrn:w:rf:cor:rankfive`) covers the bipartite
  components of source 16's reduction (source 16 cites a rank-four package,
  batch-73 manuscript 26, which this intake prints there as source 77,
  `mrn:v:rf4:thm:main`); its two by two stability theorem
  (`mrn:w:sb:thm:main`, with the real-rootedness route
  `mrn:v:rf4:thm:mixed`) is the bipartite, disjoint-cover case of source
  20's theorem.
- No formal project is continued. The collection lives under
  `SetTheory/Cardinals/` beside Lean developments, but placement there
  confers no formal status: no statement of this report is formalized in
  Lean or Rocq, and no Lean declaration corresponds to any of its results.

## Build

```
cd <scratch copy of this directory>
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX with the standard `amsmath`, `amssymb`, `amsthm`, `mathtools`,
`lmodern`, `microtype`, `geometry`, `booktabs`, `longtable`, `array`,
`enumitem`, `fancyhdr`, `xurl` and `hyperref` packages; three passes. The
committed PDF was built this way with MiKTeX: 40 pages, no errors, no
undefined references or citations, no multiply defined labels, no duplicate
destinations, no overfull boxes. Build in a scratch copy; do not commit the
auxiliary files.

## Rerun instructions, reconstruction and discrepancies

Rerun instructions, how to retrieve or rebuild every delivered file that is not
shipped, the licence notice for third-party data, and the list of delivery names
and discrepancies are added in the last step of this intake (4/4). Until then:
every delivered file that is not shipped is in the arrival commit `f8c3a392a`
(`git show f8c3a392a:docs/incoming/<archive>.zip > <archive>.zip`, then unzip),
and no delivered driver runs inside this directory.
