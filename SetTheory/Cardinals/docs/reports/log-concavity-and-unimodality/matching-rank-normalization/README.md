# Normalization by the Matching Number for Weighted Matching-Support Polynomials

**Small ranks, unit and one-shore counterexamples, rank six, and eventual scaling**

This is a research report dated 1 October 2026, merged from the 27
manuscripts of batch 72, cluster C, of ProveIt's incoming-report intake:
26 archives that arrived in `1512ef835` and one manuscript (08s,
*Top Conditional Gaps and the Rank Seven Reduction*) that was delivered only
inside archive 08. They study whether the bipartite matching-support
polynomial `p_G(t)` (each pair of endpoint sets of a matching counted once,
weighted by its vertex activities) is ultra-log-concave of the order of its
matching number `nu(G)`, the question of Parts XI–XIII of
[`preorder-root-polytopes`](../../enumerative-combinatorics/preorder-root-polytopes).
A 28th archive of the cluster (78) is byte-identical to the batch-71 archive
printed there as Part XIII and is not a source. All sources were placed in
`8bb543f0f`. Author line of every source: "Research note prepared for
Vladimir Reshetnikov with OpenAI", except source 72: "AI-assisted
mathematical research".

The report is written in four commits, one per Part. **At this state Part
I is printed (sources 74, 72, 76, 75); Parts II–IV follow.** The support
files of all 27 sources are already in the directory (placed in `8bb543f0f`).

| Source | Batch-72 manuscript | Archive (`docs/incoming/…` at `1512ef835`) | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 74 | 74 (base) | `ProveIt_Weighted_Rank_Five_and_Two_Shore_Covers.zip` (*Weighted Rank Five and Covers with a Two Vertex Shore*, 16 pp.) | `1b3960d8a`, `a866ff9a2` | `8bb543f0f` | Part I, Sections 2–13 |
| 72 | 72 | `strictness_equality_package.zip` (*Strictness and equality for weighted matching support polynomials*, 8 pp.; indexed in cluster E, handed to C) | none | `8bb543f0f` | Part I, Section 14 |
| 76 | 76 | `ProveIt_Weighted_Rank_Four_Stability.zip` (*Stability of Two by Two Covers and Weighted Rank Four*, 8 pp.) | `1b3960d8a`, `a866ff9a2` | `8bb543f0f` | Part I, Section 15 |
| 75 | 75 | `ProveIt_Sharp_Full_Hall_Classification.zip` (*A Sharp Weighted Classification of Full Hall Bottleneck Graphs*, 9 pp.) | `4a3b6991d` | `8bb543f0f` | Part I, Section 16 |
| 71 | 71 | `ProveIt_Unit_Weight_Rank_Normalization_Counterexample.zip` (*Unit Weight Failure of Matching Rank Normalization*) | `a866ff9a2` | `8bb543f0f` | Part II (not yet written) |
| 73 | 73 | `ProveIt_One_Shore_Counterexamples.zip` (*One Shore Activities Can Destroy Matching Rank ULC*) | `4a3b6991d` | `8bb543f0f` | Part II (not yet written) |
| 55 | 55 | `ProveIt_Sharp_Rank_38_Hall_Endpoint.zip` (*A Sharp Rank 38 Boundary for the Last Hall Inequality*) | none | `8bb543f0f` | Part II (not yet written) |
| 47 | 47 | `ProveIt_Sharp_Rank_38_Full_Hall_ULC.zip` (*The Sharp Rank 38 ULC Boundary for Full Hall Graphs*) | none | `8bb543f0f` | Part II (not yet written) |
| 51 | 51 | `ProveIt_Last_Hall_Gap_Separation.zip` (*The Last Hall Gap Does Not Control Ultra Log Concavity*) | none | `8bb543f0f` | Part II (not yet written) |
| 60 | 60 | `ProveIt_Rank_Two_Matrix_Blocks_and_Conditioning.zip` (*Rank Two Matrix Blocks and Exterior Conditioning*) | none | `8bb543f0f` | Part III (not yet written) |
| 10 | 10 | `ProveIt_Three_Vertex_Marginals_and_Star_Cores.zip` (*Lorentzian Marginals on Three Vertices*) | none | `8bb543f0f` | Part III (not yet written) |
| 23 | 23 | `ProveIt_Rooted_Hall_Sectors_and_Cubic_Obstruction.zip` (*Rooted Lorentzian Hall Sectors and an Unrooted Cubic Obstruction*) | none | `8bb543f0f` | Part III (not yet written) |
| 13 | 13 | `ProveIt_Rank_Six_Finite_Last_Gap.zip` (*The Last Newton Inequality at Rank Six*) | none | `8bb543f0f` | Part III (not yet written) |
| 05 | 05 | `ProveIt_Rank_Six_Second_Newton_Inequality.zip` (*The Second Newton Inequality at Rank Six*) | none | `8bb543f0f` | Part III (not yet written) |
| 69 | 69 | `ProveIt_Rank_Six_Common_Exterior_Theorem.zip` (*Rank Six With Common Exterior Neighborhoods*) | none | `8bb543f0f` | Part III (not yet written) |
| 63 | 63 | `ProveIt_Rank_Six_Nested_and_Conditional_Results.zip` (*Nested Rank Six Families and Conditional Barriers*) | none | `8bb543f0f` | Part III (not yet written) |
| 08s | inside 08 | `ProveIt_Eventual_One_Shore_Scaling_Through_Rank_Seven.zip`, nested `Rank7_Eventual_Report/companion/structural_companion_source.zip` (*Top Conditional Gaps and the Rank Seven Reduction*) | none | `8bb543f0f` | Part IV (not yet written) |
| 21 | 21 | `ProveIt_Rank_Six_Conditioning_for_Every_Core.zip` (*Rank Six Conditioning for Every Core*) | none | `8bb543f0f` | Part IV (not yet written) |
| 43 | 43 | `ProveIt_Rank_Six_Complete_Core_Cubic.zip` (*A Rank Six Cubic Sector with a Complete Core*) | none | `8bb543f0f` | Part IV (not yet written) |
| 38 | 38 | `ProveIt_Rank_Six_Matching_Hole_Cores.zip` (*Rank Six Cubic Sectors for Matching Hole Cores*) | none | `8bb543f0f` | Part IV (not yet written) |
| 35 | 35 | `ProveIt_Rank_Six_Two_Complete_Rows.zip` (*Rank Six Cores with Two Complete Rows*) | none | `8bb543f0f` | Part IV (not yet written) |
| 32 | 32 | `ProveIt_Rank_Six_Two_Complete_Columns.zip` (*Rank Six Cores with Two Complete Columns*) | none | `8bb543f0f` | Part IV (not yet written) |
| 29 | 29 | `ProveIt_Rank_Six_At_Least_Six_Core_Edges.zip` (*Rank Six Cores with at Least Six Edges*) | none | `8bb543f0f` | Part IV (not yet written) |
| 08 | 08 | `ProveIt_Eventual_One_Shore_Scaling_Through_Rank_Seven.zip` (*Eventual One Shore Scaling Through Rank Seven*) | none | `8bb543f0f` | Part IV (not yet written) |
| 03 | 03 | `ProveIt_Eventual_Five_Plus_Three_Covers.zip` (*Eventual Scaling for Five Plus Three Covers*) | none | `8bb543f0f` | Part IV (not yet written) |
| 02 | 02 | `ProveIt_Four_Plus_Four_Top_Gap.zip` (*The Top Conditional Gap for Four Plus Four Covers*) | none | `8bb543f0f` | Part IV (not yet written) |
| 01 | 01 | `ProveIt_Eventual_One_Shore_Scaling_Through_Rank_Eight.zip` (*Eventual One Shore Scaling Through Rank Eight*) | none | `8bb543f0f` | Part IV (not yet written) |

Pins are the commits the manuscripts themselves cite: `1b3960d8a` is
`1b3960d8acdabd983147b7c609bd9dfb2d67a0a0`, the batch-70 archive of the
manuscript now printed as Part XII of `preorder-root-polytopes`;
`a866ff9a2` is the batch-68 archive of the Hall-bottleneck manuscript, now
its Part XI; `4a3b6991d` is `4a3b6991d0cc12cc09b884e22728e2128a54c6e3`, the
commit that wrote Part XI. Sources with no pin cite their siblings by
archive name only. Every manuscript is dated 1 October 2026.

**Status: AI-assisted, unrefereed, not formalized.** The sources give
ordinary mathematical proofs supported by exact finite checks. Nothing here
is formalized in Lean or Rocq, and no Lean or Rocq development in the
repository states or uses these results.

## Files

```
article.tex                                                              the report, standalone LaTeX with an internal bibliography (pdfLaTeX)
article.pdf                                                              the compiled report, 49 pages, A4
README.md                                                                this guide
05-second-newton-VERIFICATION.md                                         source 05, Part III (Part III not yet written): delivered `VERIFICATION.md`
10-three-vertex-VERIFICATION.md                                          source 10, Part III (Part III not yet written): delivered `VERIFICATION.md`
13-last-newton-VERIFICATION.md                                           source 13, Part III (Part III not yet written): delivered `VERIFICATION.md`
21-every-core-VERIFICATION.md                                            source 21, Part IV (Part IV not yet written): delivered `VERIFICATION.md`
23-rooted-sectors-VERIFICATION.md                                        source 23, Part III (Part III not yet written): delivered `VERIFICATION.md`
29-six-edges-VERIFICATION.md                                             source 29, Part IV (Part IV not yet written): delivered `VERIFICATION.md`
32-two-columns-VERIFICATION.md                                           source 32, Part IV (Part IV not yet written): delivered `VERIFICATION.md`
35-two-rows-VERIFICATION.md                                              source 35, Part IV (Part IV not yet written): delivered `VERIFICATION.md`
38-matching-hole-VERIFICATION.md                                         source 38, Part IV (Part IV not yet written): delivered `Rank_Six_Matching_Hole_Cores/VERIFICATION.md`
43-complete-core-VERIFICATION.md                                         source 43, Part IV (Part IV not yet written): delivered `Rank_Six_Complete_Core_Cubic/VERIFICATION.md`
47-rank38-ulc-VERIFICATION.md                                            source 47, Part II (Part II not yet written): delivered `Sharp_Rank_38_Full_Hall_ULC/VERIFICATION.md`
51-last-gap-QA.md                                                        source 51, Part II (Part II not yet written): delivered `Last_Hall_Gap_Separation/QA.md`
55-rank38-endpoint-QA.md                                                 source 55, Part II (Part II not yet written): delivered `Sharp_Rank_38_Hall_Endpoint/QA.md`
71-unit-weight-PROOF_STATUS.md                                           source 71, Part II (Part II not yet written): delivered `ProveIt_Unit_Weight_Rank_Normalization_Counterexample/PROOF_STATUS.md`
71-unit-weight-SOURCES.md                                                source 71, Part II (Part II not yet written): delivered `ProveIt_Unit_Weight_Rank_Normalization_Counterexample/SOURCES.md`
72-strictness-SOURCES.md                                                 source 72, Part I: delivered `Strictness_Equality/SOURCES.md`
74-weighted-rank-five-PROOF_STATUS.md                                    source 74, Part I: delivered `ProveIt_Weighted_Rank_Five/PROOF_STATUS.md`
76-rank-four-PROOF_STATUS.md                                             source 76, Part I: delivered `ProveIt_Weighted_Rank_Four_Stability/PROOF_STATUS.md`
76-rank-four-SOURCES.md                                                  source 76, Part I: delivered `ProveIt_Weighted_Rank_Four_Stability/SOURCES.md`
code/01-rank-eight-independent-check_minor_supports.py                   source 01, Part IV (Part IV not yet written): delivered `code/independent/check_minor_supports.py`
code/01-rank-eight-independent-check_transition.py                       source 01, Part IV (Part IV not yet written): delivered `code/independent/check_transition.py`
code/01-rank-eight-independent-replay_hyperplane.py                      source 01, Part IV (Part IV not yet written): delivered `code/independent/replay_hyperplane.py`
code/01-rank-eight-primary-check_hyperplane_transition.py                source 01, Part IV (Part IV not yet written): delivered `code/primary/check_hyperplane_transition.py`
code/01-rank-eight-primary-support_counts.py                             source 01, Part IV (Part IV not yet written): delivered `code/primary/support_counts.py`
code/01-rank-eight-replay_all.py                                         source 01, Part IV (Part IV not yet written): delivered `code/replay_all.py`
code/02-four-plus-four-independent-replay.py                             source 02, Part IV (Part IV not yet written): delivered `code/independent/replay.py`
code/02-four-plus-four-independent-replay_coupled.py                     source 02, Part IV (Part IV not yet written): delivered `code/independent/replay_coupled.py`
code/02-four-plus-four-primary-check_generic_six_profiles.py             source 02, Part IV (Part IV not yet written): delivered `code/primary/check_generic_six_profiles.py`
code/02-four-plus-four-primary-check_top_coupled_five.py                 source 02, Part IV (Part IV not yet written): delivered `code/primary/check_top_coupled_five.py`
code/02-four-plus-four-primary-check_top_coupled_six.py                  source 02, Part IV (Part IV not yet written): delivered `code/primary/check_top_coupled_six.py`
code/02-four-plus-four-primary-support_counts.py                         source 02, Part IV (Part IV not yet written): delivered `code/primary/support_counts.py`
code/02-four-plus-four-primary-verify_real_counterexample.py             source 02, Part IV (Part IV not yet written): delivered `code/primary/verify_real_counterexample.py`
code/02-four-plus-four-replay_all.py                                     source 02, Part IV (Part IV not yet written): delivered `code/replay_all.py`
code/03-five-plus-three-check_four_quotient_unit.py                      source 03, Part IV (Part IV not yet written): delivered `code/check_four_quotient_unit.py`
code/03-five-plus-three-endpoint_profiles.py                             source 03, Part IV (Part IV not yet written): delivered `code/endpoint_profiles.py`
code/03-five-plus-three-replay_all.py                                    source 03, Part IV (Part IV not yet written): delivered `code/replay_all.py`
code/03-five-plus-three-verify_five_by_three.py                          source 03, Part IV (Part IV not yet written): delivered `code/verify_five_by_three.py`
code/03-five-plus-three-verify_plane_profiles.py                         source 03, Part IV (Part IV not yet written): delivered `code/verify_plane_profiles.py`
code/05-second-newton-build_core_schur_certificate.py                    source 05, Part III (Part III not yet written): delivered `verification/build_core_schur_certificate.py`
code/05-second-newton-check_R_determinants.py                            source 05, Part III (Part III not yet written): delivered `verification/check_R_determinants.py`
code/05-second-newton-check_core_endpoint_formulas.py                    source 05, Part III (Part III not yet written): delivered `verification/check_core_endpoint_formulas.py`
code/05-second-newton-check_fifth_truncation_barrier.py                  source 05, Part III (Part III not yet written): delivered `verification/check_fifth_truncation_barrier.py`
code/05-second-newton-check_zero_core_schur.py                           source 05, Part III (Part III not yet written): delivered `verification/check_zero_core_schur.py`
code/05-second-newton-independent-check_finite_compression.py            source 05, Part III (Part III not yet written): delivered `verification/independent/check_finite_compression.py`
code/05-second-newton-independent-check_relations.py                     source 05, Part III (Part III not yet written): delivered `verification/independent/check_relations.py`
code/05-second-newton-independent-finalize.py                            source 05, Part III (Part III not yet written): delivered `verification/independent/finalize.py`
code/05-second-newton-independent-reconstruct.py                         source 05, Part III (Part III not yet written): delivered `verification/independent/reconstruct.py`
code/05-second-newton-run_core_schur_profiles.py                         source 05, Part III (Part III not yet written): delivered `verification/run_core_schur_profiles.py`
code/05-second-newton-verify.py                                          source 05, Part III (Part III not yet written): delivered `verify.py`
code/08-rank-seven-endpoint_profiles.py                                  source 08, Part IV (Part IV not yet written): delivered `Rank7_Eventual_Report/code/endpoint_profiles.py`
code/08-rank-seven-replay_all.py                                         source 08, Part IV (Part IV not yet written): delivered `Rank7_Eventual_Report/code/replay_all.py`
code/08-rank-seven-top-gap-endpoint_profiles.py                          source 08s, Part IV (Part IV not yet written): delivered `Rank7_Top_Gap_Report/code/endpoint_profiles.py`
code/08-rank-seven-top-gap-replay_all.py                                 source 08s, Part IV (Part IV not yet written): delivered `Rank7_Top_Gap_Report/code/replay_all.py`
code/08-rank-seven-top-gap-supplement-search.py                          source 08s, Part IV (Part IV not yet written): delivered `Rank7_Top_Gap_Report/supplement/search.py`
code/08-rank-seven-top-gap-supplement-search_heavy_right.py              source 08s, Part IV (Part IV not yet written): delivered `Rank7_Top_Gap_Report/supplement/search_heavy_right.py`
code/08-rank-seven-top-gap-supplement-search_rayleigh_seed.py            source 08s, Part IV (Part IV not yet written): delivered `Rank7_Top_Gap_Report/supplement/search_rayleigh_seed.py`
code/08-rank-seven-top-gap-verify_barrier.py                             source 08s, Part IV (Part IV not yet written): delivered `Rank7_Top_Gap_Report/code/verify_barrier.py`
code/08-rank-seven-top-gap-verify_rayleigh_seed.py                       source 08s, Part IV (Part IV not yet written): delivered `Rank7_Top_Gap_Report/code/verify_rayleigh_seed.py`
code/08-rank-seven-verify_middle.py                                      source 08, Part IV (Part IV not yet written): delivered `Rank7_Eventual_Report/code/verify_middle.py`
code/10-three-vertex-check_supports.py                                   source 10, Part III (Part III not yet written): delivered `code/check_supports.py`
code/10-three-vertex-generate_determinant.py                             source 10, Part III (Part III not yet written): delivered `code/generate_determinant.py`
code/10-three-vertex-independent_replay.py                               source 10, Part III (Part III not yet written): delivered `code/independent_replay.py`
code/10-three-vertex-replay_all.py                                       source 10, Part III (Part III not yet written): delivered `code/replay_all.py`
code/13-last-newton-check_last_gap_quadratic.py                          source 13, Part III (Part III not yet written): delivered `code/check_last_gap_quadratic.py`
code/13-last-newton-generate_certificate.py                              source 13, Part III (Part III not yet written): delivered `code/generate_certificate.py`
code/13-last-newton-replay_all.py                                        source 13, Part III (Part III not yet written): delivered `code/replay_all.py`
code/13-last-newton-replay_certificate.py                                source 13, Part III (Part III not yet written): delivered `code/replay_certificate.py`
code/13-last-newton-verify_virtual_orbits.py                             source 13, Part III (Part III not yet written): delivered `code/verify_virtual_orbits.py`
code/21-every-core-check_weighted_planes.py                              source 21, Part IV (Part IV not yet written): delivered `code/check_weighted_planes.py`
code/21-every-core-replay_all.py                                         source 21, Part IV (Part IV not yet written): delivered `code/replay_all.py`
code/21-every-core-verify_incidence.py                                   source 21, Part IV (Part IV not yet written): delivered `code/verify_incidence.py`
code/23-rooted-sectors-independent_full_field.py                         source 23, Part III (Part III not yet written): delivered `code/independent_full_field.py`
code/23-rooted-sectors-support_helpers.py                                source 23, Part III (Part III not yet written): delivered `code/support_helpers.py`
code/23-rooted-sectors-verify_base_dynamic.py                            source 23, Part III (Part III not yet written): delivered `code/verify_base_dynamic.py`
code/23-rooted-sectors-verify_common_field.py                            source 23, Part III (Part III not yet written): delivered `code/verify_common_field.py`
code/23-rooted-sectors-verify_connected.py                               source 23, Part III (Part III not yet written): delivered `code/verify_connected.py`
code/23-rooted-sectors-verify_rooted_hessians.py                         source 23, Part III (Part III not yet written): delivered `code/verify_rooted_hessians.py`
code/29-six-edges-check_core_orbits.py                                   source 29, Part IV (Part IV not yet written): delivered `code/check_core_orbits.py`
code/29-six-edges-check_star_edge.py                                     source 29, Part IV (Part IV not yet written): delivered `code/check_star_edge.py`
code/29-six-edges-check_star_edge_transpose.py                           source 29, Part IV (Part IV not yet written): delivered `code/check_star_edge_transpose.py`
code/29-six-edges-check_triangular.py                                    source 29, Part IV (Part IV not yet written): delivered `code/check_triangular.py`
code/29-six-edges-independent_reconstruction.py                          source 29, Part IV (Part IV not yet written): delivered `code/independent_reconstruction.py`
code/29-six-edges-replay_all.py                                          source 29, Part IV (Part IV not yet written): delivered `code/replay_all.py`
code/32-two-columns-check_degree_one_counts.py                           source 32, Part IV (Part IV not yet written): delivered `code/check_degree_one_counts.py`
code/32-two-columns-check_flag_algebra.py                                source 32, Part IV (Part IV not yet written): delivered `code/check_flag_algebra.py`
code/32-two-columns-check_zero_column_counts.py                          source 32, Part IV (Part IV not yet written): delivered `code/check_zero_column_counts.py`
code/32-two-columns-independent_reconstruction.py                        source 32, Part IV (Part IV not yet written): delivered `code/independent_reconstruction.py`
code/32-two-columns-verify_degree_one_certificate.py                     source 32, Part IV (Part IV not yet written): delivered `code/verify_degree_one_certificate.py`
code/35-two-rows-check_degree_one_counts.py                              source 35, Part IV (Part IV not yet written): delivered `code/check_degree_one_counts.py`
code/35-two-rows-check_flag_algebra.py                                   source 35, Part IV (Part IV not yet written): delivered `code/check_flag_algebra.py`
code/35-two-rows-check_zero_row_counts.py                                source 35, Part IV (Part IV not yet written): delivered `code/check_zero_row_counts.py`
code/35-two-rows-verify_degree_one_certificate.py                        source 35, Part IV (Part IV not yet written): delivered `code/verify_degree_one_certificate.py`
code/38-matching-hole-verify_first_gap.py                                source 38, Part IV (Part IV not yet written): delivered `Rank_Six_Matching_Hole_Cores/code/verify_first_gap.py`
code/38-matching-hole-verify_support_counts.py                           source 38, Part IV (Part IV not yet written): delivered `Rank_Six_Matching_Hole_Cores/code/verify_support_counts.py`
code/43-complete-core-verify_complete_core.py                            source 43, Part IV (Part IV not yet written): delivered `Rank_Six_Complete_Core_Cubic/code/verify_complete_core.py`
code/47-rank38-ulc-check_population_identity.py                          source 47, Part II (Part II not yet written): delivered `Sharp_Rank_38_Full_Hall_ULC/code/check_population_identity.py`
code/47-rank38-ulc-check_support_identity.py                             source 47, Part II (Part II not yet written): delivered `Sharp_Rank_38_Full_Hall_ULC/code/check_support_identity.py`
code/47-rank38-ulc-compare_certificates.py                               source 47, Part II (Part II not yet written): delivered `Sharp_Rank_38_Full_Hall_ULC/code/compare_certificates.py`
code/47-rank38-ulc-difference_coeff.py                                   source 47, Part II (Part II not yet written): delivered `Sharp_Rank_38_Full_Hall_ULC/code/difference_coeff.py`
code/47-rank38-ulc-independent_replay.py                                 source 47, Part II (Part II not yet written): delivered `Sharp_Rank_38_Full_Hall_ULC/code/independent_replay.py`
code/47-rank38-ulc-population_coeff.py                                   source 47, Part II (Part II not yet written): delivered `Sharp_Rank_38_Full_Hall_ULC/code/population_coeff.py`
code/47-rank38-ulc-verify_all_populations.py                             source 47, Part II (Part II not yet written): delivered `Sharp_Rank_38_Full_Hall_ULC/code/verify_all_populations.py`
code/51-last-gap-verify_counterexample.py                                source 51, Part II (Part II not yet written): delivered `Last_Hall_Gap_Separation/verify_counterexample.py`
code/55-rank38-endpoint-verify_boundary.py                               source 55, Part II (Part II not yet written): delivered `Sharp_Rank_38_Hall_Endpoint/verify_boundary.py`
code/55-rank38-endpoint-verify_symbolic.py                               source 55, Part II (Part II not yet written): delivered `Sharp_Rank_38_Hall_Endpoint/verify_symbolic.py`
code/60-rank-two-blocks-check_eventual_scaling.py                        source 60, Part III (Part III not yet written): delivered `checks/check_eventual_scaling.py`
code/60-rank-two-blocks-check_kernel_compression.py                      source 60, Part III (Part III not yet written): delivered `checks/check_kernel_compression.py`
code/60-rank-two-blocks-check_matrix_lifts.py                            source 60, Part III (Part III not yet written): delivered `checks/check_matrix_lifts.py`
code/60-rank-two-blocks-check_rank_three_boundary.py                     source 60, Part III (Part III not yet written): delivered `checks/check_rank_three_boundary.py`
code/60-rank-two-blocks-check_reductions.py                              source 60, Part III (Part III not yet written): delivered `checks/check_reductions.py`
code/60-rank-two-blocks-run_all.py                                       source 60, Part III (Part III not yet written): delivered `checks/run_all.py`
code/63-nested-exterior-run_all.py                                       source 63, Part III (Part III not yet written): delivered `checks/run_all.py`
code/63-nested-exterior-verify_marginal_barrier.py                       source 63, Part III (Part III not yet written): delivered `checks/verify_marginal_barrier.py`
code/63-nested-exterior-verify_nested.py                                 source 63, Part III (Part III not yet written): delivered `checks/verify_nested.py`
code/63-nested-exterior-verify_sector_formulas.py                        source 63, Part III (Part III not yet written): delivered `checks/verify_sector_formulas.py`
code/63-nested-exterior-verify_small_supports.py                         source 63, Part III (Part III not yet written): delivered `checks/verify_small_supports.py`
code/63-nested-exterior-verify_two_core_sector.py                        source 63, Part III (Part III not yet written): delivered `checks/verify_two_core_sector.py`
code/69-common-exterior-run_all.py                                       source 69, Part III (Part III not yet written): delivered `checks/run_all.py`
code/69-common-exterior-verify_barrier.py                                source 69, Part III (Part III not yet written): delivered `checks/verify_barrier.py`
code/69-common-exterior-verify_certificate.py                            source 69, Part III (Part III not yet written): delivered `checks/verify_certificate.py`
code/71-unit-weight-Makefile                                             source 71, Part II (Part II not yet written): delivered `ProveIt_Unit_Weight_Rank_Normalization_Counterexample/Makefile`
code/71-unit-weight-verify.py                                            source 71, Part II (Part II not yet written): delivered `ProveIt_Unit_Weight_Rank_Normalization_Counterexample/code/verify.py`
code/71-unit-weight-verify_gadget_identity.py                            source 71, Part II (Part II not yet written): delivered `ProveIt_Unit_Weight_Rank_Normalization_Counterexample/code/verify_gadget_identity.py`
code/71-unit-weight-verify_unit_witness.py                               source 71, Part II (Part II not yet written): delivered `ProveIt_Unit_Weight_Rank_Normalization_Counterexample/code/verify_unit_witness.py`
code/72-strictness-build.sh                                              source 72, Part I: delivered `Strictness_Equality/build.sh`
code/72-strictness-verify.py                                             source 72, Part I: delivered `Strictness_Equality/verify.py`
code/72-strictness-verify_witnesses.py                                   source 72, Part I: delivered `Strictness_Equality/verify_witnesses.py`
code/73-one-shore-gadget_verification-exact_gadget_tails.py              source 73, Part II (Part II not yet written): delivered `gadget_verification/exact_gadget_tails.py`
code/73-one-shore-gadget_verification-verify_explicit_witness.py         source 73, Part II (Part II not yet written): delivered `gadget_verification/verify_explicit_witness.py`
code/73-one-shore-gadget_verification-verify_gadget_identity.py          source 73, Part II (Part II not yet written): delivered `gadget_verification/verify_gadget_identity.py`
code/73-one-shore-verify_full_hall.py                                    source 73, Part II (Part II not yet written): delivered `verify_full_hall.py`
code/74-weighted-rank-five-Makefile                                      source 74, Part I: delivered `ProveIt_Weighted_Rank_Five/Makefile`
code/74-weighted-rank-five-run_all.py                                    source 74, Part I: delivered `ProveIt_Weighted_Rank_Five/checks/run_all.py`
code/74-weighted-rank-five-verify_forced_core.py                         source 74, Part I: delivered `ProveIt_Weighted_Rank_Five/checks/verify_forced_core.py`
code/74-weighted-rank-five-verify_full_lift.py                           source 74, Part I: delivered `ProveIt_Weighted_Rank_Five/checks/verify_full_lift.py`
code/74-weighted-rank-five-verify_line_matroid.py                        source 74, Part I: delivered `ProveIt_Weighted_Rank_Five/checks/verify_line_matroid.py`
code/74-weighted-rank-five-verify_negative_shapes.py                     source 74, Part I: delivered `ProveIt_Weighted_Rank_Five/checks/verify_negative_shapes.py`
code/74-weighted-rank-five-verify_star_scaling.py                        source 74, Part I: delivered `ProveIt_Weighted_Rank_Five/checks/verify_star_scaling.py`
code/74-weighted-rank-five-verify_transversal_lift.py                    source 74, Part I: delivered `ProveIt_Weighted_Rank_Five/checks/verify_transversal_lift.py`
code/74-weighted-rank-five-verify_union_formula.py                       source 74, Part I: delivered `ProveIt_Weighted_Rank_Five/checks/verify_union_formula.py`
code/75-full-hall-compare_finite_tables.py                               source 75, Part I: delivered `ProveIt_Sharp_Full_Hall_Classification/compare_finite_tables.py`
code/75-full-hall-increment_families.py                                  source 75, Part I: delivered `ProveIt_Sharp_Full_Hall_Classification/increment_families.py`
code/75-full-hall-prove_families.py                                      source 75, Part I: delivered `ProveIt_Sharp_Full_Hall_Classification/prove_families.py`
code/75-full-hall-verify_formulas.py                                     source 75, Part I: delivered `ProveIt_Sharp_Full_Hall_Classification/verify_formulas.py`
code/75-full-hall-verify_negative.py                                     source 75, Part I: delivered `ProveIt_Sharp_Full_Hall_Classification/verify_negative.py`
code/75-full-hall-verify_separation.py                                   source 75, Part I: delivered `ProveIt_Sharp_Full_Hall_Classification/verify_separation.py`
code/76-rank-four-Makefile                                               source 76, Part I: delivered `ProveIt_Weighted_Rank_Four_Stability/Makefile`
code/76-rank-four-verify_boundary.py                                     source 76, Part I: delivered `ProveIt_Weighted_Rank_Four_Stability/verify_boundary.py`
code/76-rank-four-verify_complete_core.py                                source 76, Part I: delivered `ProveIt_Weighted_Rank_Four_Stability/verify_complete_core.py`
code/76-rank-four-verify_covariance.py                                   source 76, Part I: delivered `ProveIt_Weighted_Rank_Four_Stability/verify_covariance.py`
data/01-rank-eight-independent_hyperplane_certificate.json               source 01, Part IV (Part IV not yet written): delivered `data/independent_hyperplane_certificate.json`
data/01-rank-eight-minor_support_result.json                             source 01, Part IV (Part IV not yet written): delivered `data/minor_support_result.json`
data/01-rank-eight-primary-check_hyperplane_transition.json              source 01, Part IV (Part IV not yet written): delivered `code/primary/check_hyperplane_transition.json`
data/01-rank-eight-transition_result.json                                source 01, Part IV (Part IV not yet written): delivered `data/transition_result.json`
data/02-four-plus-four-independent_certificate.json                      source 02, Part IV (Part IV not yet written): delivered `data/independent_certificate.json`
data/02-four-plus-four-independent_coupled_certificate.json              source 02, Part IV (Part IV not yet written): delivered `data/independent_coupled_certificate.json`
data/02-four-plus-four-primary-check_generic_six_profiles.json           source 02, Part IV (Part IV not yet written): delivered `code/primary/check_generic_six_profiles.json`
data/02-four-plus-four-primary-check_top_coupled_five.json               source 02, Part IV (Part IV not yet written): delivered `code/primary/check_top_coupled_five.json`
data/02-four-plus-four-primary-check_top_coupled_six.json                source 02, Part IV (Part IV not yet written): delivered `code/primary/check_top_coupled_six.json`
data/02-four-plus-four-primary-verify_real_counterexample.json           source 02, Part IV (Part IV not yet written): delivered `code/primary/verify_real_counterexample.json`
data/03-five-plus-three-check_four_quotient_unit.json                    source 03, Part IV (Part IV not yet written): delivered `data/check_four_quotient_unit.json`
data/03-five-plus-three-verify_five_by_three.json                        source 03, Part IV (Part IV not yet written): delivered `data/verify_five_by_three.json`
data/03-five-plus-three-verify_plane_profiles.json                       source 03, Part IV (Part IV not yet written): delivered `data/verify_plane_profiles.json`
data/05-second-newton-check_core_endpoint_formulas.json                  source 05, Part III (Part III not yet written): delivered `verification/check_core_endpoint_formulas.json`
data/05-second-newton-check_fifth_truncation_barrier.json                source 05, Part III (Part III not yet written): delivered `verification/check_fifth_truncation_barrier.json`
data/05-second-newton-check_zero_core_schur.json                         source 05, Part III (Part III not yet written): delivered `verification/check_zero_core_schur.json`
data/05-second-newton-core_R_block_inverses.json                         source 05, Part III (Part III not yet written): delivered `verification/core_R_block_inverses.json`
data/05-second-newton-core_schur_1_0_0.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_1_0_0.json`
data/05-second-newton-core_schur_1_0_1.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_1_0_1.json`
data/05-second-newton-core_schur_1_0_2.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_1_0_2.json`
data/05-second-newton-core_schur_1_0_3.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_1_0_3.json`
data/05-second-newton-core_schur_1_0_6.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_1_0_6.json`
data/05-second-newton-core_schur_1_0_7.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_1_0_7.json`
data/05-second-newton-core_schur_1_1_1.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_1_1_1.json`
data/05-second-newton-core_schur_1_1_2.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_1_1_2.json`
data/05-second-newton-core_schur_1_1_3.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_1_1_3.json`
data/05-second-newton-core_schur_1_1_6.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_1_1_6.json`
data/05-second-newton-core_schur_1_1_7.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_1_1_7.json`
data/05-second-newton-core_schur_1_2_2.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_1_2_2.json`
data/05-second-newton-core_schur_1_2_3.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_1_2_3.json`
data/05-second-newton-core_schur_1_2_4.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_1_2_4.json`
data/05-second-newton-core_schur_1_2_5.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_1_2_5.json`
data/05-second-newton-core_schur_1_2_6.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_1_2_6.json`
data/05-second-newton-core_schur_1_2_7.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_1_2_7.json`
data/05-second-newton-core_schur_1_3_3.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_1_3_3.json`
data/05-second-newton-core_schur_1_3_5.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_1_3_5.json`
data/05-second-newton-core_schur_1_3_6.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_1_3_6.json`
data/05-second-newton-core_schur_1_3_7.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_1_3_7.json`
data/05-second-newton-core_schur_1_6_6.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_1_6_6.json`
data/05-second-newton-core_schur_1_6_7.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_1_6_7.json`
data/05-second-newton-core_schur_1_7_7.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_1_7_7.json`
data/05-second-newton-core_schur_3_0_0.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_3_0_0.json`
data/05-second-newton-core_schur_3_0_1.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_3_0_1.json`
data/05-second-newton-core_schur_3_0_3.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_3_0_3.json`
data/05-second-newton-core_schur_3_0_4.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_3_0_4.json`
data/05-second-newton-core_schur_3_0_5.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_3_0_5.json`
data/05-second-newton-core_schur_3_0_7.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_3_0_7.json`
data/05-second-newton-core_schur_3_1_1.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_3_1_1.json`
data/05-second-newton-core_schur_3_1_2.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_3_1_2.json`
data/05-second-newton-core_schur_3_1_3.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_3_1_3.json`
data/05-second-newton-core_schur_3_1_4.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_3_1_4.json`
data/05-second-newton-core_schur_3_1_5.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_3_1_5.json`
data/05-second-newton-core_schur_3_1_6.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_3_1_6.json`
data/05-second-newton-core_schur_3_1_7.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_3_1_7.json`
data/05-second-newton-core_schur_3_3_3.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_3_3_3.json`
data/05-second-newton-core_schur_3_3_4.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_3_3_4.json`
data/05-second-newton-core_schur_3_3_5.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_3_3_5.json`
data/05-second-newton-core_schur_3_3_7.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_3_3_7.json`
data/05-second-newton-core_schur_3_4_4.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_3_4_4.json`
data/05-second-newton-core_schur_3_4_5.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_3_4_5.json`
data/05-second-newton-core_schur_3_4_7.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_3_4_7.json`
data/05-second-newton-core_schur_3_5_5.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_3_5_5.json`
data/05-second-newton-core_schur_3_5_6.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_3_5_6.json`
data/05-second-newton-core_schur_3_5_7.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_3_5_7.json`
data/05-second-newton-core_schur_3_7_7.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_3_7_7.json`
data/05-second-newton-core_schur_7_0_0.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_7_0_0.json`
data/05-second-newton-core_schur_7_0_1.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_7_0_1.json`
data/05-second-newton-core_schur_7_0_3.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_7_0_3.json`
data/05-second-newton-core_schur_7_0_7.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_7_0_7.json`
data/05-second-newton-core_schur_7_1_1.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_7_1_1.json`
data/05-second-newton-core_schur_7_1_2.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_7_1_2.json`
data/05-second-newton-core_schur_7_1_3.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_7_1_3.json`
data/05-second-newton-core_schur_7_1_6.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_7_1_6.json`
data/05-second-newton-core_schur_7_1_7.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_7_1_7.json`
data/05-second-newton-core_schur_7_3_3.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_7_3_3.json`
data/05-second-newton-core_schur_7_3_5.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_7_3_5.json`
data/05-second-newton-core_schur_7_3_7.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_7_3_7.json`
data/05-second-newton-core_schur_7_7_7.json                              source 05, Part III (Part III not yet written): delivered `verification/core_schur_7_7_7.json`
data/05-second-newton-core_schur_manifest.json                           source 05, Part III (Part III not yet written): delivered `verification/core_schur_manifest.json`
data/05-second-newton-independent-endpoint_audit.json                    source 05, Part III (Part III not yet written): delivered `verification/independent/endpoint_audit.json`
data/05-second-newton-independent-finite_compression.json                source 05, Part III (Part III not yet written): delivered `verification/independent/finite_compression.json`
data/05-second-newton-independent-independent_manifest.json              source 05, Part III (Part III not yet written): delivered `verification/independent/independent_manifest.json`
data/05-second-newton-independent-relations_audit.json                   source 05, Part III (Part III not yet written): delivered `verification/independent/relations_audit.json`
data/05-second-newton-independent-replay_1_0_0.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_1_0_0.json`
data/05-second-newton-independent-replay_1_0_1.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_1_0_1.json`
data/05-second-newton-independent-replay_1_0_2.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_1_0_2.json`
data/05-second-newton-independent-replay_1_0_3.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_1_0_3.json`
data/05-second-newton-independent-replay_1_0_6.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_1_0_6.json`
data/05-second-newton-independent-replay_1_0_7.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_1_0_7.json`
data/05-second-newton-independent-replay_1_1_1.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_1_1_1.json`
data/05-second-newton-independent-replay_1_1_2.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_1_1_2.json`
data/05-second-newton-independent-replay_1_1_3.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_1_1_3.json`
data/05-second-newton-independent-replay_1_1_6.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_1_1_6.json`
data/05-second-newton-independent-replay_1_1_7.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_1_1_7.json`
data/05-second-newton-independent-replay_1_2_2.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_1_2_2.json`
data/05-second-newton-independent-replay_1_2_3.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_1_2_3.json`
data/05-second-newton-independent-replay_1_2_4.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_1_2_4.json`
data/05-second-newton-independent-replay_1_2_5.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_1_2_5.json`
data/05-second-newton-independent-replay_1_2_6.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_1_2_6.json`
data/05-second-newton-independent-replay_1_2_7.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_1_2_7.json`
data/05-second-newton-independent-replay_1_3_3.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_1_3_3.json`
data/05-second-newton-independent-replay_1_3_5.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_1_3_5.json`
data/05-second-newton-independent-replay_1_3_6.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_1_3_6.json`
data/05-second-newton-independent-replay_1_3_7.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_1_3_7.json`
data/05-second-newton-independent-replay_1_6_6.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_1_6_6.json`
data/05-second-newton-independent-replay_1_6_7.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_1_6_7.json`
data/05-second-newton-independent-replay_1_7_7.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_1_7_7.json`
data/05-second-newton-independent-replay_3_0_0.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_3_0_0.json`
data/05-second-newton-independent-replay_3_0_1.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_3_0_1.json`
data/05-second-newton-independent-replay_3_0_3.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_3_0_3.json`
data/05-second-newton-independent-replay_3_0_4.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_3_0_4.json`
data/05-second-newton-independent-replay_3_0_5.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_3_0_5.json`
data/05-second-newton-independent-replay_3_0_7.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_3_0_7.json`
data/05-second-newton-independent-replay_3_1_1.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_3_1_1.json`
data/05-second-newton-independent-replay_3_1_2.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_3_1_2.json`
data/05-second-newton-independent-replay_3_1_3.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_3_1_3.json`
data/05-second-newton-independent-replay_3_1_4.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_3_1_4.json`
data/05-second-newton-independent-replay_3_1_5.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_3_1_5.json`
data/05-second-newton-independent-replay_3_1_6.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_3_1_6.json`
data/05-second-newton-independent-replay_3_1_7.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_3_1_7.json`
data/05-second-newton-independent-replay_3_3_3.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_3_3_3.json`
data/05-second-newton-independent-replay_3_3_4.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_3_3_4.json`
data/05-second-newton-independent-replay_3_3_5.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_3_3_5.json`
data/05-second-newton-independent-replay_3_3_7.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_3_3_7.json`
data/05-second-newton-independent-replay_3_4_4.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_3_4_4.json`
data/05-second-newton-independent-replay_3_4_5.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_3_4_5.json`
data/05-second-newton-independent-replay_3_4_7.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_3_4_7.json`
data/05-second-newton-independent-replay_3_5_5.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_3_5_5.json`
data/05-second-newton-independent-replay_3_5_6.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_3_5_6.json`
data/05-second-newton-independent-replay_3_5_7.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_3_5_7.json`
data/05-second-newton-independent-replay_3_7_7.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_3_7_7.json`
data/05-second-newton-independent-replay_7_0_0.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_7_0_0.json`
data/05-second-newton-independent-replay_7_0_1.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_7_0_1.json`
data/05-second-newton-independent-replay_7_0_3.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_7_0_3.json`
data/05-second-newton-independent-replay_7_0_7.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_7_0_7.json`
data/05-second-newton-independent-replay_7_1_1.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_7_1_1.json`
data/05-second-newton-independent-replay_7_1_2.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_7_1_2.json`
data/05-second-newton-independent-replay_7_1_3.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_7_1_3.json`
data/05-second-newton-independent-replay_7_1_6.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_7_1_6.json`
data/05-second-newton-independent-replay_7_1_7.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_7_1_7.json`
data/05-second-newton-independent-replay_7_3_3.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_7_3_3.json`
data/05-second-newton-independent-replay_7_3_5.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_7_3_5.json`
data/05-second-newton-independent-replay_7_3_7.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_7_3_7.json`
data/05-second-newton-independent-replay_7_7_7.json                      source 05, Part III (Part III not yet written): delivered `verification/independent/replay_7_7_7.json`
data/05-second-newton-requirements.txt                                   source 05, Part III (Part III not yet written): delivered `requirements.txt`
data/08-rank-seven-middle_checks.json                                    source 08, Part IV (Part IV not yet written): delivered `Rank7_Eventual_Report/data/middle_checks.json`
data/08-rank-seven-replay.log                                            source 08, Part IV (Part IV not yet written): delivered `Rank7_Eventual_Report/data/replay.log`
data/08-rank-seven-top-gap-barrier_checks.json                           source 08s, Part IV (Part IV not yet written): delivered `Rank7_Top_Gap_Report/data/barrier_checks.json`
data/08-rank-seven-top-gap-rayleigh_seed_checks.json                     source 08s, Part IV (Part IV not yet written): delivered `Rank7_Top_Gap_Report/data/rayleigh_seed_checks.json`
data/08-rank-seven-top-gap-replay.log                                    source 08s, Part IV (Part IV not yet written): delivered `Rank7_Top_Gap_Report/data/replay.log`
data/08-rank-seven-top-gap-search_summary.json                           source 08s, Part IV (Part IV not yet written): delivered `Rank7_Top_Gap_Report/data/search_summary.json`
data/08-rank-seven-top-gap-supplement-run_diffuse_left.log               source 08s, Part IV (Part IV not yet written): delivered `Rank7_Top_Gap_Report/supplement/run_diffuse_left.log`
data/08-rank-seven-top-gap-supplement-run_heavy_right.log                source 08s, Part IV (Part IV not yet written): delivered `Rank7_Top_Gap_Report/supplement/run_heavy_right.log`
data/08-rank-seven-top-gap-supplement-run_middle.log                     source 08s, Part IV (Part IV not yet written): delivered `Rank7_Top_Gap_Report/supplement/run_middle.log`
data/08-rank-seven-top-gap-supplement-run_rayleigh_seed.log              source 08s, Part IV (Part IV not yet written): delivered `Rank7_Top_Gap_Report/supplement/run_rayleigh_seed.log`
data/10-three-vertex-check_supports.json                                 source 10, Part III (Part III not yet written): delivered `code/check_supports.json`
data/10-three-vertex-determinant.json                                    source 10, Part III (Part III not yet written): delivered `data/determinant.json`
data/10-three-vertex-independent_replay.json                             source 10, Part III (Part III not yet written): delivered `code/independent_replay.json`
data/13-last-newton-check_last_gap_quadratic.json                        source 13, Part III (Part III not yet written): delivered `data/check_last_gap_quadratic.json`
data/13-last-newton-exact_certificate.json                               source 13, Part III (Part III not yet written): delivered `data/exact_certificate.json`
data/13-last-newton-replay_certificate.json                              source 13, Part III (Part III not yet written): delivered `data/replay_certificate.json`
data/13-last-newton-verify_virtual_orbits.json                           source 13, Part III (Part III not yet written): delivered `data/verify_virtual_orbits.json`
data/21-every-core-check_weighted_planes.json                            source 21, Part IV (Part IV not yet written): delivered `data/check_weighted_planes.json`
data/21-every-core-verify_incidence.json                                 source 21, Part IV (Part IV not yet written): delivered `data/verify_incidence.json`
data/23-rooted-sectors-independent_full_field.json                       source 23, Part III (Part III not yet written): delivered `data/independent_full_field.json`
data/23-rooted-sectors-verify_base_dynamic.json                          source 23, Part III (Part III not yet written): delivered `data/verify_base_dynamic.json`
data/23-rooted-sectors-verify_common_field.json                          source 23, Part III (Part III not yet written): delivered `data/verify_common_field.json`
data/23-rooted-sectors-verify_connected.json                             source 23, Part III (Part III not yet written): delivered `data/verify_connected.json`
data/23-rooted-sectors-verify_rooted_hessians.json                       source 23, Part III (Part III not yet written): delivered `data/verify_rooted_hessians.json`
data/29-six-edges-check_core_orbits.json                                 source 29, Part IV (Part IV not yet written): delivered `data/check_core_orbits.json`
data/29-six-edges-check_star_edge.json                                   source 29, Part IV (Part IV not yet written): delivered `data/check_star_edge.json`
data/29-six-edges-check_star_edge_transpose.json                         source 29, Part IV (Part IV not yet written): delivered `data/check_star_edge_transpose.json`
data/29-six-edges-check_triangular.json                                  source 29, Part IV (Part IV not yet written): delivered `data/check_triangular.json`
data/29-six-edges-find_star_edge_first.json                              source 29, Part IV (Part IV not yet written): delivered `data/find_star_edge_first.json`
data/29-six-edges-find_transpose_first.json                              source 29, Part IV (Part IV not yet written): delivered `data/find_transpose_first.json`
data/29-six-edges-find_triangular_first.json                             source 29, Part IV (Part IV not yet written): delivered `data/find_triangular_first.json`
data/29-six-edges-independent_reconstruction.json                        source 29, Part IV (Part IV not yet written): delivered `data/independent_reconstruction.json`
data/29-six-edges-replay_all.json                                        source 29, Part IV (Part IV not yet written): delivered `data/replay_all.json`
data/32-two-columns-degree_one_certificate.json                          source 32, Part IV (Part IV not yet written): delivered `data/degree_one_certificate.json`
data/32-two-columns-degree_one_counts.json                               source 32, Part IV (Part IV not yet written): delivered `data/degree_one_counts.json`
data/32-two-columns-degree_one_replay.json                               source 32, Part IV (Part IV not yet written): delivered `data/degree_one_replay.json`
data/32-two-columns-flag_algebra_checks.json                             source 32, Part IV (Part IV not yet written): delivered `data/flag_algebra_checks.json`
data/32-two-columns-independent_reconstruction.json                      source 32, Part IV (Part IV not yet written): delivered `data/independent_reconstruction.json`
data/32-two-columns-zero_column_counts.json                              source 32, Part IV (Part IV not yet written): delivered `data/zero_column_counts.json`
data/35-two-rows-degree_one_certificate.json                             source 35, Part IV (Part IV not yet written): delivered `data/degree_one_certificate.json`
data/35-two-rows-degree_one_counts.json                                  source 35, Part IV (Part IV not yet written): delivered `data/degree_one_counts.json`
data/35-two-rows-degree_one_replay.json                                  source 35, Part IV (Part IV not yet written): delivered `data/degree_one_replay.json`
data/35-two-rows-flag_algebra_checks.json                                source 35, Part IV (Part IV not yet written): delivered `data/flag_algebra_checks.json`
data/35-two-rows-zero_row_counts.json                                    source 35, Part IV (Part IV not yet written): delivered `data/zero_row_counts.json`
data/38-matching-hole-first_gap_certificate.json                         source 38, Part IV (Part IV not yet written): delivered `Rank_Six_Matching_Hole_Cores/data/first_gap_certificate.json`
data/38-matching-hole-first_gap_replay.json                              source 38, Part IV (Part IV not yet written): delivered `Rank_Six_Matching_Hole_Cores/data/first_gap_replay.json`
data/38-matching-hole-support_checks.json                                source 38, Part IV (Part IV not yet written): delivered `Rank_Six_Matching_Hole_Cores/data/support_checks.json`
data/43-complete-core-requirements.txt                                   source 43, Part IV (Part IV not yet written): delivered `Rank_Six_Complete_Core_Cubic/requirements.txt`
data/43-complete-core-verification.json                                  source 43, Part IV (Part IV not yet written): delivered `Rank_Six_Complete_Core_Cubic/data/verification.json`
data/47-rank38-ulc-certificate-rank_06.json                              source 47, Part II (Part II not yet written): delivered `Sharp_Rank_38_Full_Hall_ULC/data/certificate/rank_06.json`
data/47-rank38-ulc-certificate-rank_07.json                              source 47, Part II (Part II not yet written): delivered `Sharp_Rank_38_Full_Hall_ULC/data/certificate/rank_07.json`
data/47-rank38-ulc-certificate-rank_08.json                              source 47, Part II (Part II not yet written): delivered `Sharp_Rank_38_Full_Hall_ULC/data/certificate/rank_08.json`
data/47-rank38-ulc-certificate-rank_09.json                              source 47, Part II (Part II not yet written): delivered `Sharp_Rank_38_Full_Hall_ULC/data/certificate/rank_09.json`
data/47-rank38-ulc-certificate-rank_10.json                              source 47, Part II (Part II not yet written): delivered `Sharp_Rank_38_Full_Hall_ULC/data/certificate/rank_10.json`
data/47-rank38-ulc-certificate-rank_11.json                              source 47, Part II (Part II not yet written): delivered `Sharp_Rank_38_Full_Hall_ULC/data/certificate/rank_11.json`
data/47-rank38-ulc-certificate-rank_12.json                              source 47, Part II (Part II not yet written): delivered `Sharp_Rank_38_Full_Hall_ULC/data/certificate/rank_12.json`
data/47-rank38-ulc-certificate-rank_13.json                              source 47, Part II (Part II not yet written): delivered `Sharp_Rank_38_Full_Hall_ULC/data/certificate/rank_13.json`
data/47-rank38-ulc-certificate-rank_14.json                              source 47, Part II (Part II not yet written): delivered `Sharp_Rank_38_Full_Hall_ULC/data/certificate/rank_14.json`
data/47-rank38-ulc-certificate-rank_15.json                              source 47, Part II (Part II not yet written): delivered `Sharp_Rank_38_Full_Hall_ULC/data/certificate/rank_15.json`
data/47-rank38-ulc-certificate-rank_16.json                              source 47, Part II (Part II not yet written): delivered `Sharp_Rank_38_Full_Hall_ULC/data/certificate/rank_16.json`
data/47-rank38-ulc-certificate-rank_17.json                              source 47, Part II (Part II not yet written): delivered `Sharp_Rank_38_Full_Hall_ULC/data/certificate/rank_17.json`
data/47-rank38-ulc-certificate-rank_18.json                              source 47, Part II (Part II not yet written): delivered `Sharp_Rank_38_Full_Hall_ULC/data/certificate/rank_18.json`
data/47-rank38-ulc-certificate-rank_19.json                              source 47, Part II (Part II not yet written): delivered `Sharp_Rank_38_Full_Hall_ULC/data/certificate/rank_19.json`
data/47-rank38-ulc-certificate-rank_20.json                              source 47, Part II (Part II not yet written): delivered `Sharp_Rank_38_Full_Hall_ULC/data/certificate/rank_20.json`
data/47-rank38-ulc-certificate-rank_21.json                              source 47, Part II (Part II not yet written): delivered `Sharp_Rank_38_Full_Hall_ULC/data/certificate/rank_21.json`
data/47-rank38-ulc-certificate-rank_22.json                              source 47, Part II (Part II not yet written): delivered `Sharp_Rank_38_Full_Hall_ULC/data/certificate/rank_22.json`
data/47-rank38-ulc-certificate-rank_23.json                              source 47, Part II (Part II not yet written): delivered `Sharp_Rank_38_Full_Hall_ULC/data/certificate/rank_23.json`
data/47-rank38-ulc-certificate-rank_24.json                              source 47, Part II (Part II not yet written): delivered `Sharp_Rank_38_Full_Hall_ULC/data/certificate/rank_24.json`
data/47-rank38-ulc-certificate-rank_25.json                              source 47, Part II (Part II not yet written): delivered `Sharp_Rank_38_Full_Hall_ULC/data/certificate/rank_25.json`
data/47-rank38-ulc-certificate-rank_26.json                              source 47, Part II (Part II not yet written): delivered `Sharp_Rank_38_Full_Hall_ULC/data/certificate/rank_26.json`
data/47-rank38-ulc-certificate-rank_27.json                              source 47, Part II (Part II not yet written): delivered `Sharp_Rank_38_Full_Hall_ULC/data/certificate/rank_27.json`
data/47-rank38-ulc-certificate-rank_28.json                              source 47, Part II (Part II not yet written): delivered `Sharp_Rank_38_Full_Hall_ULC/data/certificate/rank_28.json`
data/47-rank38-ulc-certificate-rank_29.json                              source 47, Part II (Part II not yet written): delivered `Sharp_Rank_38_Full_Hall_ULC/data/certificate/rank_29.json`
data/47-rank38-ulc-certificate-rank_30.json                              source 47, Part II (Part II not yet written): delivered `Sharp_Rank_38_Full_Hall_ULC/data/certificate/rank_30.json`
data/47-rank38-ulc-certificate-rank_31.json                              source 47, Part II (Part II not yet written): delivered `Sharp_Rank_38_Full_Hall_ULC/data/certificate/rank_31.json`
data/47-rank38-ulc-certificate-rank_32.json                              source 47, Part II (Part II not yet written): delivered `Sharp_Rank_38_Full_Hall_ULC/data/certificate/rank_32.json`
data/47-rank38-ulc-certificate-rank_33.json                              source 47, Part II (Part II not yet written): delivered `Sharp_Rank_38_Full_Hall_ULC/data/certificate/rank_33.json`
data/47-rank38-ulc-certificate-rank_34.json                              source 47, Part II (Part II not yet written): delivered `Sharp_Rank_38_Full_Hall_ULC/data/certificate/rank_34.json`
data/47-rank38-ulc-certificate-rank_35.json                              source 47, Part II (Part II not yet written): delivered `Sharp_Rank_38_Full_Hall_ULC/data/certificate/rank_35.json`
data/47-rank38-ulc-certificate-rank_36.json                              source 47, Part II (Part II not yet written): delivered `Sharp_Rank_38_Full_Hall_ULC/data/certificate/rank_36.json`
data/47-rank38-ulc-certificate-rank_37.json                              source 47, Part II (Part II not yet written): delivered `Sharp_Rank_38_Full_Hall_ULC/data/certificate/rank_37.json`
data/47-rank38-ulc-certificate-rank_38.json                              source 47, Part II (Part II not yet written): delivered `Sharp_Rank_38_Full_Hall_ULC/data/certificate/rank_38.json`
data/47-rank38-ulc-certificate-summary.json                              source 47, Part II (Part II not yet written): delivered `Sharp_Rank_38_Full_Hall_ULC/data/certificate/summary.json`
data/47-rank38-ulc-independent_summary.json                              source 47, Part II (Part II not yet written): delivered `Sharp_Rank_38_Full_Hall_ULC/data/independent_summary.json`
data/47-rank38-ulc-population_identity_checks.json                       source 47, Part II (Part II not yet written): delivered `Sharp_Rank_38_Full_Hall_ULC/data/population_identity_checks.json`
data/51-last-gap-verification.json                                       source 51, Part II (Part II not yet written): delivered `Last_Hall_Gap_Separation/data/verification.json`
data/55-rank38-endpoint-rank_certificate.json                            source 55, Part II (Part II not yet written): delivered `Sharp_Rank_38_Hall_Endpoint/data/rank_certificate.json`
data/55-rank38-endpoint-requirements.txt                                 source 55, Part II (Part II not yet written): delivered `Sharp_Rank_38_Hall_Endpoint/requirements.txt`
data/55-rank38-endpoint-verification.json                                source 55, Part II (Part II not yet written): delivered `Sharp_Rank_38_Hall_Endpoint/data/verification.json`
data/60-rank-two-blocks-QA.txt                                           source 60, Part III (Part III not yet written): delivered `QA.txt`
data/60-rank-two-blocks-eventual_scaling_checks.json                     source 60, Part III (Part III not yet written): delivered `data/eventual_scaling_checks.json`
data/60-rank-two-blocks-kernel_compression_checks.json                   source 60, Part III (Part III not yet written): delivered `data/kernel_compression_checks.json`
data/60-rank-two-blocks-matrix_lift_checks.json                          source 60, Part III (Part III not yet written): delivered `data/matrix_lift_checks.json`
data/60-rank-two-blocks-rank_three_boundary_checks.json                  source 60, Part III (Part III not yet written): delivered `data/rank_three_boundary_checks.json`
data/60-rank-two-blocks-reduction_checks.json                            source 60, Part III (Part III not yet written): delivered `data/reduction_checks.json`
data/60-rank-two-blocks-requirements.txt                                 source 60, Part III (Part III not yet written): delivered `requirements.txt`
data/63-nested-exterior-QA.txt                                           source 63, Part III (Part III not yet written): delivered `QA.txt`
data/63-nested-exterior-exact_certificate.json                           source 63, Part III (Part III not yet written): delivered `data/exact_certificate.json`
data/63-nested-exterior-marginal_barrier.json                            source 63, Part III (Part III not yet written): delivered `data/marginal_barrier.json`
data/63-nested-exterior-sector_checks.json                               source 63, Part III (Part III not yet written): delivered `data/sector_checks.json`
data/63-nested-exterior-small_support_checks.json                        source 63, Part III (Part III not yet written): delivered `data/small_support_checks.json`
data/63-nested-exterior-summary.json                                     source 63, Part III (Part III not yet written): delivered `data/summary.json`
data/63-nested-exterior-two_core_sector_checks.json                      source 63, Part III (Part III not yet written): delivered `data/two_core_sector_checks.json`
data/69-common-exterior-QA.txt                                           source 69, Part III (Part III not yet written): delivered `QA.txt`
data/69-common-exterior-barrier_verification.json                        source 69, Part III (Part III not yet written): delivered `data/barrier_verification.json`
data/69-common-exterior-exact_certificate.json                           source 69, Part III (Part III not yet written): delivered `data/exact_certificate.json`
data/69-common-exterior-verification.json                                source 69, Part III (Part III not yet written): delivered `data/verification.json`
data/71-unit-weight-gadget_identity_verification.json                    source 71, Part II (Part II not yet written): delivered `ProveIt_Unit_Weight_Rank_Normalization_Counterexample/data/gadget_identity_verification.json`
data/71-unit-weight-unit_deficiency_one_witness.json                     source 71, Part II (Part II not yet written): delivered `ProveIt_Unit_Weight_Rank_Normalization_Counterexample/data/unit_deficiency_one_witness.json`
data/71-unit-weight-unit_rank3450_witness.json                           source 71, Part II (Part II not yet written): delivered `ProveIt_Unit_Weight_Rank_Normalization_Counterexample/data/unit_rank3450_witness.json`
data/71-unit-weight-verification.json                                    source 71, Part II (Part II not yet written): delivered `ProveIt_Unit_Weight_Rank_Normalization_Counterexample/data/verification.json`
data/71-unit-weight-visual_qa.json                                       source 71, Part II (Part II not yet written): delivered `ProveIt_Unit_Weight_Rank_Normalization_Counterexample/data/visual_qa.json`
data/72-strictness-validation.json                                       source 72, Part I: delivered `Strictness_Equality/validation.json`
data/72-strictness-verification.json                                     source 72, Part I: delivered `Strictness_Equality/verification.json`
data/72-strictness-verification.log                                      source 72, Part I: delivered `Strictness_Equality/verification.log`
data/72-strictness-witness_verification.json                             source 72, Part I: delivered `Strictness_Equality/witness_verification.json`
data/72-strictness-witness_verification.log                              source 72, Part I: delivered `Strictness_Equality/witness_verification.log`
data/73-one-shore-full_hall_verification.json                            source 73, Part II (Part II not yet written): delivered `full_hall_verification.json`
data/73-one-shore-gadget_verification-gadget_identity_verification.json  source 73, Part II (Part II not yet written): delivered `gadget_verification/gadget_identity_verification.json`
data/73-one-shore-gadget_verification-one_shore_rank310_witness.json     source 73, Part II (Part II not yet written): delivered `gadget_verification/one_shore_rank310_witness.json`
data/74-weighted-rank-five-forced_core_verification.json                 source 74, Part I: delivered `ProveIt_Weighted_Rank_Five/data/forced_core_verification.json`
data/74-weighted-rank-five-full_lift_verification.json                   source 74, Part I: delivered `ProveIt_Weighted_Rank_Five/data/full_lift_verification.json`
data/74-weighted-rank-five-line_matroid_verification.json                source 74, Part I: delivered `ProveIt_Weighted_Rank_Five/data/line_matroid_verification.json`
data/74-weighted-rank-five-negative_shapes_verification.json             source 74, Part I: delivered `ProveIt_Weighted_Rank_Five/data/negative_shapes_verification.json`
data/74-weighted-rank-five-qa_report.json                                source 74, Part I: delivered `ProveIt_Weighted_Rank_Five/qa_report.json`
data/74-weighted-rank-five-requirements.txt                              source 74, Part I: delivered `ProveIt_Weighted_Rank_Five/requirements.txt`
data/74-weighted-rank-five-star_scaling_verification.json                source 74, Part I: delivered `ProveIt_Weighted_Rank_Five/data/star_scaling_verification.json`
data/74-weighted-rank-five-transversal_lift_verification.json            source 74, Part I: delivered `ProveIt_Weighted_Rank_Five/data/transversal_lift_verification.json`
data/74-weighted-rank-five-union_formula_verification.json               source 74, Part I: delivered `ProveIt_Weighted_Rank_Five/data/union_formula_verification.json`
data/75-full-hall-finite_table_verification.json                         source 75, Part I: delivered `ProveIt_Sharp_Full_Hall_Classification/finite_table_verification.json`
data/75-full-hall-formula_verification.json                              source 75, Part I: delivered `ProveIt_Sharp_Full_Hall_Classification/formula_verification.json`
data/75-full-hall-negative_verification.json                             source 75, Part I: delivered `ProveIt_Sharp_Full_Hall_Classification/negative_verification.json`
data/75-full-hall-positivity_verification.json                           source 75, Part I: delivered `ProveIt_Sharp_Full_Hall_Classification/positivity_verification.json`
data/75-full-hall-regression_rank5_orbits.json                           source 75, Part I: delivered `ProveIt_Sharp_Full_Hall_Classification/regression_rank5_orbits.json`
data/75-full-hall-regression_rank6_orbits.json                           source 75, Part I: delivered `ProveIt_Sharp_Full_Hall_Classification/regression_rank6_orbits.json`
data/75-full-hall-requirements.txt                                       source 75, Part I: delivered `ProveIt_Sharp_Full_Hall_Classification/requirements.txt`
data/75-full-hall-separation_verification.json                           source 75, Part I: delivered `ProveIt_Sharp_Full_Hall_Classification/separation_verification.json`
data/76-rank-four-boundary_verification.json                             source 76, Part I: delivered `ProveIt_Weighted_Rank_Four_Stability/boundary_verification.json`
data/76-rank-four-complete_core_verification.json                        source 76, Part I: delivered `ProveIt_Weighted_Rank_Four_Stability/complete_core_verification.json`
data/76-rank-four-covariance_verification.json                           source 76, Part I: delivered `ProveIt_Weighted_Rank_Four_Stability/covariance_verification.json`
data/76-rank-four-qa_report.json                                         source 76, Part I: delivered `ProveIt_Weighted_Rank_Four_Stability/qa_report.json`
data/76-rank-four-requirements.txt                                       source 76, Part I: delivered `ProveIt_Weighted_Rank_Four_Stability/requirements.txt`
```

Every file except `article.tex`, `article.pdf` and this README is
byte-identical to the delivery and carries its source's prefix; the second
column gives its delivered path inside the archive (for 08s, inside the
nested companion zip). Subdirectories of the deliveries are flattened into
the name (for example `checks/run_all.py` of source 74 is
`code/74-weighted-rank-five-run_all.py`). Not shipped: the 27 manuscripts
(their text is in `article.tex`), their PDFs and delivery READMEs (this
README replaces them), checksum ledgers (all verified at placement), 26
identical copies of a TeX Live helper `build_local.sh` (byte-identical to
the tracked
[`code/15-leaf-compression-build_local.sh`](../../enumerative-combinatorics/preorder-root-polytopes/code/15-leaf-compression-build_local.sh)
of `preorder-root-polytopes`), the embedded copies of sibling archives, and
everything of archive 78. They survive in the archives of `1512ef835`.
Source 74's `article.tex` was delivered with eight section files
(`first_gap.tex`, `forced_core.tex`, `full_lift.tex`,
`geometric_corollary.tex`, `negative_ranks.tex`, `scaling_threshold.tex`,
`star_transfer.tex`, `verification_scope.tex`); they were placed beside it
in `8bb543f0f`, are inlined into `article.tex` by this write and are removed.

## Labels

Every label in `article.tex` carries the prefix `mrn:`. Labels written in
the merge are `mrn:sec:…`, `mrn:part:…`, `mrn:src:NN` (the start of source
NN) and `mrn:w:sec:shapes`, `mrn:w:tab:shapes`; a delivered label `X` of
source NN becomes `mrn:<part>:<slug>:X`:

| Part | Source → sub-prefix |
|---|---|
| I (`mrn:w:`) | 74 `rf`, 72 `se`, 76 `sb`, 75 `fh` |
| II (`mrn:u:`) | 71 `uw`, 73 `os`, 55 `ep`, 47 `ag`, 51 `sp` |
| III (`mrn:s:`) | 60 `rb`, 10 `tv`, 23 `rs`, 13 `lg`, 05 `sn`, 69 `ce`, 63 `ne` |
| IV (`mrn:e:`) | 08s `tg`, 21 `ec`, 43 `cc`, 38 `mh`, 35 `tr`, 32 `tc`, 29 `se`, 08 `r7`, 03 `fp`, 02 `ff`, 01 `r8` |

The article has 99 labels: 84 under `mrn:w:`,
0 under `mrn:u:`, 0 under `mrn:s:`, 0 under
`mrn:e:` and 15 others. Labels were added to unlabelled delivered
sections or statements so that the merge could refer to them:
`mrn:w:rf:sec:lorentz` and `mrn:w:rf:sec:tworow` (source 74; its text
"Section 3" became a reference) and `mrn:w:sb:sec:tools` (source 76).
No delivered label was dropped. No label has a Lean or Rocq mapping.

## What is claimed

Part I (weighted activities on both shores):

- **Source 74.** If `G` has a vertex cover `A ⊔ B` with `A` two left
  vertices (a displayed `2+q` cover), the homogeneous left marginal is
  Lorentzian, via an explicit rank-`(q+2)` transversal matroid; so `p_G` is
  `ULC_{q+2}` for every positive activity assignment, and `ULC_{nu(G)}` when
  the cover is minimum (Theorem 2.1). Consequently every graph with
  `nu(G) ≤ 5` is `ULC_nu` for arbitrary positive activities on both shores,
  and, with the rank-six counterexample `H_{3,33}` of Part XI of
  `preorder-root-polytopes`, the least weighted failure rank is exactly six;
  there are failures at every rank `≥ 6` (Corollary 2.2). Any weighted
  failure has every minimum cover meeting both shores in at least three
  vertices. Also: forced-sector `ULC_q` and strict eventual scaling of the
  two cover vertices (Theorem 2.3), the sharp all-core constants `2q/(q−1)`
  and `3`, star-core transfer proofs, an Ehrhart `h*` corollary at unit
  weights, and quantitative strictness thresholds.
- **Source 72.** Under the same cover hypothesis (in particular for
  `2 ≤ nu ≤ 5`), equality in any one normalized gap holds exactly for
  balanced star forests (`p_G = (1+Et)^r`); otherwise every gap is strict.
  A weighted Chan–Pak contraction criterion is proved for real weights.
- **Source 76.** A vertex cover with two vertices on each shore makes the
  complemented-row basis polynomial real stable, so `p_G` is real-rooted
  for every positive activity assignment; the complete `2×s` mixed core is
  stable exactly when `(m+2)(n+2)s ≥ 2(m+1)(n+1)(s−1)`; a 17-vertex graph
  has an unstable signed polynomial but a real-rooted unit diagonal.
- **Source 75.** The full Hall graphs `H_{a,b;n,m}` are `ULC_{a+b}` for
  every population and every positive activity assignment exactly when
  `min(a,b) ≤ 2`, strictly when the minimum is two; explicit failures for
  all `a, b ≥ 3`; a strictly `ULC_5` example with nonreal zeros.

Table 3 of the article (written in the merge from source 74's recorded
verifier output, recomputed independently) lists seven exact last-gap
failures of `H_{a,b;N,M}`, five of them not in `preorder-root-polytopes`
(ranks 7–11; the rank-seven one has 38 vertices).

## What is not claimed

- Source 74's theorem asserts neither real-rootedness nor stability of the
  support polynomial; it does not address the unrestricted unit-weight and
  one-shore problems at higher rank; it gives no uniform scaling threshold.
- Sources 72 and 74: finite computations are regression checks, not proofs.
- Source 76 does not assert real-rootedness for every graph of matching
  number four; its stability argument has a genuine rank-five boundary.
- Source 75 classifies the full Hall family only; its negative assertion
  concerns neither unit nor one-shore weights.
- No source claims global priority, Lean certification or referee review.

What `preorder-root-polytopes` already proves is cited, not claimed: the
smaller-shore inequality (its Theorem 70.1, Lemma 205.1), leaf compression
and singleton covers (Lemma 206.1, Theorem 206.2), the first-gap inequality
and its equality case (Theorem 180.2, Corollary 180.3, Theorems 190.2 and
190.3), the witnesses `H_{3,33}` and `H_{4,11}` (Theorems 177.1 and 176.1),
and the stability tools of its Part VI (Theorems 85.3, 91.2, 93.2, 94.1,
Corollary 94.3). Where a source re-proves one of them, the article marks the
proof as a second route (sources 74 and 72 on the first gap) or replaces it
by a pointer (source 74's two small lemmas; source 76's gluing and
expected-determinant lemmas).

## Research questions of `preorder-root-polytopes`

| Question there | Status after this report |
|---|---|
| RQ 86 `hb:q:rank` | answered: least weighted failure rank exactly 6 (source 74 with Part XI) |
| RQ 87 `hb:q:order` | in part: `D(4) = 4`, `D(5) = 5` (source 74) |
| RQ 93 `mr:q:rankfour` | answered affirmatively, unit and weighted (source 74; source 76 by real stability) |
| RQ 89 `hb:q:asymmetry` | in large part: full Hall classification (source 75), asymmetric failures (sources 74, 75) |
| RQ 90 `hb:q:defects` | bears on it: equality at every gap under the cover hypothesis (source 72) |
| RQ 37 `lor:q:first` (Part V) | weighted: holds through `nu = 5`, fails from 6 |

## Relation to neighbouring reports and formal projects

- [`preorder-root-polytopes`](../../enumerative-combinatorics/preorder-root-polytopes)
  introduced the question (its Part V, Research question 37) and proves,
  in Parts XI–XIII, the results this report builds on; they are cited by
  printed number and label in Section 1.2 of the article and not reprinted.
  This report answers several of its research questions (table above);
  that report receives dated pointers to this one in a separate
  reciprocal-notes commit of the same write.
- Placement in this collection beside other work confers no formal status.
  No Lean or Rocq declaration in the repository concerns matching-support
  polynomials; nothing in this report is formalized.

## Build

```sh
cp article.tex /path/to/scratch/ && cd /path/to/scratch
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX (MiKTeX or TeX Live) with `amsmath`, `amssymb`, `amsthm`,
`mathtools`, `geometry`, `lmodern`, `microtype`, `booktabs`, `array`,
`longtable`, `hyperref` and `xurl`. The build has no errors, no undefined
references or citations, no multiply defined labels and no duplicate PDF
destinations. `article.tex` is self-contained (no `\input`, no figures).

## Rerun the checks

The delivered scripts write their outputs under their **delivery** names,
in place or beside themselves, and some import siblings by delivery path.
Do not run them in this directory: they would create unprefixed files or
fail to import. Rerun on a fresh copy of the delivered layout instead:

```sh
W=$(mktemp -d)
git -C /path/to/ProveIt show 1512ef835:docs/incoming/<ARCHIVE>.zip > "$W/a.zip"
cd "$W" && unzip -q a.zip && cd <INNER DIRECTORY>
<COMMAND>
```

and compare the outputs with the shipped files (on Windows the scripts write
CRLF line endings; compare modulo line endings).

| Source | Archive / inner directory | Command | Time (placement run) |
|---|---|---|---|
| 74 | `ProveIt_Weighted_Rank_Five_and_Two_Shore_Covers` / `ProveIt_Weighted_Rank_Five` | `python checks/run_all.py` (SymPy ≥ 1.12) | 63 s |
| 72 | `strictness_equality_package` / `Strictness_Equality` | `python verify.py` then `python verify_witnesses.py` (standard library) | 1 s, 2 s |
| 76 | `ProveIt_Weighted_Rank_Four_Stability` / same | `python verify_covariance.py`, `python verify_complete_core.py`, `python verify_boundary.py` (SymPy ≥ 1.10) | 18–19 s each |
| 75 | `ProveIt_Sharp_Full_Hall_Classification` / same | `python verify_formulas.py`, `python prove_families.py`, `python compare_finite_tables.py`, `python verify_negative.py`, `python verify_separation.py` (SymPy 1.14.0) | under 1 min |

At placement every suite was run on such a copy (the times above); all
passed, except that three long certificates were replayed only in part:
source 05's full mode, ranks 30–38 of source 47's certificate, and source
02's complete driver (its parts pass separately). Regenerated outputs equal
the shipped ones apart from line endings and timing fields.

## Delivery names and discrepancies

- The shipped audit and provenance files keep their delivered text, which
  uses delivery names. `code/74-weighted-rank-five-Makefile`
  runs `python3 checks/run_all.py` and builds `article.tex` (its delivered
  layout); `code/76-rank-four-Makefile` runs `verify_*.py` beside itself and
  builds the unshipped manuscript; `code/72-strictness-build.sh` builds the
  unshipped `strictness_equality.tex`. Use them only in a delivered-layout
  copy.
- `72-strictness-SOURCES.md` records a SHA-256 of source 74's delivered PDF,
  which is not shipped; it is kept as delivered.
- `76-rank-four-PROOF_STATUS.md` says that "the smallest failure rank is
  reduced to five or six"; source 74 makes it exactly six. It also says that
  leaf attachment, vertex gluing and the independent-column expectation "are
  proved directly"; in the article those proofs are replaced by pointers to
  the identical proofs of Part VI of `preorder-root-polytopes`.
- Source 75's delivered README (not shipped) says that general weighted rank
  five "remain[s] open here"; source 74 settles it.
- Source 74's delivered README, placed as `README.md` in `8bb543f0f`, is
  replaced by this README; it named `checks/run_all.py`, `requirements.txt`,
  `build_local.sh`, `SHA256SUMS`, `PROOF_STATUS.md` and `qa_report.json`,
  which are shipped as `code/74-weighted-rank-five-run_all.py`,
  `data/74-weighted-rank-five-requirements.txt`,
  `74-weighted-rank-five-PROOF_STATUS.md` and
  `data/74-weighted-rank-five-qa_report.json` (the helper and the ledger are
  not shipped). The QA records `data/74-weighted-rank-five-qa_report.json`,
  `data/76-rank-four-qa_report.json`, `data/71-unit-weight-visual_qa.json` and
  `data/72-strictness-validation.json` describe delivered PDFs that are not
  shipped.
- Source 74's text cites its companions as `[Rank]`, `[Leaf]`, `[Four]`,
  `[Hall]`, `[OldHall]`; in the article these are Part XII, Part XIII,
  source 76, source 75 and Part XI respectively (bibliography notes).

