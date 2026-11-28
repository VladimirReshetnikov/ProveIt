# Generalized Riemann Hypothesis

A research article on what lies beyond the generalized Riemann hypothesis for Dirichlet
L-functions, merged from 209 delivered research reports.

[`Article/article.pdf`](Article/article.pdf) states each result of the reports once, in the
strongest form they prove. Repeated material and results implied by stronger or more general
ones are left out, and the reports' many accounts of the upstream proof are replaced by one
section. The input theorem, RH and GRH for Dirichlet L-functions as stated in the external
Lean development [`lsernau/grh-lean`](https://github.com/lsernau/grh-lean) at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, is taken as given. The article reproduces the
reports' mathematics without recomputing it. The [Lean formalization](Lean/README.md)
tracks checked results against the article. The upstream proof has its own Lean package
in [`Lean/grh`](Lean/grh/README.md). Every result is marked as unconditional, as using Dirichlet GRH, or as a
reduction whose target estimate is open. The [article README](Article/README.md) lists its
sections.

## The reports

The reports were delivered as 209 archives from 25 to 27 November 2026: 61 to the
repository's [`docs/incoming`](../../docs/incoming/README.md) and 148 to this project's own
`docs/incoming`. Each was placed, unchanged and without verification, in a directory
`Research/<archive name>/`, with the archive's single wrapper directory removed and with
checksum manifests, files matched by `.gitignore` and copies of files of earlier packets left
out (`Research/OMITTED.tsv` listed them).

Once their content was merged into the article, the packets were removed from the working
tree. They remain in the history. The first two batches, with their `Research/OMITTED.tsv`,
are present at commit `10802a6b36`, the third batch at commit `f2f9fd7531`, the fourth at commit
`64f3896557`, the fifth at commit `fd9a9cb2bd`, the sixth at commit `f6b5955e13`, the seventh at commit
`7f951e1dfd` and the eighth at commit `3c4d27a69c`, each with its own
`Research/OMITTED.tsv`; each is the last commit before the removal
of that batch. Packet names are
unique across the batches:

```
git show 10802a6b36:Analysis/GeneralizedRiemannHypothesis/Research/<packet>/<path>   # batches 1-2
git show f2f9fd7531:Analysis/GeneralizedRiemannHypothesis/Research/<packet>/<path>   # batch 3
git show 64f3896557:Analysis/GeneralizedRiemannHypothesis/Research/<packet>/<path>   # batch 4
git show fd9a9cb2bd:Analysis/GeneralizedRiemannHypothesis/Research/<packet>/<path>   # batch 5
git show f6b5955e13:Analysis/GeneralizedRiemannHypothesis/Research/<packet>/<path>   # batch 6
git show 7f951e1dfd:Analysis/GeneralizedRiemannHypothesis/Research/<packet>/<path>   # batch 7
git show 3c4d27a69c:Analysis/GeneralizedRiemannHypothesis/Research/<packet>/<path>   # batch 8
```

The article cites delivered certificates and data files by their path under `Research/`;
those paths refer to the commit of the packet's batch. The [provenance tables](Article/provenance/README.md)
record, for every section of every report file, where its material went in the article and,
for each omitted result, the result that supersedes it.

| Batch | Archives | Drop directory | Arrival commits | Placement |
|---|---:|---|---|---|
| First | 61 | `docs/incoming` | `1e1728ad22` to `de7b92e9c3` | `21c0252ffe`, with copies of earlier packets removed in `0b53cb0257` |
| Second | 42 | `Analysis/GeneralizedRiemannHypothesis/docs/incoming` | `0b4d634fdb` to `2c45d19807` | `dedc2966ea` |
| Third | 17 | `Analysis/GeneralizedRiemannHypothesis/docs/incoming` | `54fb88e936` to `4dfb7aaf87` | `1a50d416ba` |
| Fourth | 11 | `Analysis/GeneralizedRiemannHypothesis/docs/incoming` | `22e5c8b7dd` to `42bca35561` | `28ec545c4d` |
| Fifth | 11 | `Analysis/GeneralizedRiemannHypothesis/docs/incoming` | `9ab4d2073b` to `edca076fde` | `6f4c5c47e8` |
| Sixth | 42 | `Analysis/GeneralizedRiemannHypothesis/docs/incoming` | `a4404ca024` to `05f6dcb1f6` | `44374877d8` |
| Seventh | 10 | `Analysis/GeneralizedRiemannHypothesis/docs/incoming` | `8c6032a195` to `6d284fcf75` | `7f1f4e01e3` |
| Eighth | 15 | `Analysis/GeneralizedRiemannHypothesis/docs/incoming` | `29ef78b839` to `f9f1016ec7` | `eeb7ebd855` |

By their own account, the reports start from `lsernau/grh-lean` and ask what its theorem
settles elsewhere and which methods inside its proof carry over to other problems. Several
packets contained excerpts of that development, under the Apache-2.0 licence. The excerpts
left with the packets. The [import record](vendor/grh-lean/README.md) identifies the
upstream revision used for [the local proof](Lean/grh/README.md).

## Reports placed and not yet merged

33 further archives arrived in `Analysis/GeneralizedRiemannHypothesis/docs/incoming` on
27 November 2026, in 12 arrival commits from `641cd62961` to `36ca617407`. They are placed as before, one
directory per archive under `Research/`, and retired from the drop directory. Of their 605
members, 572 are placed and 33 are listed in [`Research/OMITTED.tsv`](Research/OMITTED.tsv):
27 matched by `.gitignore`, 1 checksum manifest of its own packet, and 5 files of
`kozma_oravecz_three_frequency_2026-11-28/m3_cross_check/` that are byte-identical to the files of
`kozma_oravecz_147_2026-11-27`, an earlier packet of this batch. The archives named `... (2).zip`
and `... (1).zip` differ from their namesakes and are placed with the suffixes `_2` and `_1`. Their
content is merged into the article next, after which these directories are removed like the
earlier ones.

| Directory | Archive | Arrival | Wrapper | Members | Placed | Omitted | Title in the delivery README |
|---|---|---|---|---:|---:|---:|---|
| [grh_finite_observation_and_critical_recovery](Research/grh_finite_observation_and_critical_recovery/README.md) | `grh_finite_observation_and_critical_recovery.zip` | `641cd62961` | `grh_finite_observation` | 25 | 24 | 1 | Finite observations of arithmetic Levy paths and critical recovery of symplectic forms |
| [padic-sharp-exponent-digits](Research/padic-sharp-exponent-digits/README.txt) | `padic-sharp-exponent-digits.zip` | `641cd62961` | none | 6 | 5 | 1 | Exact sparse p-adic root counts and a sharp exponent-digit bound. |
| [grh_research_extensions_2026-11-27](Research/grh_research_extensions_2026-11-27/README.md) | `grh_research_extensions_2026-11-27.zip` | `8528159d15` | `grh_research_extensions_2026-11-27` | 25 | 24 | 1 | Two continuations of the ProveIt GRH program |
| [grh_research_extensions_2026-11-27_2](Research/grh_research_extensions_2026-11-27_2/README.md) | `grh_research_extensions_2026-11-27 (2).zip` | `5943d6e66f` | `grh_research_extensions_2026-11-27` | 21 | 20 | 1 | Research extensions of the ProveIt GRH article |
| [kozma_oravecz_147_2026-11-27](Research/kozma_oravecz_147_2026-11-27/README.md) | `kozma_oravecz_147_2026-11-27.zip` | `5943d6e66f` | none | 5 | 5 | 0 | Zero-free gaps for the spectrum ±{N,4N,7N} |
| [multipartite-ehrhart](Research/multipartite-ehrhart/README.md) | `multipartite-ehrhart.zip` | `c84f65aa01` | `multipartite-ehrhart` | 19 | 19 | 0 | Reconstructing complete multipartite graphs from Ehrhart polynomials |
| [critical_symplectic_experiment_2026-11-27](Research/critical_symplectic_experiment_2026-11-27/README.txt) | `critical_symplectic_experiment_2026-11-27.zip` | `4ad0247ca1` | `critical_symplectic_experiment_2026-11-27` | 26 | 25 | 1 | THE COMPLETE CRITICAL LAW FOR HIDDEN SYMPLECTIC FORMS |
| [cycle-complements-and-dirichlet-zero-matching](Research/cycle-complements-and-dirichlet-zero-matching/README.md) | `cycle-complements-and-dirichlet-zero-matching.zip` | `f7967b82f3` | `cycle-complements-and-dirichlet-zero-matching` | 21 | 21 | 0 | Cycle complements and Dirichlet zero matching |
| [euler_factor_agreement_research](Research/euler_factor_agreement_research/README.md) | `euler_factor_agreement_research.zip` | `f7967b82f3` | `cubic_euler_agreement` | 32 | 31 | 1 | Euler-factor agreement: a conjecture counterexample and sharp cubic theorems |
| [grh_research_2026-11-27](Research/grh_research_2026-11-27/README.txt) | `grh_research_2026-11-27.zip` | `f7967b82f3` | `grh_research_2026-11-27` | 32 | 31 | 1 | RESEARCH SUPPLEMENT TO THE PROVEIT GRH TRANSFER PROGRAM |
| [grh_sharp_endpoint](Research/grh_sharp_endpoint/README.md) | `grh_sharp_endpoint.zip` | `f7967b82f3` | `grh_sharp_endpoint` | 8 | 7 | 1 | The sharp endpoint for full-spectrum positive Dirichlet zero filters |
| [moment_rigidity_2026-11-27](Research/moment_rigidity_2026-11-27/README.md) | `moment_rigidity_2026-11-27.zip` | `f7967b82f3` | `moment_rigidity` | 9 | 8 | 1 | Rigidity at the moment barrier in even-step abelian graph towers |
| [proveit_zero_detection_research](Research/proveit_zero_detection_research/README.md) | `proveit_zero_detection_research.zip` | `f7967b82f3` | none | 14 | 13 | 1 | Exponentially smaller zero detectors for symmetric-group extensions |
| [gram_column_number_2026-11-27](Research/gram_column_number_2026-11-27/README.md) | `gram_column_number_2026-11-27.zip` | `3a0fece374` | `gram_column_number` | 9 | 8 | 1 | Sharp growth of integral Gram determinants and generic modular column numbers |
| [grh_bounded_support_2026-11-27](Research/grh_bounded_support_2026-11-27/README.md) | `grh_bounded_support_2026-11-27.zip` | `3a0fece374` | `grh_bounded_support` | 13 | 12 | 1 | Bounded-excess positive filters for Dirichlet zero spectra |
| [grh_lower_degree_detector_2026-11-27](Research/grh_lower_degree_detector_2026-11-27/README.md) | `grh_lower_degree_detector_2026-11-27.zip` | `3a0fece374` | `grh_lower_degree_detector` | 8 | 7 | 1 | Exponentially smaller fields detecting nonabelian Riemann hypotheses |
| [kozma_oravecz_three_frequency_2026-11-28](Research/kozma_oravecz_three_frequency_2026-11-28/README.md) | `kozma_oravecz_three_frequency_2026-11-28.zip` | `ce35f320bc` | none | 13 | 8 | 5 | Exact gaps for wide three-frequency progressions |
| [padic_sparse_research](Research/padic_sparse_research/README.md) | `padic_sparse_research.zip` | `ce35f320bc` | none | 9 | 7 | 2 | Exact residue transport for sparse p-adic roots |
| [radical_square_density_2026-11-27](Research/radical_square_density_2026-11-27/README.md) | `radical_square_density_2026-11-27.zip` | `ce35f320bc` | `radical_square_density` | 7 | 6 | 1 | The radical-square invariant for geometric-progression-free polynomial sets |
| [sharp_global_filters](Research/sharp_global_filters/README.md) | `sharp_global_filters.zip` | `ce35f320bc` | none | 5 | 5 | 0 | The sharp localization barrier for positive Dirichlet zero filters |
| [symmetric_group_grh_multiplicity_2026-11-27](Research/symmetric_group_grh_multiplicity_2026-11-27/README.md) | `symmetric_group_grh_multiplicity_2026-11-27.zip` | `ce35f320bc` | none | 14 | 13 | 1 | Asymptotically sharp symmetric-group zero-multiplicity bounds |
| [torsion_power_patterns](Research/torsion_power_patterns/README.md) | `torsion_power_patterns.zip` | `ce35f320bc` | `torsion_power_patterns` | 9 | 8 | 1 | Sharp torsion selection across nonunit power patterns |
| [erdelyi_ellipse_and_proveit_extensions](Research/erdelyi_ellipse_and_proveit_extensions/README.md) | `erdelyi_ellipse_and_proveit_extensions.zip` | `9d90189d98` | `erdelyi_ellipse_and_proveit_extensions` | 22 | 22 | 0 | The Lorentz degree in a thin ellipse and three ProveIt extensions |
| [ProveIt_New_Results_2026-11-27](Research/ProveIt_New_Results_2026-11-27/README.txt) | `ProveIt_New_Results_2026-11-27.zip` | `42efb89335` | `ProveIt_New_Results_2026-11-27` | 22 | 21 | 1 | PROVEIT: SHARP ZERO INEQUALITIES AND HIGH-DERIVATIVE POSITIVITY |
| [critical_window_laws_2026-11-27](Research/critical_window_laws_2026-11-27/README.txt) | `critical_window_laws_2026-11-27.zip` | `42efb89335` | `critical_window_laws` | 29 | 27 | 2 | CRITICAL-WINDOW LAWS FOR QUADRATIC RELATIONS, CODE PRODUCTS, |
| [positive-fourier-zeros](Research/positive-fourier-zeros/README.md) | `positive-fourier-zeros.zip` | `42efb89335` | `positive-fourier-zeros` | 28 | 27 | 1 | Positive averages and prescribed Fourier zeros |
| [ProveIt_research_2026-11-27](Research/ProveIt_research_2026-11-27/README.txt) | `ProveIt_research_2026-11-27.zip` | `847b690439` | `ProveIt_research_2026-11-27` | 26 | 25 | 1 | FOUR RESEARCH ADVANCES FROM THE PROVEIT GRH ANALYSIS |
| [anticodes-egyptian-fractions-and-li-spectra](Research/anticodes-egyptian-fractions-and-li-spectra/README.md) | `anticodes-egyptian-fractions-and-li-spectra.zip` | `847b690439` | none | 21 | 21 | 0 | Four results extending ProveIt |
| [quadratic-turning-points-and-critical-filters](Research/quadratic-turning-points-and-critical-filters/README.md) | `quadratic-turning-points-and-critical-filters.zip` | `847b690439` | none | 10 | 10 | 0 | Quadratic central derivatives and positive filters for Dirichlet zeros |
| [deep_padic_roots_2026-11-27](Research/deep_padic_roots_2026-11-27/README.md) | `deep_padic_roots_2026-11-27.zip` | `36ca617407` | `deep_padic_roots` | 30 | 29 | 1 | Exact exponent compression and positive-filter rigidity |
| [kozma_oravecz_half_integer_2026-11-28](Research/kozma_oravecz_half_integer_2026-11-28/README.md) | `kozma_oravecz_half_integer_2026-11-28.zip` | `36ca617407` | none | 9 | 9 | 0 | Half-integer steps in wide three-frequency progressions |
| [proveit_three_extensions_2026-11-27_1](Research/proveit_three_extensions_2026-11-27_1/README.md) | `proveit_three_extensions_2026-11-27 (1).zip` | `36ca617407` | `proveit_three_extensions_2026-11-27` | 37 | 36 | 1 | Three extensions of the ProveIt research program |
| [proveit_three_extensions_2026-11-27](Research/proveit_three_extensions_2026-11-27/README.md) | `proveit_three_extensions_2026-11-27.zip` | `36ca617407` | `proveit_three_extensions_2026-11-27` | 41 | 38 | 3 | Three extensions of the ProveIt methods |
| Total | 33 archives | | | 605 | 572 | 33 | |
