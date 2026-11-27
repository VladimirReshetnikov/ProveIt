# Generalized Riemann Hypothesis

A research article on what lies beyond the generalized Riemann hypothesis for Dirichlet
L-functions, merged from 194 delivered research reports.

[`Article/article.pdf`](Article/article.pdf) states each result of the reports once, in the
strongest form they prove. Repeated material and results implied by stronger or more general
ones are left out, and the reports' many accounts of the upstream proof are replaced by one
section. The input theorem, RH and GRH for Dirichlet L-functions as stated in the external
Lean development [`lsernau/grh-lean`](https://github.com/lsernau/grh-lean) at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, is taken as given. The article reproduces the
reports' mathematics without recomputing it. The [Lean formalization](Lean/README.md)
tracks checked results against the article. The `grh` directory of the upstream
development is vendored, unmodified and unbuilt, in [`vendor/grh-lean`](vendor/grh-lean/README.md). Every result is marked as unconditional, as using Dirichlet GRH, or as a
reduction whose target estimate is open. The [article README](Article/README.md) lists its
sections.

## The reports

The reports were delivered as 194 archives from 25 to 27 November 2026: 61 to the
repository's [`docs/incoming`](../../docs/incoming/README.md) and 133 to this project's own
`docs/incoming`. Each was placed, unchanged and without verification, in a directory
`Research/<archive name>/`, with the archive's single wrapper directory removed and with
checksum manifests, files matched by `.gitignore` and copies of files of earlier packets left
out (`Research/OMITTED.tsv` listed them).

Once their content was merged into the article, the packets were removed from the working
tree. They remain in the history. The first two batches, with their `Research/OMITTED.tsv`,
are present at commit `10802a6b36`, the third batch at commit `f2f9fd7531`, the fourth at commit
`64f3896557`, the fifth at commit `fd9a9cb2bd`, the sixth at commit `f6b5955e13` and the seventh at commit
`7f951e1dfd`, each with its own
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

By their own account, the reports start from `lsernau/grh-lean` and ask what its theorem
settles elsewhere and which methods inside its proof carry over to other problems. Several
packets contained excerpts of that development, under the Apache-2.0 licence. The excerpts
left with the packets; the whole `grh` directory, at the commit the reports pin, is in
[`vendor/grh-lean`](vendor/grh-lean/README.md).

## Reports placed and not yet merged

15 further archives arrived in `Analysis/GeneralizedRiemannHypothesis/docs/incoming` on
27 November 2026, in 4 arrival commits from `29ef78b839` to `f9f1016ec7`. They are placed as before, one
directory per archive under `Research/`, and retired from the drop directory. Of their 261
members, 243 are placed and 18 are listed in [`Research/OMITTED.tsv`](Research/OMITTED.tsv):
17 matched by `.gitignore` and 1 checksum manifest of its own packet. No member is a copy of a
file of an earlier packet. The archive `grh_extensions_2026-11-27(2).zip` differs from both
earlier archives of that name, and since the sixth batch already has a packet
`grh_extensions_2026-11-27_2`, it is placed as `grh_extensions_2026-11-27_3`. Their content is
merged into the article next, after which these directories are removed like the earlier ones.

| Directory | Archive | Arrival | Wrapper | Members | Placed | Omitted | Title in the delivery README |
|---|---|---|---|---:|---:|---:|---|
| [dirichlet-sharp-window-transport](Research/dirichlet-sharp-window-transport/README.md) | `dirichlet-sharp-window-transport.zip` | `29ef78b839` | `sharp-window-transport` | 9 | 9 | 0 | Sharp-window transport of Dirichlet zeros |
| [euler_agreement_2026-11-27](Research/euler_agreement_2026-11-27/README.md) | `euler_agreement_2026-11-27.zip` | `29ef78b839` | `euler_agreement_2026-11-27` | 18 | 17 | 1 | Sharp Euler-factor agreement beyond prime exponent |
| [grh_extensions_2026-11-27_3](Research/grh_extensions_2026-11-27_3/README.md) | `grh_extensions_2026-11-27(2).zip` | `29ef78b839` | `grh_extensions` | 20 | 19 | 1 | Two extensions of the ProveIt GRH transfer program |
| [residue87_2026-11-27](Research/residue87_2026-11-27/README.md) | `residue87_2026-11-27.zip` | `29ef78b839` | none | 8 | 7 | 1 | Six-term exclusions at discriminant -87 |
| [sparse-padic-roots-and-graph-towers](Research/sparse-padic-roots-and-graph-towers/README.md) | `sparse-padic-roots-and-graph-towers.zip` | `29ef78b839` | none | 10 | 9 | 1 | Sparse p-adic polynomials and four-step graph towers |
| [symplectic_joint_observations_2026-11-27](Research/symplectic_joint_observations_2026-11-27/README.md) | `symplectic_joint_observations_2026-11-27.zip` | `29ef78b839` | `symplectic_joint_observations` | 23 | 22 | 1 | Hidden higher-order dependence in symplectic observations |
| [coupled-dirichlet-inverse-spectrum](Research/coupled-dirichlet-inverse-spectrum/README.md) | `coupled-dirichlet-inverse-spectrum.zip` | `556edb6bb4` | `coupled-dirichlet-inverse-spectrum` | 15 | 14 | 1 | Recovering the characters and the graph from a coupled Dirichlet spectrum |
| [dirichlet-coupled-zeros-and-prime-variances](Research/dirichlet-coupled-zeros-and-prime-variances/README.md) | `dirichlet-coupled-zeros-and-prime-variances.zip` | `556edb6bb4` | none | 13 | 13 | 0 | Inverse problems for Dirichlet zeros and prime variances |
| [grh_cayley_and_filters](Research/grh_cayley_and_filters/README.txt) | `grh_cayley_and_filters.zip` | `556edb6bb4` | none | 10 | 9 | 1 | TWO RESULTS FROM THE PROVEIT DIRICHLET GRH PROJECT |
| [padic-support-rank](Research/padic-support-rank/README.txt) | `padic-support-rank.zip` | `556edb6bb4` | none | 6 | 5 | 1 | Exact rank rule for sparse roots in closed p-adic disks. |
| [five_step_refinement_2026-11-27](Research/five_step_refinement_2026-11-27/README.md) | `five_step_refinement_2026-11-27.zip` | `7908088f6c` | none | 10 | 9 | 1 | A sharper five-step graph-tower bound |
| [grh_hidden_forms_and_filters_2026-11-27](Research/grh_hidden_forms_and_filters_2026-11-27/README.md) | `grh_hidden_forms_and_filters_2026-11-27.zip` | `7908088f6c` | `grh_hidden_forms_and_filters` | 33 | 26 | 7 | Two research extensions of the ProveIt GRH program |
| [spectral_extremes_2026-11-27](Research/spectral_extremes_2026-11-27/README.txt) | `spectral_extremes_2026-11-27.zip` | `7908088f6c` | `spectral_extremes_2026-11-27` | 29 | 28 | 1 | CONDITIONAL SPECTRAL EXTREMES AND A FUNCTIONAL BRIDGE |
| [symplectic_dependence_research_2026-11-27](Research/symplectic_dependence_research_2026-11-27/README.txt) | `symplectic_dependence_research_2026-11-27.zip` | `7908088f6c` | `symplectic_cycle_dependence_2026-11-27` | 39 | 38 | 1 | SYMPLECTIC DEPENDENCE: RESEARCH PAPERS AND REPRODUCIBLE ARTIFACTS |
| [gram-euler-and-zero-filters](Research/gram-euler-and-zero-filters/README.md) | `gram-euler-and-zero-filters.zip` | `f9f1016ec7` | none | 18 | 18 | 0 | Three extremal problems from the ProveIt Dirichlet GRH program |
| Total | 15 archives | | | 261 | 243 | 18 | |
