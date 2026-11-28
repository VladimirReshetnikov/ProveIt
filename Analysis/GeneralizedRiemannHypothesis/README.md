# Generalized Riemann Hypothesis

A research article on what lies beyond the generalized Riemann hypothesis for Dirichlet
L-functions, merged from 242 delivered research reports.

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

The reports were delivered as 242 archives from 25 to 27 November 2026: 61 to the
repository's [`docs/incoming`](../../docs/incoming/README.md) and 181 to this project's own
`docs/incoming`. Each was placed, unchanged and without verification, in a directory
`Research/<archive name>/`, with the archive's single wrapper directory removed and with
checksum manifests, files matched by `.gitignore` and copies of files of earlier packets left
out (`Research/OMITTED.tsv` listed them).

Once their content was merged into the article, the packets were removed from the working
tree. They remain in the history. The first two batches, with their `Research/OMITTED.tsv`,
are present at commit `10802a6b36`, the third batch at commit `f2f9fd7531`, the fourth at commit
`64f3896557`, the fifth at commit `fd9a9cb2bd`, the sixth at commit `f6b5955e13`, the seventh at commit
`7f951e1dfd`, the eighth at commit `3c4d27a69c` and the ninth at commit `2f9fb0b144`, each with its own
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
git show 2f9fb0b144:Analysis/GeneralizedRiemannHypothesis/Research/<packet>/<path>   # batch 9
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
| Ninth | 33 | `Analysis/GeneralizedRiemannHypothesis/docs/incoming` | `641cd62961` to `36ca617407` | `835c3695d0` |

By their own account, the reports start from `lsernau/grh-lean` and ask what its theorem
settles elsewhere and which methods inside its proof carry over to other problems. Several
packets contained excerpts of that development, under the Apache-2.0 licence. The excerpts
left with the packets. The [import record](vendor/grh-lean/README.md) identifies the
upstream revision used for [the local proof](Lean/grh/README.md).
