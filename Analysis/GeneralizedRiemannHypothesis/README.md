# Generalized Riemann Hypothesis

A research article on what lies beyond the generalized Riemann hypothesis for Dirichlet
L-functions, merged from 184 delivered research reports.

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

The reports were delivered as 184 archives from 25 to 27 November 2026: 61 to the
repository's [`docs/incoming`](../../docs/incoming/README.md) and 123 to this project's own
`docs/incoming`. Each was placed, unchanged and without verification, in a directory
`Research/<archive name>/`, with the archive's single wrapper directory removed and with
checksum manifests, files matched by `.gitignore` and copies of files of earlier packets left
out (`Research/OMITTED.tsv` listed them).

Once their content was merged into the article, the packets were removed from the working
tree. They remain in the history. The first two batches, with their `Research/OMITTED.tsv`,
are present at commit `10802a6b36`, the third batch at commit `f2f9fd7531`, the fourth at commit
`64f3896557`, the fifth at commit `fd9a9cb2bd` and the sixth at commit `f6b5955e13`, each with its own
`Research/OMITTED.tsv`; each is the last commit before the removal
of that batch. Packet names are
unique across the batches:

```
git show 10802a6b36:Analysis/GeneralizedRiemannHypothesis/Research/<packet>/<path>   # batches 1-2
git show f2f9fd7531:Analysis/GeneralizedRiemannHypothesis/Research/<packet>/<path>   # batch 3
git show 64f3896557:Analysis/GeneralizedRiemannHypothesis/Research/<packet>/<path>   # batch 4
git show fd9a9cb2bd:Analysis/GeneralizedRiemannHypothesis/Research/<packet>/<path>   # batch 5
git show f6b5955e13:Analysis/GeneralizedRiemannHypothesis/Research/<packet>/<path>   # batch 6
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

By their own account, the reports start from `lsernau/grh-lean` and ask what its theorem
settles elsewhere and which methods inside its proof carry over to other problems. Several
packets contained excerpts of that development, under the Apache-2.0 licence. The excerpts
left with the packets; the whole `grh` directory, at the commit the reports pin, is in
[`vendor/grh-lean`](vendor/grh-lean/README.md).

## Reports placed and not yet merged

10 further archives arrived in `Analysis/GeneralizedRiemannHypothesis/docs/incoming` on
27 November 2026, in 4 arrival commits from `8c6032a195` to `6d284fcf75`. They are placed as before, one
directory per archive under `Research/`, and retired from the drop directory. Of their 145
members, 136 are placed and the 9 matched by `.gitignore` are listed in
[`Research/OMITTED.tsv`](Research/OMITTED.tsv). No member is a checksum manifest of its own
packet or a copy of a file of an earlier packet. Their content is merged into the article
next, after which these directories are removed like the earlier ones.

| Directory | Archive | Arrival | Wrapper | Members | Placed | Omitted | Title in the delivery README |
|---|---|---|---|---:|---:|---:|---|
| [grh_quarter_density](Research/grh_quarter_density/README.md) | `grh_quarter_density.zip` | `8c6032a195` | `grh_quarter_density` | 9 | 9 | 0 | Exact quarter-density support for disjoint products of small primes |
| [grh_zero_filter_tradeoff](Research/grh_zero_filter_tradeoff/README.md) | `grh_zero_filter_tradeoff.zip` | `8c6032a195` | none | 7 | 6 | 1 | Positive filters for Dirichlet zeros |
| [prime_cubature_grh_2026-11-27](Research/prime_cubature_grh_2026-11-27/README.md) | `prime_cubature_grh_2026-11-27.zip` | `8c6032a195` | none | 9 | 9 | 0 | Exact prime cubature after adversarial erasures |
| [prime_legendre_codes_2026-11-27](Research/prime_legendre_codes_2026-11-27/README.md) | `prime_legendre_codes_2026-11-27.zip` | `8c6032a195` | none | 11 | 10 | 1 | Prime-labelled codes with two-sided Gilbert–Varshamov distances |
| [grh-two-open-questions](Research/grh-two-open-questions/README.md) | `grh-two-open-questions.zip` | `f04559d2e2` | none | 12 | 11 | 1 | Two open questions from the ProveIt GRH article |
| [dirichlet_li_recovery](Research/dirichlet_li_recovery/README.md) | `dirichlet_li_recovery.zip` | `089c6881ea` | `dirichlet_li_recovery` | 18 | 17 | 1 | Finite Li measurements and two further transfers |
| [gaussian-singular-moduli](Research/gaussian-singular-moduli/README.txt) | `gaussian-singular-moduli.zip` | `089c6881ea` | none | 7 | 6 | 1 | Sparse equations for Gaussian singular moduli |
| [grh_uniform_extensions_2026-11-27](Research/grh_uniform_extensions_2026-11-27/README.md) | `grh_uniform_extensions_2026-11-27.zip` | `6d284fcf75` | `grh_uniform_extensions_2026-11-27` | 20 | 18 | 2 | Two extensions of the ProveIt GRH research program |
| [rectangular_symplectic_blocks](Research/rectangular_symplectic_blocks/README.md) | `rectangular_symplectic_blocks.zip` | `6d284fcf75` | `rectangular_symplectic_blocks` | 32 | 31 | 1 | Uniform rank and joint-defect laws for rectangular symplectic blocks |
| [uniform_symplectic_blocks](Research/uniform_symplectic_blocks/README.md) | `uniform_symplectic_blocks.zip` | `6d284fcf75` | `uniform_symplectic_blocks` | 20 | 19 | 1 | Uniform rank blindness in rectangular symplectic blocks |
| Total | 10 archives | | | 145 | 136 | 9 | |
