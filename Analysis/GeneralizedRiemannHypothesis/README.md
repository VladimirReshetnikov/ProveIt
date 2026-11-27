# Generalized Riemann Hypothesis

A research article on what lies beyond the generalized Riemann hypothesis for Dirichlet
L-functions, merged from 131 delivered research reports.

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

The reports were delivered as 131 archives from 25 to 27 November 2026: 61 to the
repository's [`docs/incoming`](../../docs/incoming/README.md) and 70 to this project's own
`docs/incoming`. Each was placed, unchanged and without verification, in a directory
`Research/<archive name>/`, with the archive's single wrapper directory removed and with
checksum manifests, files matched by `.gitignore` and copies of files of earlier packets left
out (`Research/OMITTED.tsv` listed them).

Once their content was merged into the article, the packets were removed from the working
tree. They remain in the history. The first two batches, with their `Research/OMITTED.tsv`,
are present at commit `10802a6b36`, the third batch at commit `f2f9fd7531` and the fourth at commit
`64f3896557`, each with its own `Research/OMITTED.tsv`; each is the last commit before the removal
of that batch. Packet names are
unique across the batches:

```
git show 10802a6b36:Analysis/GeneralizedRiemannHypothesis/Research/<packet>/<path>   # batches 1-2
git show f2f9fd7531:Analysis/GeneralizedRiemannHypothesis/Research/<packet>/<path>   # batch 3
git show 64f3896557:Analysis/GeneralizedRiemannHypothesis/Research/<packet>/<path>   # batch 4
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

By their own account, the reports start from `lsernau/grh-lean` and ask what its theorem
settles elsewhere and which methods inside its proof carry over to other problems. Several
packets contained excerpts of that development, under the Apache-2.0 licence. The excerpts
left with the packets; the whole `grh` directory, at the commit the reports pin, is in
[`vendor/grh-lean`](vendor/grh-lean/README.md).

## Reports placed and not yet merged

11 further archives arrived in `Analysis/GeneralizedRiemannHypothesis/docs/incoming` on
27 November 2026, in 6 arrival commits from `9ab4d2073b` to `edca076fde`. They are placed as before, one
directory per archive under `Research/`, and retired from the drop directory. Of their 166
members, 141 are placed and 25 are listed in [`Research/OMITTED.tsv`](Research/OMITTED.tsv):
9 matched by `.gitignore` and 16 files byte-identical to a file of an earlier packet
(upstream Lean excerpts), whose reference column gives a path under `Research/` at one of
the history commits `10802a6b36`, `f2f9fd7531` and `64f3896557`. One small `lean-toolchain`
file that equals an earlier one is kept. Their content is merged into the article next,
after which these directories are removed like the earlier ones.

| Directory | Archive | Arrival | Wrapper | Members | Placed | Omitted | Title in the delivery README |
|---|---|---|---|---:|---:|---:|---|
| [dirichlet-li-kernels](Research/dirichlet-li-kernels/README.md) | `dirichlet-li-kernels.zip` | `9ab4d2073b` | `dirichlet-li-kernels` | 12 | 11 | 1 | Dirichlet Li kernels |
| [dirichlet_zero_filters](Research/dirichlet_zero_filters/README.md) | `dirichlet_zero_filters.zip` | `a78e32fb7e` | `dirichlet_zero_filters` | 10 | 10 | 0 | The shortest positive average that cancels two Dirichlet zeros |
| [disjoint-prime-products](Research/disjoint-prime-products/README.md) | `disjoint-prime-products.zip` | `c0f2782360` | `disjoint-prime-products` | 9 | 9 | 0 | When do disjoint products of small primes cover every residue tuple? |
| [dirichlet-zero-multiplicity-and-reconstruction](Research/dirichlet-zero-multiplicity-and-reconstruction/README.md) | `dirichlet-zero-multiplicity-and-reconstruction.zip` | `2a9f8e3ee7` | none | 9 | 9 | 0 | Dirichlet zeros from prime sums |
| [grh_exact_extensions_2026-11-27](Research/grh_exact_extensions_2026-11-27/README.txt) | `grh_exact_extensions_2026-11-27.zip` | `2a9f8e3ee7` | `grh_exact_extensions` | 49 | 32 | 17 | EXACT EXTENSIONS OF THE GRH RESEARCH PROGRAMME |
| [grh_extensions_2026-11-27](Research/grh_extensions_2026-11-27/README.md) | `grh_extensions_2026-11-27.zip` | `2a9f8e3ee7` | `grh_extensions` | 19 | 17 | 2 | Two extensions of the ProveIt GRH development |
| [grh_path_rigidity_2026-11-27](Research/grh_path_rigidity_2026-11-27/README.txt) | `grh_path_rigidity_2026-11-27.zip` | `2a9f8e3ee7` | `grh_path_rigidity_2026-11-27` | 27 | 25 | 2 | ARITHMETIC HIDDEN IN SMALL JUMPS |
| [euler-packet-rigidity](Research/euler-packet-rigidity/README.txt) | `euler-packet-rigidity.zip` | `31f8087cd1` | `euler-packet-rigidity` | 11 | 11 | 0 | Rigidity and gaps in Euler-factor matching |
| [dirichlet-zero-recovery](Research/dirichlet-zero-recovery/README.md) | `dirichlet-zero-recovery.zip` | `edca076fde` | `dirichlet-zero-recovery` | 6 | 5 | 1 | When blurred Dirichlet zeros determine their sources |
| [odd-order-euler-factor-matching](Research/odd-order-euler-factor-matching/README.md) | `odd-order-euler-factor-matching.zip` | `edca076fde` | none | 6 | 5 | 1 | How often can two products of Dirichlet L-functions agree locally? |
| [odd_prime_order_euler_packets](Research/odd_prime_order_euler_packets/README.md) | `odd_prime_order_euler_packets.zip` | `edca076fde` | none | 8 | 7 | 1 | Sharp local agreement for products of odd-prime-order Dirichlet L-functions |
| Total | 11 archives | | | 166 | 141 | 25 | |
