# Generalized Riemann Hypothesis

A research article on what lies beyond the generalized Riemann hypothesis for Dirichlet
L-functions, merged from 120 delivered research reports.

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

The reports were delivered as 120 archives on 25 and 26 November 2026: 61 to the repository's
[`docs/incoming`](../../docs/incoming/README.md) and 59 to this project's own
`docs/incoming`. Each was placed, unchanged and without verification, in a directory
`Research/<archive name>/`, with the archive's single wrapper directory removed and with
checksum manifests, files matched by `.gitignore` and copies of files of earlier packets left
out (`Research/OMITTED.tsv` listed them).

Once their content was merged into the article, the packets were removed from the working
tree. They remain in the history. The first two batches, with their `Research/OMITTED.tsv`,
are present at commit `10802a6b36`, and the third batch, with its own `Research/OMITTED.tsv`, at
commit `f2f9fd7531`; each is the last commit before the removal of that batch. Packet names are
unique across the batches:

```
git show 10802a6b36:Analysis/GeneralizedRiemannHypothesis/Research/<packet>/<path>   # batches 1-2
git show f2f9fd7531:Analysis/GeneralizedRiemannHypothesis/Research/<packet>/<path>   # batch 3
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

By their own account, the reports start from `lsernau/grh-lean` and ask what its theorem
settles elsewhere and which methods inside its proof carry over to other problems. Several
packets contained excerpts of that development, under the Apache-2.0 licence. The excerpts
left with the packets; the whole `grh` directory, at the commit the reports pin, is in
[`vendor/grh-lean`](vendor/grh-lean/README.md).

## Reports placed and not yet merged

11 further archives arrived in `Analysis/GeneralizedRiemannHypothesis/docs/incoming` on
26 and 27 November 2026, in 5 arrival commits from `22e5c8b7dd` to `42bca35561`. They are placed as before,
one directory per archive under `Research/`, and retired from the drop directory. Of their
179 members, 168 are placed and 11 are listed in [`Research/OMITTED.tsv`](Research/OMITTED.tsv):
10 matched by `.gitignore` and 1 checksum manifest of the packet's own files
(`MANIFEST.sha256` of `nondegenerate_symplectic_blocks_2026-11-27`). No file duplicates a
file of an earlier packet. `symplectic_compression_2026-11-26 (2).zip` differs from the
archive of the third batch with the same stem and is placed as
`symplectic_compression_2026-11-26_2`. Their content is merged into the article next, after
which these directories are removed like the earlier ones.

| Directory | Archive | Arrival | Wrapper | Members | Placed | Omitted | Title in the delivery README |
|---|---|---|---|---:|---:|---:|---|
| [exact_symplectic_compressions_2026-11-26](Research/exact_symplectic_compressions_2026-11-26/README.md) | `exact_symplectic_compressions_2026-11-26.zip` | `22e5c8b7dd` | `exact_symplectic_compressions` | 18 | 17 | 1 | Exact laws and hidden dependence in arbitrary symplectic compressions |
| [padic_symplectic_corners](Research/padic_symplectic_corners/README.md) | `padic_symplectic_corners.zip` | `22e5c8b7dd` | `padic_symplectic_corners` | 29 | 25 | 4 | Exact p-adic symplectic corner laws |
| [symplectic_compression_2026-11-26_2](Research/symplectic_compression_2026-11-26_2/README.md) | `symplectic_compression_2026-11-26 (2).zip` | `22e5c8b7dd` | `symplectic_compression` | 17 | 16 | 1 | Exact laws for arbitrary symplectic compressions |
| [dirichlet_zero_windows](Research/dirichlet_zero_windows/README.txt) | `dirichlet_zero_windows.zip` | `f34b73cf0f` | none | 5 | 5 | 0 | Identifying Dirichlet characters from short windows of zeros |
| [dirichlet_li_heat_kernel](Research/dirichlet_li_heat_kernel/README.txt) | `dirichlet_li_heat_kernel.zip` | `dec3e4f216` | `dirichlet_li_heat_kernel` | 7 | 7 | 0 | Dirichlet characters from a single Li heat kernel |
| [dirichlet-character-zero-windows](Research/dirichlet-character-zero-windows/README.md) | `dirichlet-character-zero-windows.zip` | `b6253012cf` | `dirichlet-character-zero-windows` | 7 | 7 | 0 | Identifying a primitive Dirichlet character from a short window of zeros |
| [dirichlet-zero-reconstruction](Research/dirichlet-zero-reconstruction/README.md) | `dirichlet-zero-reconstruction.zip` | `b6253012cf` | `dirichlet-zero-reconstruction` | 14 | 14 | 0 | Recovering Dirichlet characters and twist packets from zeros |
| [grh_sharp_extensions_2026-11-27](Research/grh_sharp_extensions_2026-11-27/README.md) | `grh_sharp_extensions_2026-11-27.zip` | `b6253012cf` | `grh_sharp_extensions_2026-11-27` | 26 | 25 | 1 | Sharp congruence bounds and finite prime sampling |
| [dirichlet-zero-windows](Research/dirichlet-zero-windows/README.md) | `dirichlet-zero-windows.zip` | `42bca35561` | `dirichlet-zero-windows` | 7 | 7 | 0 | Identifying abelian number fields from a short interval of zeta zeros |
| [grh_positive_spectral_extensions_2026-11-27](Research/grh_positive_spectral_extensions_2026-11-27/README.md) | `grh_positive_spectral_extensions_2026-11-27.zip` | `42bca35561` | `grh_positive_spectral_extensions_2026-11-27` | 25 | 23 | 2 | Positive prime signals and optimal zero cancellation |
| [nondegenerate_symplectic_blocks_2026-11-27](Research/nondegenerate_symplectic_blocks_2026-11-27/README.md) | `nondegenerate_symplectic_blocks_2026-11-27.zip` | `42bca35561` | `nondegenerate_symplectic_blocks` | 24 | 22 | 2 | Nondegenerate symplectic blocks |
| Total | 11 archives | | | 179 | 168 | 11 | |
