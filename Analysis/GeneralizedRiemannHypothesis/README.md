# Generalized Riemann Hypothesis

A research article on what lies beyond the generalized Riemann hypothesis for Dirichlet
L-functions, merged from 103 delivered research reports.

[`Article/article.pdf`](Article/article.pdf) states each result of the reports once, in the
strongest form they prove. Repeated material and results implied by stronger or more general
ones are left out, and the reports' many accounts of the upstream proof are replaced by one
section. The input theorem, RH and GRH for Dirichlet L-functions as stated in the external
Lean development [`lsernau/grh-lean`](https://github.com/lsernau/grh-lean) at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, is taken as given. The article is a merge, not a
review: its mathematics is that of the reports, nothing was recomputed, and nothing is
formalized here. Every result is marked as unconditional, as using Dirichlet GRH, or as a
reduction whose target estimate is open. The [article README](Article/README.md) lists its
sections.

## The reports

The reports were delivered as 103 archives on 25 and 26 November 2026: 61 to the repository's
[`docs/incoming`](../../docs/incoming/README.md) and 42 to this project's own
`docs/incoming`. Each was placed, unchanged and without verification, in a directory
`Research/<archive name>/`, with the archive's single wrapper directory removed and with
checksum manifests, files matched by `.gitignore` and copies of files of earlier packets left
out (`Research/OMITTED.tsv` listed them).

Once their content was merged into the article, the packets were removed from the working
tree. They remain in the history. All of them, with `Research/OMITTED.tsv`, are present at
commit `10802a6b36`, the last commit before their removal:

```
git show 10802a6b36:Analysis/GeneralizedRiemannHypothesis/Research/<packet>/<path>
git restore --source=10802a6b36 -- Analysis/GeneralizedRiemannHypothesis/Research
```

The article cites delivered certificates and data files by their path under `Research/`;
those paths refer to that commit. The [provenance tables](Article/provenance/README.md)
record, for every section of every report file, where its material went in the article and,
for each omitted result, the result that supersedes it.

| Batch | Archives | Drop directory | Arrival commits | Placement |
|---|---:|---|---|---|
| First | 61 | `docs/incoming` | `1e1728ad22` to `de7b92e9c3` | `21c0252ffe`, with copies of earlier packets removed in `0b53cb0257` |
| Second | 42 | `Analysis/GeneralizedRiemannHypothesis/docs/incoming` | `0b4d634fdb` to `2c45d19807` | `dedc2966ea` |

By their own account, the reports start from `lsernau/grh-lean` and ask what its theorem
settles elsewhere and which methods inside its proof carry over to other problems. Several
packets contained excerpts of that development, under the Apache-2.0 licence; none remain in
the working tree.

## Reports placed and not yet merged

17 further archives arrived in `Analysis/GeneralizedRiemannHypothesis/docs/incoming` on
26 November 2026, in 7 arrival commits from `54fb88e936` to `4dfb7aaf87`. They are placed as before, one
directory per archive under `Research/`, and retired from the drop directory. Of their 331
members, 300 are placed and 31 are listed in [`Research/OMITTED.tsv`](Research/OMITTED.tsv):
12 matched by `.gitignore`, 1 checksum manifest of the packet's own files
(`provenance/upstream_source_subset/subset_manifest.json` of
`dirichlet_zero_transport_2026-11-26`), and 18 files byte-identical to a file of an earlier
packet, whose reference column gives a path under `Research/` at commit `10802a6b36`. One small
`lean-toolchain` file that equals an earlier one is kept. Their content is merged into the
article next, after which these directories are removed like the earlier ones.

| Directory | Archive | Arrival | Wrapper | Members | Placed | Omitted | Title in the delivery README |
|---|---|---|---|---:|---:|---:|---|
| [dirichlet_prime_frequency_inverse](Research/dirichlet_prime_frequency_inverse/README.txt) | `dirichlet_prime_frequency_inverse.zip` | `54fb88e936` | `prime_frequency_inverse` | 7 | 7 | 0 | Hearing a differential operator and a conductor at one prime |
| [graph_coupled_zeros_2026-11-26](Research/graph_coupled_zeros_2026-11-26/README.txt) | `graph_coupled_zeros_2026-11-26.zip` | `54fb88e936` | `graph_coupled_zeros` | 29 | 28 | 1 | ELECTRICAL LAWS FOR GRAPH-COUPLED ZEROS |
| [robust_dirichlet_spectra_2026-11-26](Research/robust_dirichlet_spectra_2026-11-26/README.txt) | `robust_dirichlet_spectra_2026-11-26.zip` | `54fb88e936` | `robust_dirichlet_spectra` | 27 | 26 | 1 | ROBUST SPECTRAL IDENTIFICATION OF DIRICHLET CHARACTERS |
| [hermite_thresholds_and_quadratic_primes](Research/hermite_thresholds_and_quadratic_primes/README.md) | `hermite_thresholds_and_quadratic_primes.zip` | `e5a86180ee` | `hermite_thresholds` | 11 | 11 | 0 | Sharp parity bias for a missing Hamming ball |
| [ramified_branch_recovery](Research/ramified_branch_recovery/README.md) | `ramified_branch_recovery.zip` | `e5a86180ee` | `ramified_branch_recovery` | 26 | 25 | 1 | Exact error correction for ramified branch measurements |
| [prime_observations_and_progression_free_sets](Research/prime_observations_and_progression_free_sets/README.md) | `prime_observations_and_progression_free_sets.zip` | `041d803254` | `prime_observations_and_progression_free_sets` | 14 | 13 | 1 | Sparse prime observations and progression-free sets |
| [local_euler_recovery](Research/local_euler_recovery/README.md) | `local_euler_recovery.zip` | `f8cebeac18` | `local_euler_recovery` | 6 | 6 | 0 | Identifying Dirichlet characters from a short window of zeros |
| [squarefree_factorizations](Research/squarefree_factorizations/README.md) | `squarefree_factorizations.zip` | `f8cebeac18` | `squarefree_factorizations` | 11 | 10 | 1 | Simultaneous congruences for factors of a squarefree integer |
| [Gaussian_prime_races](Research/Gaussian_prime_races/README.md) | `Gaussian_prime_races.zip` | `e961346628` | `Gaussian_prime_races` | 23 | 22 | 1 | Gaussian prime races |
| [dirichlet_packet_reconstruction](Research/dirichlet_packet_reconstruction/README.md) | `dirichlet_packet_reconstruction.zip` | `e961346628` | `dirichlet_packet_reconstruction` | 15 | 14 | 1 | Dirichlet zero packets and quadratic Euler factors |
| [dirichlet_zero_transport_2026-11-26](Research/dirichlet_zero_transport_2026-11-26/README.txt) | `dirichlet_zero_transport_2026-11-26.zip` | `e961346628` | `dirichlet_zero_transport` | 37 | 32 | 5 | LOCAL CAUCHY LAWS AND INFINITE TRANSPORT OF DIRICHLET ZEROS |
| [logarithmic_dirichlet_zero_filters_2026-11-26](Research/logarithmic_dirichlet_zero_filters_2026-11-26/README.md) | `logarithmic_dirichlet_zero_filters_2026-11-26.zip` | `e961346628` | `logarithmic_dirichlet_zero_filters` | 44 | 28 | 16 | Positive averaging with logarithmic support at Dirichlet zeros |
| [symplectic_compression_2026-11-26](Research/symplectic_compression_2026-11-26/README.md) | `symplectic_compression_2026-11-26.zip` | `e961346628` | `symplectic_compression` | 39 | 38 | 1 | Exact symplectic compression laws |
| [translated_dirichlet_zero_divisors](Research/translated_dirichlet_zero_divisors/README.md) | `translated_dirichlet_zero_divisors.zip` | `e961346628` | `translated_dirichlet_zero_divisors` | 14 | 13 | 1 | Zeros and poles of translated Dirichlet L-functions |
| [dirichlet_low_zero_identification](Research/dirichlet_low_zero_identification/README.md) | `dirichlet_low_zero_identification.zip` | `12fe397b37` | `dirichlet_low_zero_identification` | 9 | 9 | 0 | Distinguishing Dirichlet characters from low zeros |
| [prime_endpoints_and_symplectic_compressions](Research/prime_endpoints_and_symplectic_compressions/README.md) | `prime_endpoints_and_symplectic_compressions.zip` | `12fe397b37` | none | 10 | 9 | 1 | Prime endpoint densities and finite symplectic compressions |
| [dirichlet_zeros_and_abelian_fields](Research/dirichlet_zeros_and_abelian_fields/README.md) | `dirichlet_zeros_and_abelian_fields.zip` | `4dfb7aaf87` | `dirichlet_zeros_and_abelian_fields` | 9 | 9 | 0 | Distinguishing Dirichlet characters and abelian number fields by low zeros |
| Total | 17 archives | | | 331 | 300 | 31 | |
