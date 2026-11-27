# Generalized Riemann Hypothesis

A research article on what lies beyond the generalized Riemann hypothesis for Dirichlet
L-functions, merged from 142 delivered research reports.

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

The reports were delivered as 142 archives from 25 to 27 November 2026: 61 to the
repository's [`docs/incoming`](../../docs/incoming/README.md) and 81 to this project's own
`docs/incoming`. Each was placed, unchanged and without verification, in a directory
`Research/<archive name>/`, with the archive's single wrapper directory removed and with
checksum manifests, files matched by `.gitignore` and copies of files of earlier packets left
out (`Research/OMITTED.tsv` listed them).

Once their content was merged into the article, the packets were removed from the working
tree. They remain in the history. The first two batches, with their `Research/OMITTED.tsv`,
are present at commit `10802a6b36`, the third batch at commit `f2f9fd7531`, the fourth at commit
`64f3896557` and the fifth at commit `fd9a9cb2bd`, each with its own `Research/OMITTED.tsv`; each is the last commit before the removal
of that batch. Packet names are
unique across the batches:

```
git show 10802a6b36:Analysis/GeneralizedRiemannHypothesis/Research/<packet>/<path>   # batches 1-2
git show f2f9fd7531:Analysis/GeneralizedRiemannHypothesis/Research/<packet>/<path>   # batch 3
git show 64f3896557:Analysis/GeneralizedRiemannHypothesis/Research/<packet>/<path>   # batch 4
git show fd9a9cb2bd:Analysis/GeneralizedRiemannHypothesis/Research/<packet>/<path>   # batch 5
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

By their own account, the reports start from `lsernau/grh-lean` and ask what its theorem
settles elsewhere and which methods inside its proof carry over to other problems. Several
packets contained excerpts of that development, under the Apache-2.0 licence. The excerpts
left with the packets; the whole `grh` directory, at the commit the reports pin, is in
[`vendor/grh-lean`](vendor/grh-lean/README.md).

## Reports placed and not yet merged

42 further archives arrived in `Analysis/GeneralizedRiemannHypothesis/docs/incoming` on
25 to 27 November 2026, in 5 arrival commits from `a4404ca024` to `05f6dcb1f6`. They are placed as before, one
directory per archive under `Research/`, and retired from the drop directory. Of their 375
members, 338 are placed and 37 are listed in [`Research/OMITTED.tsv`](Research/OMITTED.tsv):
36 matched by `.gitignore` and 1 file byte-identical to a file of an earlier packet of
this batch. The archives named `... (2).zip` differ from their namesakes and are placed
with the suffix `_2`. Their content is merged into the article next, after which these
directories are removed like the earlier ones.

| Directory | Archive | Arrival | Wrapper | Members | Placed | Omitted | Title in the delivery README |
|---|---|---|---|---:|---:|---:|---|
| [cubic_quintic_euler_agreement](Research/cubic_quintic_euler_agreement/README.md) | `cubic_quintic_euler_agreement.zip` | `a4404ca024` | none | 5 | 5 | 0 | Sharp Euler-factor agreement for cubic and quintic character packets |
| [dirichlet_spectral_conditioning_2026-11-27](Research/dirichlet_spectral_conditioning_2026-11-27/README.md) | `dirichlet_spectral_conditioning_2026-11-27.zip` | `a4404ca024` | `dirichlet_spectral_conditioning_2026-11-27` | 28 | 26 | 2 | Sharp conditional gamma limits for reciprocal completed L-functions |
| [five_step_graph_towers_2026-11-26](Research/five_step_graph_towers_2026-11-26/README.md) | `five_step_graph_towers_2026-11-26.zip` | `a4404ca024` | none | 6 | 5 | 1 | Five-step spanning-tree divisibility |
| [five_step_sharpness_2026-11-27](Research/five_step_sharpness_2026-11-27/README.md) | `five_step_sharpness_2026-11-27.zip` | `a4404ca024` | none | 9 | 7 | 2 | The five-step sharpness classification |
| [gamma-euler-quartic](Research/gamma-euler-quartic/README.txt) | `gamma-euler-quartic.zip` | `a4404ca024` | none | 6 | 5 | 1 | A fourth-order certificate for the original finite Euler Gamma sampler. |
| [grh-moving-zero-windows](Research/grh-moving-zero-windows/README.txt) | `grh-moving-zero-windows.zip` | `a4404ca024` | none | 5 | 4 | 1 | GRH transfer supplement, 26 November 2026 |
| [grh_cubic_matching_and_precision_2026-11-27](Research/grh_cubic_matching_and_precision_2026-11-27/README.md) | `grh_cubic_matching_and_precision_2026-11-27.zip` | `a4404ca024` | `grh_cubic_matching_and_precision` | 37 | 35 | 2 | Exact Cubic Euler-Factor Matching and Optimal Unequal-Precision Recovery |
| [grh_extensions_2026-11-27_2](Research/grh_extensions_2026-11-27_2/README.txt) | `grh_extensions_2026-11-27 (2).zip` | `a4404ca024` | `grh_extensions` | 22 | 21 | 1 | UNEQUAL BRANCH DATA AND RESONANT ZERO FILTERS |
| [hermite_threshold_research](Research/hermite_threshold_research/README.md) | `hermite_threshold_research.zip` | `a4404ca024` | none | 6 | 6 | 0 | Sharp Hermite-threshold constants |
| [odd_prime_euler_agreement](Research/odd_prime_euler_agreement/README.md) | `odd_prime_euler_agreement.zip` | `a4404ca024` | `odd_prime_euler_agreement` | 9 | 9 | 0 | Sharp Euler-factor agreement at odd prime exponent |
| [padic-fewnomial-root-count](Research/padic-fewnomial-root-count/README.txt) | `padic-fewnomial-root-count.zip` | `a4404ca024` | none | 6 | 5 | 1 | Exact root counts for two to five terms in deep p-adic disks. |
| [padic-six-term](Research/padic-six-term/README.txt) | `padic-six-term.zip` | `a4404ca024` | none | 8 | 7 | 1 | Exact p-adic root counts for six terms. |
| [seven_step_graph_towers_2026-11-27](Research/seven_step_graph_towers_2026-11-27/README.md) | `seven_step_graph_towers_2026-11-27.zip` | `a4404ca024` | none | 9 | 8 | 1 | Seven-step graph towers and the prime-step obstruction |
| [short_tower_distributions_2026-11-27](Research/short_tower_distributions_2026-11-27/README.md) | `short_tower_distributions_2026-11-27.zip` | `a4404ca024` | none | 6 | 5 | 1 | Three- and four-step graph towers |
| [singular-modulus-support](Research/singular-modulus-support/README.txt) | `singular-modulus-support.zip` | `a4404ca024` | none | 9 | 8 | 1 | Seven terms are necessary at discriminant -152 |
| [singular_moduli_seven_terms_2026-11-26](Research/singular_moduli_seven_terms_2026-11-26/README.md) | `singular_moduli_seven_terms_2026-11-26.zip` | `a4404ca024` | none | 7 | 6 | 1 | Seven terms for ten singular moduli |
| [spanning-tree-sharp-cutoff](Research/spanning-tree-sharp-cutoff/README.txt) | `spanning-tree-sharp-cutoff.zip` | `a4404ca024` | none | 6 | 5 | 1 | A sharp residue cutoff for spanning trees in abelian Cayley towers |
| [spanning-tree-unit-stabilization](Research/spanning-tree-unit-stabilization/README.txt) | `spanning-tree-unit-stabilization.zip` | `a4404ca024` | none | 6 | 5 | 1 | Sharp stabilization of the prime-to-p part of spanning-tree counts |
| [grh_entropy_products_2026-11-27](Research/grh_entropy_products_2026-11-27/README.md) | `grh_entropy_products_2026-11-27.zip` | `ef14477a84` | `grh_entropy_products` | 8 | 8 | 0 | Robust entropy-scale prime products |
| [grh_inverse_spectral_2026-11-27](Research/grh_inverse_spectral_2026-11-27/README.md) | `grh_inverse_spectral_2026-11-27.zip` | `ef14477a84` | `grh_inverse_spectral_2026-11-27` | 7 | 6 | 1 | Inverse spectral rigidity for Dirichlet L-functions |
| [odd_prime_euler_agreement_2](Research/odd_prime_euler_agreement_2/README.md) | `odd_prime_euler_agreement (2).zip` | `ef14477a84` | `odd_prime_euler_agreement` | 6 | 6 | 0 | Sharp Euler-factor agreement for odd-prime-order Dirichlet characters |
| [optimal_zero_filters](Research/optimal_zero_filters/README.md) | `optimal_zero_filters.zip` | `ef14477a84` | `optimal_zero_filters` | 5 | 5 | 0 | Shortest robust positive filters for Dirichlet zeros |
| [prime_order_euler_agreement](Research/prime_order_euler_agreement/README.md) | `prime_order_euler_agreement.zip` | `ef14477a84` | `prime_order_euler_agreement` | 6 | 6 | 0 | Sharp Euler-factor agreement for prime-order Dirichlet character packets |
| [sharp_zeta_filters](Research/sharp_zeta_filters/README.md) | `sharp_zeta_filters.zip` | `ef14477a84` | `sharp_zeta_filters` | 9 | 9 | 0 | Sharp logarithmic support for positive Riemann-zero filters |
| [entropy_optimal_prime_factorizations_2026-11-27](Research/entropy_optimal_prime_factorizations_2026-11-27/README.md) | `entropy_optimal_prime_factorizations_2026-11-27.zip` | `612d1f9217` | none | 8 | 6 | 2 | Entropy-optimal simultaneous factorizations into distinct small primes |
| [grh_prime_fingerprints_2026-11-27](Research/grh_prime_fingerprints_2026-11-27/README.md) | `grh_prime_fingerprints_2026-11-27.zip` | `612d1f9217` | none | 7 | 6 | 1 | Universal prime fingerprints at list-decoding capacity |
| [grh_ritz_relative_asymptotics](Research/grh_ritz_relative_asymptotics/README.md) | `grh_ritz_relative_asymptotics.zip` | `612d1f9217` | `grh_ritz_relative_asymptotics` | 13 | 9 | 4 | Exact relative error laws for Li moment pencils |
| [odd_prime_euler_packets](Research/odd_prime_euler_packets/README.md) | `odd_prime_euler_packets.zip` | `612d1f9217` | none | 7 | 7 | 0 | Odd-prime Euler-factor packets: a partial solution of the article's open question |
| [prime_sparse_recovery_2026-11-27](Research/prime_sparse_recovery_2026-11-27/README.md) | `prime_sparse_recovery_2026-11-27.zip` | `612d1f9217` | `prime_sparse_recovery` | 10 | 10 | 0 | Error-correcting prime samples for sparse Dirichlet character mixtures |
| [sharp_positive_zero_filters](Research/sharp_positive_zero_filters/README.md) | `sharp_positive_zero_filters.zip` | `612d1f9217` | none | 9 | 8 | 1 | Sharp positive zero-cancelling filters |
| [grh_fixed_cardinality_torsion](Research/grh_fixed_cardinality_torsion/README.md) | `grh_fixed_cardinality_torsion.zip` | `ec99bc9e22` | none | 6 | 5 | 1 | Fixed-cardinality torsion specialization |
| [grh_growing_factorizations](Research/grh_growing_factorizations/README.md) | `grh_growing_factorizations.zip` | `ec99bc9e22` | `grh_growing_factorizations` | 8 | 7 | 1 | Small-prime factorizations at arbitrary retained density |
| [grh_prime_routing_2026-11-27](Research/grh_prime_routing_2026-11-27/README.md) | `grh_prime_routing_2026-11-27.zip` | `ec99bc9e22` | none | 9 | 7 | 2 | Locally resilient rainbow routing with small prime multipliers |
| [optimal_dirichlet_zero_filters](Research/optimal_dirichlet_zero_filters/README.md) | `optimal_dirichlet_zero_filters.zip` | `ec99bc9e22` | none | 6 | 6 | 0 | Optimal positive filters for clusters of Dirichlet zero frequencies |
| [prime_character_codes_2026-11-27](Research/prime_character_codes_2026-11-27/README.md) | `prime_character_codes_2026-11-27.zip` | `ec99bc9e22` | none | 8 | 7 | 1 | Sparse Dirichlet mixtures as error-correcting codes |
| [prime_exponent_euler_agreement](Research/prime_exponent_euler_agreement/README.md) | `prime_exponent_euler_agreement.zip` | `ec99bc9e22` | none | 6 | 6 | 0 | Sharp Euler-factor agreement for prime-exponent Dirichlet packets |
| [grh_global_positive_filters_2026-11-27](Research/grh_global_positive_filters_2026-11-27/README.md) | `grh_global_positive_filters_2026-11-27.zip` | `05f6dcb1f6` | none | 7 | 6 | 1 | Positive filters for the full Dirichlet zero spectrum |
| [grh_optimal_positive_filters](Research/grh_optimal_positive_filters/README.md) | `grh_optimal_positive_filters.zip` | `05f6dcb1f6` | none | 7 | 6 | 1 | Optimal logarithmic support for positive Dirichlet zero filters |
| [grh_quadratic_fibre](Research/grh_quadratic_fibre/README.md) | `grh_quadratic_fibre.zip` | `05f6dcb1f6` | none | 9 | 8 | 1 | The quadratic-fibre transition for squarefree products of small primes |
| [odd_euler_agreement](Research/odd_euler_agreement/README.md) | `odd_euler_agreement.zip` | `05f6dcb1f6` | none | 8 | 7 | 1 | Sharp Euler-factor agreement for cubic and quintic Dirichlet packets |
| [prime_sparse_recovery_2026-11-27_2](Research/prime_sparse_recovery_2026-11-27_2/README.md) | `prime_sparse_recovery_2026-11-27 (2).zip` | `05f6dcb1f6` | none | 10 | 9 | 1 | Sharp error correction for sparse Dirichlet spectra from small primes |
| [sharp_zero_filters](Research/sharp_zero_filters/README.md) | `sharp_zero_filters.zip` | `05f6dcb1f6` | `sharp_zero_filters` | 6 | 6 | 0 | Sharp support constants for positive filters of Riemann and Dirichlet beta zeros |
| Total | 42 archives | | | 375 | 338 | 37 | |
