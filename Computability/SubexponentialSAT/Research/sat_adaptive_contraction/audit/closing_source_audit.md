# Closing source audit: fifteenth packet and placement verification

**Closing repository pin:** `474ddba696a5d385c091c23fb2995f69edd13e00`.

This supplement updates the initial review at `ab2fbc9e03d5c3d0ad6dec8686960bfe498b0b06`. The final comparison corpus contains **15 refinement packets and two primary manuscripts**. It supersedes the earlier count of fourteen packets, while preserving that earlier audit as a chronological record.

## Changes since the initial snapshot

- `d098ba436b33df19365a44dd178694ff52845d19`: added the new archive `ETH_Matching_Packing_Thin_Gaps_2026-10-27.zip` to incoming, at 2026-10-26 19:00:24 Pacific.
- `6d3adc45061535ebe6fa7cd3d9b37dff7dcfc22a`: placed that archive and the seven already reviewed incoming archives into `Computability/SubexponentialSAT/Research`, at 2026-10-26 19:03:44 Pacific.
- The additional packet is now `Computability/SubexponentialSAT/Research/eth_matching_refinement/`.

No proposed improvement in the present work needs to be withdrawn or weakened because of the new packet.

## Additional packet: matching packing and thin precision gaps

I read its complete `report.tex`, `README.txt`, and mathematical implementation `code/refinement.py`, and inspected its file inventory and validation descriptions.

Its main theorem gives the normalized coefficient

`C_54 = (2*pi/ln 2) sqrt((40/3) log2 54)/(8/9)^(3/2)`

`     = 94.74820225953415...`

on the scale `s/sqrt(log2 s)`, for root wire count at most s. The more general stated interface multiplies this coefficient by the fixed root wire-budget constant C. The result retains polynomial space and assumes the unchanged deformation, Hermite, Cauchy-mode, and child-contraction framework.

The new ingredients of that packet are:

1. A matching-potential derandomization. Edge coloring separates a bipartite multigraph into matchings, and exact conditional expectation controls all ordered label-pair loads. Its sufficient packing scale is `D_arr*Delta*polylog(s)` rather than the old `D_arr^2*Delta` scale.
2. Thin additive precision gaps and a fully integral r=54 schedule, with a slowly varying inward retreat from the packing boundary.
3. Exact reference routines for the potential, graph labeling, logarithm intervals, integer budgets, Hermite precision, and colored weighted-partition counts.

The coefficient is the same value, up to displayed rounding, as the independently reviewed balanced-packing and high-moment packets. It is weaker than the asymmetric packet's displayed `76.90899495...` certificate and does not alter the stronger composable baseline established in this audit.

It explicitly claims **no improved unrestricted logarithmic order**, **no complete SAT solver**, and **no measured practical speedup**. It also explicitly declines numerical dominance over the separate Claude manuscript, whose matched constants are unspecified.

### Overlap check against the new contributions

The packet does not contain:

- uncached recursive conditioning of the exact-weight mode-pair graph;
- the ancestor-cut path accounting or the `v(16)=170` polynomial-space improvement;
- an adaptive partition of group vertices based on a fixed exact-weight array;
- a modular joint-Cauchy feature-table implementation, cached unit inverses, or streamed modular feature columns;
- a stronger full-orientation Cauchy basis than the already reviewed joint-Cauchy packet.

Its phrase “adaptive slack” concerns approaching a schedule's asymptotic packing boundary with logarithmic guard terms. That is prior scheduling work and should not be presented as a new general idea of the current report. It is distinct from choosing a mode-graph block partition adaptively from the weight array.

The only production mathematical module contains exact Fraction-based packing and scheduling routines and a one-dimensional weighted-tuple counting DP. It has no mode-graph contraction code and no finite-precision feature-preparation benchmark. The new result therefore leaves the current report's recursive-conditioning theorem, adaptive partition theorem, and independently measured modular-kernel improvement intact.

## Verification that the seven previously incoming packets were only relocated

I compared every `.tex`, `.py`, `.sh`, and `Makefile` source in the seven initially extracted archives with its closing filed path. Missing duplicated sources were matched to the updated `Research/OMITTED.tsv` using both the exact Git blob hash and byte count. The result is:

| Initially incoming packet | Filed source files, byte-identical | Recorded duplicate-source omissions | Mismatches or unexplained omissions |
|---|---:|---:|---:|
| `3sat_round2_refinement_20261027.zip` | 10 | 12 | 0 |
| `eth_asymmetric_packet_balancing_2026-10-26.zip` | 10 | 4 | 0 |
| `eth_balanced_packing_2026-10-26.zip` | 7 | 0 | 0 |
| `eth_high_moment_2026-10-26.zip` | 8 | 0 | 0 |
| `eth_joint_cauchy_2026-10-26.zip` | 9 | 0 | 0 |
| `eth_packet_refinement_2026-10-26.zip` | 8 | 2 | 0 |
| `eth_recursive_refinement_2026-10-26.zip` | 8 | 0 | 0 |
| **Total** | **60** | **18** | **0** |

Thus all **78** relevant TeX and executable-source members are accounted for. Omissions include byte-identical upstream sources and copies of earlier packet sources, all explicitly recorded by the placement ledger. This check concerns source identity; it is not a claim to have re-executed every imported program or verified every imported theorem.

The full per-file SHA-256, Git blob, byte count, relative path, and omission records are in `closing_packet_byte_audit.json`. New-packet source identities and claim status are in `closing_matching_packet_audit.json`.

## Final comparative conclusion

The fifteenth packet strengthens the provenance coverage without changing the established composed reference certificates. The present work may still compare its new polynomial-space and optional exponential-space certificates against those compatible combinations of the reviewed packets. This is not a proof of optimality over every possible composition or schedule. Its practical evidence remains specifically an improvement of the finite-precision Cauchy feature kernel, not a complete SAT runtime comparison.
