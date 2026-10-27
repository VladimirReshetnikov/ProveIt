# Audit of nine incoming SAT archives

Snapshot supplied by the root review: `73dfb5e5ab6e91bd7375e5b97ef85d7e1cc8e81d`.

The project README at this snapshot still summarizes 20 placed packets. The
nine incoming ZIPs therefore have to be read independently. The following are
their displayed claims, not independent certifications of every theorem.
All numerical contraction constants are on `s / sqrt(log2 s)` (or the
asymptotically identical ceiling-log scale), with general root degree at most
`s^(9/10)`, unless a lower-degree promise is stated.

| Incoming packet | Polynomial-space coefficient | Cached time / space | Other important claim |
|---|---:|---:|---|
| `3sat_round3_frontier_20261027` | 63.75735555 | 37.93010908 / 33.62304092 | Low-degree polynomial 23.66616881; low-degree cached 14.23918819 / 12.36130146 |
| `ETH_Adaptive_Exact_Kernels_2026-10-27` | 55.331622 | 35.0706136705 / 33.9995016442 | Degree at most s^.51 polynomial 25.163765; sparse scoring and fused Cauchy kernels |
| `eth_adaptive_schedules_2026-10-26` | 63.781173756244 | 37.591702555541 / 33.623040921657 | Incremental matching potential and exact common-denominator arithmetic |
| `sat_adaptive_bounds_2026-10-26` | **46.184845586731** | 34.325282797285 / 34.024178007491 | Complete binary linear flags; low-degree cached 13.379649066270 / 13.253024933008 |
| `sat_adaptive_frontier_2026-10-26` | 50.30468921409 | 31.252397312651 / 31.252397312651 | Joint adaptive cache evaluation; conserved degree flow does not close entry-cost interface |
| `sat_adaptive_matrix_partition_2026-10-26` | 50.210434836331 | 34.325282797285 / 34.024178007491 | Second-moment adaptive partitions and exact balanced-tree selection |
| `sat_adaptive_tree_certificate_2026-10-26` | — | **30.891018920366 / 30.753912832055** | Uniform mean of three plan support sets, schedule 9→13→7 |
| `subexponential_sat_adaptive_four_2026-10-26` | 50.393725700505 | 32.915813864924 / 31.661706786194 | Optional 19/8 backend: 32.856345276006 / 31.467483188098 |
| `subsat_rectangular_2026-10-26` | 53.9775311981 | 33.9938908592 / 33.9937208906 | Genuine rectangular backend, asymmetric Hermite minimax and inventory barriers |

All nine explicitly retain the worst-case SAT order
`n log log n / sqrt(log n)`. None closes the previous conditional
`n log log n / log n` interface. The strongest incoming polynomial-space
and cached claims are therefore respectively 46.184845586731 and
30.891018920366 / 30.753912832055, rather than the older placed 55.709 and
35.355 numbers. Low-degree cases and polynomial-space results cannot be
ranked interchangeably with the generic cached branch.

## Primary mathematical sources examined closely

- `sat_adaptive_bounds/.../report/flags.tex`: complete binary linear flags,
  common-origin intersection proof, sharp local balanced-tree norm, schedule.
- `sat_adaptive_tree_certificate/.../report.tex`, sections on operation
  supports, three-plan norm certificates and the paid 9→13→7 recursion.
- `subsat_rectangular/.../sections/rectangular.tex`: the exact rectangular
  field/ring bridge, including input/output work and endpoint slack.
- Placed `sat_adaptive_contraction/adaptive_sat_review.tex`: exact pair-list
  entropy, cached factor calls, streamed conditioning and canonical lifts.

The new adaptive rectangular method imports the same algebraic and counting
interfaces. Its exact convex-hull minimax formula is a new finite certificate
method relative to all 29 inspected packets. The affine-plane menu and the
explicit 10/12-group menus are independently checked constructions. The
finite local algebra and rational constants are certified; no independent
end-to-end verification of the upstream ETH claim is implied.
