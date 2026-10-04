# Recorded benchmark summary

Times are seconds; medians of three fresh processes for completed cases.
A capped case has only one attempt and is a lower bound, not a runtime.
Inputs and imports are outside timing for both versions.

| Case | Operation | Baseline | Accelerated | Baseline / accelerated |
|---|---|---:|---:|---:|
| Conway (11 crossings) | scan | 0.0336674 | 0.0108186 | 3.11x |
| Conway (11 crossings) | pipeline | 0.03563 | 0.000915175 | 38.9x |
| Kinoshita--Terasaka (11) | scan | 0.0391302 | 0.0118891 | 3.29x |
| Kinoshita--Terasaka (11) | pipeline | 0.0392966 | 0.000886231 | 44.3x |
| Hard unknot (8) | scan | 0.0021391 | 0.00189777 | 1.13x |
| Hard unknot (8) | pipeline | 0.0016206 | 0.00181852 | 0.891x |
| Five-strand example (36) | scan | >20 (capped) | 1.28467 | >15.5x |
| Five-strand example (36) | pipeline | 0.00808199 | 0.00521673 | 1.55x |
| Unknot braid (40) | scan | 0.00858844 | 0.00400333 | 2.15x |
| Unknot braid (40) | pipeline | 0.00641076 | 0.00635306 | 1.01x |
| Torus knot T(3,5) (10) | scan | 0.0109729 | 0.0104668 | 1.05x |
| Torus knot T(3,5) (10) | pipeline | 0.000589676 | 0.000904148 | 0.652x |
| Two Conway summands (22) | forced-scan-pipeline | 1.42746 | 0.0109347 | 131x |
| Three Conway summands (33) | forced-scan-pipeline | >20 (capped) | 0.0121963 | >1.63e+03x |
| Unknot chain (64) | order | 0.0140004 | 0.00174923 | 8x |
| Unknot chain (256) | order | 0.217324 | 0.00720871 | 30.1x |
| Unknot chain (1024) | order | 3.41498 | 0.0328571 | 104x |

## Caveats

`scan` does not include preprocessing or filters. The 36-crossing case
is already cheap in the baseline default pipeline (its Alexander test
rejects it after reduction), so its backend improvement is not a
corresponding full-pipeline speedup. `forced-scan-pipeline` disables
Alexander and, for the new code, Jones; it isolates decomposition.
`order` measures only greedy scan ordering, not knot recognition.
A ratio below one is an observed regression on that case.

The `old-algebra-fill` ablation changes only pivot scheduling and uses
the baseline uncached algebra. It independently gives reduced rank
2949 for the 36-crossing case, agreeing with the optimized backend.
Neither benchmark agreement nor d-squared checks are formal verification.
