# Frozen coordinated benchmark summary

Source: `work/fast/results/corridor_benchmark_20261008.json`.

Seven paired, shuffled rounds. Each implementation is warmed. Fixed per-arm repeated batches target 20 ms (cap 32), with equal repetition counts for the identical standard/control arms. Fresh scanner construction is included for actual scans and excluded for synthetic elimination kernels. Common diagram/order preparation and explicit verification are excluded. The garbage collector is collected before each measured batch, then stays enabled. Every scanner has a 30-second cooperative deadline.

No other team agent was intentionally running heavy CPU tools during this final run. Nonetheless identical-control ratios remain noisy. Small timing differences must not be presented as reliable gains. Earlier standalone actual/kernel files were exploratory and potentially affected by another short audit; the combined file is the final dataset.

## Actual knot diagrams

| Case | Standard ms | Full auto ms | Adaptive ms | Standard / auto | Standard / adaptive | A/A | Adaptive switches |
|---|---:|---:|---:|---:|---:|---:|---:|
| two_strand_201 | 124.044 | 1324.193 | 192.852 | 0.094 | 0.679 | 0.913 | 0 |
| torus_3_10 | 8.936 | 29.650 | 9.692 | 0.311 | 0.954 | 1.268 | 0 |
| alternating_3_4 | 5.059 | 14.435 | 4.705 | 0.367 | 1.141 | 1.009 | 0 |
| morton | 2.075 | 4.801 | 2.351 | 0.412 | 1.026 | 0.947 | 0 |
| conway | 5.828 | 17.704 | 6.937 | 0.319 | 0.864 | 0.878 | 0 |
| hard_unknot_8 | 1.195 | 2.796 | 1.335 | 0.475 | 0.934 | 0.938 | 0 |

Full corridor transfer is 2.1–10.7 times slower than ordinary sparse reduction on these cases. The adaptive mode supplies no reliable general improvement. This supports preserving the standard default. Every timed result agrees by homological degree.

## Homogeneous two-term kernels

| Family | Prior / auto | Standard / auto | A/A | Prior radical attempts | Auto radical attempts | Auto total propagations |
|---|---:|---:|---:|---:|---:|---:|
| source_heavy | 3.631 | 0.506 | 1.237 | 3940 | 307 | 421 |
| sink_heavy | 0.365 | 0.243 | 0.755 | 317 | 317 | 462 |
| balanced | 1.070 | 0.397 | 1.028 | 2142 | 2142 | 4256 |
| dead_branches | 9.690 | 1.346 | 0.849 | 72204 | 342 | 495 |
| shared_suffix_15 | 1.975 | 0.157 | 1.025 | 465 | 45 | 77 |
| shared_suffix_63 | 7.091 | 0.105 | 1.042 | 8001 | 189 | 317 |
| shared_suffix_255 | 28.409 | 0.098 | 0.822 | 130305 | 765 | 1277 |
| dead_leaves_255 | 0.498 | 0.120 | 1.399 | 256 | 1 | 3 |

The strict shared-suffix family has R=M odd, all scalar pivots equal to 1, and a nonzero three-dot output from every source. The old forward traversal performs R(1+2M) radical-edge product attempts. Reverse traversal performs R+2M. At 255 this is 130,305 versus 765, a deterministic factor of 170 1/3, while measured total reduction is about 28.4 times faster than the prior transfer. Ordinary sparse Markowitz reduction is still about ten times faster than the new full transfer on that case.

The dead-leaf family reduces radical attempts from 256 to 1, but total setup dominates and ordinary sparse elimination wins. The planted dense dead-branch case has a modest 1.35 ratio versus ordinary sparse reduction; that is too small relative to observed timing drift to make a strong practical speedup claim.

All prior and full corridor arms produce exactly the same minimal differential in the fixed binary-contraction basis, recorded by SHA-256. Sparse and adaptive arms can select a different homogeneous basis; their survivor multiplicities and the rank of the single top-monomial coefficient matrix agree independently. All planted two-term inputs were checked for homogeneity and square-zero before timing. They are valid category complexes, not asserted to be actual knot-scan stages.

## Interpretation

The proved advance is support-sensitive transfer and an exact choice between forward/reverse path evaluation. Scalar contraction, graph construction, reach masks and result assembly remain separate setup terms. Global packed object/endpoint masks can themselves consume quadratic bit volume on sparse families; the transfer edge bound does not remove that cost. A follow-up experiment will test sparse component setup and port-count selection.
