# Targeted compressed-setup benchmark

Source: `work/fast/results/compressed_corridor_20261008.json`.

Seven paired rounds with six arms. The comparison keeps the former corridor implementation frozen, and adds only port-count/Boolean selection and sparse scalar support. The same batching, fresh-state, resource, and garbage-collection controls as the earlier full matrix were used. Other team CPU work was paused. All actual homological and quantum ranks agree; all planted survivor counts and nonzero top-monomial coefficient ranks agree.

| Case | Standard ms | Frozen auto ms | Compressed ms | Auto / compressed | Standard / compressed | A/A |
|---|---:|---:|---:|---:|---:|---:|
| two_strand_201 | 132.338 | 1269.243 | 1448.700 | 0.803 | 0.091 | 1.087 |
| conway | 7.702 | 20.762 | 26.421 | 0.804 | 0.292 | 1.110 |
| hard_unknot_8 | 1.260 | 2.746 | 2.866 | 0.934 | 0.441 | 0.795 |
| shared_suffix_15 | 0.076 | 0.562 | 0.423 | 1.250 | 0.174 | 1.191 |
| shared_suffix_63 | 0.204 | 1.672 | 1.422 | 1.202 | 0.132 | 1.056 |
| shared_suffix_255 | 0.855 | 7.847 | 8.178 | 0.871 | 0.101 | 1.011 |
| dead_leaves_255 | 0.306 | 2.663 | 2.392 | 1.113 | 0.154 | 0.997 |

There is no reliable timing improvement from compressed setup at these tested sizes. It is slower on all three actual examples and on the largest strict shared-suffix instance, and the small apparent gains elsewhere are comparable to identical-control drift. Ordinary sparse reduction remains substantially faster. The reason for retaining the optional compressed representation is the exact support-size and complete-stage complexity theorem, not these local timings.

The strict R=M=255 case uses 512 scalar components, all singletons or scalar pairs, with 768 total nonzero i/p/h indices and no nontrivial local binary block. The inherited global-mask bit length is 164,735; this is a representation-size statistic, not a measurement of Python object memory. With fixed algebra size the sparse-component/Boolean/port-count implementation has an O((R+M) log(R+M)) complete-stage word bound. The forward path evaluation alone needs R(1+2M) radical attempts. This family-level separation is independent of a practical win over sparse Markowitz cancellation, which already handles this family well.

The current module hash, frozen corridor hash, full raw timing batches, chosen repetitions, and all counters are recorded in the JSON. The earlier combined nine-arm data remain unchanged.
