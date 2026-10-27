# Independent audit of the ratio-fused Cauchy refinement

**Verdict: PASS for the stated finite component scope.** This audit concerns a constant-factor refinement of an existing quadratic full-table algorithm. The late `sat_frontier_improvements` packet already contains the quadratic recurrence; that result is prior work, not novelty of this deliverable. The new refinement caches transition unit ratios and absorbs the common target prefactor into each target column's initial state.

No incoming archive code was executed or imported. The late `fast_cauchy.py` was read only as text. Its one-inversion preparation, two ring products per transition, and one product per target emission match the mathematical baseline used here. It contains neither the transition-ratio cache nor the globally absorbed target prefactor. This is a scoped comparison to the inspected implementation, not a claim of originality across all numerical software.

## Exactness and state handling

For a real column slot x=s_j and consecutive pivot gap g=s_(b+1)-s_b, put d=x-s_(b+1)>=0. The target transition is `(d+g)/(T+d)` and the source transition is `(-d-g)/(T-d)`. The only possible gaps are 1 and R+1, or just 2 when R=1. Factoring the numerator and denominator into an exact power of two and a unit permits the unit quotient to be cached. Each transition then adds the cached valuation change and performs one ring multiplication.

The target seed multiplies the prefactor's normalized residue by the normalized T once. Subsequent target states already include that residue, so target emission shifts by `pref_v+feature_v+E_b`, while source emission shifts by `feature_v-E_b`. Both are nonnegative by the inherited integral-feature property and the prefactor valuation bound. A state must not be assumed invertible: a zero prefactor creates zero target states. The implementation never inverts states; it only inverts the batched normalized denominator units.

The integer valuation is retained separately from the unit/state residue. A displayed low-precision source value may therefore be zero at one pivot and nonzero at the next without information loss. The explicit a=3,i=0,t=1,zeta=(1,0),p=1 regression verifies precisely that behavior. Exact prefactor zeros give identically zero targets and nontrivial sources without attempting zero normalization or nonunit inversion.

## Independent verification

`qa/fused_audit_checks.py` has a separately written exact Q(U) direct-product oracle; it imports neither the incoming program nor the authored checker's oracle. Its slot set is independently enumerated by the missing-bit condition. Rational coordinates must be integral at 2 before reduction, and full rational feature reconstruction is checked against the direct Cauchy kernel. The script uses explicit exceptions, so its tests remain active under `python -O`.

Final normal and optimized runs both passed with:

| Check | Count |
|---|---:|
| All-grid rational configurations, a=1 through 4 | 260 |
| Modular configurations, p=1,3,9,17 | 1,040 |
| Exact feature equalities | 86,800 |
| Exact rational reconstructed kernel entries | 10,898 |
| Zero-prefactor configurations | 208 |
| Exact setup/table/total count controls | 8,320 |
| Explicit zero-output then nonzero-output recovery | 1 |
| Large signed shift-coordinate configurations | 6 |
| Large-coordinate exact feature checks | 192 |
| Exact difference/gap-cache controls, a=1 through 6 | 21 |
| Mask/modulo reduction, addition and multiplication equalities | 1,260 |
| Mask/modulo shift equalities | 2,100 |
| Mask/modulo unit-inverse equalities | 332 |
| Nonunit rejections across the two backends | 224 |
| Batch/empty-batch controls | 12 |
| Negative-shift rejections | 12 |
| Backend operation-counter equivalence checks | 6 |
| Final benchmark records checked | 23 |
| Raw provenance-file hash checks / exact disjoint-union check | 2 / 1 |

Every valid nonzero grid t is tested, not only t=±2^i. The shift choices include non-prime-field extension residues, negative coordinates, zero shifts, and additional coordinates of 60–70 bits. The mask-versus-modulo tests use randomized negative and unreduced coordinates, with precisions 1,2,5,17,65,257, plus fixed nonunits. They independently verify that signed Python bit masking agrees with modular arithmetic and that unit inversion and failure behavior are preserved. The implemented algebra is the degree-two unramified ring `(Z/2^p Z)[U]/(U^2+U+1)`. This does not certify arbitrary extension degrees, arbitrary nilpotent tensor coordinates, or a complete SAT solver.

## Counts, overhead and baseline fairness

Let K be the signed difference-set size and g the number of possible gap types. K is odd and the nonnegative differences have cardinality (K+1)/2. Caching both signs gives exactly g(K+1) entries. This O(L) cache includes some unused combinations, all of whose preparation work is charged.

Both algorithms share identical preparation and exactly one unit inversion, including the scalar prefactor denominator in that batch. For a nonzero extension prefactor, the common counted initialization is `I=3K+2L+3`. Scalar denominator products and integer valuation/index arithmetic are additional shared work, not silently counted as ring products. The exact total ring-multiplication counts are:

- baseline: `I+(5N^2+N)/2`;
- fused: `I+g(K+1)+1+N^2+N`.

The fused extra `+1` is its target seed. The limiting counted multiplication ratio is 5/2. Both methods still require quadratic table work and dense output space; this is not an asymptotic-order improvement. Multiplication by a scalar unit and multiplication by a general extension element need not have equal bit cost, so a 5/2 counted-operation ratio is not itself a guaranteed wall-time ratio.

All O(L) preparation and both N-by-N outputs are included in each timed call. The benchmark uses the same ring backend and operation counters for both implementations, symmetric warmup, five alternating-order samples, and growing precision p=4N+16. The final shared `MaskRing` backend uses power-of-two bit masks for both algorithms, matching the late implementation's backend optimization rather than crediting it to fusion. The independently retained modulo-based `BasicRing` remains the arithmetic control. The comparison is to a self-authored operation-matched quadratic baseline, not direct timing of the incoming executable. No old cubic baseline is used for this new performance claim.

## Final benchmark and provenance

The authoritative file is `results/fused_cauchy_benchmark_mask_all.json`. It combines two disjoint full runs covering N=2..16 and N=32..256, rather than selecting favorable samples. The independent checker validates both raw source-file SHA-256 hashes, exact equality of the concatenated records (including every raw sample), uniqueness and completeness of the 23 fixture keys, five positive wall/CPU samples per method, their medians and ratios, one-inverse statistics, preparation/table/total counts, and p=4N+16. Every timed output was compared with the checked warmup outside the timed region.

The final wall-time speedup range is **0.441x–3.054x**, with **4 measured regressions** retained. The corresponding CPU range is 0.434x–3.072x. At N=256:

| i | Baseline/fused wall ratio | Baseline/fused CPU ratio |
|---|---:|---:|
| 0 | 1.724x | 1.717x |
| 4 | 2.294x | 2.303x |
| 8 | 1.457x | 1.435x |

Ratios below one mean the fused implementation was slower for that fixture. Extra cache setup and small-sample noise can dominate small tables. Earlier modulo-backend timings, including their regressions, are historical evidence and are not the final optimized-backend comparison.

All timing ratios are local Python component measurements **versus the matched authored one-inversion quadratic baseline**. They are not direct timing of the incoming executable, end-to-end SAT acceleration, memory savings, production-kernel throughput, universal speedups, or an improved leading SAT exponent. Partial-table and aggressively truncated low-precision workloads require separate comparisons. The full dense-output operation reduction remains valid independently of timing noise.

## Reproduction and final binding

```
python -B qa/fused_audit_checks.py
python -B -O qa/fused_audit_checks.py
```

An optional positional output-JSON path keeps sealed replay from overwriting packaged results. Final JSON and stdout logs are `qa/fused_audit_checks_{normal,optimized}.{json,log}`. Both runs bind the fused implementation, authored checker, benchmark script, independent base ring, final benchmark and raw provenance files by SHA-256. No incoming archive executable participates.

| Input | SHA-256 |
|---|---|
| `code/fused_cauchy.py` | `b1b470e701b84d9ed061e613054f3e6c765668cbfe37ab6d1b2034fdbeb8edcb` |
| `code/verify_fused_cauchy.py` | `d176ad901c3b76a0fe6bb63623fcec3141a5886b746ba5c1719ed5768f619948` |
| `code/benchmark_fused_cauchy.py` | `044b7e98ca70f84e8f27dc34366b453dd7244bfe8fc473f77d1aafedaa86fc57` |
| `code/cauchy_kernel.py` | `8d0179539269cea2fd27120bc9b6f73c5b3ec10d65121bb1d8308545138f9f59` |
| `results/fused_cauchy_benchmark_mask_all.json` | `df1ad84f5a3357bd25a98e358d11b00fb09504f0950762596e090d4d35b02c36` |
| `results/fused_cauchy_benchmark_mask_small.json` | `650c619ac608e29d0dcdc01595f5ff434e7a30ddac7bb0f1ab18e14f72087409` |
| `results/fused_cauchy_benchmark_mask.json` | `4416d99850b8ae40b562c66829d21b2ff2c96287e75d3f43e1ee5360fded7bec` |
