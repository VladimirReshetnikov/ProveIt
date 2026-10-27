# Independent audit of the new performance kernels

**Late-cutoff scope correction:** This earlier audit establishes component correctness and comparisons to the earlier supplied formulas, not novelty against all late-arriving sources. The quadratic Cauchy recurrence was subsequently found in prior work. The final ratio-fused refinement is audited separately in `qa/fused_audit.md`.

**Historical binding note:** References below to a final ten-file freeze describe the pre-late audit checkpoint, not the complete later release. The final archive manifest and separate fused audit identify the additional files and revised benchmark backend.

**Verdict: PASS for the stated finite component scope.** No correctness defect was found in the sparse-delta conditional-expectation algorithm or the full-table consecutive-pivot Cauchy recurrence. Both are meaningful improvements over the inspected formulas without crediting common preprocessing improvements to the new algorithms. This is not a full SAT implementation, a formal proof verification, or certification of the inherited ETH claim.

## Evidence and execution boundary

The reviewer inspected the six newly authored files in `code/`, the new proof/review notes, and the incoming `balanced_packing.py` and `joint_cauchy.py` **as text only**. No incoming program was imported or executed. The independent checker `qa/performance_audit_checks.py` imports only the newly authored `sparse_balancing` and `cauchy_kernel` modules; its exact rational oracles are separately written. It uses explicit exceptions, not Python `assert`, so optimization cannot silently remove its tests.

Both commands completed successfully after the final packaging freeze against the same final source and benchmark hashes:

```
python qa/performance_audit_checks.py
python -O qa/performance_audit_checks.py
```

Run from the bundle root, or use their full paths. Final results and full stdout are preserved in `performance_audit_checks_{normal,optimized}.{json,log}`. The final checker binds all ten Python files in `code/` and both authoritative benchmark files by SHA-256. The two kernels are byte-identical to the original audited versions; later changes only expanded benchmark fixtures, routed check outputs, and added packaging/comparison utilities. Utility-file hashes identify the final release inputs, not an independent certification of every utility or theorem. Earlier six-file snapshots and the intermediate metadata refresh are retained in `qa/prepackaging/`. Repeated runs do not multiply the independent coverage counts. Each final run established:

| Independent check | Count |
|---|---:|
| Three-method exact packing configurations | 760 |
| Checked/counted versus unchecked/uncounted equivalence controls | 2,280 |
| Brute-force completion configurations / conditional steps | 90 / 252 |
| Exact rational Cauchy configurations | 260 |
| Modular Cauchy configurations | 1,040 |
| Exact modular feature equalities | 86,800 |
| Exact rational reconstructed kernel entries | 10,850 |
| Zero-prefactor controls | 208 |
| Exact operation-count controls | 2,080 |
| Extension-ring unit inverse controls / nonunit rejections | 224 / 16 |
| Final frozen benchmark records checked for samples, medians and ratios | 31 |

Packing coverage includes all binary 2-by-3 matrices, deterministic random weighted inputs, empty matrices and zero-column shapes, empty columns, label counts 1, 2, 3, 6, two smoothness values, nontrivial multiplicities, and an explicit repeated-column tie cycle. Cauchy coverage includes **every valid nonzero interpolation-grid t** for a=1 through 4, five shifts (including negative coordinates and non-prime-field residues), and precisions 1, 3, 9, 17. The supplied authored suites additionally exercise larger tables, 32-bit and growing precisions, further shifts, and invalid inputs.

## Packing exactness and edge cases

Let `w[a,j]` be the aggregated multiplicity, `l[a,b]` the current load, and `F'[a]` the remaining future factor after the current column is removed. Expanding the candidate score gives a label-independent part plus

`delta[b] = sum_active_a F'[a] (q^w[a,j]-1) (q^l[a,b]-1)`.

Averaging the exact candidate scores yields the current potential `P`. Hence the update and reconstructed score are exactly

`P_next(b) = P + delta[b] - sum_c delta[c]/Q`.

All dictionary contributions are strictly positive because `q>1`, active multiplicities are positive, and stored cells have positive load. Therefore a missing dictionary key really means zero and beats every present key. Choosing the smallest missing label, or the least label among dictionary minima when every label is present, preserves the reference's lexicographic minimizer. The independent completion oracle verifies the individual scores, not merely agreement among implementations using the same update.

Empty input has potential `Q^2`. A column with no incident edges leaves the potential unchanged and chooses label zero. `Q=1` is valid. Parallel edges are aggregated as multiplicities of whole vertices; no unjustified independence of individual parallel edges is introduced. `count=False` only suppresses instrumentation, and `checks=False` only suppresses invariant checks: 2,280 explicit equivalence controls found no change to labels, loads, potentials, or certificates.

## Packing cost accounting

Write `A = Nrow*Ncol` for the size of the supplied dense adjacency representation, `W` for the number of nonzero aggregated row-column incidences, and

`T = sum_j sum_(a active at j) |positive_load_support_of_a_before_j|`.

The sparse scoring work is `O(Ncol+T)` exact rational operations/lookups, where `T <= W Q <= Ncol Q^2`. The dense-delta scorer costs `O(W Q)`, while the authored cubic formula reference performs `Theta(Ncol Q^3)` score terms and `Theta(Ncol Q^2)` score multiplications. The cubic loop agrees with the inspected incoming mathematical formula; the new baseline is already strengthened with common sparse aggregation, a heap, and caches.

These scoring bounds **are not the entire implementation cost**. All three implementations also pay for dense input reading `O(A)`, row grouping `O(Q+Nrow log Q)`, `O(M)` cached powers, `O(W)` factors and updates, `O(Ncol Q)` future-list copies, and `O(Q^2)` final potential/dense-output materialization. Certificate generation adds `O(Ncol Q)` values and is disabled in all timed calls. Space includes the dense input, `O(M+W+Q)` preparation, and `O(Q^2)` output; optional certificates add their own space.

Here `M` is total edge multiplicity, **not** the bit length of a succinct matrix of weights. The power cache is pseudo-polynomial if weights are binary-encoded as a succinct input. These are arithmetic-operation bounds; arbitrary-precision exact rational operations are not unit-cost bit operations. This caveat is material even when every rational has polynomial bit length in the explicit-edge size.

## Cauchy exactness, valuation and extension scope

The recurrence cancels the previous pivot denominator algebraically:

`f_(b+1)(x) = f_b(x) (x-s_b)/(T+x-s_(b+1))`,

with the corresponding reversed difference for the source factor. For a fixed slot `s_j`, entries beyond `b=j` vanish; the code does not attempt to normalize the resulting zero numerator. The `Gamma(T)/T` prefactor cancels its `T` factor before modular arithmetic. If a remaining interpolation-grid factor is exactly zero, the target table is correctly zero without attempting to invert zero.

Nonzero factors are split into an exact integer valuation and a unit **before** reduction modulo `2^p`. Valuation changes, including negative changes in a ratio, are kept separate from the unit computation. Emission requires `v-E_b >= 0`; no division of a reduced residue by a power of two is performed. Consequently a low-precision intermediate zero cannot be incorrectly promoted back to a nonzero value. The rational oracle checks integrality of both coordinates before reduction and independently reconstructs the direct Cauchy kernel.

The implementation is specifically `(Z/2^p Z)[U]/(U^2+U+1)`, whose residue field is F4. It handles true extension units, including elements not lying in the prime subring; a norm is odd precisely for a unit. Batch inversion uses one inversion on a product of units. Tests include p=1 and p>1, so they cover a field and extension rings with zero divisors. They do **not** implement or certify arbitrary extension degree, arbitrary nilpotent tensor coordinates, every possible commutative ring, or all 2-adic-integral rational shifts. The implemented shift interface uses two integer coordinates.

## Cauchy cost and baseline fairness

There are `K=(2N/R-1)(2R-1)<4N` possible slot differences. Denominator preparation is linear-size, not a hidden quadratic difference-table construction. Both new implementations share that cache, batch unit inversion, the prefactor, known triangular zeros, ring arithmetic, precision, and full dense output. They are stronger comparators than a fresh denominator inversion per feature.

With identical initialization count `I`, the recorded multiplication counts are exactly

- product: `I + N(N+1)(2N+1)/3 + N(N+1)/2`;
- recurrence: `I + 2N^2 + N(N+1)/2`.

This establishes a cubic-to-quadratic **ring-operation** improvement for complete feature tables. Both store two dense N-by-N tables and must pay for quadratic output. Each ring operation acts on p-bit coordinates; bit complexity also includes the cost of p-bit multiplication, modular reduction, unit inversion, and O(log N)-bit index/valuation arithmetic. For the benchmark's growing precision `p=4N+16`, it would be incorrect to describe the total bit cost simply as `O(N^2)`.

The streaming-space observation in the review is an algorithmic possibility, not a claim that this dense-return implementation is streaming. Likewise, a full-table result does not imply the same speedup for a caller requesting only a few features or a heavily truncated small-p workload.

## Timing audit and limitations

The authoritative JSON benchmarks each contain five raw samples per method/fixture, with wall and process-CPU medians. Input generation and correctness comparison are outside the timed regions; full common preparation and full output allocation remain inside. Packing uses untimed checked warmup/counter collection and disables checks and counters equally for all timed methods. Cauchy retains a multiplication counter in both timed paths, so its results describe instrumented Python implementations. Orders rotate/alternate and both methods receive warmup.

The final packing benchmark contains 11 fixtures: the eight fixed-shape fixtures and three additional fixtures with 2Q rows, 2Q columns and four ones in each row, for Q=8,16,24. The extra fixtures ensure both vertex sets are larger than the label set. All 31 final packing/Cauchy records were rechecked for sample count, positive timing samples, wall/CPU medians and ratios. The extra fixture dimensions and row multiplicities were independently checked. The kernels and benchmark files were then frozen. Packaging-only output-path changes were separately checked, and both complete independent normal/-O runs were repeated against the final code identities and 31 benchmark records without changing or multiplying the mathematical coverage counts.

Verified final authoritative wall-time ratios:

| Comparison | Minimum | Maximum |
|---|---:|---:|
| Cubic packing / sparse-delta | 1.187x | 177.745x |
| Dense-delta packing / sparse-delta | 0.764x | 3.395x |
| Product Cauchy / recurrence | 0.272x | 32.438x |

A ratio below one is a measured regression and **must not be discarded**. In particular, sparse delta is slower than dense delta for two fixtures; both N=2 Cauchy fixtures regress. Tiny submillisecond samples are especially variable. At N=128 the three Cauchy wall-time ratios are 32.438x, 30.047x, and 27.166x; corresponding CPU ratios are 32.321x, 29.976x, and 27.138x. These are observations on this environment, not universal speed guarantees. The three added fixtures give cubic/sparse wall ratios 8.537x, 39.772x, 100.871x and dense/sparse ratios 1.531x, 2.474x, 2.735x. Earlier passes are preserved separately and are not the authoritative eleven-fixture packing benchmark; the original eight-fixture audited file remains byte-identical as `results/balancing_benchmark_fixed_shape.json`.

The benchmark evidence concerns local feature preparation and packing. It does not measure full SAT runtime, memory consumption, tensor-contraction throughput, a production implementation, arbitrary inputs, or the largest inherited time/space tradeoff. No full-SAT speedup follows numerically from these ratios. The proven component operation reductions remain useful independently of small/noisy benchmark outcomes and can be composed with stronger schedules without pretending to improve their leading SAT exponent merely by changing polynomial preprocessing.

## Packaging output routing

`qa/performance_cli_validation.json` records 14 custom-output checks, normally and with `-O`, for the component, schedule and aggregate certificate scripts. Their explicit outputs were written outside the bundle; the eight relevant packaged default JSON destinations stayed byte-identical during those routing checks. The aggregate driver writes child results into a temporary directory. Separate explicitly authorized final checker runs regenerated only its two default QA result files and logs. The independent checker itself supports an optional output path, permitting sealed-archive replay without replacing packaged JSON.

## Final frozen identities

The final binding is recorded in `qa/performance_audit_refresh.json`; both complete final checker runs agree. Full SHA-256 identities are:

| File | SHA-256 |
|---|---|
| `code/benchmark_balancing.py` | `1333857b068cd03dc6c8b9faabe526bf6d07557d9a820125ca1637177310ed79` |
| `code/benchmark_cauchy.py` | `7678ee60d98c7dd7335ba18fa24adee5a02a80e8cc631a9f2efc9882220752ec` |
| `code/cauchy_checks.py` | `2740e3a51cb8a0eb1073ad97d0f29579b141d9ef069f6d26870fc92d6aaa319f` |
| `code/cauchy_kernel.py` | `8d0179539269cea2fd27120bc9b6f73c5b3ec10d65121bb1d8308545138f9f59` |
| `code/check_balancing.py` | `d8ef88b60943bfd8acd94c1af2c94f4f39d65f3ba06bc00e46db0535d99a2d21` |
| `code/replay_archive.py` | `56aee2cc1ff9aa6c5f524c5a95eab0998415f89f43ed4fb0151615775a64b65a` |
| `code/sparse_balancing.py` | `0e6a811a639cce414697469789874787c39f22e1b02edc33e76d48146d951edb` |
| `code/verify_bundle.py` | `978e8f260ce52494036b8c56361e989e7b70e1474cbca2e7ce4c2cf312dfb124` |
| `code/verify_cache_schedule.py` | `5046e8d6c2c026966ba6fa66b4770fdb5e6d02af84e1a9cf950b934e9b0e8569` |
| `code/verify_comparison.py` | `6e4a597db46a947f07625b110247150eb846ee47f6b72d0289aff9ccdf49a71f` |
| `qa/performance_audit_checks.py` | `ff225058652954c061efc0d05b95b283979bf036054079a245f79156279db8c0` |
| `results/balancing_benchmark.json` | `0c2d5d0b9438824bfa5a15a92e300b2ef690cceabc5b67a8e4a42328c2436c8c` |
| `results/cauchy_benchmark.json` | `f87acf2ecd10a8455e20743461435cf0dc5262e3d96eeeb281a9e0864bf7817b` |
