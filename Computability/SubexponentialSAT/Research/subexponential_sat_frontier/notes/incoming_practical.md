# Assigned incoming review and two implemented arithmetic improvements

Snapshot: ProveIt `ab2fbc9e03d5c3d0ad6dec8686960bfe498b0b06`.

## 1. Review of the three assigned incoming packets

### `3sat_round2_refinement_20261027.zip`

The report's strongest explicit normalized polynomial-space certificate is
`84.06627149423657...`, with conservative eventual coefficient 85, on the
scale `s / sqrt(log2 s)`. The full proof is in `report/combined.tex`.
Its new packing uses edge-coloring into at most `2 Delta - 1` matchings and
conditional expectation of a rational exponential potential. This gives
`B <= (1+1/lambda) M + 20 q^2 Delta lambda^2 + L q^2` padded ports per side,
and a child-size ratio `(2/r)(1+o(1))`. It counts the exact crossing fraction
`1 - 1/r`. The schedule uses root `r0=37`, taper fraction `10/1043`, then
tail `r=8`, taper fraction `1/236` decaying by `5/2`; cumulative packet
exponents include only an additive squared-log guard. It imports the old
factorial slope-3 Cauchy modes and sharp leading Hermite precision six.

The displayed coefficient is an upper-bound certificate, not a runtime,
not a variable-level SAT coefficient, and not an improvement of logarithmic
order. The unproved mode-summation interfaces remain unproved.
Its `report/actual_domain.tex` identifies an actual permissible Cauchy
subblock with exact Smith valuations `4b - 2 popcount(b)`, while explicitly
crediting the older density report for that Smith spectrum. This is a local
integral-rank barrier, not a barrier to algorithms for SAT.

### `eth_joint_cauchy_2026-10-26.zip`

`report.tex`, sections on full-block modes and mode entropy, constructs a
source/target-local, finite integral decomposition of an entire crossing
orientation at every retained level i. The mode weights are
`a+1-i + 4q - 2 popcount(q)`, where q is the coarse index. This raises the
uniform slope from three to four with the same certified family count.
The actual-packet domain and source/target support are crucial; a generic
Smith decomposition would not alone justify the same recursive topology.

Using an older packing schedule, the packet obtains polynomial-space
coefficient `319.685757...`. It also implements exact mode-graph caching,
three-block tables, and division-free Strassen multiplication. Its faster
alternative has time coefficient `225.597057...`, space coefficient
`196.199445...`, and uses subexponential space. The graph prototype and
Strassen identity are exact, but are not a complete SAT solver.

Sections 7--8 of its report correctly pay for cached child calls, internal
block summation, boundary tables, and final rectangular multiplication.
No candidate coefficient should be multiplied by a matrix exponent factor
without recomputing this full recursion. Combining the full-block modes
with newer asymmetric packing is a legitimate direction; the already
existing table method must be included when defining a combined baseline.

### `eth_packet_refinement_2026-10-26.zip`

The certificate is `95.6639404728982... = 9*pi*sqrt(22)/(2*ln 2)`, again
normalized polynomial-space contraction. Its two-stage deterministic
labeling replaces a sufficient `D^2 Delta` packing scale by `D Delta`
times logarithmic factors; near-unit padding improves both child sizes
and mode-family multiplicity. Additive precision guards replace doubled
cumulative taper. It still uses slope-3 factorial modes.

All three packages explicitly preserve the original unrestricted SAT
logarithmic order. None contains empirical end-to-end SAT timings. I found
no unresolved defect in the local identities reviewed here; this is not a
full independent verification of their inherited ETH framework.

## 2. Exact faster implementation of the existing balancing routine

The fastest convenient prior code baseline is the **asymmetric** packet's
`code/balanced_packing.py`. Unlike the older balanced-packing prototype,
it already maintains future-column products. Its remaining score loop
still recomputes Q entries of each of Q row sums for each of Q labels.
Thus its candidate-scoring phase costs O(N Q^3) rational operations for
N column vertices and Q labels. Comparing only with the older prototype
that also recomputed future products would overstate the new advance.

The exact input baseline was preserved byte-for-byte as
`practical/reference_balanced_packing.py`; SHA256:
`5e899df4fd25b1371fe6f42c13f87caba49637fb92da0f12b12dd01a831bb6d2`.
The root repository license is preserved as `LICENSE-ProveIt.txt`.

### Formula and proof

After row balancing, let w_av be the edge weight from row group a to
column v. Put z=1+1/(h C), with the same base as the old implementation,
and maintain

    F_av = (Q - 1 + z^w_av) / Q,
    P_a  = product_{unassigned v} F_av,
    B_ab = z^{current cell load_ab},
    S_a  = sum_b B_ab.

Before assigning v, let `P'_a=P_a/F_av`. Assigning v label b changes only
cell b in every row, so its exact candidate potential is

    candidate_b = C0 + sum_a P'_a (z^w_av - 1) B_ab,
    C0 = sum_a P'_a S_a.

Compute C0 once, then each candidate in O(Q) rational operations. The
smallest-index minimizer is exactly the old algorithm's minimizer because
the formula is an algebraic identity. After selecting b, update

    increment_a = B_ab (z^w_av - 1),
    B_ab += increment_a,
    S_a  += increment_a,
    P_a   = P'_a.

Both cache identities hold initially and are preserved by these updates.
Therefore every exact score, label, tie break, pair load, and certificate
is unchanged. Conditional-expectation averaging and final potential
checks remain active. The candidate-scoring phase is O(N Q^2) rational
operations, using O(Q^2) additional cached rationals. Shared power and
input construction costs are unchanged. Rational bit lengths have the
same polynomial bounds because every cache entry equals an old exact
power, row sum, or future product. This is a reduction in a polynomial
factor of the construction; it does not alter its exponential SAT bound.

### Verification and genuine prior-code timing

`verify_cached_balancing.py` compares the complete returned dictionary,
including every exact candidate score, against the preserved incoming
implementation. The deterministic suite passed:

- 840 complete certificate comparisons;
- 9,724 candidate-score comparisons;
- 840 certificate-disabled comparisons;
- 12 invalid-input rejections across both implementations.

The normal and `python -O` records are identical. Tests include all 81
2x2 matrices with entries 0,1,2, empty and asymmetric cases, and 80 seeded
random cases. The seed is 20261027.

The benchmark uses five paired trials with alternating execution order,
Python 3.12.14 on Linux x86_64, identical input matrices, and exact internal
checks enabled in both implementations. Certificate-string construction
is disabled in both. All complete outputs were compared for every timed
invocation. Timings include each complete `balance_pair_labels` call.

| Rows | Columns | Q | Edges | Prior median | Cached median | Ratio |
|---:|---:|---:|---:|---:|---:|---:|
| 12 | 16 | 4 | 50 | 1.652 ms | 1.100 ms | 1.50 |
| 16 | 24 | 8 | 96 | 10.974 ms | 4.111 ms | 2.67 |
| 20 | 32 | 12 | 155 | 39.088 ms | 9.140 ms | 4.28 |
| 24 | 40 | 16 | 256 | 103.253 ms | 18.320 ms | 5.64 |
| 24 | 40 | 24 | 266 | 304.464 ms | 31.833 ms | 9.56 |

These are timings of an actual prior packing subroutine, not SAT solver
timings. The small inputs do not satisfy the reports' enormous eventual
asymptotic packing gates; that does not affect the exact-score identity
or the measured optimization of the routine itself. They do not establish
that this phase is the practical bottleneck of a future full solver.

Files: `cached_balancing.py`, `reference_balanced_packing.py`,
`verify_cached_balancing.py`, `benchmark_cached_balancing.py`,
`cached_balancing_verification.json`,
`cached_balancing_verification_optimized.json`,
`cached_balancing_benchmark.json`, and `LICENSE-ProveIt.txt`.

## 3. Precision peeling prototype and evidence

The parent/baseline agent supplies the general theorem. Implemented local
identity: if each tensor is `2^v_j` times an integral tensor and
`V=sum v_j<P`, perform the normalized contraction modulo `2^(P-V)`, then
multiply the result by `2^V`. If V>=P the contraction vanishes modulo 2^P.
The tensor network must be multilinear in the scaled tensors.

The code receives frozen canonical P-bit representatives and divides them
by their known powers before reducing to Q=P-V. It checks Q+v_j<=P;
it never divides a residue already reduced to Q. In a recursive caller,
the normalized Q-bit result must be frozen as its new creation-time
representative. This is not permission to recompute an old tensor formula
at arbitrarily higher precision later.

### Independent actual-domain algebra checks

The verifier independently builds the actual permissible i=0 packet
subblock with slots 2k,2j, t=1, zeta=1:

    W[k,j] = A/(T+2(k-j)),
    T=1+2^(a+1), A=C(T)/C'(0),
    C(X)=product_{h=-2^a}^{2^a-1}(X-h).

Exact rational LDU elimination independently constructs the mode factors.
Its pivot valuations are checked against `a+1+4b-2 popcount(b)`. The test
compares direct cyclic contraction of the original W kernels against
both the full-precision mode sum and the peeled mode sum. Eighteen checks
cover a=2,3,4, cycle lengths 4,3,2, and precisions 8,13,20,32,50,80.
No previous packet's executable code is used for these algebra checks.

Additionally, 544 seeded randomized modular cycle contractions passed,
including 120 cases that vanish by valuation, four invalid normalization
inputs were rejected, and 1,601 canonical-cap regression checks passed.
The explicit bad-ordering example is 224/32=7 mod 8: reducing 224 mod 8
first loses the answer. The frozen-cap regression is old representative
5 at precision3, reduced to precision2 representative1, then lifted to
precision4: the correct new representative remains1. Normal and -O
verification records are identical.

### Work model

For a fixed mode inventory, define `N(t)=#{beta: V(beta)<t}`. Then exactly

    sum_{V(beta)<P} (P-V(beta)) = sum_{t=1}^P N(t).

For any cost f with f(0)=0, the corresponding exact identity is

    sum_beta f(P-V(beta))
      = sum_{q=1}^P [f(q)-f(q-1)] N(P-q+1).

The implementation counts colored partitions with weights
`5+4b-2 popcount(b)` and records exact integers, not samples. At P=1024
and four families, mean residual precision is 25.0368 bits; linear charge
is 0.024450 of the full-P charge and quadratic charge is 0.00115798.
These are arithmetic work models. The mode count and number of recursive
calls are unchanged; a sharper leading contraction exponent does not
follow just from this identity.

### Scoped kernel benchmark

Five dense 12x12 matrices, P=2048, seven paired trials, alternating order.
The same frozen input residues are supplied to both branches, and input
generation is excluded from both. The peeled timing includes validation
and normalization. These are synthetic homogeneous cyclic tensor
contractions, not execution of an old SAT solver.

| Total V | Residual Q | Full median | Peeled median | Ratio |
|---:|---:|---:|---:|---:|
| 0 | 2048 | 42.011 ms | 42.498 ms | 0.99 |
| 512 | 1536 | 28.863 ms | 17.732 ms | 1.63 |
| 1024 | 1024 | 29.307 ms | 9.433 ms | 3.11 |
| 1536 | 512 | 41.679 ms | 6.282 ms | 6.63 |
| 1792 | 256 | 30.809 ms | 3.252 ms | 9.48 |
| 1984 | 64 | 27.795 ms | 1.938 ms | 14.34 |

The zero-valuation case shows the expected normalization overhead. These
observations do not imply a uniform speedup. Input construction costs,
recursive-entry generation costs, and full solver overhead can dominate.

Files: `precision_peeling.py`, `verify_precision_peeling.py`,
`benchmark_precision_peeling.py`, `precision_peeling_verification.json`,
`precision_peeling_verification_optimized.json`, and
`precision_peeling_benchmark.json`.

## 4. Reproduction

From `analysis/practical` or the corresponding delivered code directory:

    python3 verify_cached_balancing.py --output cached_balancing_verification.json
    python3 -O verify_cached_balancing.py --output cached_balancing_verification_optimized.json
    python3 benchmark_cached_balancing.py --output cached_balancing_benchmark.json
    python3 verify_precision_peeling.py --output precision_peeling_verification.json
    python3 -O verify_precision_peeling.py --output precision_peeling_verification_optimized.json
    python3 benchmark_precision_peeling.py --output precision_peeling_benchmark.json

No third-party Python packages or network calls are required. Benchmark
timings vary by machine and load; exact verification outputs should agree.
