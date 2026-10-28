> Final benchmark note: the authoritative matched-mask results are results/fused_cauchy_benchmark_mask_all.json (raw-run hashes included). Earlier percent-reduction timing examples, if mentioned below, are historical. The exact algorithm and operation counts are unchanged.

# Ratio fusion beyond the late quadratic Cauchy implementation

## Corrected novelty and comparison

The final-cutoff `sat_frontier_improvements` packet already supplies the
quadratic consecutive-mode recurrence. That result is credited, and the
earlier cubic-to-quadratic implementation in this bundle is now classified
as independent reproduction. The new change here is narrower: **precompute
transition unit ratios and absorb the common target prefactor once**.
It reduces the leading ring-multiplication count inside the already
quadratic algorithm. No further asymptotic-order improvement is claimed.

The matched baseline here is a self-authored implementation of the late
packet's mathematical algorithm, including its stronger one-inversion
preparation. It is not an execution of the archive's program. Both variants
use identical modular ring operations, full fresh initialization, dense
target/source outputs, known triangular zeros and one unit inversion.

## Two elementary changes

Keep the inherited notation N=L/2, R=2^i,
`s_b=(b mod R)+2R floor(b/R)` and `E_b=2 floor(b/R)-s2(floor(b/R))`.
For a fixed real slot x=s_j, the unnormalized features obey

`f_(b+1)(x)=f_b(x)(x-s_b)/(T+x-s_(b+1))`,
`g_(b+1)(x)=g_b(x)(s_b-x)/(T+s_(b+1)-x)`.

Consecutive pivot gaps g_b=s_(b+1)-s_b belong to `{1,R+1}`; for R=1
only g_b=2 occurs. Write d=x-s_(b+1)>=0. The target transition is

`(d+g_b)/(T+d)`,

and its source counterpart is

`(-d-g_b)/(T-d)`.

For each nonnegative slot difference d and each possible gap, precompute
the exact valuation difference e and the quotient of the two unit parts
modulo 2^p. There are O(L) such ratios, because the entire signed difference
set has K=(2N/R-1)(2R-1)<2L elements. Each later transition updates its
integer valuation by e and its unit residue by **one** multiplication,
rather than separate numerator and inverse-denominator multiplications.

Write the common prefactor Gamma(T)/T as 2^h v, with v known modulo2^p.
Compute the target starting unit seed v*T_unit once. Thereafter target
states already contain v; their output is `2^(h+v_f+E_b)*state`, where
v_f is the exact unnormalized feature valuation. Source output remains
`2^(v_g-E_b)*state`. The existing integral-feature lemma gives v_f,v_g>=E_b,
so all output shifts are nonnegative. A zero prefactor gives zero target
states. No unit inversion of those states is attempted.

The precise same known-valuation/unit bookkeeping as in the late packet
prevents loss of information when an intermediate displayed source residue
is zero and a later normalized output becomes nonzero. All inversions remain
of normalized denominator units. The new ratio cache can be shared across
both orientations, which have the same scalar difference kernel.

## Exact operation count

Let K be the signed difference-set size, and let g=1 if R=1 and g=2
otherwise. The independent implementation caches g(K+1) transition
ratios, a safe O(L) envelope (some are unused), and spends one multiplication
on the common target seed. Its table work is exactly

`N(N-1) + 2N = N^2+N`

ring multiplications: one for each of the N(N-1) total transitions and
2N initial target/source states. The late quadratic algorithm uses exactly

`(5N^2+N)/2`

table multiplications. Common initialization costs I; for the benchmark's
nonzero extension prefactor, I=3K+2L+3 in both implementations. Thus total
counts are

* baseline: `I+(5N^2+N)/2`;
* fused: `I+g(K+1)+1+N^2+N`.

Both use one unit inversion and O(N^2+L) ring storage including output.
The leading multiplication-count ratio tends to **5/2**. The additional
precomputation can lose on tiny cases; this is not a universal wall-clock
speedup or a new quadratic complexity class.

## Independent verification and benchmark

`code/fused_cauchy.py` implements both variants without importing any
reviewed archive code. `code/verify_fused_cauchy.py` compares both against
the prior independent implementation and the independent exact Q(U) oracle.
It includes non-prime extension residues, p=1, zero prefactors, and the
explicit zero-output-then-unit regression. Exact per-table multiplication
counts and one inversion are checked on every case.

`code/benchmark_fused_cauchy.py` times full preparation and both complete
tables, using a symmetric warmup, five alternating-order repetitions, raw
wall/CPU samples and parameters zeta=U, p=4N+16. The counterpart is a
one-inversion quadratic baseline, **not the old cubic comparator**.
Results are in `results/fused_cauchy_checks.json` and
`results/fused_cauchy_benchmark.json`. Timings are local component evidence,
not SAT solve times; shared-host timing noise and small-case regressions
are retained rather than hidden.

The final inspected late implementation has no cached transition ratio
or globally absorbed target prefactor. The novelty claim is scoped to that
inspected code and report, not to all numerical software or classical
common-subexpression elimination. This component can be used inside any
compatible contraction schedule, but its polynomial setup cost does not
change the established SAT exponential coefficient by itself.
