# Optional strict-majority witnesses for compressed relator overlap

Baseline: `8a95834940cf77cdab1b39571ffc102ca8b6bede`.

Owned production change: `fast/fastunknot/compressed_overlap.py`.
Focused tests: `fast/tests/test_overlap_witness.py`.
Paired benchmark: `fast/benchmark_overlap_witness.py`.
Primary raw data: `audit_notes/overlap_witness_20261008.json`.
Replayable real-knot trace: `audit_notes/gordian_witness_certificate.json`.

## Policy and actual API

`cyclic_overlap_move(arena, roots, witness_first=True)` is an optional API.
The historical default remains `witness_first=False`.
The new helper is `_extend_cyclic_witness` in the same module. It uses only
existing exact arena slicing, inversion and LCP operations, and returns an
ordinary existing-format `relator` move. Application and both certificate
verifiers are unchanged.

The final integration also exposes `--group-overlap-witness`, which enables
compressed group search and relator moves. Python callers can use
`group_decide(..., compressed_search=True, relator_moves=True,
overlap_witness=True)` or `recognize(..., use_group=True,
group_compressed_search=True, group_relators=True,
group_overlap_witness=True)`. The supported standalone producer takes
`compressed_certificate(..., relator_moves=True, overlap_witness=True)`.
All optional defaults remain false.

The original component benchmark installed the optional helper in the
existing dispatch with a benchmark-local patch; its saved timings concern
that controlled helper comparison. The later public API/CLI plumbing has
separate integration tests. No claim that default recognition changed or
that the corpus timed the new partial-overlap path follows from these data.

## Theorem 1: existence completeness

For a donor of length m, strict raw shortening requires integer overlap
k > m/2. Let tau = floor(m/2)+1. The current exact LCS API accepts cap=tau
and returns min(LCS,tau), with an exact substring witness. Thus its return
is tau precisely when this ordered pair/orientation has a shortening overlap.

As in the existing proof, doubling both relators includes every cyclic
factor of length at most m, and reducing offsets modulo their original
lengths recovers a cyclic witness. The shorter member of every unordered
pair is used as donor, because if the longer donor has positive gain for
an overlap k, the shorter donor has at least that gain. Both donor signs
are searched. The existing absolute-count rejection is safe because it
uses an upper bound on any one-turn overlap. Consequently replacing cap=M
(the shared-count bound) by cap=tau preserves existence completeness of the
whole local query when resources are uncapped. It need not preserve the
chosen move or any later greedy search trajectory.

## Theorem 2: exact maximal extension of one alignment

Suppose a checked length-k cyclic witness starts at i in R and j in D,
where |D|=m <= |R|. Normalize i and j to one turn. In the doubled roots,
compute an exact LCP of the as-yet-unmatched intervals starting at i+k and
j+k and ending at i+m and j+m. Add its length to k to obtain q.

If q<m, compare the preceding m-q letters backwards by taking the LCP of
their inverses. Let b be this second LCP length. Return length q+b, target
start i-b modulo |R| and donor start j-b modulo m. If q=m, no backwards
query is needed.

The first query stops at the first forward disagreement or at the one-turn
cap. The second stops at the first backwards disagreement or at the
remaining one-turn allowance. The returned cyclic common factor therefore
contains the original witness and is maximal at this relative alignment.
If shorter than m, its two boundary letters disagree. This uses at most two
LCP calls and no expanded words. It does not compare other alignments.

## Local complexity statement

The thresholded LCS query retains the established polynomial bit bound in
grammar size s and length bit-size b. At most a constant number of slices
and inversions and two LCP calls follow a successful query. Slices add only
O(grammar height) rules; inversion is a DAG traversal. Therefore this
extension retains a polynomial local bit bound. All operations consume the
same arena allowance and cancellation callback, and failures remain
inconclusive. It adds no global bound on move count, grammar growth or
recognition completeness.

On the explicit binary-power families below, the prefix arm does not visit
any cut pair; the interior arm visits one pair and one aligned-cut extension.
The specified grammars have O(h) rules for N=2^h. The fixed-alphabet count
summaries, inverse construction and slices have polynomial cost in h;
the fixed common subgrammars resolve the needed prefix comparisons without
occurrence tables. This gives a direct polynomial-in-log(N) bound on these
complete local search/application operations. A conservative implementation
bound is O(h log(h+1)) DAG/arithmetic operations, with polynomial bit cost
on O(h)-bit lengths. No numerical speed ratio is assigned to exhausted arms.

## Hard family and proof of its exact optimum

Let P=(ab)^N, T=aabbccacbabc (length 12), and

    D=P c T a,       R=P a T b,       N>=16.

Both cyclic words have length 2N+14. The fixed T already contains all nine
directed pairs on {a,b,c}, so the existing alphabet/transition filters do not
separate them. Their count vectors differ by one c versus one b, hence
neither entire donor fits the other target; this prevents the preceding
whole-donor matcher from consuming the budget. The common prefix P has
length 2N, above the strict-majority threshold N+8.

The exact cyclic LCS is 2N. A direct proof uses maximal alternating a,b runs.
In D the unique alternating run of length at least four is P; it is preceded
by a (creating aa at its left boundary) and followed by c. In R the unique
such run is b P a, of length 2N+2; its predecessor is c and its successor is
a (creating aa at its right boundary). All other alternating runs have
length at most three. Any common factor longer than 2N contains at least
2N-13 letters from D's P, split into at most two intervals, hence contains
an alternating interval of length at least ten when N>=16. This must align
the two principal alternating runs. Such an alignment cannot pass the left
end of D's P: either it encounters R's preceding c while D is still in P,
or D's preceding a meets the b forced by R's alternation. It cannot pass the
right end either: D's next c disagrees with R's alternating run, or R's aa
departure first disagrees with D's alternation. The common factor is thus
contained in D's P and has length at most 2N, contradiction. The prefix
attains 2N.

The new move replaces R by (cTa)^(-1)(aTb), a freely and cyclically reduced
word of length 28, so total expanded relator length falls by exactly
2N-14. The target rotations initially begin at zero. Rotating both spellings
to cTaP and aTbP yields an interior/suffix witness: there is no common
prefix, but the first zero-offset aligned-cut extension in the doubled
roots finds P. This family gives the same overlap and gain.

## A necessary correction to the tempting earlier example

The previously documented linear-LCS negative control P cT, P aT does not
remain hard after cyclic doubling. The common T wraps around before P, so
the old matcher already finds exact overlap 2N+12 using the first aligned
cut and shared-count cap. We retained this as `shared-tail-control` and
make no improvement claim for it.

## Theorem 3: no uniform gain approximation

An arbitrary threshold witness can have an arbitrarily worse gain than the
best alignment even after exact maximal extension. Take a donor with 2m
distinct symbols, and a target containing its first m+1 symbols, then fresh
separators, then its first 2m-1 symbols, then another fresh separator.
The initial common prefix is locally maximal at m+1, with gain 2. Another
alignment has overlap 2m-1, with gain 2m-2. The gain ratio is 1/(m-1).

The tested m=4 example is donor `abcdefgh`, target `abcdeXYZabcdefgW`:
old overlap 7/gain 6 versus optional overlap 5/gain 2. Whole-donor search
fails in both. Replacing every letter by two consecutive copies also
removes all singleton occurrences; the actual weighted Whitehead cut has
value zero on this doubled example (checked independently during audit).
Thus the local greedy concern is not confined to states whose first stage
would immediately eliminate a singly occurring generator. The default
policy is retained because no full-search quality preservation is proved.

## Validation

Four test methods pass in approximately 1.05 seconds. They include all 900
pairs of nonempty positive binary words of length <=4, 400 random signed
words with random grammar parses, literal enumeration of all cyclic starts
and both signs, strict shortening, exact output words and two-sided
maximality. Exponential prefix and interior families through N=2^500 run
with expansion and occurrence tables forbidden. Invalid option types,
work exhaustion and node exhaustion are checked.

A real reachable Gordian residual is obtained by replaying the first 132
moves of the archived `gordian_relator_power.json` certificate. Its ten
remaining nonempty relator lengths are 378,8140,4,370,1704,370,2026,128,888,
1022. The optional query selects target slot124, donor73, rotations81 and3,
positive sign, overlap4. The unchanged continuation produces a 142-move
complete original-PD certificate. Both independent literal and compressed
replayers accept with producer/helper calls forbidden, and reject a forged
overlap. This same certificate is included as a separate replayable record.

A different experiment forcing the compressed overlap path from the start
of Gordian exhausted 20 million work units before completing. The residual
success is not a claim to accelerate that forced whole query. Ordinary
production routing uses the explicit bridge at these sizes.

## Primary five-round controlled measurements

One excluded warmup; shuffled arm order with seed3110; archived helper at
baseline above, A/A repeat, and optional witness helper in the same current
arena/application/search/replay harness. Kernel cap2M work; node cap100k;
full query group cap20M and15seconds/global18seconds. Full knot timings
include fresh PD validation, recognition and independent replay; certificate
digests are checked outside the timer. Local timings include construction,
unsuccessful whole-donor search, cyclic query and checked application.

| Case | Archived ms | A/A ms | Optional ms | Archived work | Optional work | Optional nodes |
|---|---:|---:|---:|---:|---:|---:|
| Prefix h8 |174.971|161.297|0.551|245591|708|64|
| Prefix h32 |LIMIT|LIMIT|0.731|2000001|1308|112|
| Prefix h500 |LIMIT|LIMIT|5.220|2000001|13008|1048|
| Interior h8 |201.398|159.737|0.503|319306|962|76|
| Interior h32 |LIMIT|LIMIT|1.239|2000001|1898|148|
| Interior h500 |LIMIT|LIMIT|8.100|2000001|20150|1552|
| Shared-tail h500 |7.012|5.772|6.916|15080|12939|1042|
| Gain tradeoff |0.240|0.231|0.190|635|488|43|

For no-majority inputs (ab)^N and (aabb)^N, all h500 arms exhaust during
the preceding whole-donor probe: `overlap_witness_queries=0`. At h8/h32 all
complete, but there is no measured improvement. This is an unchanged route
bottleneck, not an observed failure of the optional helper itself.

225 measured complete knot queries retain identical certificate digests and
none reaches compressed LCS. Fourteen-small-case sums of medians are140.334,
140.396,138.959ms for archived/A/A/optional. Gordian medians are1.5253,
1.5104,1.4790seconds. These data give no evidence of a knot-corpus speedup.

The genuine residual test gives the SAME first move, 142-move certificate,
and4280 allocated nodes in every arm. Charged work changes155142->155168,
only26 units. Its five-round timing medians are69.55/63.42/87.21ms. The large
wall-clock spread is not accompanied by substantial extra charged work and
does not support a stable residual improvement. Do not present it as a
demonstrated recognition speedup or use its timing spread as an asymptotic
claim.

## Research questions suggested by the audit

1. Can a budgeted witness policy preserve an approximation to maximal gain
   while still admitting cheap early positive completion? The unbounded
   gain-ratio counterexample rules out an unconditional approximation for
   the present first-witness rule.
2. Can a move scheduler exploit cheap witnesses yet prove a bound on total
   moves or grammar growth? Local existence completeness alone does not do
   this and does not make greedy reduction complete for unknot recognition.
3. Can the impossible full-donor query on (ab)^N versus (aabb)^N be rejected
   by a cheap exact run-length/period incompatibility summary? Its position
   before the partial-overlap stage matters for any end-to-end improvement.
4. Can parameterized periodic-defect matching avoid the full cut-pair table
   on both positive and negative queries? The proved one-defect family
   suggests measuring defect count separately from represented length.
5. Obtain real knot residuals actually requiring the new compressed partial
   stage above the explicit cap. Existing corpus timings do not exercise it.

