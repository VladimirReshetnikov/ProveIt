> Historical intermediate analysis: the closing five-packet intake supersedes some novelty and frontier claims below. These derivations remain valid supporting work, not the final headline. See report.tex, streamed_composition_new.md, late_cache_refinement.md, late_review_cauchy.md and fused_cauchy_new.md for the closing comparison.

# Review: joint Cauchy, packet, recursive refinements

**Final-cutoff correction (27 October, 02:35 UTC):** the late packet
`sat_frontier_improvements_2026-10-26.zip` at repository cutoff
`fa6e904d109b738154db7fe41e7f2777e6d24aee` already contains the quadratic
full-table recurrence, valuation-unit implementation and batch inversion.
The component below is therefore an independent reproduction and validation,
not a novel improvement over the final reviewed corpus. That packet even
uses one unit inversion, versus this independent implementation's two.
See `late_review_cauchy.md` for the corrected comparison. Its polynomial-space
63.857409 and cached 38.484496/34.274803 certificates also supersede the
older baselines in this chronological note; our later explicit schedules
remain smaller than those particular late-packet coefficients.

Snapshot assigned by parent: `ab2fbc9e03d5c3d0ad6dec8686960bfe498b0b06`.
Inspection was static: TeX, README, selected implementation and audit records.
No supplied archive program was executed or imported. New programs below were
written independently from displayed mathematical formulas.

## Findings that change the comparison

1. **Joint Cauchy is genuinely composable.** It supplies integral full-orientation
   modes with weights `a+1-i+4q-2s2(q)` and exactly the old multiplicity: `2^i`
   per orientation, two orientations per unequal-symbol packet. Each mode has
   one source group and one target group; wires, child maximum degrees,
   creation-precision tags, Hermite recovery and packet entry upper bounds
   are unchanged. Thus it composes with every audited packing schedule.
   The coefficient improvement from slope three to four is `sqrt(3)/2`.
2. The packet-refinement packet's `95.6639404729...` certificate uses
   deterministic one-sided exponential-potential packing, linear
   `D_arr Delta` dependence, nearly unit padding and additive guard. This
   largely overlaps the previous user's matching-packing report
   (`94.7482022595...`), and is dominated by the newer asymmetric packet.
3. Recursive-refinement gives generic coefficient `133.207...`, using the
   weaker variance packing and a residue-aware slope `64/21` basis. Its
   root degree regrouping is a different low-degree promise, not a better
   generic `s^0.9` result. Full-orientation slope four dominates its mode
   entropy. Its variance refinement is useful with known parallel-edge
   multiplicity, but not stronger than the asymmetric exponential-potential
   packer in the generic comparison.
4. **Do not omit the existing extra-space combination.** The joint packet's
   cached group tables and division-free Strassen construction compose with
   asymmetric packing, not only with the old r=256 schedule in that report.

### Strong inherited combined certificates

With nearly unit padding and unequal-packet fraction `1-1/r`, slope four
gives local natural-log entropy

`ln N <= (pi sqrt(2(1-1/r))+o(1)) M/sqrt(u)`.

The asymmetric packet has r=16, root `u0=lambda/81`, tail
`ud=lambda/(108*4^(d-1))`, and child ratio `1/8+o(1)`. Its path sum is
`9+sqrt(3)`. Therefore its inherited polynomial-space combination is

`C_PS = pi sqrt(15/8) (9+sqrt(3))/ln(2)
      = 66.60514340761482...`.

Its stated boundary infimum `76.4327736858...` similarly scales by
`sqrt(3)/2`, approximately `66.1927`; a boundary infimum is not an
attained finite-slack schedule. The low-degree `31.064132063...` scales
by the same factor, but must remain a separately labeled interface.

For the extra-space construction use the weighted pair entropy scale
`K = pi sqrt(2) M/(ln(2) sqrt(u))`. Split the sixteen groups into 5,5,6.
The three directed pair-class sizes are 50,60,60. Put `omega=log2(7)`:

* `a0=sqrt(30)/16=0.3423265984...` (group cache calls);
* `aB=sqrt(150)/16=0.7654655446...` (building a block table);
* `bS=sqrt((170-(1-(omega-2)^2)*50)/256)=0.7720485597...`;
* `jB=sqrt(120)/16=0.6846531969...` (stored boundary tables).

Root `K0=9*pi*sqrt(2)/ln(2)=57.68752663918...`, and tail
`K1=(pi*sqrt(2)/ln(2))*sqrt(108)/8=8.32647725850...` decreases by 1/4.
The root matrix term dominates: all work first reached at depth at least
one has coefficient at most
`a0*K0 + max(a0*K1/(1-1/4), bS*K1)=26.17642...`.
The largest boundary table is also the root's. Thus an already available
composite certificate is

* time `44.53757185496245...`;
* space `39.495949533699765...`;

on the normalized `s/sqrt(log2 s)` scale. This is a time/space tradeoff,
not a polynomial-space result. A new `<64` polynomial-space schedule does
not have a lower time coefficient than every resource-unrestricted
inherited combination.

## Independently reproduced component: quadratic full feature-table construction

The inspected `joint_cauchy.py` constructs each b-th feature by traversing
all h<b, then repeats for every row/column. Its full dense feature tables
therefore use cubic unit-ratio arithmetic. This observation concerns its
full-table workload, not every possible on-demand use.

Let `N=L/2`, `R=2^i`, `s_j=(j mod R)+2R floor(j/R)`,
`E_b=2 floor(b/R)-s2(floor(b/R))`. The packet's features are

`f_b(x)=T/(T+x-s_b) * product_{h<b}(x-s_h)/(T+x-s_h)`,
`g_b(y)=T/(T+s_b-y) * product_{h<b}(s_h-y)/(T+s_h-y)`.

Direct cancellation proves the computational recurrence (also proved in the
late frontier packet)

`f_(b+1)(x)=f_b(x)*(x-s_b)/(T+x-s_(b+1))`,
`g_(b+1)(y)=g_b(y)*(s_b-y)/(T+s_(b+1)-y)`.

For fixed j only b<=j need be emitted; subsequent entries vanish.
The normalized factors are `F_b=2^-E_b f_b`, `G_b=2^-E_b g_b`, and the
actual target factor is `(Gamma(T)/T)*2^(2E_b)*F_b`.

### Safe p-adic implementation

Represent each nonzero unnormalized feature as `(v,unit mod 2^p)`.
For each recurrence numerator and denominator, extract its *known exact*
power of two before reduction. Update v by their valuation difference
and multiply by their unit ratio. Emit `2^(v-E_b)*unit`; the audited
valuation lemma guarantees `v-E_b>=0`. A negative intermediate exponent
of the ratio does not require dividing a p-bit residue by a nonunit:
the integer valuation account is separate from the unit residue.

All denominators are `T+d`. The set of possible differences is

`{2R*q+r: -(N/R-1)<=q<=N/R-1, -(R-1)<=r<=R-1}`,

with cardinality `K=(2N/R-1)(2R-1)<4N=2L`. Precompute the unit part
of each denominator and batch-invert these units in any commutative
ring. Prefix products plus one inversion and a reverse pass require
3K ring multiplications. This remains valid in unramified extension
rings and with nilpotent tensor coordinates because these are scalar
units. The implementation checks the genuine degree-two unramified
extension `(Z/2^p)[U]/(U^2+U+1)`, including non-prime residues.

### Provable operation counts and scope

The independent baseline is deliberately stronger than the supplied
product implementation: both baseline and recurrence share cached/batch
denominator inverses, skip known triangular zeros, use identical modular
arithmetic, and include initialization and full dense output. Let I be
the identical initialization multiplication count. For the supplied
code's nonzero-prefactor cases, `I=3K+4L-1`. Including target scaling,
the independent implementations use exactly

* product: `I + N(N+1)(2N+1)/3 + N(N+1)/2` multiplications;
* recurrence: `I + 2N^2 + N(N+1)/2` multiplications.

Both use two unit inversions including the prefactor, or fewer in the
zero-prefactor case. Consequently full-table arithmetic drops from
Theta(N^3) to Theta(N^2), which is optimal up to constants if all dense
output ring elements must be written. Full output storage is Theta(N^2).
Streaming columns needs O(L+N) working ring elements excluding output.

This does **not** reduce the proven SAT exponential order or leading
coefficient; feature preparation is already polynomial/lower order there.
For small p or partial feature requests, high modes may already vanish
or never be requested. Those workloads need separate benchmarking;
the full table result alone is not a universal speedup claim.

## Self-authored deliverables and verification

* `code/cauchy_kernel.py`: product reference and recurrence, modular ring,
  valuation accounting, shared batch inverse initialization and exact
  operation counters.
* `code/cauchy_checks.py`: separate exact rational oracle in Q(U), direct
  cancelled kernel comparison, exact/modular reconstructions and counts.
* `code/benchmark_cauchy.py`: full initialization in every timed call,
  symmetric warmup, alternated order, raw timing samples and output equality.
* `results/cauchy_checks.json`: PASS. 120 rational configurations, 480
  modular configurations, 30,048 feature equalities, 15,024 modular kernel
  entries, 3,756 exact kernel entries, 960 operation count equalities,
  20 zero-prefactor configurations, 11 larger cases, 5 invalid inputs.
* Benchmark first pass is preserved separately. Confirmatory run records
  five samples and CPU as well as wall time, since shared-host scheduling
  noise is substantial. Small-table regressions must be retained and shown.

Finite checks are evidence about these components, not a formal proof,
complete SAT implementation, or independent validation of the upstream
claimed ETH refutation.
