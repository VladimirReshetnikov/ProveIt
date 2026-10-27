# Late-cutoff review: kernel and frontier packets

Final repository cutoff assigned by the parent:
`fa6e904d109b738154db7fe41e7f2777e6d24aee`.
Reviewed files are under `late_incoming/`. This was static inspection of
README, TeX, proof-status and implementation source. No supplied archive
program was executed or imported.

## Mandatory correction: quadratic Cauchy tables are already present

`sat_frontier_improvements_2026-10-26.zip` contains **the same** consecutive
mode recurrence, triangular skipping, exact separate valuation/unit states,
O(L) denominator difference set and batch inversion. It states and implements
the same `(5N^2+N)/2` table multiplication count. Its `code/fast_cauchy.py`
also includes the odd denominator of C'(0) in the common inversion batch,
so it needs **one** unit inversion, whereas our independently written
prototype uses two.

Therefore our cubic-to-quadratic kernel claim must be reclassified as an
independent reproduction and validation. Our raw benchmark remains a valid
comparison against our cubic product reference, not a speedup over the
latest quadratic implementation and not over every current proposal.
Its p=64 benchmarks and ours p=4N+16 use different workloads; their timing
numbers cannot be ranked as direct comparisons. We did not execute its code.

### Contraction certificates in this late frontier packet

* Generic polynomial space: `63.85740947110328...`, eventual 64.
* Root degree s^(3/5): `31.9287047356...`, eventual 32.
* Root degree s^(1/12): `26.9023275131...`, eventual 27.
* Generic cached method: time `38.48449590573546...`, space
  `34.27480300502269...`, eventual 39/35.

The generic polynomial schedule already uses alphabets 13,14,8,6 followed
by an r=4 geometric tail. Thus variable/adaptive alphabet scheduling itself
is not new in our final snapshot. Our `63.758994...` result is a further
explicit schedule retuning; it is smaller than this particular certificate.
Our cached `37.591702.../33.623041...` likewise remains smaller in both
resources than this packet's r=8 cached schedule. Other late packets are
being checked separately, so this is not a statement about the final global
frontier by itself.

The late packet's fixed r=8 cached proof uses u_d=lambda/(61*2^d),
near-unit asymmetric packing, full-orientation slope four, group caching,
3,3,2 blocks and rectangular Strassen. Its recurrence accounts for child
calls with a0=sqrt(14)/8 and gamma=sqrt(2)/4; a0/(1-gamma)<3/4<bS makes
the root matrix term dominate. Static inspection found no mismatch with
the earlier joint-packet interfaces in this composition.

## Distinct local advances in the late kernel-improvements packet

`subexponential_sat_kernel_improvements_2026-10-26.zip` has no stronger
generic global certificate than its comparison examples 66.6051 polynomial
space and 44.5376/39.4959 cached. Its contributions are different local
primitives and must not be ignored:

1. **Adaptive actual-matrix modes.** Minimum-valuation elimination over
   the finite unramified chain ring separates the real-port crossing matrix
   into integral rank-one modes with its Smith weights. Complexity is
   O(mn min(m,n)) ring work and O(mn) ring storage. It needs no precision
   beyond the prepared matrix's p bits. The sorted adaptive weights
   dominate those of every integral rank-one decomposition of the same
   matrix, so its feasible exponent-tuple inventory is no larger.
   The proof uses minimal generators/socles of modules over a chain ring;
   it does not incorrectly assume a field or claim the result for general
   nilpotent coefficient rings. Source/target group support survives.
   A reported sparse fixture has 260 versus 3,013 feasible tuples after
   giving the full-block comparator zero-mode removal and valuation
   normalization. These are local inventory counts, not SAT runtimes.
2. **Gray affine evaluation.** For R factors, q positive homogenized
   exponents and G grid points, reflected mixed-radix Gray updates reduce
   the dense row-evaluation overhead from O(RqG) to O(RG), at unchanged
   precision p+nu. Integer binomial weights are updated by exact integer
   division, not inversion of an even residue.
3. **Antipodal centered evaluation.** It uses floor(G/2) product
   evaluations at precision p+nu+O-1, where O is the sum of odd exponents.
   The greater precision for some profiles prevents a universal runtime
   claim from sample-count halving alone.
4. **Projective roots-of-unity extraction.** For positive exponents one
   or two, fixing an axis removes an evaluation dimension. With q1 ones
   and q2 twos, evaluation counts are 2^(q1-1)3^q2 when q1>0 and
   3^(q2-1) otherwise, with stated exact precision budgets. Required cubic
   roots must already exist in the ring; no free ring extension is assumed.

Its reported extraction speedups (roughly 2.16--7.86x in one suite) are
for different coefficient-extraction workloads than our feature-table
benchmark. They cannot be compared numerically without matched workloads.
The paper explicitly does not claim a new worst-case logarithmic SAT order.

### Compatibility and remaining claim

The adaptive actual-matrix modes can be retained as an optional polynomial
setup step in our schedule: the packet's weight-profile domination preserves
the old entropy upper envelope and the same group locality. Gray/projective
coefficient extraction can also be retained where their stated hypotheses
hold. These are inherited improvements, not our discoveries. No uniform
better generic slope, complete SAT solver or end-to-end benchmark follows.

After correcting novelty, the remaining candidate contribution from our
work is the further explicit schedule certificates and their independent
checks. Practical artifacts are still useful reproducible validation, but
their mere presence is not a practical-performance improvement over all
late proposals.
