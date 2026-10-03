# Independent audit addendum: displacement, contextual reads, and validation

## Result and version

All three requested points are confirmed for the frozen candidate `lazy_reversible.py`, SHA-256 `42e8aa65c05fcf373a03a02be51ebb89a4fdcb1f1070ad776ffe1e8e99049c61`, against reference SHA-256 `f95a6028c9d3cc6f8b0b497cfc0cad68104da6d70e55205df04ad234e5d0c76f`.

Only this addendum and new `addendum_checks.py`, logs, and receipts were written. Existing implementation, proof, tests, and prior audit artifacts were not edited. The targeted checks passed under normal Python and `python -O`; checks use explicit exceptions and are not removed by optimization.

## 1. The 2B3 displacement bound

The precise statement is an existence-of-matching bound for indistinguishable particles. It does not add persistent physical labels to the CA.

For a factor at key u, both finite endpoint supports satisfy

`u+P, u+Q subset [u-B,u+B]`, with `|P|=|Q|` and `B <= B3`.

Consequently every input endpoint position `u+p` and every output endpoint position `u+q` satisfy

`|(u+q)-(u+p)|=|q-p| <= 2B <= 2B3`.

Choose any bijection between equal-cardinality endpoint supports, such as their increasing-order matching. Unchanged particles can be matched to themselves. Within one factor, eligible keys are more than M apart, while `M >= 4B+2`; their radius-B rewrite windows are therefore disjoint. Raw/isolation tests also exclude any unchanged particle from the unused sites of a rewrite window. These local matchings combine into a whole-support matching, each matched displacement at most 2B3.

The containment bound holds for **every factor family**, including reverse endpoints:

- Free pairs: coordinates are `{0,d+}` or `{w,w+d-}`; their magnitudes are at most `D+1=B2`
- Phase pairs: coordinates are between 0 and D, hence in `[-B2,B2]`
- Behind triples: the largest possible anchor magnitude is `L+1`; adding the signed-mode gap gives the conservative bound `L+1+D=4D+5=B3`
- Ahead triples: anchor magnitudes are at most L, hence all sites have magnitude at most `L+D=B3-1`
- Dispatch, commit, direct, and home-phase triples: anchors have magnitude S, hence sites have magnitude at most `S+D=3D+2 <= B3`
- Endpoint forward support: anchor magnitude S and marker 0, giving the same `S+D` bound
- Endpoint reverse support: the marker has coordinate `v*Delta` of magnitude at most 1, and pair anchor `v*Delta-v*S` has magnitude at most `S+1`; thus every site has magnitude at most `S+1+D=3D+3 <= B3`
- Near-phase triples: anchor magnitude at most L, giving `L+D=B3-1`

Here D is at least 2 for every accepted source: at least one control must exist to name start and halt. The displayed inequalities also hold for all nonnegative D relevant to the formulas.

After K changing factors, composing these particle matchings and applying the triangle inequality gives displacement at most `2K*B3` per matched particle. In particular, if initial coordinates have magnitude at most H0, every occupied coordinate encountered during the step has magnitude at most `H0+2K*B3`. Many eligible occurrences in one factor do not multiply this bound; a particle participates in at most one of that factor's disjoint rewrites. Nonchanging factors contribute zero.

Contextual radii involving Z and J affect which particles are **read**, not where particles are written. They therefore belong in the arithmetic bit-width bound but do not enlarge the 2B3 movement bound. The `PROOF.md` bound including `Z+J` for read coordinates is appropriate.

Executable checks verified equal endpoint cardinalities, every endpoint's containment, and all input-output coordinate-pair distances for 2,672 gate descriptors, comprising 23,488 endpoint-pair distances on the J=17 and J=64 sources. The family argument, rather than these finite samples, establishes the general bound.

## 2. Multiple-particle contextual reads

A contextual guard's left read sites are exactly

`{u-Z-k : k=0,...,J}`,

and its right read sites are exactly

`{u+Z+k : k=0,...,J}`.

Since accepted supports contain only exact integers, these sets are exactly the integer sites of the closed intervals `[u-Z-J,u-Z]` and `[u+Z,u+Z+J]`. Bisect-right at the upper endpoint minus bisect-left at the lower endpoint therefore counts precisely the particles the original explicit k-loop finds.

For either side:

- Count zero returns the class `J+1`, matching the original all-zero-read convention
- Count one returns the unique k: `u-z-Z` on the left, `z-u-Z` on the right
- Count at least two returns false immediately, irrespective of the truth table

Particles just outside either endpoint do not count. Both boundaries are included. A support is a set, so repeated occupancy of one site is impossible; for J=0 a single read interval cannot contain two distinct occupied integer sites. The two sides are treated separately, exactly as in the original. None of these facts depends on the state being a valid encoding.

The targeted suite used actual all-true dispatch class guards at J=17 and J=64, so a false result caused by multiple reads could not be hidden by a false table entry. It checked 864 patterns spanning empty, singleton, endpoint, interior, two-particle, and immediately-outside combinations on both sides, translated by 0, `-10^50`, and `10^70`. Every original/sparse/independently-expected result agreed. These are checks of the contextual predicate itself; unrelated gate isolation or raw-key exclusion cannot mask an error in these cases.

## 3. Source validation, strict types, and arbitrary finite J

### Mathematical equivalence

The validators invoke the same pinned primitive exact-type/schema checks, guard parser, and postfix guard evaluator. Every row is visited in the same input order. Each row's domain and image tables use the same representative counter pairs `(c0,c1)` with `0 <= c0,c1 <= J+1`, the same natural-output check, and the same inverse-counter reconstruction. The same syntactic threshold test rejects an atom if `k>J` or if the selected-counter update makes its image threshold exceed J. This check applies even inside an identically false compound predicate, as in the frozen compiler.

The differing overlap implementation is equivalent for every finite J. Let `N=J+2`. Class `(c0,c1)` maps injectively to integer bit index `c0*N+c1`. For each control, the accumulated union mask records exactly classes enabled by at least one incident branch. Intersecting that union with a new branch mask identifies precisely classes enabled by at least two branches; accumulating these intersections records every and only forbidden class. Python integers do not truncate at a machine-word boundary.

After **all** rows have been validated, controls are visited in their original order. The least set bit of the union of domain and image conflict masks identifies the first `(c0,c1)` in the frozen row-major class order. Testing the domain conflict first at that bit reproduces the original domain-before-image preference. Thus acceptance, rejection class/message for the audited schema/semantic conditions, branch tables, and immutable source values agree. The argument is uniform over all finite nonnegative J; it does not extrapolate from J=64 by empirical assumption.

### Targeted checks

Both execution modes passed 123 exact source-outcome comparisons, including:

- 32 accepted large-cut sources with J=17/J=64, both counter sides, increments, decrements, zero updates, compound predicates, maximum accepted image thresholds, and predicates on the unmodified counter
- Threshold failures above J, increment image thresholds above J, dead-predicate threshold failures, and guards permitting a negative post-counter
- 54 malformed-schema cases, including exact-type rejection of dict/list/str/int subclasses, bools in integer fields, floats, wrong containers, non-string keys, subclassed string keys, missing/extra keys, malformed Boolean-expression nodes, and cyclic guard nodes
- 15 overlap-precedence cases, including the highest class bit, tied domain/image conflicts, an earlier image conflict versus a later domain conflict, and malformed last rows following earlier overlapping branches at J=0/J=17/J=64

Python does not permit subclassing bool. The suite explicitly confirms that language restriction and separately tests actual bool values where exact integers are required. It also verifies returned ledgers, branch tables, and source snapshots for accepted cases.

### Limits of the large-J evidence

J=17 and J=64 test real multiword conflict masks and large class tables; they are still only two finite positive cuts. The tests do not exhaust every malformed object graph or all sources, prove the original compiler's source-machine theorem, establish practical feasibility at arbitrarily large binary-encoded J, or guarantee identical resource-exhaustion behavior.

The uniform validation result follows from the shared primitive routines, identical class computations, and exact conflict-mask argument above, assuming sufficient resources for both validators to finish. The lazy validator intentionally retains explicit `(J+2)^2` tables and masks whose bit lengths scale with that class count. Therefore large J remains expensive, and allocation/timing/resource-failure behavior need not match the eager implementation. No polynomial-in-log(J) claim is warranted.

## Reproduction and receipts

Run `python addendum_checks.py` and `python -O addendum_checks.py` in this directory. Results are recorded separately in `addendum-receipt.json` and `addendum-receipt-optimized.json`, including the frozen implementation hash, all case outcomes, execution mode, and test counts. The tested core hash was checked before and after each run and remained unchanged.
