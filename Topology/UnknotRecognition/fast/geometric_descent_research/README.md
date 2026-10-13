# Cochain versus geometric first descent

This new protocol compares explicit `pachner_descent_method='cochain'` and
`'geometric'`. Both arms enable `reduce_pachner_descent`, vertex reduction,
boundary unlayering and strict 3→2 preprocessing. The default native method
remains cochain. The geometric search enumerates every D or UDD first descent
directly; its independent geometric packet does not carry a cover or cochain
witness. The raw whole-diagram recognizer is used throughout, including TT;
the separate visible-factor wrapper is not invoked.

This is a protocol, not a record of completed measurements. Do not execute the
audit or benchmark until the complete native/package source set is frozen and
the root agent coordinates CPU use. Generated evidence belongs outside this
package. Every native Python module and every package file, including this
README, is pinned at start and finish. No old research checker or archive is
imported, and historical source pins are not reinterpreted as current pins.

## Fixed whole-call audit

`common.py` fixes the same seven diagrams as the earlier cochain-enable audit:
circle, trefoil, figure eight, TT=`braid(3,[1,1,1,2,2,2])`,
T25=`braid(2,[1]*5)`, T27=`braid(2,[1]*7)`, and
W34=`braid(3,[1,-2]*4)`. Actual PDs and braid definitions are retained. The
audit makes exactly fourteen fresh recognition calls in that case order, with
cochain before geometric for each case. There are no additional supplied-source
normal queries, ray searches, heuristic simplifications or repeated attempts.

Each call has the same explicit finite search caps: 256 tree nodes, 10,000 LP
pivots, anchors, candidate hitting subsets, ellipsoid iterations and feasibility
calls; 256 sectors and 10,000 bases. The transversal conflict policy uses the
source model and polynomial LP policy with its default bounded fast-path prefix
(`lp_fast_path_pivots=None`). Sector order is diversified with quantum 64.
The shared reduction allowance `max_crushes` is unlimited; every accepted
reduction still strictly decreases the tetrahedron count. No wall cutoff is
used. Cochain and geometric macro searches are both the native uncapped fixed
U=1 implementations.

Every returned result is saved before independent replay, including every
INCONCLUSIVE result and its authenticated partial chain. Interruptions and
errors retain any returned result, an explicit active/failure record, and
incomplete coverage; unreturned work is never labelled complete. A complete
audit requires all fourteen returns and all replays. INCONCLUSIVE is not a
knot verdict and does not become a negative-cone claim.

The independent checker binds exact PDs, option maps, coverage, source pins and
result fields. It checks the full diagram recognition proof or partial chain.
Cochain calls must emit v4 chains and only legacy macro packets; geometric
calls must emit v5 chains and only geometric macro packets. Every macro is
additionally replayed against the exact preceding labelled source. Elementary
counts and D/UDD sizes are reconstructed directly from the corresponding proof
format. Accepted crush, peel, strict32 and macro totals must agree with the
chain and all nine budget contracts.

All retained counters must be literal nonnegative integers, and every capped
statistic must be present. Search/LP counters are reported diagnostics checked
for cap consistency, not independently reconstructed execution traces. Macro
nodes and work have different units in the two implementations; they cannot
be divided to obtain a runtime ratio. Unsuccessful searches contribute to
discovery totals, while accepted elementary counts describe only retained
macros. Complete returned work means the driver returned its diagnostic totals,
not that an independent checker reconstructed all internal operations.

After each two-call case, the checker compares the actual final labelled source
tables using type-sensitive equality. It records both source hashes and finite
manifold validation summaries, tetrahedron/vertex/boundary-face counts, terminal
endpoints and whether the two calls share a completed verdict. Equality is an
observed outcome, never an admission requirement. No isomorphism or knot-type
substitute is used. Different endpoints receive no transferred h bound. Even an
equal pair is not bound here to any older h witness; such a claim needs a separate
exact-source evidence replay. The terminal circle is compared as `None`, without
pretending that it has a retained triangulation.

## Optional fixed timing protocol

Before timings, all five predeclared cases—circle, trefoil, figure eight, TT and
T25—must have the same conclusive verdict under both arms in the new audit.
Otherwise the entire optional benchmark is declined with a retained preflight
failure. T27 and W34 are excluded before measurement, regardless of their
outcomes; they remain mandatory audit cases. There is no post hoc replacement
or selection of benchmark cases.

Each case receives one warmup per arm, three pairs in alternating order, and
one cochain A/A pair, exactly fifty calls. Pair order is cochain/geometric when
`(case_index+round_index)%2 == 0` and the reverse otherwise. Each sample retains
its complete result and replay summary. Exact result hashes must match the new
audit for the same case and arm; no diagnostic fields are discarded. A changed
or partial timed return is retained as a failed run, never silently excluded.

Timers include fresh whole recognition, independent complete/partial proof
replay and operation/source accounting, canonical full-result serialization and
SHA256. Native module initialization, validated input Diagram construction,
option preparation and reference serialization are outside the timer. The
runner asserts that no additional native module initializes inside a sample.
Evidence-file writes and cross-sample comparisons are outside. No Regina call
occurs in a timer. The checker revalidates fifty-call coverage, all payload
hashes, immutable warmups, pair order, medians and A/A ratios.

Ratios concern only the same completed whole-diagram verdict. They are not
same-source Euler-query ratios, since endpoints may differ. Keep every pair
and the A/A control visible, including regressions. These finite controls
establish neither a population timing claim, h monotonicity, a universal
performance gain, nor general quasi-polynomial recognition.

Run from `Topology/UnknotRecognition/fast` after source freeze:

```sh
PYTHONPATH=. python -B -S -m geometric_descent_research.audit \
  --output ../synthesis/data/geometric-descent-audit.json
PYTHONPATH=. python -B -S -m geometric_descent_research.check_evidence \
  --audit ../synthesis/data/geometric-descent-audit.json
PYTHONPATH=. python -B -S -m geometric_descent_research.benchmark \
  --audit ../synthesis/data/geometric-descent-audit.json \
  --output ../synthesis/data/geometric-descent-benchmark.json
PYTHONPATH=. python -B -S -m geometric_descent_research.check_evidence \
  --audit ../synthesis/data/geometric-descent-audit.json \
  --benchmark ../synthesis/data/geometric-descent-benchmark.json
```
