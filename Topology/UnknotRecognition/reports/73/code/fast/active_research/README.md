# Certified active normal cones

This is an additive research path for supplied finite triangulations. It does
not change the main recognizer and does not infer an unknot verdict from a
positive relaxed LP or from a positive-Euler normal surface.

`fastunknot.normal_active.active_positive_cone` uses one lifted exact LP to
produce a complete active-support primal/dual pair, or a source-sized negative
Farkas multiplier. `normal_active_verify` independently checks these objects
without importing an LP solver. Binary incompatible-coordinate splits support
complete proof trees; the normal wrapper also checks every triangle-anchor
assignment needed for canonical positive-Euler exclusion.

The default search runs a smaller ordinary LP first. Negative cones and an
already admissible basic witness terminate immediately. The larger support
query runs only after an incompatible positive relaxation. `precheck=False`
selects the pure experimental active-support tree. All node, depth and pivot
caps are inconclusive outcomes.

## Evidence

`sources.json` freezes seven actual finite manifold triangulations from the
preceding dual-certificates package, with source archive hash and construction
descriptions. `results/audit.json` contains the literal masks, timings, counters,
and exact certificates for 20 normal-coordinate queries. Seventeen positive
cases agree with a unary baseline that skips coordinates already witnessed by
an earlier LP. Three negative trefoil cases terminate in the ordinary precheck.
Seven complete normal-search controls include a verified 20-anchor negative
trefoil proof and positive meridians in layered solid tori.

The single lifted LP was **slower in all 17 positive paired timings**. The unary
baseline took approximately 0.00056–0.276 seconds using 2–11 LP calls; the lift
took 0.00466–6.69 seconds using one larger LP. An exploratory unrestricted
five-tetrahedron trefoil lift took 2,664 pivots and 78.58 seconds. The default
precheck avoids this negative-case regression. A reduced LP-call count is not
a runtime improvement. This module is retained for its proof interface,
structural analysis, and future sparse-backend work.

The root ambiguity-rank statistic in the normal wrapper is the maximum over
active queries actually performed. Zero when none ran is an empty-observation
convention; it does not assert that the underlying unrestricted cone has rank
zero. Indeed the article proves that every unrestricted one-vertex anchored
root has active ambiguity rank at least `t-1`.

## Reproduction

From `fast/`:

```sh
python -m unittest discover -s tests -p test_normal_active.py -v
python active_research/replay.py
python active_research/benchmark.py --seconds 25
```

The first command runs 17 tests, including malformed rationals, hidden active
coordinates, omitted binary branches, cancellation, source/anchor substitution,
and an actual essential meridian passed to the maintained geometric counter.
The second replays 37 support proofs and seven complete normal-search proofs
without any solver. The third regenerates the paired experiment. An optional
`--include-slow-negative` flag deliberately invokes the expensive lift on
negative cases; the per-query wall allowance still applies.

The inherited `exact_lp.py` is copied unchanged from the preceding incoming
dual-certificates package. It uses exact Bland simplex and has no polynomial
pivot guarantee. The article's polynomial per-node theorem refers to a
polynomial rational-LP backend, not to this implementation.
