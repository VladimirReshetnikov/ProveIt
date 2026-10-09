# Compiled interval-orbit point queries

This additive experiment compiles an independently verified AHT orbit trace
into exact point queries. The original orbit producer, independent verifier,
normal geometry adapter and default recognizer remain unchanged.

## Public API

```python
from fastunknot.interval_orbits import IntervalPairing
from fastunknot.orbit_index import prepare_orbit_index

pairings = [IntervalPairing(0, 15, 8, 23)]
index, discovery = prepare_orbit_index(24, pairings)
assert discovery.complete
assert index.representative(22) == 6
assert index.same_orbit(2, 18)
assert index.count == 8
assert {index.select(i) for i in range(index.count)} == set(range(8))
assert index.minimum_intervals == ((0, 8),)
assert index.orbit_rank(22) == 6
assert index.select_minimum(6) == 6
```

`OrbitIndex.from_certificate(size, pairings, certificate)` accepts a complete
source-bound certificate without rediscovering an orbit schedule. It first
runs the maintained independent verifier. Preparation copies both source
pairings and the supplied certificate; the retained index data are immutable.
Invalid or unfinished certificates raise `ValueError`.

`representative(x)` returns the **minimum original point** of the orbit and is
independent of the valid reduction trace used. `locate(x)` additionally returns
a binary ordinal and operation counters. `select(i)` recovers the minimum of
the orbit with that ordinal, without enumerating earlier orbits. Ordinals use
trace emission order; they are not stable component names across traces.

The additional `minimum_intervals` property lists the complete set of original
orbit minima as immutable, sorted, disjoint half-open intervals. The number of
intervals is at most the number of static gaps in the source trace, even when
the number of components is exponentially larger. `minimum_rank(minimum)` and
`select_minimum(rank)` use binary search over this union and are inverse
canonical rank/select operations. `minimum_rank` rejects a source point that
is not a minimum. `orbit_rank(point)` first finds the point's minimum. These
sorted ranks are stable across valid traces of the same source relation.

The documented factory is the verification boundary. As with other in-process
Python objects, manually constructing or modifying private class internals is
outside that contract. Query arithmetic is a small trusted implementation of
the proved point-transport formulas, not a new independently replayed proof for
each returned minimum. The compiler shares canonical row and transmission
reconstruction with the existing trace verifier. The audit independently
checks all returned minima against literal union-find graphs.

All functions accept cooperative `check` callbacks. The discovery factory
returns `(None, discovery)` if the existing `max_cycles` allowance expires.
That allowance measures discovery cycles; it does not meter verification,
compilation or later queries. Supplied integer endpoints and queried points
accept exact integer/hexadecimal transport. No represented points are expanded.

## Reproduction

Run from the repository's `Topology/UnknotRecognition/fast` directory:

```bash
python orbit_index_research/audit.py
python orbit_index_research/benchmark.py --rounds 7
python orbit_index_research/rank_select.py --rounds 7
```

The audit writes `results/orbit_index_audit.json` and
`results/orbit_index_tests.log`. The benchmark writes
`results/orbit_index.json`; redirect stdout if a separate human-readable timing
log is wanted. Both drivers pin the source files they use before and after
execution. The third driver writes `results/orbit_rank_select.json`; it compares
prepared emission-order selection to prepared canonical sorted selection, with
corresponding ranks chosen to request the same original representative. It
also measures canonical rank queries. Preparation is reported separately and
excluded from every lookup timer. No optional native package is required.

The eleven tests cover every at-most-two-generator system on universes through
five points, up to generator order (7,398 indices across both merger rules),
3,200 random relations under both maintained merger
rules, 67 supplied normal vectors under both rules and both surface/boundary
arc graphs, every local event type, original-minimum recovery after coordinate
contraction, noncanonical emission orders, malformed proofs, source rebinding,
disabled producer entry points, cooperative cancellation, and binary endpoints
with 16,000 to 20,000 bits. Complete minimum sets and canonical sorted
rank/select agree with literal graph calculations. A separate fixture attains
the sharp 512-interval minimum-set bound while representing a 4,107-bit
universe and a 4,106-bit component count.

The benchmark has five shuffled arms and one excluded warmup. The compiled arm
includes trace discovery, independent verification, compilation and all point
comparisons. The current `same_orbit` API is one baseline. A stronger baseline
shares the initial count and applies exact connected/singleton shortcuts before
discovering augmented relations. Identical controls accompany the shared and
compiled arms. Normal triangulation/vector construction and conversion to
interval systems are outside every timer: this measures repeated queries on a
supplied interval relation, not a complete normal-surface call or unknot search.

## Integration boundary

Only `fastunknot/orbit_index.py` is new runtime code. Its direct dependencies
are existing `integer_codec`, `interval_orbit_verify`, and (for discovery only)
`interval_orbits`. The test and research drivers are additive. No public import
in `fastunknot/__init__.py` or default recognition dispatch is changed.

The mathematical section also proves a signed-cover point-query corollary.
There is no new signed wrapper in this delivery. Component keys refer to one
source interval presentation and retain neither arbitrary attachment maps nor
a bound on the number of states in a knot hierarchy.
