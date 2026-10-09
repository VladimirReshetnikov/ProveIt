# Raw singleton saturation and compiled interval-orbit queries

This continuation targets ProveIt commit
`fdeb5b1a20b84b93cb150e0232031837bb7d30cb`.

It adds two exact operations. It does not establish general quasi-polynomial
unknot recognition. The complete mathematical article and experimental records
are supplied with the integration archive.

## Complete raw singleton discovery

`fastunknot.raw_saturation` computes source Horn closure using exact raw
occurrences in the shared word grammar. For specified survivors, it decides
whether **any** sequence of raw singleton Tietze eliminations can eliminate
all other generators. Free/cyclic reduction and other presentation moves
between eliminations are outside that theorem.

The production option tries every singleton survivor, then compiles a successful
source plan into the existing version-eight `elimination_batch` format. The
original independent verifiers are unchanged. All residual relators must pass
the existing rank-one exponent-zero check.

```python
from fastunknot import Diagram, recognize
from fastunknot.group_certificate import group_decide

diagram = Diagram.from_braid(64, list(range(1, 64)))
result = group_decide(
    diagram, seconds=None, max_work=10_000_000,
    raw_saturation=True,
)
assert result['status'] == 'UNKNOT'

# Full recognition retains the usual earlier filters.
answer = recognize(diagram, use_group=True, group_raw_saturation=True)
assert answer.is_unknot
```

CLI:

```bash
python3 -m fastunknot recognize examples/unknot_braid40.json \
  --group-raw-saturation
```

The CLI switch enables the group stage. In the library API, use
`use_group=True` with `group_raw_saturation=True`. The default is false.
The option implies compressed group search and compressed verification.

The low-level interfaces are `build_index`, `seed_closure`, and
`find_rank_one_plan`. Discovery does not change roots, the live alphabet, or
grammar nodes. Source caches bind arena identity, ordered roots, and live
labels. An uncapped completed failure is exact only for raw singleton
reachability; an interrupted query or attempt cap has no negative knot meaning.

After source metadata, fixed-seed closure costs O(r+m+I) structural operations;
all singleton seeds cost O(r(r+m+I)). Source-summary bit costs and historical
arena storage are additional and remain explicit in the article. A complete
raw epoch can be compiled into O(M+qH+q) grammar nodes from its frozen source.
Only same-donor flattening is guaranteed to preserve the previous epoch's
free-group homomorphism; raw spellings can differ.

## Prepared orbit membership and canonical rank/select

```python
from fastunknot.interval_orbits import IntervalPairing
from fastunknot.orbit_index import prepare_orbit_index

index, discovery = prepare_orbit_index(
    24, [IntervalPairing(0, 15, 8, 23)]
)
assert discovery.complete
assert index.representative(22) == 6
assert index.same_orbit(2, 18)
assert index.minimum_intervals == ((0, 8),)
assert index.orbit_rank(22) == 6
assert index.select_minimum(6) == 6
```

`OrbitIndex.from_certificate` verifies a complete source-bound orbit trace and
compiles immutable retained data. It does not call the orbit producer. The
representative is the least **original** integer point in the component and
agrees across valid traces of the same source relation.

`minimum_intervals` is the sorted union of half-open intervals containing all
component minima. If the trace contains g static gaps, there are at most g
intervals. Canonical `minimum_rank` and `select_minimum` use binary search and
O(B log(g+2)) bit work after preparation. `orbit_rank` first finds the queried
point's minimum. The older `select` interface uses trace-emission ordinals;
those ordinals can differ between valid traces.

The factory is the verification boundary. Query arithmetic is audited trusted
code; there is no separate per-query proof format. The index does not change
recognition dispatch, find normal vectors, or encode arbitrary attachment maps.
The mathematical signed-cover corollary is not a new implemented signed API.

## Evidence and scope

The final combined suite passes 1,114 tests, compared with 1,090 at the pinned
baseline. The independent raw audit checks 85,303 occurrence matrices and
1,896 completed signed raw epochs. Source replay checks use both old and new
verifiers. Orbit audits make 315,554 explicit minimum comparisons, in addition
to membership and canonical rank/select checks.

Recorded improvements include a 46.720 median paired ratio for the complete
group stage on an elementary 255-crossing unknot closure, and ratios 15.629
and 20.686 for complete 32-query orbit workloads on two supplied normal systems.
The full recognizer corpus does not show a broad speedup. Negative controls,
failed probes, and resource-limited outcomes are retained; the article explains
the timing boundaries and the reasons for keeping the group option opt-in.

See `raw_saturation_research/`, `orbit_index_research/`, and `results/` for
reproduction drivers and full evidence. The article provides complete proofs,
counterexamples, encoded-cost conventions, and ten further research questions.
