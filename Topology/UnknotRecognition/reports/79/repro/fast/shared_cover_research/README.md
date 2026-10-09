# Shared connected-cover Pachner search

This extension replaces one bounded search per initial dual-graph region with
one search of their union. It retains the maintained exact native move
generator, integral cochain transport, and source-bound endpoint verifier.

## APIs

```python
from fastunknot.pachner_cover_search import (
    search_pachner_cover, find_pachner_descent,
)
from fastunknot.pachner_cover_verify import verify_pachner_descent

answer = find_pachner_descent(
    triangulation, heights,
    max_upward=1,
    max_nodes=10000,
    max_regions=100000,
    max_work=2000000,
)
if answer['status'] == 'DESCENT_FOUND':
    assert verify_pachner_descent(
        triangulation, heights, answer['certificate'], max_upward=1,
    )
```

`max_upward` counts **all** 2–3 moves in a trace. The default descent radius
is `min(t, 3*max_upward+3)`, supplied by the first-descent birth-component
theorem. This is a tetrahedron count and an initial consumed-cell cover bound;
it is not graph distance and is not the maximum height above the initial size.

`search_pachner_cover` exposes the more general finite family. Its exact
parameters are `max_region_size`, `max_components`, and `max_upward`. The
initial cells actually consumed need only be contained in a permitted region.
They may be a disconnected subset of that connected region. New cells born
inside a trace remain eligible. Only `sleep` and the small-instance reference
method `naive` are supported. The older restarted implementation and its
commitment route remain unchanged.

| Result | Meaning |
|---|---|
| `DESCENT_FOUND` | Independent replay verifies strictly fewer tetrahedra and the total upward bound. |
| `COMPLETE_BOUNDED_DESCENT` | No strict descent exists within the supplied total upward bound, using the sufficient connected radius. |
| `COMPLETE_BOUNDED_LOCAL_DESCENT` | The explicitly smaller local search family is exhausted. |
| `COMPLETE_BOUNDED_COVER_FAMILY` | The declared union of covered cochain endpoint families is exhausted. |
| `DISC_FOUND` | Independent source replay verifies an essential normal-disc component. |
| `ENDPOINT_SELECTED` | A caller-supplied endpoint predicate selected a reachable endpoint. |
| `INCONCLUSIVE` | At least one required index, search, work, or disc-query operation was capped. |

None of the exhaustion results is a nontrivial-knot certificate. A supplied
manifold's disc certificate also needs the maintained diagram-exterior binding
before it can be used as a diagram recognition certificate.

## Exact sharing and certificates

The complete cover family is indexed by source-cell incidence. A search frame
retains exactly the cover IDs containing its accumulated consumed original
cells. Advancing an event intersects those IDs with the lists for newly
consumed source cells. Empty intersections reject that event. At the root,
`None` represents all covers without copying the full index.

This construction recognizes exactly the union of the old per-region trace
languages. Region containment is hereditary under taking prefixes and depends
only on the total original consumption. Consequently swapping two disjoint
consecutive moves in an admissible trace remains admissible, including when
other permitted prefixes cannot combine because no common cover contains them.
The maintained sleep-set reduction therefore applies to the union language.
Exact marked endpoint deduplication suppresses repeated endpoint queries only;
it never deletes continuation frames.

Queued branches retain a parent and pending geometric event. Native move
construction and cochain transport occur only when that branch is visited.
This avoids computing unused siblings before an early positive result, and a
node cap is checked before materializing the next unvisited child.

Each endpoint retains the existing `pachner-cochain-endpoint-v1` schema with a
concrete admissible covering region in `active_initial_tetrahedra`. The new
scope verifier counts that region's induced dual-graph components itself and
uses the maintained independent source replay. It imports no region enumerator,
search, native move producer, or cochain transport producer. Descent verification
also checks the actual total upward count, the final tetrahedron count, and
the identity `final = initial + upward - downward`.

## Resource limits

`max_regions` is a cap on the complete index, including the empty region.
If index construction stops early, the status is `INCONCLUSIVE` even if some
regions were fully indexed. `max_nodes` counts visited frames. `max_work`
counts cooperative checkpoints throughout preparation, indexing, search and
positive replay; it is not a bit-operation count. `max_cycles` bounds each
optional disc query. If any required endpoint disc query is capped, final
family exhaustion remains inconclusive. User callback exceptions propagate
unchanged, including callbacks raising the same exception class as a budget.

## Validation and benchmark

From the containing `fast/` directory:

```bash
python -m unittest tests.test_pachner_cover_search -v
python -m shared_cover_research.benchmark \
  --sizes 1,2 --repeats 3 \
  --output shared_cover_research/results/exhaustion.json
python -m shared_cover_research.benchmark \
  --descent-only --sizes 1,2,4,8 --repeats 3 \
  --output shared_cover_research/results/descent.json
python -m shared_cover_research.benchmark \
  --replay shared_cover_research/results/exhaustion.json
python -m shared_cover_research.benchmark \
  --replay shared_cover_research/results/descent.json
```

The tests compare exact incidence intersections against literal subset
containment, compare complete endpoint families against the older restarted
and naive searches on genuine solid-torus triangulations, and exercise scope
rejection, independent replay with producers disabled, callback isolation,
and exact resource boundaries. The six-cell fixture has no initial downward
move; radius five fails for `U=1`, while radius six finds one upward and two
downward moves with all six original gadget cells consumed.

The benchmark constructs each source once and uses identical `U=1,r=6`
options for both implementations. Full-exhaustion timed runs disable endpoint
collection and disc queries in both. First-descent timed runs include the same
independent verifier. Run order alternates, and every sample is retained.
Endpoint equality is checked separately by comparing full exact signed-cochain
isomorphism tuples, not digests. This comparison forgets source cell markings;
source reachability and scope are independently certified for every retained
shared endpoint and every old geometric representative.

The fixture family is designed to isolate this bottleneck. Its finite measured
speedups do not predict runtime on arbitrary knot exteriors. The theorem gives
the relevant parameter dependence; a global small-upward-barrier theorem would
still be needed for a general quasi-polynomial unknot-recognition algorithm.
