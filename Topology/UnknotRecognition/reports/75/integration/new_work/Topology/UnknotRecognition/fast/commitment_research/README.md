# Bounded Pachner search by commitments and commuting traces

This additive research delivery enumerates all cochain endpoints reachable by
formal 2–3 and 3–2 moves with at most a supplied number of upward moves. It
also accepts a supplied set of original tetrahedra that may be consumed. Cells
created during search are eligible; protected original cells remain present.

The new source modules are `fastunknot/pachner_commitments.py` and
`fastunknot/pachner_commitments_verify.py`. They use the maintained Pachner
replacement checkers and the incoming geometric-transport implementation. No
existing default recognizer is modified.

## Interfaces

```python
from fastunknot.pachner_commitments import search_pachner_endpoints

answer = search_pachner_endpoints(
    triangulation, heights,
    max_upward=1,
    active_initial_tetrahedra=[0, 1, 2],
    method="sleep",
    max_nodes=10000,
    max_work=None,
    seek_disc=True,
)
```

`commitments` is the finite-assignment algorithm with the direct proved bound.
`sleep` avoids permutations of disjoint moves and inherits that bound by
visiting at most one representative of each commuting trace class. `naive` is an explicit small-input
reference traversal. The sleep and naive routes use identical legal move
generation and transport. Independent Regina comparisons separately check
that move generator and every replacement in the audited states.

If `r` original cells may be consumed and at most `u` upward moves occur,
there are at most `r+u` downward moves and `3r+5u` assigned tetrahedron
incarnations. Every incarnation has eleven possible commitments: idle, six
local edges, or four local faces. With no upward moves there are seven choices.
The direct assignment bounds are therefore `11**(3*r+5*u)` and `7**(3*r)`,
up to a polynomial factor. The generic assignment method can be much slower
than the sleep traversal on small inputs; the saved results include that
regression.

The sleep-set inheritance uses the specific geometric event relation.
Disjoint formal replacements preserve each other's geometric enabledness and
exact event keys. A different replacement sharing a source incarnation consumes
that incarnation, permanently disabling the former event; it cannot later
reappear with the same birth name. The total upward count is unchanged by
commutation. These persistence and nonresurrection conditions are necessary
parts of the proof, and no analogous bound is asserted for an arbitrary
state-dependent independence relation. The bound concerns traces and their
finite prefixes, including endpoints at which additional moves remain legal.

Exact dictionary interning represents birth terms as a DAG. A key contains the
move kind and the integer incarnation IDs and local ports of its source cells.
Tuple equality checks names exactly; a cryptographic hash is not used to merge
states. Output certificates do not depend on those internal names.

`DISC_FOUND` includes independent source-to-endpoint replay and a verified
essential-disc component certificate. `ENDPOINT_SELECTED` means only that a
caller callback selected a reachable endpoint. `COMPLETE_BOUNDED_FAMILY` means
every represented cochain endpoint was visited. A cap yields `INCONCLUSIVE`.
None of these family-exhaustion statuses is a negative knot certificate.

Every certificate records the full sequence of intermediate triangulations and
cochain transport proofs. The independent consumer checks the allowed upward
count, original-cell ancestry, every move, every transported cochain, and the
final coherent coordinates. Full triangulations in the transcript can take
quadratic space along a long trace. The module does not claim compact local
transcripts or preservation of fibre connectivity through reselection.

## Reproduction

Run these commands from the enclosing `fast` directory:

```sh
PYTHONPATH=. python -m unittest tests.test_pachner_commitments -v
PYTHONPATH=. python -m commitment_research.run audit --output reproduced_audit.json
PYTHONPATH=. python -m commitment_research.run benchmark --repeats 3 --output reproduced_benchmark.json
PYTHONPATH=. python -m commitment_research.run replay --input commitment_research/results/audit.json --output replay_audit.json
PYTHONPATH=. python -m commitment_research.run replay --input commitment_research/results/benchmark.json --output replay_benchmark.json
PYTHONPATH=. python -m commitment_research.regina_audit --input commitment_research/results/audit.json --output reproduced_regina.json
```

Only the final command requires optional Regina. The recorded version is 7.4.
The replay mode imports the endpoint verifier without importing the search,
Pachner move, or cochain-transport producers. Its maintained disc checker shares
the project's low-level geometry and component-proof code.

## Retained results

- Eight focused test methods passed, including source ancestry, exact commuting
  diagrams, malformed proof rejection, callback propagation, and 2,048-bit
  height input.
- Eleven complete source/scope cases were compared across all three search
  routes. Exact rooted-traversal cochain-isomorphism keys agreed in every case.
- The audit retains 91 accepted endpoint proofs and rejects 90 changed final
  coordinate proofs. Independent replay accepted all 91 audit proofs and all
  126 retained benchmark proofs.
- Regina agreed on all legal move sites for 23 distinct labelled source states
  and on all 176 resulting replacement triangulations.
- The maintained eight-tetrahedron coherent obstruction has no certified
  initial disc in the tested fibre. The search finds a verified disc after one
  downward move, with two endpoint disc queries. This is a supplied-manifold
  result, and is not an additional knot-diagram coverage claim.

For a real solid-torus family containing `p` independent inverse bipyramids,
the exhaustive naive traversal visits `sum(p!/(p-j)!, j=0..p)` trace prefixes.
The sleep traversal visits exactly `2**p` subsets in the tested instances.
At `p=6`, these counts are 1,957 and 64. Three measured randomized-order pairs
give medians 9,224.509 ms and 415.842 ms, with median within-pair speedup
22.183. At `p=1` the sleep method regresses (paired ratio 0.876). Input fixture
construction and external replay are excluded from timing; complete search,
internal move replay, and endpoint-certificate copying are included. A warm-up
pair per case is retained separately. Shared-host timing noise remains visible.

The recorded benchmark improves bounded geometric-family enumeration. It does
not measure or establish a general end-to-end unknot recognition speedup.

## Fixture provenance

`fixtures.py` constructs disjoint inverse regions by performing one 2–3 move
inside every disjoint adjacent pair of cells of a Fibonacci layered solid
torus. Its construction does not call the new search. The independent move
and cochain proofs authenticate every construction step.

`coherent-obstruction-certificate.json` is copied unchanged from
`Topology/UnknotRecognition/synthesis/data/coherent-obstruction-certificate.json`
at ProveIt commit `66098968e88bba797143ac1bf7ad0ac4c5f697df`. It is input research
evidence, not a claim newly established by this delivery. `results/audit.json`
retains the new one-move essential-disc proof on its final triangulation.
