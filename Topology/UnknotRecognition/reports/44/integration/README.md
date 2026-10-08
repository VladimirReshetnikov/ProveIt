# Optional upstream integration — not executed in this release

The additive adapter preserves the reviewed `BoundaryTait` contract. It does not
change production dispatch, add a knot verdict, or bypass its geometric checks.
The delivered tests use a protocol fixture, NOT an upstream knot corpus.

To replay a real accepted-query stream against a complete local checkout:

```sh
python integration/replay_upstream.py \
  --checkout /path/to/ProveIt \
  --queries accepted_completion_stream.json \
  --output upstream_replay_result.json
```

The input file is a JSON array, with one record per suffix stage:

```json
[
  {
    "name": "a-descriptive-stage-name",
    "pd": [[1, 4, 2, 3], [3, 2, 4, 1]],
    "order": [0, 1],
    "stage": 1,
    "matchings": [[[1, 2], [3, 4]]]
  }
]
```

This shows the JSON shape only; it is NOT a retained validated upstream fixture.
Use completion streams exported by the maintained geometry and scanner. Every
listed matching is expected to be accepted; geometry declines fail the replay
instead of being silently skipped. The script checks values AND metadata against
the current rational observer and records the actual checkout revision.

## API

```python
from integration.boundary_adapter import ModularBoundaryObserver

observer = ModularBoundaryObserver(existing_boundary_tait)
value_and_metadata = observer.evaluate(matching)
batched = observer.evaluate_many(matching_stream)
```

`evaluate_many` validates every geometry query, compiles the terminal partitions
to a merge trie, then uses exact modular dynamic updates. Its compilation cost is
additional to the supplied-tree theorem. A badly shared stream may perform worse
than the static method. Initial prime preparation and every high-level static
path do not yet support the maintained production deadline and inference-budget
contracts. Keep this adapter research-only until that work and a full upstream
replay are complete.

The algebra verifier checks the supplied graph quotient, not the derivation of
that graph from a planar diagram. The phase and projection-component metadata
must continue to come from the maintained geometry object.
