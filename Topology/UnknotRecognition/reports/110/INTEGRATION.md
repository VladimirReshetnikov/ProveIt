# Integration contract and proposed placement

Targeted reference revision: `ac9c845a5c507c5d7a17d45b2d8de84fc046d455`.

Place the delivered report under the next available `Topology/UnknotRecognition/reports/<NN>/`. Do not apply a production change during mere intake. No production patch is supplied because the current native interfaces, source authentication and transport must be reviewed together, and no full checkout was executed here.

## Entry point

The inspected `fast/fastunknot/core_handlebody.py` exports capped occurrence rows from authentic handle cycles after a selected forest. Those counts distinguish 0, 1 and at least 2, which is sufficient for this optimizer. They are not exact passive-count transport or embedded attaching words.

`integration/occurrence_adapter.py::propose_occurrence_reduction` accepts a dictionary of original nonnegative row labels to dictionaries of original column labels and unsigned counts. Optional weights must have exactly the same row-label inventory. It validates the abstract data, runs forced private peeling followed by width-dependent optimization, and independently replays the selected matching on the original matrix. A dense-adaptation limit and state budget can return `INCONCLUSIVE`.

Its status `REDUCTION_PLAN` means an abstract legal schedule exists. It is never a knot or handlebody verdict. The returned `remaining_rows` are unresolved genuine source two-handles. Preserve every geometric one-handle not explicitly cancelled, including those whose columns were isolated or omitted from the optimization copy.

```python
from integration.occurrence_adapter import propose_occurrence_reduction

result = propose_occurrence_reduction(
    {7: {100: 1, 102: 1}, 17: {100: 1, 102: 2}},
    weights={7: 3, 17: 9},
)
assert result["status"] == "REDUCTION_PLAN"
assert result["remaining_rows"] == [7]
```

## Retain the existing fast paths

The full private queue should remain the first operation. It is complete for full elimination in the unsigned positive calculus and is much cheaper than the width DP. The new prepeeling theorem says an optimal solution can always include this queue's removed rows. On a fully peelable input, no DP is needed.

The minimum-fill decomposition is a heuristic, not a promised approximation to minimum treewidth. A validated geometry-supplied decomposition is preferable when available. The reference state limit is checked after a table is built, not before every allocation; it is not a strict memory ceiling. Production adaptation should integrate the native cumulative work budget and cancellation callback rather than interpret a local state cap as an end-to-end resource guarantee.

## Geometric replay requirements

Reconstruct counts from source charts before checking a supplied schedule. Do not trust producer-declared transformed counts, signed exponent sums, or a mere homology presentation. Pass every selected unit pair through the actual geometric cancellation verifier. That verifier must transport all surviving attaching curves, repeated passive intersections, cyclic order and protected patterns. Numerical optimization has not supplied those objects.

`retained_weight` means retained in the matching, hence cancelled; `deferred_weight` means unresolved row weight. Avoid confusing the two. Deferred rows that become zero after positive transport must not be silently removed. Do not call a final genus/handlebody census while unresolved two-handles remain unless that terminal verifier has its own applicable theorem.

## Review before promotion

Compare the ordered-state theorem and prepeeling result with the newly incoming private-cocore transport report; only that archive's metadata was accessible here. Run source-geometric regression tests and independently replay all old and new accepted traces. Measure occurrence preparation, forest choice, decomposition, optimization, geometric replay, serialization, and downstream residual processing together. Include small cases and cases where no new useful reduction is found.

The delivered tests exercise synthetic unsigned matrices, connected graph templates, bad inputs and source-label preservation. They do not authenticate native source geometry. Neither this adapter nor its benchmark results should be promoted as a native recognition improvement before that review.
