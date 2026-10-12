# Native integration contract

## Intended insertion point

The existing source-authenticated cancellation path has a fixed zero/one-handle forest and an occurrence dictionary reconstructed from actual two-handle attaching charts. Preserve its complete private-column queue and its existing complete-success schema. This packet optimizes **partial** cancellation after full cancellation stalls.

`native_adapter.optimize_retained_occurrences` accepts only a numerical occurrence dictionary. Its output is `PARTIAL_MATRIX_KERNEL` or `INCONCLUSIVE`, never an unknot/handlebody verdict. It does not supply the preceding geometric authentication.

## Required read / reconstruct / replay sequence

1. The native producer and the enclosing independent verifier authenticate the source triangulation, normal-cut charts, forest, finite handle inventory and marking data using their established checks.
2. Independently reconstruct the original nonnegative occurrence matrix from those charts, including repeated unsigned occurrences. Do not replace these by signed exponent sums or a free-group presentation.
3. Run `optimize_counts` on the producer's reconstruction. A supplied decomposition must refer to the graph indexing returned by `Matrix.graph()` for its documented `decomposition_scope_rows`; do not reuse an index map after changing that scope.
4. Replay the returned schedule with `verify_plan` on the verifier's independent source reconstruction. This certifies the schedule and its reported weight. Generic optimality follows from the complete DP theorem, not from this feasibility checker alone. The two-support result additionally has an independent tight stopping-set certificate.
5. Transport **all retained** two-handle data using the source cancellation convention. `transport_counts` carries exact or saturated numerical counts, including inert columns outside the decision graph. It does not carry cyclic ordering, embedded bands or markings.
6. Retain every deferred two-handle and every unpivoted one-handle, including zero/inert columns omitted from the graph. Use the full original inventory for any handle census. A matrix with omitted zero columns cannot alone determine genus.
7. Supply a new native partial geometric certificate with independently replayed ordered charts before downstream geometric simplifiers use the result. This packet does not implement that schema or its chart transport.

## Prepeeling and width

Automatic dispatch has an exact safe prefix: full-matrix private peeling never removes a member of any stopping set. Therefore a nonnegative-weight optimum can be chosen entirely inside the canonical residual. Without a caller-supplied decomposition, automatic mode optimizes that residual and packages the schedule on the original labels. `decomposition_scope_rows` explicitly records any smaller matrix whose decomposition is returned. With a supplied decomposition, the original indexing is preserved rather than silently rewritten.

The complexity theorem concerns a **validated supplied width**, not optimal treewidth found for free. The minimum-fill builder is a polynomial heuristic. Uniformly nonunit columns are omitted only from the decision graph; nonunit entries in columns containing some unit remain blockers and must not be dropped.

## Failure and resource behavior

`RESOURCE_LIMIT` and a canceled call authorize no negative topological or mathematical conclusion. Row costs are fixed nonnegative integers; default cost is cardinality. A lower weight does not automatically mean fewer handles or cheaper ordered transport. The DP's work counter excludes parsing and heuristic decomposition construction; callers must impose their own whole-query deadline and memory policy. The callback may raise a cancellation exception, which propagates.

Do not pass `ordered-deferral-v1` to the existing native full-handlebody verifier as though it were a recognized complete certificate. Do not discard a nonempty residual. Three-handles, admissibility, patterned normality, source-size growth and hierarchy restart bounds remain external obligations.

## Suggested native validation

Start with read-only source-paired experiments: construction, forest, independent matrix reconstruction, full peeling, optimization, source replay, transport, census and serialization charged together. Preserve every accepted cut and refusal. Compare with both the existing full-success queue and a fair partial-optimization baseline, distinguishing the two questions. The supplied local corpus is not evidence of native difficult-knot speedup.

No native checkout patch, benchmark, live commit or pull request was performed. Keep this module opt-in and inside the intact research report until the geometric and schema requirements above are implemented and independently reviewed.
