# Proposed additive integration

Suggested initial location:

`Topology/UnknotRecognition/reports/<next-assigned-report>/sparse-cut-grammars/`

Keep this report isolated until a native importer and end-to-end tests exist. The package does not patch recognizer defaults and does not assume an unverified native API.

## Importer obligations

The importer must authenticate the actual graph represented by every rule, fresh edge occurrence ownership, quotient vertex identities, terminal ordering, and every retained future attachment point. It must record how each leaf edge address maps back to the source boundary pattern. It must not alias repeated rule occurrences or count a shared geometric edge twice.

The graph query owner must separately supply the carrier surface/embedding, ball certificate, cubic status, and inventory of vertex-free circle components. The producer can check abstract component and degree metadata; it cannot check the missing geometric facts. Do not convert `marked_cut_exists` into a knot verdict without the complete surrounding hierarchy argument.

## Producer interface

```python
from sparse_cuts import solve, witness_dag, cut_addresses, mark_address
from checker import verify_certificate, verify_addresses

result = solve(grammar, k=3, operation_limit=10_000_000,
               state_limit=100_000)
certificate = result.certificate()
verify_certificate(grammar, certificate)

# Only after forgetting every root terminal:
if result.has_marked_cut():
    witness = witness_dag(result)
    cuts = cut_addresses(result)
    marks = [mark_address(result, color) for color in (0, 1)]
    verify_addresses(grammar, witness, cuts, marks)
```

The caps count documented producer candidates and per-table entries. Exhaustion raises `BudgetExceeded` and is inconclusive, never a certificate of absence. A production service must add its own process isolation and hard resource limits.

## Complete native comparison

Time source extraction, grammar construction, geometry/provenance replay, query, complete graph replay, and source witness lifting under a common budget. Compare the literal source oracle, the four-copy route, the sparse DAG route, and a hybrid where applicable. Include identical A/A runs and small cases that show overhead. The included benchmark numbers cover none of the native extraction or hierarchy work.

## Semantic incompatibilities to reject

Zero or negative capacities; missing isolated-vertex inventory; attachment to forgotten private vertices; repeated parent terminal classes; forward/cyclic rule references; identified or deleted graph edges; double ownership of an edge; edge aliases in place of fresh copies; invented spherical or ball metadata; artificial degree-two encodings of vertex-free circles passed as cubic patterns.

The supplied JSON Schema is a structural guide. Length equality, contiguous quotient labels, complete explicit vertex inventory, child ordering, and graph semantics are checked by the Python validators.
