# Exceptional-column dual-forest selector

This is a standalone, exact finite graph/matrix research operator. It chooses
a spanning tree whose deleted rows leave a matrix removable by raw
unit-column peeling. It does not authenticate triangulations or issue knot,
nonball, or nonhandlebody verdicts.

The new theorem and complete proof are in `PROOF.md`. The parameter is
`u`, the number of rows incident with active columns of support greater than
two. The selector uses at most `Bell(u+1)` polynomial independent-
representatives calls, giving `2^{O(u log(u+2))} poly(N)` complexity. For the
original native source-core columns, `u <= 3k`, where `k` counts exceptional
columns of shape `(1,1,1)`. Added annular/boundary rows need the general `u`
bound; the native three-occurrence theorem cannot silently be extended to
that larger matrix. No logarithmic bound on `k` and no complete
quasi-polynomial unknot-recognition theorem are claimed.

## Files and attribution

- `exceptional_forest.py`: new bounded-interface reduction, exact Horn
  closure, partial-partition enumeration, and graph-edge cloning.
- `degree_two_backend.py`: unmodified copy of
  `ProveIt_Dual_Forest_Normalization_2026-10-12/code/forest_search/dual_forest_search.py`
  from the incoming research package. Its input validation, SCC helper,
  forest extension, peeling, and classical graphic/partition
  matroid-intersection implementation are reused with attribution. The new
  contribution is the interface/partial-partition reduction, not a new
  matroid-intersection algorithm.
- `audit_exceptional.py`: independent oracle enumerating every spanning
  tree and applying literal, uncapped unit-column peeling. It does not use
  the solver's forest or peeling routines for expected results or replay.
- `audit_results.json`: complete exhaustive and randomized audit results.
- `quick_audit.json`: smaller smoke audit.
- `PROOF.md`: full theorem, proofs, counting, and scope.
- `CLAIM_LEDGER.json`: established results and limitations.

Only Python's standard library is needed. Place the two solver modules in
the same directory.

## Input and output

The exact JSON input schema is:

```json
{
  "vertices": 3,
  "columns": 1,
  "edges": [[0, 1], [1, 2], [0, 2]],
  "rows": [[[0, 1]], [[0, 1]], [[0, 1]]]
}
```

There is one edge record per row. Vertex 0 is the boundary root. An edge
record may be `null` to forbid that row's selection in the tree; loops are
also never selected. Rows are sparse `[column, positive_integer_count]`
lists with distinct column indices. Original counts are capped at two for
the solver's zero/one decision. Any separate geometric parity check must
use unsaturated source counts.

`SUCCESS` carries a `certificate` with `tree` and `peeling` lists. Recheck
that the tree spans the authenticated dual graph and that each `[row,
column]` pair has total column occurrence exactly one in the current row
restriction. The source geometry and topological interpretation must be
authenticated separately by the enclosing native producer/verifier.

`NO_FOREST` means exhaustive failure in this restricted matrix/graph class.
The full-partition negative is an algorithm result, not a succinct
standalone negative certificate. `INCONCLUSIVE` means a resource budget or
implementation recursion limit interrupted the exact search. It never
means exhaustive failure.

## Reproduce

```bash
python audit_exceptional.py --output audit_results.json
python audit_exceptional.py --quick --output quick_audit.json
python exceptional_forest.py input.json
python exceptional_forest.py input.json --max-partitions 10000
```

The complete audit exhausts all `4^3 * 3^6 = 46,656` instances with three
rows, two columns, entries in `{0,1,2}`, and two-vertex edge records chosen
from `null`, a root loop, an ordinary edge, and a loop at vertex 1. It also
uses 2,000 seeded general weighted cases and 2,000 seeded parity-compatible
cycle-column cases, plus two edge cases. Positive output is independently
replayed using actual uncapped counts. Partial-partition counts through
six interface rows and two zero-budget checks are included.

These audits validate the finite implementation and its cases, not
topological realization of random matrices. This package has no native
source adapter: source extraction should use the repository's existing
authenticated incidence and dual-endpoint routines. In particular, no
matrix is accepted as a replacement for its geometric charts.
