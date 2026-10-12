# Choosing a dual forest while preserving complete raw cancellation

This additive research module solves a finite graph and unsigned matrix problem.
It assumes that a separate geometric importer has already authenticated the
dual two/three-handle graph and all one/two-handle occurrence counts. It does
not recognize knots and does not authenticate topology.

The main result is a polynomial algorithm when each non-inert matrix column
has at most two nonzero rows. Peeling becomes directed reachability; the
unseeded source strongly connected components are exactly the groups a
dual spanning tree must meet. Graphic/partition matroid intersection then
finds an independent transversal or a short rank-defect obstruction. The
independent checker verifies source stopping sets and graph ranks, so it
does not trust the producer's strongly connected component computation,
augmenting search or maximality claim.

For general nonnegative matrices, a complete obstruction-guided search
branches only on eligible edges in a source stopping set. Contracted loops
are excluded, a single available edge is forced, and the selected graph
rank bounds the search depth. Deterministic resource caps return
`INCONCLUSIVE` without a negative certificate.

## Files

- `dual_forest_search.py`: the polynomial and general solvers.
- `dual_forest_verify.py`: an independent finite certificate verifier; it
  imports no producer code and uses different graph rank bookkeeping.
- `forest_selection_theorems.tex`: theorem/proof section for the parent
  research article, including the geometric two-choice example and the
  nonmatroid counterexample.
- `test_dual_forest.py`: 18 focused tests, including mutation attacks.
- `audit.py`: exhaustive and seeded random comparisons with a separate
  spanning-tree/nonempty-stopping-subset oracle.
- `benchmark.py`: a controlled tree-enumeration comparison and exact
  structural counters.
- `../../results/forest_search/`: recorded audit and benchmark output.
- `examples/` and `replay_demo.py`: deterministic positive and negative finite replay.
- `REFERENCES.txt`: attribution and prior incoming results to retain.

## Input and certificate contract

Vertex zero is the distinguished root. Rows are indexed consecutively and
have one associated graph edge or `null` if ineligible for top cancellation.
Parallel edges and loops are allowed. A sparse row is a list of distinct
`[column, positive_count]` pairs. Counts are capped at two by the producer
and checker, which is exact for the raw singleton/stopping predicates.

```json
{
  "vertices": 2,
  "columns": 1,
  "edges": [[0, 1], [0, 1]],
  "rows": [[[0, 1]], [[0, 3]]]
}
```

Here the successful tree deletes row 1 and leaves the unit row 0. Deleting
row 0 instead leaves a stopping singleton. This is the combinatorial form
of the ball example in the theorem note.

`SUCCESS` comes with a dual spanning tree and a complete column-leaf
schedule on the surviving rows. `NO_FOREST` means that **no tree has a
complete raw schedule in this fixed graph/matrix model**. Its certificate
is an unrooted graph cut, a disjoint stopping-set rank defect, or a complete
stopping-witness proof tree. It is not a nonball or knottedness conclusion.

The degree-two solver returns `INCONCLUSIVE` if an active column meets
more than two rows. The general solver can then be requested independently.
Budget exhaustion also returns `INCONCLUSIVE`; no unfinished proof is
accepted by the checker. The general Python implementation additionally
reports interpreter recursion exhaustion as inconclusive.

All algorithms use sparse column dictionaries. A huge binary column
namespace with few named columns is not expanded. A huge declared graph
namespace with omitted vertices yields a compact isolated-vertex cut,
without allocating a vertex-sized array.

## Reproduction

Use Python 3.10 or later, with no third-party dependencies:

```bash
python -m unittest -v test_dual_forest.py
python audit.py
python benchmark.py
python dual_forest_search.py examples/positive_problem.json --method degree-two > result.json
python dual_forest_search.py examples/positive_problem.json --method search --max-nodes 10000 > result.json
python dual_forest_verify.py examples/positive_problem.json result.json
python replay_demo.py
```

The last command expects the solver's JSON output in `result.json`. The
checker accepts only completed certificates. Reproduction scripts write a new local `results/` directory, including measured
timings; the recorded results under the package root remain separate.

## Recorded scope and evidence

All 18 focused tests pass. The independent finite audit compares 33,995
instances: 4,554 are feasible and 29,441 infeasible. Every general-search
certificate verifies. The degree-two solver completes and verifies 23,849
calls; 10,146 further calls correctly decline the unsupported active-column
regime. These counts include disconnected graphs, ineligible rows, loops,
parallel edges and nonunit incidences. They are synthetic finite cases,
not native normal-cut measurements.

The benchmark family has `k` parallel dual links and exactly `2^k` spanning
trees. Its only successful tree consists of the forced nonunit rows.
At `k = 12`, the specified enumeration tests 4,096 trees; the two optimized
solvers avoid that enumeration. Every positive timed arm also runs the same
independent certificate checker. Small inputs show overhead, which remains
in the recorded results. The large cases run only the polynomial solver;
their hypothetical enumeration counts are labelled formulas, not measured
enumeration runs.

The source stopping criterion, Rado's theorem and the matroid-intersection
framework are prior results. The new contribution is their proved
connection to the fixed dual-forest choice, the exact two-row-column
regime, and independently checked implementation. No general
quasi-polynomial unknot-recognition bound follows from this local result.
