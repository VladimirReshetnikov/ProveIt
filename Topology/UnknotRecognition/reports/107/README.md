# Matroidal dual-forest selection for unknot recognition

Research continuation for Vladimir Reshetnikov's ProveIt project, 12 October 2026.

**Read the article:** `article/article.pdf` (23 pages; editable source: `article/article.tex`; self-contained snapshot: `article/standalone.tex`).

This package solves a **local unsigned-matrix / rooted-dual-graph selection problem**. It is not an unknot recognizer. A negative result is not a non-handlebody or knottedness certificate.

## Results

The article proves a directed-reachability characterization for usable columns of support at most two, a polynomial graphic/partition-matroid selector, and an exact rank formula for the minimum additional deletion deficit after the best dual tree. For an arbitrary matrix, the selector uses at most `b! Bell(b)` matroid subproblems, where `b` counts rows incident to usable columns with support at least three. It also gives an explicit NP-completeness reduction for abstract support-three inputs; geometric realizability of those gadgets is not claimed.

“Usable” means a column has at least one entry equal to one. Columns without a unit entry are inert for static peeling, even if they have large support. Entries are unsigned intersection counts, saturated at two, not field elements.

The maintained source checkpoint is `c6d0ec8aa0b6308310ab6c081ba29d8bc363ede5`. See `SOURCE_AUDIT.md` for the actual readings, including the limitation on two incoming dual-forest archives.

## Run

Use Python 3.10 or later; the recorded runs used Python 3.13.5. No third-party package is required for the mathematical code.

```sh
python -m unittest discover -s tests -v
python -m experiments.validate
python -m experiments.sat_audit
python -m experiments.benchmark
python -m dualforest examples/repository_loop.json --max-branches 10000
sh article/build.sh
```

LaTeX building requires `pdflatex` with ordinary TeX packages, including `xurl`, `listings`, and Latin Modern. The build regenerates the tables and numerical macros from the retained JSON records, then runs three passes to resolve internal references. The standalone source embeds the delivered tables and can be compiled separately with three `pdflatex` passes; it is a snapshot rather than a live data build. The PDF is already included.

The CLI accepts a normalized JSON instance, **not a knot diagram**. It independently replays completed answers. Exit 0 means a completed local yes/no query; exit 2 means invalid input; exit 3 means resource-limited unknown. The default branch limit is 10,000, and the default input byte limit is 5 MB. Python's ordinary JSON integer-parser limits also apply. The very large integer unit test uses the in-memory factory, not an unlimited JSON parser.

## Python API

```python
from dualforest import from_dense, solve, verify_positive

inst = from_dense(
    2,
    [(0, 1), (0, 1), (1, 1)],
    [[1, 0], [2, 1], [0, 1]],
)
answer = solve(inst, max_branches=10000)
if answer["status"] == "yes":
    assert verify_positive(inst, answer["certificate"])
```

Rows are `0..m-1`. There must be one dual edge for every row. The dual graph is connected and has a specified root, by default 0. Loops and parallel edges are retained. For sparse matrices with source column labels, use `make_instance(vertices, edges, rows, columns=..., root=...)`, where each row is a mapping from a nonnegative column ID to a nonnegative Python integer. Use the validated factories rather than constructing `Instance` fields manually.

`solve_pair` requires every usable column to have support at most two. It returns an optimal additional-deletion packet even when the local selection answer is negative. The extra deletions are a formal deficit measure; they are not automatically legal geometric moves.

`solve` first tries its deterministic incumbent tree unless `try_incumbent=False`. It then dispatches to the polynomial pair case or the exceptional-boundary algorithm. `max_branches=None` means uncapped exact search, potentially expensive. Hitting a cap produces `unknown`, never `no`. The optional `check` callback is polled at search and augmentation boundaries; exceptions propagate. Input parsing and dependency preparation are not bounded by the branch cap.

`retain_negative=False` avoids retaining the general exhaustive negative trace, while preserving the exact search result. With the default `True`, the trace can have fixed-parameter-sized memory and output cost. Independent general negative verification regenerates every order/partition branch and checks its rank obstruction.

## Package map

- `article/`: comprehensive article, editable TeX, generated tables, PDF, build script.
- `dualforest/`: validated model, dependency analysis, matroid intersection, selectors, independent verifiers, CLI, and explicit CNF hardness reduction.
- `tests/`: 54 unit tests, including adapter-record tests and producer-disabled replay.
- `experiments/`: independent small enumeration oracles, exact audits, and paired matrix-stage benchmarks.
- `results/`: complete logs, structured validation data, raw paired timings and A/A controls, and example certificates.
- `examples/`: the repository's source-derived five-row matrix and smaller abstract fixtures.
- `integration/`: opt-in native source-replay seam and integration gates.
- `CLAIMS.md`: proven, inherited, tested, conditional, and unexecuted claims.
- `SOURCE_AUDIT.md`: pinned provenance and scope of the readings.

## Integration boundary

The record-level adapter was tested. Its `propose_geometry` function, which imports the full native package and invokes its independent geometric source replayer, **was not executed here**. It requires a local ProveIt checkout with the native dependencies available. It must be called only on an already authenticated enclosing source-parallelity geometry, and its result still requires all downstream core, port, pattern, and whole-cut checks.

No repository files were modified and no commit or pull request was created. This archive is an integration candidate, not a claim of completed production integration. Keep the current complete fallback and source checker.

## Measurements and limitations

The separate audit compares 35,684 matrix/graph inputs against literal spanning-tree enumeration, with zero mismatches and successful certificate replay. Other recorded comparisons include 1,000 independent-transversal assignments, 500 optimal deficits, 22,830 seed sets, 19,683 complete positive-pivot searches, and 7,988 Boolean assignments for the hardness reduction. These are finite audits, not substitutes for the proofs.

Paired timings compare **already parsed matrix kernels**. They do not include native source construction or full unknot recognition. Synthetic pair-column star families expose exponential tree enumeration and large measured kernel gains. Easy-first inputs and the five-row repository matrix favor literal enumeration; the general FPT kernel is about 32.7 times slower on that tiny example. A successful pre-existing route should remain first, and bounded literal trials are a reasonable integration policy before the more general search.

The global `n^{O(log n)}` recognition implication in the article is conditional on actual source-size, exceptional-boundary, query-count, and all-other-work bounds. These hypotheses are not proved for unrestricted knot diagrams.
