# Ordered Pivot Interfaces
## Optimal positive handle cancellation at bounded incidence width

Research continuation for Vladimir Reshetnikov's ProveIt project, 12 October 2026.

Read **`article/ordered_pivot_interfaces.pdf`**. The self-contained LaTeX source is alongside it. The package contains proofs, standard-library Python code, independent feasible-plan and full-transfer checkers, exhaustive audits, paired raw timing samples, an additive occurrence adapter, and eleven research questions.

### Main result

For an unsigned occurrence matrix and a supplied width-`w` tree decomposition of its **bipartite support incidence graph**, optimal nonnegative-weight positive cancellation has an exact algorithm with time

`poly(encoded input size) * 2^O(w log(w+2))`.

The bag state is a total order plus one matched/unmatched bit per boundary vertex. An order-amalgamation proof establishes the join step. The algorithm also optimizes private schedules with explicitly forbidden unit pivots; the unrestricted positive-fill completeness theorem is stated only for the unrestricted calculus.

The existing private-column queue is a safe first stage: it preserves the optimal deferred weight. On an entirely peelable matrix, the wrapper skips the width-dependent DP.

A four-row counterexample also shows a concrete improvement in partial reduction: the inspected minimum-fill rule cancels two rows, while the optimizer cancels three, with an independent stopping-set proof of optimality. The old rule never promised optimal partial cancellation; this is not a correctness bug. The example is an abstract matrix, not a claimed native geometric instance.

Complete max-plus continuation tables extend this optimization to repeat-safe, typed path templates with binary repetition. A separate checker verifies all table entries, maximizing witnesses, and power lengths, giving an **optimality** certificate for these abstract repeated graphs.

A connected family with incidence treewidth exactly two has full row rank and a unit maximal minor but requires deferral of one row per tile. Thus fast optimization does not imply a small residual core.

### What this does not establish

This is not a general quasi-polynomial unknot recognizer, a new source-geometry authenticator, or an embedded boundary-pattern transport routine. No full native checkout was available, no production patch was applied, and no native knot benchmark or full repository test suite was run. The incoming private-cocore archive's metadata was visible, but its binary body was not reviewed. See `SOURCE_AUDIT.json`, `CLAIMS.md`, and `INTEGRATION.md`.

### Minimal use

From the package root, with Python 3.10 or later (executed with CPython 3.13.5):

```python
from pivotwidth import Instance, replay
from pivotwidth.preprocess import peel_then_optimize

matrix = [[1, 1], [1, 2]]
weights = [3, 7]
plan = peel_then_optimize(Instance.from_dense(matrix, weights))
checked = replay(matrix, weights, plan)
assert plan["deferred_weight"] == 3
assert checked["deferred_rows"] == [0]
```

`retained_weight` is the weight retained **in the matching**, hence cancelled from the row inventory. `deferred_weight` is the weight of the actual unresolved rows. A deferred row remains a genuine two-handle even when its numerical occurrence row is zero.

For compressed powers:

```python
from examples.templates import defect_tile
from pivotwidth.transfer import power_certificate
from pivotwidth.transfer_verify import verify_power

proof = power_certificate(defect_tile(3, 7), 1 << 1024)
assert verify_power(proof)["deferred_weight"] == 3 * (1 << 1024)
```

### Reproduce

```sh
python -m unittest discover -s tests -v
python scripts/audit.py
python scripts/benchmark.py
python scripts/replay_release.py
sh build.sh
```

The 52 unit tests passed. The completed exhaustive audit includes 36,901 distinct matrices, with extra independent positive-pivot and unique-matching checks on the same 19,683 ternary 3-by-3 cases. It also includes 300 weighted instances, 150 restricted private-pivot instances, 80 decomposition comparisons, and 336 compressed-power/expansion comparisons. The unit suite additionally checks 100 preprocessing instances and malformed/forged certificates.

The frozen huge-power certificate has 1,027 proof nodes, two interface states, and maximum live bag size three. It certifies `7*2^1024` matched weight and `3*2^1024` deferred weight without graph expansion. Replaying this certificate establishes an abstract optimum, not a topological conclusion.

Audits and benchmarks overwrite their own local output files. Run on a copy to retain the delivered evidence. The benchmark compares a supplied-width optimizer plus feasible replay with an independent exhaustive deferred-set strategy, **not** the native recognizer. Small cases regress; preserve cheap native paths. All samples and measurement boundaries are retained in `results/benchmarks.json`.

### Contents and placement

`article/` contains the PDF, TeX, and generated tables. `pivotwidth/` contains the implementation. `scripts/`, `tests/`, and `results/` contain reproduction tools and evidence. `integration/` contains a guarded source-label adapter, not an applied patch. `examples/` contains connected test templates and a small plan certificate.

Intended placement is the next available `Topology/UnknotRecognition/reports/<NN>/` after ordinary report intake. Production adoption should be a separate reviewed change. Targeted source pin: `ac9c845a5c507c5d7a17d45b2d8de84fc046d455`.
