# Optimal Deferred-Handle Kernels via Ordered Incidence Interfaces

Research continuation for Vladimir Reshetnikov's ProveIt project, developed with ChatGPT, 12 October 2026.

**Main result.** Minimum-weight deferral in the explicit nonnegative positive-singleton cancellation calculus is computable in `(encoded matrix + supplied decomposition size)^O(1) * 2^O(t log(t+2))`, where `t` is the supplied width of the pivot-capable column incidence graph. The optimum may contain linearly many deferred rows. A separate two-support theorem gives a directed-reachability/SCC optimizer with independently checkable tight stopping-set lower bounds.

Read `article.pdf` or compile `article_standalone.tex`. The full paper contains all proofs, an explicit connected width-three separation family, scope qualifications, measurements, and twelve further research directions.

## Scope

This is an exact local matrix optimizer, not a replacement unknot recognizer. It does not authenticate three-dimensional handle charts, transport ordered geometric attaching data, or prove a general quasi-polynomial recognition bound. In particular, retained two-handles are **not** erased or treated as a handlebody certificate. No live repository changes were made.

Targeted maintained-source revision: `c6d0ec8aa0b6308310ab6c081ba29d8bc363ede5`. The comparison baseline is the actual delivered Positive Cancellation packet, not a claim about all newer native implementations. See `SOURCE_AUDIT.md` and `integration/INTEGRATION.md`.

## Reproduce

Python 3.10 or later; standard library only. Recorded environment: Python 3.13.5 on Linux.

```sh
python -m unittest discover -s tests -v
python scripts/audit.py
python scripts/benchmark.py
python scripts/summarize_results.py
python -m ordered_kernel examples/weighted_block.json --exact-counts
sh build.sh
```

The final recorded new suite has 47 tests. The independent audit executes 21,735 exhaustive matrix cases (overlapping subfamilies are counted as separate executed cases), 350 random weighted optima, 350 automatic-core dispatch comparisons, 118 alternate decompositions, 800 two-support weighted optima, and additional closure, predecessor and transport comparisons. Two deliberately wide alternative decompositions return the tested resource refusal. The actual predecessor's separate 34-test suite also passed; the current native repository suite was not run.

The benchmark retains every sample and compares both global and component-factored predecessor enumeration. It includes regressions and is not a knot benchmark. Its result files are overwritten when rerun. See `results/README.md`.

Building the PDF requires `pdflatex`, standard AMS/LaTeX typography packages, and TikZ. Build intermediates are placed in `.build/`. The standalone TeX embeds the measured tables and needs no additional project files, external images, or network access.

## Minimal Python use

```python
from ordered_kernel import (
    optimize_counts, verify_plan, verify_two_incidence_optimality,
    transport_counts,
)

counts = {0: {0: 1, 1: 1}, 1: {0: 1, 1: 2}}
weights = {0: 5, 1: 2}
plan = optimize_counts(counts, weights)
assert plan['status'] == 'OPTIMAL_MATRIX_PLAN'
assert plan['cost'] == 2
assert plan['deferred_rows'] == [1]
assert verify_plan(counts, plan, weights)
assert verify_two_incidence_optimality(counts, plan, weights)
residual = transport_counts(counts, plan, weights=weights, saturated=False)
assert residual == {1: {1: 3}}
```

Rows and columns use nonnegative integer identifiers. Counts and row weights are exact nonnegative integers; Boolean values are rejected. Weights must cover all rows. Empty rows remain genuine rows. Entries larger than one are blockers, not algebraically canceled signed coefficients.

Automatic dispatch first peels the canonical stopping core, returns immediately on full success, then uses the two-support theorem when applicable and otherwise the ordered DP. Supplying a decomposition prevents silent reindexing to a smaller core. The returned `decomposition_scope_rows` identifies the matrix whose graph the decomposition describes. `method='ordered'` runs the generic interface algorithm directly.

`Limits` controls DP width, live-table states and counted event work. `RESOURCE_LIMIT` is inconclusive, not infeasibility. The callback `check` supports caller interruption. Admission/parsing and the minimum-fill heuristic are outside the DP work counter. The CLI imposes a 32 MiB input cap; this is not a hardened network service.

## Files

- `article.tex`, `article_standalone.tex`, `article.pdf`: manuscript and reading copy.
- `ordered_kernel/`: optimizer, input/decomposition validation, independent witness replay, exact/saturated numerical transport, and CLI.
- `scripts/`, `tests/`: reference oracles, finite audits, complete-query timings, tests, and result generation.
- `results/`: raw executed evidence and generated manuscript tables.
- `integration/`: additive adapter and native trust-boundary contract.
- `reference/positive_predecessor/`: licensed unchanged baseline modules used by the experiments.

For intake, preserve this packet under the next available `Topology/UnknotRecognition/reports/<NN>/` directory. Native integration and report numbering remain separate intake work. No patch automatically replaces the maintained full-success verifier.

Mathematical proofs and finite audits are complementary. No proof-assistant formalization or exhaustive literature-priority claim is made.
