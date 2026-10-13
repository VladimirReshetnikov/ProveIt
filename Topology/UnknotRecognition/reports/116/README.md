# Cycle-Block Kernels for Positive Handle Cancellation

Research continuation for Vladimir Reshetnikov's **ProveIt** project, 12 October 2026.

Read **[Cycle_Block_Kernels.pdf](Cycle_Block_Kernels.pdf)**. The complete 30-page manuscript is built from `article/article.tex`; all tables and build inputs are included.

## Main result

Let `G` be the pivot-capable bipartite support graph of a nonnegative occurrence matrix, retaining nonunit edges in every pivot-capable column. For each vertex-biconnected block `B`, put `b(B) = |E(B)| - |V(B)| + 1`, and let `kappa = max b(B)`.

Maximum-weight source-private cancellation is computable in

```text
(encoded input)^O(1) * 2^O(kappa).
```

A rank-`b >= 2` block reduces to at most `3b-2` degree-two paths, each with at most six exact weighted states. Blocks join through one capacity bit. With all original unit pairs eligible, the result also optimizes unrestricted unsigned positive-singleton cancellation. Restricted eligibility is supported for source-private orders, not claimed for arbitrary dynamically restricted fill-producing moves.

The article also proves a weighted partial deferred-forest theorem under **uncapped** cycle parity, exact linear-size positive transport circuits, binary six-state powers with independent complete-table certificates, and a connected cactus family whose optimal residual grows linearly despite maximum block rank one.

This is a **local matrix/graph research engine, not a replacement unknot recognizer**. No general quasi-polynomial recognition bound, native block-rank theorem, geometric residual repair, or marked attaching-curve transport is established. No repository change was made.

Classical uniquely restricted matching, the earlier ProveIt private/positive equivalence and deferred-forest principle, and existing cactus tractability are attributed. There is no assertion of worldwide priority for the combined algorithm.

## Source baseline

Pinned maintained source revision:

```text
d9456c5bdb94820bfa9e480e9ed73c10a769e59a
```

This revision places report 110. Source review was targeted; no full native checkout or maintained geometric test suite was executed. See `SOURCE_AUDIT.md` and `integration/INTEGRATION.md`.

The inspected March 2021 Oxford talk states an announced bound `2^O((log n)^3)`. The article does not silently restate that specific announcement as the stronger `n^O(log n)`. Lackenby's July 2026 preprint is **Incompressible surfaces, hierarchies and unknot recognition**, arXiv:2607.23350v1, 54 pages. Its Section 9 distinguishes operation costs from iteration counts.

## Reproduce

Python 3.10 or later; standard library only. Recorded environment: CPython 3.13.5 on Linux x86-64.

```sh
python -m unittest discover -s tests -v
python scripts/replay_saved.py
python scripts/audit.py --suite exhaustive
python scripts/audit.py --suite randomized
python scripts/audit.py --suite large
python scripts/benchmark.py --suite all
python scripts/make_tables.py
python -m cycleblocks examples/weighted_cactus.json --transport
sh build.sh
```

Run audits and benchmarks on a **copy** to preserve the delivered evidence. They overwrite their default output files. `--output /path/to/new.json` selects an alternative result file; the large audit also writes its symbolic example certificate. Building the PDF needs `pdflatex` and ordinary TeX Live packages, including AMS, mathpazo, microtype, TikZ, hyperref, cleveref, and xurl. The delivered PDF does not require a TeX installation to read.

## Minimal Python use

```python
from cycleblocks import optimize_counts, verify_plan, transport_circuit, evaluate_circuit

counts = {
    0: {0: 1, 1: 1}, 1: {0: 1, 1: 1},
    2: {0: 1, 2: 1}, 3: {0: 1, 2: 1},
}
weights = {0: 2, 1: 7, 2: 11, 3: 3}
plan = optimize_counts(counts, weights)
assert plan['status'] == 'OPTIMAL_MATRIX_PLAN'
assert plan['matched_weight'] == 18
assert plan['deferred_weight'] == 5
assert verify_plan(counts, plan, weights)  # feasibility, NOT global optimality
circuit = transport_circuit(counts, plan, weights)
remaining_column_sum = evaluate_circuit(circuit, {0: 1, 1: 1, 2: 1})
```

For a binary cycle:

```python
from cycleblocks import periodic_cycle_optimum, verify_power_certificate

N = 1 << 1024
summary = periodic_cycle_optimum(N, certificate=True)
assert verify_power_certificate(summary['certificate'])
# The verifier certifies the full path table, not arbitrary extra wrapper fields.
valid_scores = [entry['score'] for entry in summary['certificate']['table']
                if entry['first'] + entry['last'] <= 1 and entry['direction'] == 0]
assert max(valid_scores) == summary['matched_weight'] == N - 1
assert summary['deferred_weight'] == 1
```

This second example does **not** output an exponentially long flat matching. The path API uses a uniform row weight, alternating eligibility, and fixed occupied/free potentials by vertex type. It assumes fresh repeated internal vertices and contexts; it does not discover such templates in native geometry.

## Executed evidence

The final suite passes **50 test methods**. The exhaustive audit executes **31,581 matrix-case roles**, including overlapping binary/ternary families, and checks **63,162 optimized plans** with prepeeling on/off. Of those inputs, 1,241 also undergo independent arbitrary-positive-pivot comparison.

The randomized audit records 1,000 weighted comparisons, 500 restricted comparisons, 500 relabelings, 1,000 exact transport comparisons, 300 graph contexts with **4,800 spanning-forest comparisons**, and 240 complete literal path tables. These counts are test roles, not all disjoint inputs.

A 1,000-block weighted cactus and a symbolic cycle with `2^1025` edges pass the analytic checks. The latter has a saved 5,141,912-byte complete-table certificate (including newline). No discrepancy was found.

The paired transport benchmark includes construction, plan verification, circuit validation, the requested row-sum query, and answer serialization. At 512 passive rows and 512 outside columns it gives a median paired reference/new ratio **6.973**, versus literal positive fill. The small cases regress. The matrix benchmark compares against a specified exponential subset oracle, **not** a competitive cactus solver or the maintained ordered-interface engine. None of the benchmarks is an end-to-end knot measurement.

## Resources and safety boundaries

`Limits` defaults to two million counted events, maximum block rank 12, maximum 128 paths in a block, and one million nonzero input entries. The reference recursive kernel enumerator allows `max_paths` only up to 256. A configured resource refusal is `RESOURCE_LIMIT`, not infeasibility. Callbacks propagate caller interruptions. These guards are not hard wall-clock or memory limits.

`verify_plan` certifies source-private feasibility and totals only. General optimality follows from the producer's complete algorithm and proof, not from that replay alone. In contrast, `verify_power_certificate` checks all candidates in every constant-size product and certifies the full symbolic path table.

A positive numerical transport circuit retains empty passive rows. It does not retain ordered embedded attaching maps. Unused optimization columns remain actual source handles. `deferred_forest` checks uncapped graph-cycle parity but does not authenticate source geometry.

## Contents

| Location | Contents |
|---|---|
| `Cycle_Block_Kernels.pdf`, `article/` | Complete article and all TeX inputs |
| `cycleblocks/` | Exact optimizer, witness replay, binary powers, transport, forest routine, CLI |
| `tests/` | Independent oracles and 50 test methods |
| `scripts/` | Audits, paired benchmarks, table generation |
| `results/` | Frozen logs, JSON samples, symbolic proof, PDF build/review record |
| `examples/` | Weighted plan and full forest-choice witness |
| `integration/` | Additive unpromoted core-shape adapter and geometric contract |
| `CLAIMS.md`, `SOURCE_AUDIT.md` | Scope and provenance |

For intake, preserve the delivery under the next available `Topology/UnknotRecognition/reports/<NN>/`. Do not treat placement as production promotion or automatically change the recognizer's verdict path.
