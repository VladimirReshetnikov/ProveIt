# Partial cancellation with cycle blocks

The maintained `fastunknot.cycle_block_cancellation` module optimizes a weighted
source-private subset of an unsigned occurrence matrix. Its output is an
`OPTIMAL_MATRIX_PLAN`, not a knot, handlebody, or geometric successor certificate.
It is not on the default recognition path.

The implementation adapts report 116 with an exact minimum-weight one-row
deferral prepass (at most eight candidates by default), an explicit enumeration
stack, early directed-cycle pruning with rollback reachability, and correct
propagation of caller exceptions even when they use the public `ResourceLimit`
class. Original report files remain unchanged.

```python
from fastunknot.cycle_block_cancellation import optimize_counts, verify_plan

counts = {0: {0: 1, 1: 1}, 1: {0: 1, 1: 1}, 2: {2: 1}}
plan = optimize_counts(counts, {0: 4, 1: 7, 2: 1})
assert plan['matched_weight'] == 8
assert plan['remaining_rows'] == [0]
assert verify_plan(counts, plan, {0: 4, 1: 7, 2: 1})
```

`verify_plan` checks source-private feasibility and recorded totals; it does
not certify arbitrary producer claims of optimality. Optimality relies on the
complete algorithm and its proof. Limits return `RESOURCE_LIMIT`, never an
infeasibility conclusion. Exhausting `max_single_trials` instead falls through
to the block algorithm. `single_deferral=False` isolates the latter. Every
`Limits` field accepts `None`, including `max_paths`; the uncapped algorithm
has no fixed recursion-depth restriction.

The [article](../../synthesis/cycle_block_cancellation.tex) gives the proofs and
measurement scope. The matrix bit bound is `poly(input size) * 2^O(kappa)`,
where `kappa` is the largest individual block cycle rank. It does not bound
geometric residual repair, marked transport, or aggregate hierarchy work.

Validation and reproduction:

```sh
# From fast/
python -m unittest tests.test_cycle_block_cancellation -v
python cycle_block_research/native_audit.py /tmp/cycle-native.json
python cycle_block_research/benchmark.py
python cycle_block_research/prefix_benchmark.py
python cycle_block_research/check_evidence.py
```

The native audit authenticates 126 source cuts, independently replays top
cancellation, reconstructs uncapped counts, and compares objectives with the
ordered-interface optimizer from report 110. It computes compatible forests
using exact source parity. All current matrix plans complete; 124 fully peel
and two have optimal residual weight one. The initial no-prepass audit and
the uncapped-prepass regression measurement are retained alongside final data.
No geometric partial cancellation or new whole-cut verdict is asserted.

The ten maintained tests include independent exhaustive/random subset oracles,
a completed 270-path case, resource refusals and caller interruption. Both
the original report and a scratch copy using the adapted optimizer pass the
50-test delivered suite, 31,581 exhaustive case roles (63,162 plans), and the
randomized audit. The original large symbolic/cactus audit also passes.
Evidence lives in `synthesis/data/cycle-block-*`.

Benchmarks start at prepared matrices and include normalization, optimization,
feasibility replay and JSON serialization. Native source construction and
downstream geometry are excluded. Run timing programs sequentially after
validation work has finished. Report small-case and cactus regressions as well
as improvements; never form a speedup ratio from a capped refusal.
