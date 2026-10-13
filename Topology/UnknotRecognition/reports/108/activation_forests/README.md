# Nonlinear activation and forest certificates

This package exactly decides the following finite operation. Each row of a
nonnegative occurrence matrix is associated either with an edge of a connected
graph or with `None`. Choose a spanning tree of graph edges, remove the
corresponding rows, and repeatedly remove a row whose entry is the only live
unit in some column. The question is whether some tree permits complete row
removal. Graph vertex `0` is the distinguished boundary root. Loops and `None`
rows cannot belong to a tree.

In a source-authenticated handle problem, rows describe actual two-handle
attaching occurrences, and graph edges describe top-handle caps. This package
proves the finite graph/matrix statement. The enclosing geometry must establish
that the records describe the intended manifold and handle charts.

## Use

From the parent directory of `activation_forests`, with Python 3.10 or later:

```python
from activation_forests import from_dense, parameters, solve_output, verify_output

problem = from_dense(
    3,
    [[0, 1], [1, 2], [2, 0]],
    [[1], [1], [1]],
)
result = solve_output(problem)
assert result['status'] == 'SUCCESS'
assert verify_output(problem, result)
print(parameters(problem))
```

The sparse input schema is exactly:

```python
{
    'vertices': 3,
    'columns': 1,
    'edges': [[0, 1], [1, 2], [2, 0]],
    'rows': [[[0, 1]], [[0, 1]], [[0, 1]]],
}
```

Row IDs are list positions. Column labels range from `0` to `columns - 1`.
Each sparse row contains distinct columns with strictly positive integer counts.
Supply actual uncapped counts: the parser caps counts only for unit decisions,
while the cycle-parity test uses the original counts. The SHA-256 binding also
uses the original counts, encoded canonically in hexadecimal.

## Complete and capped results

The preferred factorial-free strategy is
`solve_output(problem, max_work=None, max_assignments=None,
max_partitions=None, use_rank_layer=True)`. Its independent checker is
`verify_output(problem, result)`. It returns the same three statuses described
below and retains the same literal positive-certificate format.

The ordered strategy remains available as an exact comparison baseline:
`solve(problem, max_work=None, max_scenarios=None, max_partitions=None,
use_rank_layer=True)` returns one of:

* `SUCCESS`, with a spanning tree and a complete literal column-peeling trace.
* `NO_FOREST`, with a disconnected graph cut, immutable stopping set, or complete
  scenario/partition certificate made from graphic Rado rank defects.
* `INCONCLUSIVE`, when a supplied structural-work, scenario, partition, or Python
  recursion limit interrupts discovery. It contains no complete certificate.

`verify_result(problem, result)` checks complete positive and negative results.
`verify_success(problem, certificate_or_result)` checks only a positive trace.
The checker imports no producer or optimizer. It reconstructs free closure and
ordinary reachability independently. Partition coverage is checked by validating
distinct restricted-growth encodings against an exact Bell or Stirling count.

Resource counters are explicit research work budgets. Input parsing, hashing,
Python allocations, and big-integer implementation costs are not hard wall-time
or memory isolation. A resource refusal is not a mathematical negative result.

## The parameter and the rank refinement

Complete peeling with no chosen tree identifies rows that are automatically
activated under every future tree. The compiler omits these rows from ordinary
and nonlinear premises, while retaining their graph edges for tree extension.
`parameters(problem)` reports both raw and residual parameter values.

A nonlinear column has at least three remaining row owners and at least one
unit entry. If there are `k` such columns, with supports `s_i` and unit-target
counts `u_i`, put `P = sum(s_i - 1)`. The output-assignment strategy chooses one
unit target per nonlinear column. For each assignment it constructs mandatory
source components and the distinct exceptional prerequisites not already
reachable from their guaranteed rows and free seeds. Let their number be `q`,
so `q <= P`.

It partitions these `q` prerequisites together with one distinguished null
element. Prerequisites sharing its block impose no initial-seed requirement;
they are allowed to become active at any time. Each other block requires one
common eligible ancestor edge. The solver first forward-chains the selected
nonlinear rules from the guaranteed rows and demanded prerequisites, rejecting
partitions that fail complete activation. It then seeks independent
representatives of the mandatory groups and non-null ancestor intersections.
The resulting bound is

```
product(u_i) * Bell(P + 1) * polynomial(encoded input size).
```

For triple-unit columns, this is `3^k Bell(2k + 1) poly(input)`, hence
`2^{O(k log(k+2))} poly(input)`. One need not guess the activation order: finite
monotone closure computes it. Distinct prerequisites sharing a tree witness
belong to one block, which is necessary for completeness.

The ordered baseline instead enumerates ordered unit outputs and partitions
of at most `P` antecedent demands. Its bound is

```
k! * product(u_i) * Bell(P) * polynomial(encoded input size).
```

For triple-unit columns, this is `3^k k! Bell(2k) poly(input)`.
Mandatory source strongly connected components
are disjoint requirements; overlapping demand groups are represented by edge
clones in a graphic/partition matroid intersection.

When every column has even endpoint parity using **uncapped** counts, every
activation rule preserves graphic span. A successful selected representative
set must then have full rank `r = vertices - 1`. With `p` mandatory groups and
`q` residual prerequisites, the output strategy only needs partitions into
`r - p + 1` blocks, including the null block. Its partition count becomes
`Stirling(q + 1, r - p + 1)`. For an ordered scenario with `q` remaining demands,
the corresponding count is `Stirling(q, r - p)`. Both strategies detect the
hypothesis exactly and reject impossible cardinalities immediately.
`use_rank_layer=False` is an exact ablation.

A complete negative certificate explicitly states whether this refinement was
used; its checker verifies original-count parity before accepting any skipped
partition or scenario. Positive checking always replays the original matrix.

## Files and validation

* `model.py`: strict finite input contract, exact digest and raw parity.
* `solver.py`: free closure, unary SCCs, nonlinear scenarios, demand partitions,
  cloned graphic/partition intersection, complete proof production.
* `verify.py`: independent positive and complete-negative verification.
* `output_solver.py`: factorial-free assignment and null-block reduction, using
  the ordered module's polynomial graph and matroid primitives.
* `output_verify.py`: independent assignment/partition negative checking and
  repeated-scan selected-rule closure; imports no optimizer.
* `oracle.py`: bounded full positive-pivot and spanning-tree enumeration.
* `../tests/test_activation_forests.py`: exhaustive, randomized, mutation,
  resource, large-integer, shared-demand and raw-parity tests.
* `../run_checks.py`: executes the tests and records actual comparison counts.
* `../tests/test_output_forests.py`: a separate factorial-free oracle suite and
  independent-certificate mutation and producer-disabled replay tests.
* `../run_output_checks.py`: executes the factorial-free suite and records its
  actual comparison count.

Run `python run_checks.py --output test_results.json` from the parent directory.
Run `python run_output_checks.py --output output_test_results.json` for the
factorial-free suite separately.
Only the Python standard library is required. Existing native recognizer tests
and topology oracle runs are separate from these finite kernel tests.

The classical shortest augmenting-path/Rado primitive is adapted from the
inspected ProveIt *Dual Forest Normalization* research package of 12 October
2026. The nonlinear activation reductions, null-block elimination of the
factorial, shared-demand partitions, cycle-compatible rank refinement, and
independent complete-negative certificate formats are the contributions of
the accompanying article.
