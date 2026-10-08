# Marked determinant continuations

Research continuation for **ProveIt / Topology / UnknotRecognition**, 7 October 2026.

The article proves an exact marked residue-four continuation bound, recovers the quantum information needed for that bound from the existing ungraded component keys, and derives a singular-safe signed-Laplacian terminal kernel. Critical terminal partitions satisfy a signed square law. All arithmetic in the implementation is exact.

**This is an opt-in research companion, not a new unrestricted quasi-polynomial recognizer.** It does not modify the upstream repository. The upstream diagnostic is supplied but was not executed against a complete checkout. Graph-kernel timings are not end-to-end knot-recognition speedups.

## Read the results

`paper/article.pdf` is the comprehensive manuscript; `paper/article.tex` is self-contained LaTeX with embedded tables and bibliography. It covers complete proofs, grading conventions, the marked-arc requirement, geometry contracts, bit costs, validation, and twelve further research questions.

The main results are:

1. **Quantum recovery without a new component key.** Within a connected homogeneous differential component, matching types and coefficient dot degrees determine quantum shifts up to one constant. Equal complete ungraded keys therefore differ by only uniform quantum and homological shifts. The residue norm is invariant under those shifts.
2. **Marked residue-four obstruction.** Complete each genuine relative direct summand through the actual suffix while keeping a marked arc outside processed operations. The sum of the integer coefficient norms of its reduced Euler polynomials modulo `q^4 - 1`, with nonnegative multiplicities, is a lower bound on reduced Khovanov rank. A value above one rejects a validated knot as nontrivial. An inconclusive value never certifies an unknot.
3. **Singular-safe batch determinant reduction.** A signed graph interior of corank `r` must retain its boundary coupling. A nonzero query uses a bordered matrix of order at most `2b - 2`, where `b` is the number of terminals. For `M` supplied terminal partitions, preparation and queries use `O(N^3 + M b^3)` rational arithmetic operations, with polynomial bit costs.
4. **Critical square law and sharp corank gate.** For a partition into `r+1` blocks, its cofactor is `(-1)^r det(P) det(RQ)^2`. Nonzero critical cofactors have the same sign and rational square class. The vanishing threshold `r > b-1` is sharp, even for planar signed graphs.

The stopping-prefix estimate is `poly(n,R) * 2^O(W)`, with **physical** representation size `R` and visited frontier width `W`. It is quasi-polynomial when both `W` and `log R` are `O(log^2 n)`. No theorem in this bundle forces every input to have such a successful prefix.

## Executed validation

The delivered run passed **35 unit-test methods**. The seeded experiment checked 701 diagrams against 133,923 explicitly enumerated smoothing states, 83 reduced homology calculations, 62,904 columns of `d^2`, and 4,000 signed-graph quotient determinants on 160 graphs, including 57 with singular interior blocks.

The independent reduced cube gives rank 33 for the repository's Conway PD and rank 7 for the positive three-braid `(sigma_1 sigma_2)^5`. Both have global residue-four norm one. These are incompleteness controls, not measured early-stage observer successes.

The final paired graph-kernel benchmark, including compressed preprocessing, recorded:

| Vertices | Interior corank | Direct median (s) | Compressed median (s) | Median paired ratio | A/A control |
|---:|---:|---:|---:|---:|---:|
| 32 | 0 | 0.1054 | 0.0189 | 5.52 | 1.002 |
| 56 | 0 | 0.5727 | 0.0830 | 6.90 | 1.011 |
| 80 | 0 | 1.8632 | 0.2928 | 6.43 | 1.031 |
| 56 | 1 | 0.6086 | 0.0864 | 7.05 | 0.971 |

Each case uses six terminals, 96 queries, and three randomized paired rounds with two independent direct controls. These are small-sample measurements of exact signed-graph kernels on the recorded host. They are not confidence intervals, asymptotic fits, or timings of the full recognizer. Full graph inputs, partitions, answers, and timings are in `results/benchmark.json`.

## Run locally

Python 3.10 or later is required. The package uses only the standard library; installation is optional.

```sh
python -m unittest discover -s tests -v
PYTHONPATH=. python experiments/validate.py
PYTHONPATH=. python experiments/benchmark.py
cd paper && sh build.sh
```

`reproduce.sh` runs the code checks and experiments. Experiments overwrite their result JSON with fresh local records. Preserve the delivered data before comparisons; rerunning them does not automatically rewrite the article's embedded measurement table. The PDF needs a standard LaTeX installation with the packages listed in its preamble.

## Exact kernel example

```python
from detshadow.linalg import signed_laplacian, TerminalKernel, verify_kernel

# Interior vertex 0, terminals 1 and 2: a genuinely singular interior.
L = signed_laplacian(3, [(0, 1, 1), (0, 2, -1)])
kernel = TerminalKernel.build(L, [1, 2])
assert verify_kernel(L, kernel)
assert kernel.nullity == 1
assert kernel.query([0, 1]) == -1  # Keep terminals separate.
assert kernel.query([0, 0]) == 0   # Identify them.
```

`verify_kernel` checks exact block identities by a separate solve. It certifies algebra, not a tangle embedding. `geometry_certificate.py` separately checks a proposed quotient cofactor against an actual completed PD under a supplied vertex correspondence. It is a verifier, not an automatic terminal-partition producer, and its per-query matrix comparison costs `O(N^2)`.

## Observer and upstream integration

`detshadow.continuation.observe_scan(scan, suffix_pd, marked_label=...)` is a read-only observer for the audited `FastScan` / `ComponentScan` state shape. It requires a genuine relative complex of the original validated classical knot, correct homogeneous coefficient semantics, actual suffix geometry, and a marked arc retained outside processed operations. Merely constructing an object with the same fields does not establish these preconditions.

The important output is `reduced_rank_lower_bound`. With exact multiplicities it is monotone under parent-local extension and splitting. With multiplicities saturated at a cap of at least two, the **threshold-capped** field `reduced_rank_lower_bound_capped` is monotone; the uncapped number computed from saturated weights need not be. The record identifies the applicable statement. It always has `certifies_unknot=False`.

For a local complete checkout, the diagnostic command is:

```sh
python integration/upstream_probe.py \
  --fast-root /path/to/ProveIt/Topology/UnknotRecognition/fast \
  --output results/my_upstream_probe.json
```

This command was **not run here**. It compares proper-prefix bounds with completed upstream ranks and small independent cubes. It is not a production deadline wrapper: integer determinant probes are not yet interruptible internally. The exact inspection revisions and file hashes are in `provenance.json`; they must not be represented as a full checkout regression run.

## Remaining obligations

`CLAIMS.md` separates proved statements from implementation and integration boundaries. `RESEARCH_QUESTIONS.md` lists concrete next targets. The key unresolved bridge is a constructive theorem that useful summands are exposed before the physically materialized representation becomes large. A second, narrower target is a certified boundary-only producer for the shared graph partitions and phases.
