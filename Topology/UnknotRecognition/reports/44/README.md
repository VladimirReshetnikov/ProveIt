# Rank-Two Terminal Contractions and Singularity-Safe Modular Observers

A research contribution for `ProveIt/Topology/UnknotRecognition`, dated 8 October
2026. The article is `article/article.pdf`; its editable sources are in `article/`.

## Result and scope

A fixed-size matrix represents each anchored partition of a signed graph's
terminals. Merging source block B (anchor b) into target block A (anchor a)
changes it by

```
M_new - M_old = -(e_b - e_a) w_B^T + chi_B (e_b - e_a)^T.
```

Here `w_B` is a sum of ORIGINAL base-kernel rows, and `e_0=0` for the root.
The determinant equals the quotient cofactor without a partition-dependent sign.
Prime-specific interior normal forms retain singular null directions rather
than rejecting primes. Explicit rank normal forms handle every intermediate
singularity. A supplied merge tree with J edges and Q observations costs
`O(v^3 + J*b^2 + Q)` field operations per prime, including fresh setup and state
copies. Signed CRT and graph-derived bounds recover exact integers.

This is a boundary-observer improvement, NOT a complete unknot recognizer and NOT
a proof of general quasi-polynomial unknot recognition. A cofactor certificate
certifies its supplied graph quotient, not the derivation of that graph from a
knot diagram. Generating the queries and bounding all other recognition work
remain separate obligations. Generic matrix-tree, elimination, CRT, and dynamic
rank ingredients are not claimed as newly invented.

## Reproduce

Standard-library Python, tested with 3.13.5. No network or third-party Python
packages are needed for the algebra, tests, audits, or benchmarks.

```sh
python -m unittest discover -s tests -v
python scripts/audit.py
python scripts/benchmark.py
python scripts/verify_certificate.py certificates/cycle6-nonminimum-anchor.json
sh build.sh
```

LaTeX is needed only for `build.sh`. The build uses pdfLaTeX and standard packages
including `amsmath`, `amsthm`, `lmodern`, `microtype`, and `hyperref`.

To check the delivered files before rerunning commands that rewrite results:

```sh
python scripts/verify_manifest.py
```

Reproduction regenerates timing samples and logs, so run it in a working copy.
The manifest hashes the actual delivered files, not the outcome of future runs.

## API example

```python
from terminal_updates.terminal import SignedGraph, ExactObserver
from terminal_updates.batch import MergePlan

graph = SignedGraph(6, tuple((i, (i + 1) % 6, 1) for i in range(6)))
observer = ExactObserver(graph, (0, 1, 2))
root = observer.cursor()
assert root.value == 6
child = root.merged(2, 1)   # retain nonminimum anchor 2
assert child.labels == (0, 2, 2)
assert child.value == 5
assert child.merged(0, 2).value == 4
assert root.value == 6      # parents remain unchanged

plan = MergePlan.compile(3, [(0, 1, 2), (0, 1, 1), (0, 0, 0)])
assert plan.evaluate(observer) == [6, 5, 4]

from terminal_updates.terminal import verify_exact_certificate
assert verify_exact_certificate(child.certificate())
```

For one field use `TerminalKernel(graph, terminals, prime)`; its cursor exposes
`residue` instead of `value`. For a single independent query, `kernel.query` uses
the smaller static singular-safe border. It is often the better method for small
boundaries or heavily merged partitions.

`DynamicRank.update` is a low-level mutable operation. Persistent cursor merges
clone it before updating. Instrumented `Budget` exhaustion is an exception, never
a mathematical verdict. Prime preparation and all static high-level paths are
not yet fully interruptible production interfaces.

## What was actually checked

The release contains 39 passing unit-test methods; 19,200 matrix-update checks;
1,772 signed-graph quotient checks from 600 prime-specific kernels, including 193
singular interiors; every one of 877 partitions of seven terminals; and three
independently verified exported exact certificates. See `results/audit.json`,
`results/unittest.txt`, and the article for the precise scopes.

Seven shuffled paired warm timing rounds include fresh setup and an identical
static control arm. The comparison baseline eliminates the SMALLER singular
border at each query, not the full original graph. All raw samples and exact
workloads are in `results/benchmark.json`, with a compact CSV alongside it.

These are graph-observer microbenchmarks. They are not recognizer timings,
upstream knot traces, or evidence of a universal speedup. Small exact modular
cases lose substantially to direct integer Bareiss elimination. No current
production default should be changed solely on these results.

## Suggested additive integration

Place this directory at, for example:

```
Topology/UnknotRecognition/research/dynamic_terminal_20261008/
```

The adapter and replay script are in `integration/`. They preserve the reviewed
`BoundaryTait` interface and call its geometry validation before interpreting a
cofactor. The adapter was tested with a protocol fixture only. A full upstream
checkout was not available locally, and the upstream replay and maintained test
suite were NOT run. `integration/README.md` explains the required next validation
step. No maintained source file is overwritten or production dispatch enabled.

## Files

- `article/`: 26-page article, TeX source, generated benchmark table.
- `terminal_updates/`: finite-field rank maintenance, singular terminal kernels,
  exact observers, CRT, verifier, and merge-plan compiler.
- `tests/`: unit and regression tests.
- `scripts/`: reproducible algebra audit, paired benchmark, certificate and
  manifest checks.
- `certificates/`: exact six-cycle examples exercising modular singularity,
  nonminimum anchors, and root merging.
- `results/`: raw timing samples, audit results, test and LaTeX logs.
- `integration/`: optional geometry adapter and unexecuted upstream replay tool.
- `PROVENANCE.json`: reviewed source identities and execution boundaries.

The source review, original proofs, and code should still receive independent
mathematical and implementation review before production use. No proof-assistant
verification or global-priority claim is made. The new material is released
under MIT-0, compatible with the parent repository.
