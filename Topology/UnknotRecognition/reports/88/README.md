# Polynomial marked-cut kernels for arbitrary disconnected tile powers

Research continuation for **ProveIt / Topology / UnknotRecognition**, 12 October 2026.

The article and code extend the incoming connected four-copy reduction to arbitrary finite disconnected graph tiles. The reduction preserves every boundary coloring and every exact set of monochromatic-edge colors at a fixed cut threshold, without enumerating a full common permutation period.

## Main results

For a tile of width `w`, explicit size `q`, and positive binary repetition count `N`, the kernel has `O((k+3)(w+1)^2 q)` vertices and edges and the same complete threshold-`k` marked signature. Its construction is polynomial in `q + bits(N) + k`; `k` is a numerical parameter and is fixed at three for the intended terminal-pattern application.

The proof obtains a rank-stable power after at most `w+1` copies, retains actual source seams, separates them into connected cyclic channels and detached pieces, and caps each channel's **individual** connected period. It never expands the least common multiple of the component cycle lengths. The article also proves a polynomial transient, contextual replacement, binary source-coloring lifting, and quasi-polynomial query bounds for logarithmic-depth, polynomial-width assembly descriptions.

This does **not** establish unrestricted quasi-polynomial unknot recognition. It is an abstract graph operator with a precise future geometric input contract.

## Read first

- `article/disconnected_tile_kernels.pdf`: complete article, proofs, measurements, and research agenda.
- `article/disconnected_tile_kernels.tex`: self-contained LaTeX source; no external figures or bibliography file.
- `integration/INTEGRATION.md`: source-provenance contract and remaining native obligations.
- `SOURCE_AUDIT.json`: inspected sources, repository checkpoint, and scope of the targeted audit.

## Run

Python standard library only. Tested with CPython 3.13.5. Run commands from the package root:

```sh
PYTHONPATH=code python -m unittest discover -s tests -v
PYTHONPATH=code python experiments/audit.py partitions
PYTHONPATH=code python experiments/audit.py signatures
PYTHONPATH=code python experiments/audit.py geometry
PYTHONPATH=code python experiments/audit.py nested

PYTHONPATH=code python -m cycle_kernel \
  examples/huge-permuted-prism.json --output reproduced-proof.json
PYTHONPATH=code python -m cycle_kernel reproduced-proof.json \
  --replay --output reproduced-replay.json
```

On Windows PowerShell, set `$env:PYTHONPATH = "code"` before the Python commands. For experiment scripts importing `families`, use `$env:PYTHONPATH = "code;experiments"` (a semicolon, not the POSIX colon).

The CLI closes the single tile power's external interface. It returns only `LOW_MARKED_CUT` or `NO_LOW_MARKED_CUT`. It also reports whether local source degrees certify a cubic closure. It does not prove a sphere embedding, a ball, an embedded noose, a three-dimensional disc, or an unknot. Empty patterns and vertex-free circle components must be handled by a geometric pattern inventory before applying the cubic graph criterion.

Exit status is zero for successful production or valid replay, one for failed certificate replay, and two for supported input/resource errors. A resource error is not a graph verdict. The CLI bounds thresholds to 0..16 and has a configurable kernel-edge cap before graph query.

## Python API

```python
from cycle_kernel import Graph, kernel_power, close
from cycle_kernel.query import solve_graph
from cycle_kernel.replay import verify_graph

# A disconnected swap matching, with distinct input/output vertices.
tile = Graph(4, ((0, 3), (1, 2)), (0, 1), (2, 3))
kernel, metadata = kernel_power(tile, (1 << 4096) + 1, k=3)
closed_kernel = close(kernel)
proof = solve_graph(closed_kernel, k=3)
assert verify_graph(closed_kernel, proof, k=3)
```

`Graph` preserves loops, repeated edge occurrences, and isolated vertices. A source tile must have nonempty equal-length ordered port lists with distinct entries and disjoint input/output sets. There is no zero-exponent identity in this interface type.

`cycle_kernel.grammar.evaluate` handles expression trees with `leaf`, `serial`, `parallel`, and positive binary `power` nodes. Adjacent powers are fused. A tree is not silently treated as a bounded-depth DAG, and exceeding the evaluator's explicit resource limits aborts rather than producing a terminal verdict.

## Verification boundary

`replay.py` independently checks the **finite graph proof** and never calls the flow search or kernel constructor. CLI source binding additionally reconstructs the kernel from the source, but that reconstruction **shares normalization code with production**. It is not an independent compression checker.

`witness.py` implements binary local color-run lifts for connected periods and detached repetitions. The complete global coloring-to-original-source-edge address exporter is proved in the article but not implemented. Its geometric noose/disc transport is also absent.

The native `fastunknot` regression suite and knot corpus were not run. No upstream file, branch, or commit was modified.

## Evidence

The retained logs record 37 unit tests, 4,360 boundary partitions, 6,000 complete signature comparisons (672,000 entries), 1,800 source-cell-cover audits, 700 cubic-source checks, and 250 nested-expression comparisons. All reported completed audits passed after the cap-port regression was corrected.

Benchmark JSON files contain paired complete finite-graph construction/query/replay times, including the small-input regression and an identical-arm control. A larger 33-copy positive run was terminated before writing its final result file and is explicitly excluded; no partial ratio is published. These are graph-operator experiments, not native knot-recognition speedups.

```sh
PYTHONPATH=code:experiments python experiments/benchmark.py positive-17
PYTHONPATH=code:experiments python experiments/benchmark.py negative-1024
PYTHONPATH=code:experiments python experiments/benchmark.py AA-9
PYTHONPATH=code:experiments python experiments/benchmark.py binary
python experiments/make_table.py
sh article/build.sh
```

The full benchmark driver (`all`) includes the larger previously excluded case and may need a longer execution allowance. Regenerating the timing table uses completed JSON files only. The article uses standard LaTeX packages, including `amsmath`, `amsthm`, `tikz`, `microtype`, and `hyperref`.

## Suggested integration

Preserve this delivery as a new research-report intake under the repository's existing next-number convention, rather than overwriting the prior four-copy report. The code is an opt-in candidate pending a native geometric exporter and stronger source-independent replay. No patch is presented as applied. No font files or third-party implementation code are included.
