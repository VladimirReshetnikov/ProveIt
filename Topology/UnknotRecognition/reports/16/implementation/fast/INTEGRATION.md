# Optional dense algebra and certified finite-target search

This is a self-contained copy of the existing `Topology/UnknotRecognition/fast`
implementation, with two optional research extensions. The default composition
mode remains `legacy`, and the finite-target filter is disabled by default.
The worst-case complexity of the complete recognizer remains exponential in
crossing number; no general quasi-polynomial recognition guarantee is claimed.

## Exact composition modes

```python
from fastunknot import Diagram, khovanov_rank, recognize

diagram = Diagram.from_braid(3, [1, 2] * 5)
rank = khovanov_rank(diagram.pd, composition="adaptive")
result = recognize(diagram, composition="dense")
```

The accepted modes are:

| Mode | Behavior |
| --- | --- |
| `legacy` | Existing `Planar` composition and transfer. Default; the new dense module is not imported. |
| `adaptive` | Exact support-sensitive sparse/dense composition and bounded-support transfer. |
| `dense` | Forced dense composition/transfer, retaining exact identity shortcuts. Useful for validation and dense workloads. |

`FastScan(..., composition=...)`, `khovanov_rank`, and `recognize` accept the
mode. Nonlegacy modes require `algebra="bits"`, `pivot="minfill"`, and
`self_inverse=True` where that argument is available. Unsupported combinations
raise `ValueError`; they are never silently ignored.

```bash
python -m fastunknot khovanov examples/conway.json --composition adaptive --check-d2
python -m fastunknot recognize examples/conway.json --composition dense
```

Scanner output reports `composition`. Nonlegacy statistics additionally report
`dense_compose_calls`, `sparse_compose_calls`, `dense_transfer_calls`, and
`sparse_transfer_calls`. Identity and zero shortcuts need not increment a kernel
counter. Competing scan processes preserve the chosen composition mode, shape
cache setting, and optional d-squared checking. Factored Khovanov calls forward
the same options to each summand.

## Certified A5 filter

```python
result = recognize(
    diagram,
    quotient_max_assignments=5000,
    quotient_seconds=0.1,
)
```

`quotient_max_assignments=0` disables the filter. A positive integer enables
the seed solver, with that many complete seed-tuple conjugacy orbits available
per examined summand. `quotient_seconds=0.1` is the default cooperative cap
for one filter invocation; `None` removes this separate time cap. When a global
recognition `seconds` budget exists, the filter receives the smaller of its
own cap and the global remaining time. Later stages receive the remaining
global budget rather than a new full budget.

The filter runs after the existing modular Alexander, Jones, and selected exact
Alexander stages and before R3 search or Khovanov. It is imported lazily only
when enabled and reached. Successful certificate replay returns method
`finite-quotient-A5-seeds`. A missing representation, exhausted palette,
assignment cap, or cooperative time cap merely records `INCONCLUSIVE` evidence
and continues the recognizer. Expiration of the shared overall deadline returns
`UNKNOWN` at the existing resource boundary.

```bash
python -m fastunknot recognize examples/conway.json --no-jones \
  --quotient-max-assignments 5000 --quotient-seconds 0.1
```

Disabling Jones in this example exposes the new fallback stage; the existing
default recognizer already rejects the Conway fixture through Jones.

Evidence is stored under `evidence.finite_quotient`, or under the corresponding
factor's evidence when visible connected-sum decomposition is used. It includes
the exact normalized `diagram_pd` of the simplified summand, the seed plan,
counts, status, and explicit permutation certificate. Replay it as follows:

```python
from fastunknot.finite_quotient_check import verify_certificate

evidence = result.evidence["finite_quotient"]
checked = verify_certificate(evidence["diagram_pd"], evidence["certificate"])
assert checked["valid"]
```

An A5 failure never proves the unknot. The added `examples/torus_3_7.json`
fixture is a nontrivial determinant-one knot with no nonabelian A5 image.
Its complete palette has 231 seed-tuple orbits in the discovered three-seed
plan and returns `INCONCLUSIVE` from the filter.

## Validation

```bash
python -m unittest discover -s tests -v
```

All 74 tests passed in the recorded run: all 41 original tests, 11 dense-kernel
tests, 11 finite-target tests, and 11 integration tests. The suite includes
independent scalar composition, 8,637 sampled morphism compositions across all
2,879 noncrossing matching triples through boundary size eight,
dense crossing transfers, complete scanner ranks and degrees, d-squared,
shape caching, tail linear algebra, factorization, competing workers, CLI
configuration, direct permutation coloring enumeration, certificate tampering,
and a mocked-clock test of the shared deadline. The machine-readable result is
`integration_test_summary.json`.

## Full-scanner benchmark

```bash
python benchmark_composition_scanner.py --repeats 5 \
  --baseline-root /path/to/original/Topology/UnknotRecognition/fast \
  --output paired_scanner_benchmark.json
```

If `--baseline-root` is omitted, the local legacy mode is the baseline.
Each timed sample uses a fresh child process, one untimed warm-up, and one timed
complete scanner call. The crossing order and shape-cache choice are fixed and
shared across modes. Imports, validation, fixture parsing, and order selection
are outside the timed interval. The supplied run used the immutable original
package for legacy samples and this copy for adaptive/dense samples. All 135
timed samples completed; ranks and degree distributions agree exactly.

| Fixture | Crossings | Legacy ms | Adaptive ms | Dense ms |
| --- | ---: | ---: | ---: | ---: |
| Trefoil | 3 | 0.388 | 0.566 | 0.464 |
| Figure eight | 4 | 2.373 | 1.153 | 0.737 |
| Conway | 11 | 6.140 | 6.486 | 7.047 |
| Kinoshita–Terasaka | 11 | 8.026 | 9.865 | 11.560 |
| Hard unknot 8 | 8 | 0.863 | 1.339 | 2.424 |
| T(3,5) | 10 | 6.273 | 4.803 | 6.086 |
| T(3,7) | 14 | 11.130 | 10.156 | 12.147 |
| Generated hard unknot 27 | 27 | 16.912 | 25.202 | 33.348 |
| Stress braid5 36 | 36 | 455.644 | 478.966 | 502.907 |

These are medians of five isolated samples in a shared container. Small
fixtures show substantial timing variability: for example, figure-eight legacy
samples ranged from 0.590 to 4.099 ms, and its apparent median improvement is
not reliable evidence of a kernel speedup. The raw JSON retains every sample,
range, invariant result, operation counter, normalized PD, input hash, and
algorithm source hash. The new kernels do not establish a global full-scanner
or default-pipeline speedup on these ordinary fixtures. Keeping them optional
is supported by the paired results; their dense-algebra complexity improvement
must be assessed separately from object counts and ordinary sparse workloads.

## Files and patch integration

Existing files with intentional semantic edits:

- `fastunknot/scan_fast.py`: lazy optional algebra selection.
- `fastunknot/scan.py`: public mode argument, validation, counters, race propagation.
- `fastunknot/recognize.py`: optional bounded A5 stage and option forwarding.
- `fastunknot/__main__.py`: CLI flags and worker configuration.
- `README.md`: link to these integration notes.

New implementation modules are `fastunknot/dense_compose.py`,
`fastunknot/finite_quotient.py`, and `fastunknot/finite_quotient_check.py`.
New tests are `tests/test_dense_compose.py`, `tests/test_finite_quotient.py`,
and `tests/test_research_integration.py`. The benchmark script, its JSON, the
test summary, these notes, and `examples/torus_3_7.json` complete the supplement.

For a repository patch, compare this directory against the exact baseline at
`Topology/UnknotRecognition/fast`, retaining paths relative to the repository
root. Exclude generated `__pycache__` and `.pyc` files and unrelated results.
Baseline transport newline normalization, if required by the provenance audit,
must be recorded separately from these semantic changes. The provided
benchmark hashes identify the bytes actually measured before normalization;
the normalized PD inputs are also retained directly in the benchmark JSON.
