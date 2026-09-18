# Knots: accelerated exact recognition

This is a working replacement for the `fast/` package in the supplied `Knots.zip`.
It includes the unchanged original Python implementation, an improved recognizer,
independent reference tests, cold-process benchmarks, and a **20-page mathematical
report in LaTeX and PDF**.

**The general worst case is still exponential. No global quasipolynomial bound
is claimed.** The result is a substantial practical improvement, plus a provable
exponential improvement on a visible connected-sum family. The report distinguishes
this from Lackenby's announced quasipolynomial hierarchy algorithm.

## Start here

From the extracted directory:

```sh
cd fast
python -m fastunknot recognize examples/conway.json --output result.json
python -m fastunknot verify examples/conway.json result.json
```

Python 3.10 or later; no third-party runtime dependencies. Optional installation:

```sh
python -m pip install ./fast
```

Inputs can be a validated classical one-component PD, braid closure, or grid
code. For example `{"braid":{"strands":2,"word":[1,1,1]}}`. Every PD edge occurs
twice, rows have four cyclically ordered ports, and under/over ports are 0/2 and
1/3. `{"pd":[]}` denotes a single crossing-free circle. Links and nonspherical
rotation systems are rejected. Existing `fast/examples/` inputs work unchanged.

## What changed

The new default pipeline performs R1/R2 simplification, a linear descending test,
validated visible connected-sum decomposition, bounded exact Jones screening,
Alexander screening, and an improved exact F2 Khovanov fallback.

* **Jones frontier aggregation:** sum partial smoothing weights as soon as their
  boundary matchings agree. A modular mismatch certifies knottedness; agreement
  never certifies the unknot. The default 4096-state ceiling skips an expensive
  screen rather than disabling the complete fallback.
* **Compressed connected sums:** check dual two-edge cycles and record replayable
  cuts. Analyze summands separately. The rank command multiplies reduced
  homological polynomials without materializing a tensor-product basis. This is
  visible diagram decomposition, not topological prime decomposition.
* **Faster raw scanner:** self-inverse units in the characteristic-two square-zero
  algebra, identity and endomorphism shortcuts, bounded topology/decoration caches,
  and lazy fill-in-aware unit cancellation. The same greedy crossing order is
  constructed in O(n log n) rather than O(n^2) per starting crossing.

The patch also fixes orientation-sensitive crossing signs and updates the
Alexander matrix consistently, validates full scan-order permutations, improves
cooperative deadline checks, and supplies evidence replay.

## Measured results

Same machine, CPython 3.13.5/Linux, three fresh processes per completed case.
Times exclude imports, process startup, JSON parsing, and initial Diagram
construction. The median is reported; a timeout is not a measured completion.

| Operation and fixture | Supplied baseline | Improved | Baseline / improved |
|---|---:|---:|---:|
| Recognize Conway | 35.090 ms | 0.834 ms | 42.09x |
| Recognize Kinoshita–Terasaka | 37.594 ms | 0.904 ms | 41.58x |
| Recognize Conway # Conway | 1.372 s | 1.455 ms | 943.04x |
| Recognize three Conway copies | >30 s | 1.972 ms | >15,210x |
| Raw Khovanov, 41-crossing braid | 0.923 s | 0.283 s | 3.26x |
| Raw Khovanov, 36-crossing stress braid | >30 s | 1.487 s | >20.17x |
| Raw Khovanov, two Conway copies | 1.395 s | 0.235 s | 5.93x |

The fast raw 36-crossing result has reduced rank **2949**. It was checked with
`d^2 = 0` after each stage and against its 24-crossing R2-reduced diagram, including
the homological-degree shift. This is an invariance check of the same backend,
not an independent dense computation on 36 crossings.

The **factored rank** of 16 connected Conway copies (176 crossings) is
`1977985201462558877934081 = 33^16`, computed with its full raw homological-degree
rank map in a median 47.95 ms. This uses at most 246 pre-elimination objects in
an individual factor scan, not 246 objects' worth of total process memory.

These improvements are not universal. Default recognition of the trefoil becomes
about 0.229 ms rather than 0.092 ms, and the hard eight-crossing unknot takes
2.244 ms rather than 1.622 ms. The original default pipeline already recognizes
the 36-crossing stress braid in 8.626 ms: the large improvement on that fixture
is specifically for **raw homology**, not default recognition. All comparisons
and their min/max/sample records are included.

## Commands and APIs

```sh
# Run from fast/:
python -m fastunknot recognize examples/conway.json
python -m fastunknot recognize examples/conway.json --no-jones --no-factor
python -m fastunknot recognize examples/conway.json --seconds 10 --max-objects 50000
python -m fastunknot jones examples/conway.json --A 2 --modulus 1000000007
python -m fastunknot khovanov examples/conway.json             # factored ranks
python -m fastunknot khovanov examples/conway.json --no-factor # raw improved scan
python -m fastunknot khovanov examples/conway.json --check-d2
```

`recognize` returns UNKNOT, KNOTTED, or UNKNOWN. Exit codes are 0 for a completed
result, 2 for invalid input or rejected evidence, and 3 for resource exhaustion.
A standalone Jones evaluation is not itself an unknot decision.

```python
from fastunknot import Diagram, recognize, khovanov_rank, factored_khovanov_rank
from fastunknot import verify_result

D = Diagram.from_braid(2, [1, 1, 1])
r = recognize(D)
assert r.status == "KNOTTED"
assert verify_result(D, r.to_json())

raw = khovanov_rank(D.pd, pivot_strategy="minfill")
# pivot_strategy="stack" retains the previous pivot policy with new algebra.
compressed = factored_khovanov_rank(D)
assert raw["reduced_rank"] == compressed["reduced_rank"]
```

`by_degree` is the **unshifted cube homological degree**, not quantum grading.
For knots over F2, its unreduced ranks are twice the reduced ranks degree by
degree. Factored ranks insert the factor of two only once.

## Reproduce the validation and benchmarks

Run from the archive root:

```sh
python tools/make_inputs.py
python -m unittest discover -s tests -v
python tools/benchmark.py --repeats 3 --timeout 30
python tools/ablate.py --repeats 3 --timeout 10
python tools/validate_stress.py
python tools/make_report_tables.py
```

The final suite has **48 passing tests**. It includes 128 unit inverses, 1200
surface compositions, 60 baseline/pivot scan comparisons, 80 independent small
cubes, 100 independent Jones state sums at multiple moduli, decomposition/rank
convolutions, diagram invariances, 90 all-start order comparisons, 300 descending
test comparisons, malformed inputs, limits, CLI behavior, and tampering tests.
Counts above are cases inside test methods, not numbers of unittest methods.
`baseline/tests/` preserves the original 19 tests; `tests/test_legacy.py` adapts
those tests to exercise the old filter configuration with the new implementation.

`--quick` selects the small benchmark subset. Benchmarks can take several minutes
because censored cases intentionally use the stated deadlines. The default main
run is sequential. Caches start cold in each child process.

To rebuild the PDF, install a standard LaTeX distribution and run `report/build.sh`
or run `pdflatex report.tex` from `report/` three times. The PDF and generated
LaTeX table files are already included. Re-running the measurements and the table
generator changes the tables but does not automatically rewrite numerical
observations in the report's prose; update those explicitly for a new environment.

## Directory map

- `fast/`: improved package, examples, install metadata.
- `baseline/`: unchanged supplied sources, tests, benchmark script and old results.
- `tests/`: additional tests and independent dense-cube reference.
- `tools/`: deterministic fixture generation, benchmarks, ablation, validation, tables.
- `benchmarks/`: all raw new results, CSV summary, logs, provenance, fixtures.
- `examples/evidence/`: four generated recognition records, replayed successfully.
- `patches/fastunknot.patch`: source diff against the supplied Python package.
- `report/report.tex`, `report/report.pdf`, `report/tables/`: mathematical report.

## Boundaries of the claims

Without user resource ceilings, the mathematical fallback is complete. On an
actual finite machine, memory/time exhaustion can still return UNKNOWN. Limits
are cooperative; a large internal operation can overrun a deadline before the
next check. The object ceiling is not an operating-system memory cap. Bounded
cache entry counts do not bound bytes, since morphisms can be exponentially large.

The verifier shares topology and algebra code; a Khovanov result is checked by
recomputation, not a succinct polynomial-time certificate. This release is not
formally verified in Lean, does not compute integral or quantum-graded homology,
and is not an implementation of Lackenby's hierarchy algorithm.

A small scan boundary does **not** ensure polynomially many surviving Khovanov
objects. Connected sums of a fixed nontrivial knot have exponential reduced rank
and admit constant-width scan orders. The new factor representation avoids that
specific explosion. General worst-case complexity remains `2^O(n)`; the API
explicitly emits `quasipolynomial_guarantee: false`.

License: MIT No Attribution (MIT-0), preserving the supplied license. Baseline
attribution and external mathematical sources are documented in the report.
