# Unknot recognition speed-up — fastunknot 0.2.0

This archive contains a working, dependency-free Python implementation, the
unchanged supplied `fast/` implementation under `baseline/`, reproducible
benchmarks, independent validation, and a mathematical/engineering report.

**General complexity is still exponential, not quasi-polynomial.** The
implementation obtains large practical improvements and a genuine parameterized
bound `poly(n) + n * 2^O(b)`, where `b` is the largest factor found by its certified
*diagrammatic* connected-sum decomposition. This is polynomial when
`b = O(log n)` and quasi-polynomial when `b = O(log² n)`. It is not a bound for
all diagrams of all composite knots.

## Measured results

Same machine, CPython 3.13.5, one pinned logical CPU, cold process/caches per
sample. Small cases use medians of three samples; the 36-crossing case uses one
sample per engine. Times exclude imports and input conversion.

| Task | Supplied baseline | New version | Comparison |
|---|---:|---:|---:|
| Full rank, supplied random 5-braid, 36 crossings | No result within 60 s | 1.110 s | More than 54× within that budget |
| Same input, cached engine but original LIFO pivots | 49.576 s | 1.110 s | 44.7× from the pivot change |
| Recognize Conway diagram | 34.036 ms | 1.610 ms | 21.1× |
| Recognize Kinoshita–Terasaka diagram | 38.233 ms | 1.563 ms | 24.5× |
| Full rank, connected sum of 8 trefoils | 1.306 s | 3.638 ms | 359× |
| Full rank, connected sum of 100 trefoils | Not run | 65.597 ms | Exact reduced rank `3**100`, at most 18 live objects |

Raw rank timings do not use R1/R2 simplification. Generic raw-rank comparisons
also disable factoring; connected-sum comparisons enable it. These are measured
examples, not a universal speedup guarantee: the supplied hard eight-crossing
unknot is about 43% slower through the default pipeline (2.735 ms vs 1.915 ms).
All raw samples, budgets, memory high-water marks, input words, and source
fingerprints are in `results/benchmark.json`.

## Run immediately

Python 3.10 or later is required; there are **no runtime dependencies**.
Run these commands from the archive root:

```sh
cd fast
python -m fastunknot recognize examples/conway.json --output conway-proof.json
python -m fastunknot verify examples/conway.json conway-proof.json
python -m fastunknot khovanov examples/random_5_braid_36.json --no-factors
python -m fastunknot recognize examples/hard_unknot_8.json
```

For an installed command, `python -m pip install ./fast` from the archive root
installs `fastunknot`. Installation is optional; running the source directly is
sufficient. Input supports the original PD, closed-braid, and grid JSON formats.

The default pipeline is validation, R1/R2 reduction, descending-diagram test,
exact modular Alexander rejection, capped Jones rejection, full exact Alexander,
and complete F2 Khovanov fallback. Neither modular filter ever declares UNKNOT.
A matching evaluation is inconclusive, not probabilistic acceptance.

`--no-alexander` disables both Alexander stages, but does **not** disable Jones.
Use `--no-alexander --no-jones` to force the homological path after simplification
and descending tests. `khovanov` computes full ranks without those preprocessing
stages. `--pivot lifo` selects the old pivot order with the new arithmetic/caches.

`--seconds` is a cooperative time budget. `--max-objects` caps each scanned
factor's live objects. Limits return `UNKNOWN`; they do not return a knot verdict.
The Jones filter's `--max-jones-states` cap defaults to 4096 and merely skips the
filter if exhausted. Setting that cap to zero disables the filter.

Exit codes: 0 for either completed verdict; 3 for a resource limit; 2 for invalid
input/options. `verify` returns 0 for a verified modular rejection, 1 otherwise.
The verifier checks the reduction trace and recomputes the witness; it is not a
verifier for arbitrary Khovanov outputs.

## Reproduce the tests and measurements

From the archive root:

```sh
python -m unittest discover -s fast/tests -v
python tools/validate_exhaustive.py
python tools/benchmark.py
```

The test suite has 30 test methods, many with hundreds of subcases. The separate
exhaustive run covers all 2856 one-component 3-braid words of lengths 2, 4 and 6;
there were zero mismatches and 1144 independently recomputed rejection
certificates. The dense rank oracle is structurally independent of the scanner
and is adapted from the supplied tests. The full Jones state-sum oracle is also
independent of the frontier/gluing implementation. These tests are not a formal
proof of the Python program.

The benchmark takes several minutes, including its intentional baseline timeout
and a 50-second cached-LIFO ablation. `--only conway` or `--only ordering_` limits
the cases. Timing records are rewritten only in the selected `--output` file.
The old Windows results in `baseline/results/` are historical input, not the
source of the same-machine ratios above.

## Contents

- `fast/`: improved implementation and tests; `fast/README.md` documents the API.
- `baseline/`: unchanged user-supplied `fast/` for comparison.
- `report/unknot_speedup.tex` and `.pdf`: algorithms, proofs, bounds, limitations,
  benchmarks, and an audit of the supplied Lackenby material.
- `tools/`: independent oracles, exhaustive validator, benchmark harness.
- `results/`: actual logs and machine-readable results.
- `changes.patch`: reviewable diff against the supplied code.
- `PROVENANCE.json`: input archive/doc hashes and baseline identity checks.
- `MANIFEST.sha256`: hashes of the deliverable files.

The preserved top-level license is MIT No Attribution (MIT-0). The implementation
does not call external topology services, install packages at runtime, or depend
on an unimplemented hierarchy oracle.
