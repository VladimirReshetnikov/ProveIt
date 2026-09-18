# Unknot recognition: exact implementation and complexity audit

**Status: this package does not implement the requested `n^O(log n)` algorithm.**
The working recognizer is an exact **exponential-time** algorithm based on reduced
Khovanov homology over `F_2`. Its explicit enumeration of `2^n` resolutions prevents
it from satisfying the requested worst-case bound. It is not a heuristic and does
not confuse an inconclusive invariant with a proof of unknotness.

The package also implements a **polynomial-time terminal boundary-pattern test**
from the supplied hierarchy approach, on the boundary of a *known 3-ball*.
The accelerated hierarchy's other geometric subroutines are not implemented.
There are no hidden geometry oracles, empty implementation stubs, or mislabeled
quasipolynomial mode. The accompanying technical report explains the exact gap.

## Run without installation

Python **3.9 or newer**, standard library only. Tested on Python 3.13.5.
From the extracted `unknot-recognition` directory:

```sh
python -m unknot recognize examples/trefoil.json --check-d2
python -m unknot recognize examples/kt11n42.json --check-d2
python -m unknot recognize examples/unknot-braid12.json --check-d2
python -m unknot recognize examples/figure-eight.json > result.json
python -m unknot verify result.json
python -m unknot pattern examples/pattern-prism.json
python -m unittest discover -s tests -v
```

`--check-d2` checks the entire differential identity `d*d = 0`, not a sample.
The `verify` command reconstructs and checks the computation; it is **not** an
independent proof checker, a short certificate, or a polynomial-time verifier.

For a bounded attempt:

```sh
python -m unknot recognize examples/kt11n42.json --max-states 1024 --seconds 10
```

This deliberately returns `"status": "unknown"`, with exit code 3. It never turns
budget exhaustion into a claim that a knot is nontrivial. No budgets are imposed
by default. Time limits are cooperative, not hard real-time process deadlines.
There is no strict memory cap; the optional generator limit is a size guard.

## Input

Either a planar-diagram code:

```json
{"name":"trefoil","pd":[[1,5,2,4],[3,1,4,6],[5,3,6,2]]}
```

or a closed braid (signed Artin generators, positive = left strand over right):

```json
{"name":"figure-eight","braid":{"strands":3,"word":[1,-2,1,-2]}}
```

In each PD tuple `(a,b,c,d)`, entries occur counterclockwise around the crossing,
with the underpassing strand joining `a` to `c`. Every edge label occurs exactly
twice. Labels are arbitrary nonnegative integers and are renumbered internally.
A `basepoint` field can select an existing edge; otherwise the least label is
used. `{"pd":[]}` explicitly means **one crossing-free circle**, not an empty link.
Multi-component links, non-spherical rotation systems (virtual diagrams), and
malformed inputs are rejected. The crossing count is that of the supplied diagram,
not a computed minimum over all diagrams of the knot.

A pattern input explicitly asserts `"ambient":"3-ball"`. Each vertex supplies a
cyclic triple of darts. Edge `e` joins darts `2e` and `2e+1`; every dart appears once.
The `circles` field counts vertex-free circle components. See the examples.
**That ambient assertion is a precondition, not a 3-ball recognition certificate.**

## Output and API

Recognition JSON reports `unknot`, `knotted`, or `unknown`, along with the input,
resolution count, chain dimensions, differential ranks, homology dimensions, and
elapsed time. Homological degrees are **unnormalized cube heights**: writhe shifts
are omitted. Total homology dimension, not the displayed grading, drives the answer.
The program does not return a spanning disk, an isotopy, or a Reidemeister sequence.

```python
from unknot import Diagram, Limits, recognize

diagram = Diagram.from_json({"braid": {"strands": 3, "word": [1, -2, 1, -2]}})
result = recognize(diagram, limits=Limits(max_states=4096), check_d_squared=True)
assert result["status"] == "knotted"
assert result["reduced_homology_dimension"] == 5
```

Exit codes: `0` for a completed mathematical computation; `1` for an unverified
report; `2` for invalid input or a file error; `3` for an inconclusive resource-limited
run; `130` for interruption. Both positive and negative knot decisions exit `0`.
A failed `verify` may mean either mismatched data or an exhausted verification budget.

## Contents

- `unknot/`: original implementation, with no runtime dependencies.
- `tests/`: 45 test methods, including 160 four-letter three-braid knot closures,
  Reidemeister/Markov checks, basepoint and mirroring checks, a separate small
  reference-complex construction, and an independent dense rank calculation.
- `examples/`, `results/`: input fixtures and actual computation reports.
- `docs/technical-report.tex`, `docs/technical-report.pdf`: mathematical specification,
  correctness argument, complexity bounds, and the missing accelerated-hierarchy work.
- `docs/SOURCES.md`: source URLs, page/section references, and provenance.
- `results/TEST_RESULTS.txt`, `results/BENCHMARKS.json`: reproducible test and run records.
- `reproduce.py`: regenerate results and rerun the tests with the standard library.

The two 11-crossing examples have trivial Alexander polynomial, but the implementation
returns nontriviality from homology dimension 33. Their names and PD codes come from
Knot Atlas; the rank values in `results/` were computed here. A constructed 12-crossing unknot is also included and returns dimension 1.
Small timings do not
establish the requested asymptotic bound. No external knot package or Lean checker
was used to validate this implementation.
