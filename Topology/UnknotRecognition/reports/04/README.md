# Unknot recognition: reference implementation and hierarchy components

**Status: partial fulfillment of the requested implementation. This archive does
not contain an unknot recognizer with a proved `n^O(log n)` running time.**
The complete recognizer supplied here is exact and has an exponential
`2^O(n)` worst-case upper bound, where `n` is the input diagram's number of
crossings. It explicitly visits all `2^n` resolutions. The package does not
pretend that an exponential fallback, a timeout, or unimplemented geometric
subroutines establish a quasi-polynomial bound.

The requested route was investigated using Marc Lackenby's 109-page February
2021 talk and his July 2026 hierarchy preprint. See `docs/report.pdf` (and its
LaTeX source) for the source audit, correctness argument, precise complexity
analysis, and the remaining implementation obligations.

## What is actually implemented

* A **complete reference recognizer** for classical one-component knot diagrams:
  reduced Khovanov homology over F2, with exact bit-vector Gaussian elimination.
  Its total rank is one exactly for the unknot, by the cited unknot-detection
  theorem and the universal coefficient theorem. No floating-point linear
  algebra or unproved invariant test is used.
* A **polynomial-time terminal boundary-pattern test** for a manifold that is
  **already known to be a 3-ball**. It validates spherical rotations, builds the
  dual graph, and detects loops, parallel edges, or vertex cuts of size at most
  three. It includes the essential K3 and K4 exceptions. It is not a ball
  recognizer and does not construct or lift an embedded compression disc.
* The **bounded-depth hierarchy potential** and compression/tail-reset checks.
  These are arithmetic components only: they neither construct surfaces nor
  establish the required topological bounds on genus and depth.

All executable paths above are implemented, not placeholders. The hierarchy
construction, compressed cutting, multisurface simplification, and constructive
Heegaard/Cheeger routines needed for a complete quasi-polynomial recognizer
are **not implemented**.

## Run without installing anything

Python 3.10 or newer is required. There are no third-party runtime or test
dependencies. Python 3.13.5 was used for the recorded validation.
From the extracted archive's root directory:

```sh
python -m unknot recognize examples/trefoil.json --verify-d2
python -m unknot recognize examples/unknot_r2.json --verify-d2
python -m unknot recognize examples/torus_3_5.json --verify-d2
python -m unknot pattern examples/pattern_cube.json
python -m unittest discover -s tests -v
```

An optional installation is `python -m pip install .`; this creates the
`unknot-reference` command. Running directly from the root avoids any build
or package downloads. No network access is used by the implementation.

The first command returns `KNOTTED` with reduced F2 rank 3; the second returns
`UNKNOT` with rank 1; the third returns `KNOTTED` with rank 7. Every recognition
result includes `"quasipolynomial_guarantee": false`.

## Input format and conventions

A PD crossing is `[a,b,c,d]` in **counterclockwise** order, starting on an
**underpassing** port. Opposite ports belong to the same strand. Every arc
label must be a nonnegative integer occurring exactly twice. The following
is a trefoil PD (from the cited Knot Atlas entry):

```json
{"pd": [[1,4,2,5], [3,6,4,1], [5,2,6,3]], "basepoint": 1}
```

A raw array of crossings is also accepted. Labels are normalized; the optional
`basepoint` is an **arc label**, not a crossing number. Without it, the first
arc encountered is marked. The reduced rank for a knot is independent of the
mark. **`{"pd": []}` means one crossing-free circle**, not the empty link.
The data cannot additionally encode unrecorded crossing-free components.

Alternatively, specify a closed Artin braid:

```json
{"braid": {"strands": 3, "word": [1,-2,1,-2]}}
```

Generators are signed, one-based, and satisfy `1 <= abs(g) < strands`.
A positive generator has its upper-left strand passing over the upper-right
strand. This convention may differ by a global mirror from another package;
unknot status and total homology rank do not change under mirroring. The
converter checks the closure permutation before constructing the PD, so
untouched extra strands cannot silently disappear.

The validator rejects malformed labels, multi-component links, and
non-spherical rotation systems (virtual/nonplanar diagrams). It checks the
specified rotation system, not just abstract graph planarity. Knot recognition
accepts diagrams, **not photographs**; image-to-diagram extraction is not part
of the package.

## Resource budgets and output

Unbounded recognition is the default. Resource limits are optional:

```sh
python -m unknot recognize examples/torus_3_5.json \
    --max-states 1000 --max-generators 100000 --seconds 10
```

This example reports `UNKNOWN` because 10 crossings require 1024 states. It
never converts exhausted budgets into either topological verdict. The seconds
limit is cooperative: checks occur between Python operations and do not
preempt an individual operation. Parsing and input validation occur before the
recognizer's timed region. A hard operating-system memory kill cannot be
caught by Python; use resource limits for large diagrams.

Exit codes are 0 for a completed computation (either verdict), 2 for invalid
input or a read error, 3 for `UNKNOWN`/interruption, and 4 for an internal
algebraic invariant failure. Matrix ranks and homology dimensions are reported
in **unshifted cube degree**, not the conventional normalized bigrading.
`--verify-d2` additionally checks every adjacent differential product is zero;
this uses extra memory. These checks are not a formal verification of the code.

Python API:

```python
from unknot import Diagram, Limits, recognize

d = Diagram.from_braid(3, [1, -2, 1, -2])
r = recognize(d, Limits(max_states=4096), verify_d2=True)
assert r.status == "KNOTTED"
assert r.reduced_rank == 5
print(r.to_json())
```

## Boundary-pattern input

```json
{"vertices": [[1,2,3], [-1,-3,-2]], "circles": 0}
```

Each vertex gives a cyclic triple of **signed edge ends**. Every positive
label must occur once, and its negative must occur once. The sign here pairs
ends; it is unrelated to braid signs. `circles` counts graph components that
are simple closed curves without vertices. The example is the theta pattern;
its dual is K3 and it is essential on a ball.

The `pattern` command returns a graph obstruction when a pattern is
inessential. A separator is **not** an embedded disc certificate for a general
3-manifold. The returned object explicitly records the ball hypothesis.

## Validation and contents

`python run_validation.py` reruns the tests and regenerates
`validation/unittest.log` and `validation/results.json`. The recorded run has
**62 passing test methods**, including 360 independently checked random binary
matrices; all 168 one-component three-braid words of lengths 2 and 4; Reidemeister
II/braid cancellation, braid relations and Markov stabilization checks;
basepoint/mirror checks; external PD fixtures; invalid inputs; and resource
budget behavior. Twelve knot examples and three graph patterns are also
recorded. Many test methods contain multiple subcases.

The test suite does not constitute a proof of the complexity announcement,
and no independent Regina/KnotTheory executable or Lean verification was run.
External PD and integral-homology data used for fixture checks are attributed
in `docs/fixture_sources.json` and the report. The two-copies relationship over
F2 and the universal coefficient theorem explain how the reduced-rank checks
are derived from the cited unreduced integral tables.

The source layout is `unknot/diagram.py`, `khovanov.py`, `linear.py`,
`pattern.py`, and `potential.py`; `__main__.py` is the command-line interface.
`docs/source_audit.md` maps the notes' main steps to implementation status.
The supplied talk itself is not duplicated in this archive.
