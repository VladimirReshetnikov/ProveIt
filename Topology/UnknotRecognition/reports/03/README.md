# Unknot recognition workbench

**Status: partial implementation. The requested general `n^O(log n)` running-time
bound has NOT been achieved.** This archive must not be described as a completed
implementation of Lackenby's quasi-polynomial algorithm.

It contains a working exact reference recognizer (exponential worst case), a
polynomial-time boundary-pattern subroutine motivated by the attached notes, and
an executable arithmetic audit of the hierarchy iteration bound. There are no
mock geometry engines, assumed answers, hidden recognition services, or
unimplemented functions in the execution paths.

## Run without installation

Python 3.10 or later is required. Only the standard library is used. The tests
were actually run with CPython 3.13.5 on Linux; other Python versions were not
executed in this session. From the extracted `unknot_workbench` directory:

```sh
python -m unknot_lab recognize examples/trefoil.json
python -m unknot_lab recognize examples/torus_3_5.json --check-d2
python -m unknot_lab recognize examples/unknot_8_crossings.json --check-d2
python -m unknot_lab pattern examples/pattern_prism.json
python -m unknot_lab verify-pattern examples/pattern_prism.json results/pattern_prism.json
python -m unknot_lab bound 100 7
python -m unittest discover -s tests -v
python benchmark.py
```

On systems where the interpreter is named `python3`, use that command instead.
An optional setuptools installation exposes the same CLI as `unknot-lab`; it is
not needed to run any example or test.

## What is implemented

`recognize` validates a classical one-component planar diagram, applies an
optional exact Fox-determinant obstruction, and, when necessary, computes the
**total reduced Khovanov homology rank over F2** by the explicit cube of
resolutions. The result is `unknot` exactly when this rank is one. This is a
complete mathematical decision procedure with resource ceilings removed. It is
not just a Jones-polynomial or Alexander-polynomial heuristic.

`pattern` decides whether a boundary pattern on an **already known 3-ball** is
essential. It accepts cubic planar multigraphs, loops, parallel edges, and
vertex-free circle components. For a connected graph it searches small edge
bonds, returning a short dual-cycle witness when the pattern is inessential.
Its combinatorial running time is `O(E^3 (V+E))`. It does not recognize 3-balls,
construct a knot exterior, or establish essentiality on an arbitrary manifold.

`bound` evaluates the conditional bound `L*(g+1)^L`. The Python module also checks
lexicographic resets and the numerical Cheeger inequality. It does not compute
geometric genera, certify a Morse function, find Cheeger regions, or establish
logarithmic hierarchy depth.

## Input and output

A planar crossing lists four edge labels in cyclic order; slots 0 and 2 are the
underpassing strand, and slots 1 and 3 the overpassing strand. Each label occurs
exactly twice. Empty PD explicitly means **one** crossing-free circle, not an
empty link. Extra invisible components are not supported.

```json
{"pd": [[1,4,2,5], [3,6,4,1], [5,2,6,3]]}
```

Alternatively, an Artin braid word uses signed generator indices:

```json
{"braid": {"strands": 3, "word": [1,2,1,2,1,2,1,2,1,2]}}
```

Its closure must be a knot, not a multi-component link. The program rejects
non-spherical rotation systems (virtual diagrams), disconnected projections,
malformed labels, and multi-component braid closures. `--basepoint LABEL`
chooses an original PD edge label; the default is the smallest label.

The example above is the torus knot T(3,5). The implementation computes
determinant 1 but reduced F2 rank 7, and correctly reports `nontrivial` rather
than treating determinant 1 as an unknot certificate.

Results are JSON. Both an exact positive and an exact negative verdict exit 0.
A resource-limited computation exits 2 with `status: "unknown"` and
`is_unknot: null`. Invalid data or a rejected pattern certificate exit 3.
Detected internal arithmetic failures exit 4. Command-line syntax errors are
reported by argparse and also exit 2, with an explanatory message on stderr.

The default ceilings are 65,536 resolution states, 200,000 total chain
generators, and 128,000,000 logical matrix bits. These are combinatorial
ceilings, **not** a wall-clock or process-memory guarantee. `--unlimited` removes
them; it can consume very large amounts of time and memory. `--no-filter` forces
homology computation even when the determinant already proves nontriviality.
`--check-d2` independently composes successive differential matrices to verify
`d^2 = 0`. Homological degrees in JSON are **unshifted**; absolute and quantum
gradings are not reported.

## Validation and guarantees

The delivered run passes **49 unittest test methods**, including hundreds of
parameterized cases: exhaustive 3-by-3 binary matrix ranks, exact determinant
comparisons, knot regressions, braid relations and cancellations, positive and
negative stabilizations, mirrors, basepoints, 24 seeded conjugated unknots,
spherical rotation systems, dual-graph cross-checks, certificate tampering, and
CLI error handling. See `results/unittest.txt` and `results/validation.json`.

These tests are not a formal verification of the code. No independent complete
Khovanov package was executed. Several expected ranks are regression fixtures;
the report distinguishes the mathematical correctness argument from the finite
test evidence.

For the explicit unknot family given by the closure of
`sigma_1 sigma_2 ... sigma_n` on `n+1` strands, the implementation enumerates
`2^n` resolutions with `3^n` total chain generators. Thus its exponential
behavior is explicit even on unknots with determinant 1. Fast timings on the
small examples do not establish the requested asymptotic bound.

## Documentation and remaining work

`docs/implementation_report.pdf` and its LaTeX source explain the algorithms,
correctness arguments, bit-complexity bounds, source audit, tests, and exact
remaining obligations. `docs/source_ledger.json` records the attachment and
primary outside sources. The user's 109-page slide deck is not redistributed.

The missing parts of a general quasi-polynomial implementation are the
compressed handle/hierarchy geometry, controlled hierarchical multi-surfaces,
compression and pullback updates, geometric Cheeger-region and weak-reduction
routines, and an end-to-end proof of the depth, restart, and bit-cost bounds.
They are **not** replaced by calls to the exponential reference recognizer.

All original code is MIT-licensed; see `LICENSE`. The mathematical results cited
in the report retain their original authorship.
