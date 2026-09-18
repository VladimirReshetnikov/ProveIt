# Exact unknot recognition and the quasipolynomial implementation gap

**Status: the requested `n^O(log n)` implementation was not completed.**
This archive contains a working, terminating exact recognizer for single-component
rectangular/grid diagrams, with a worst-case upper bound `2^O(g log g)` in grid
size `g`. It also contains implemented polynomial components relevant to the
attached Lackenby notes. These components are **not connected by a completed
quasipolynomial hierarchy engine**. No missing geometric operation is disguised
as an oracle, and the exact recognizer contains no unimplemented branches.

Read `docs/report.pdf` (source: `docs/report.tex`) for the algorithms, correctness
arguments, precise complexity distinction, and remaining proof/implementation
obligations. `docs/STATUS.md` maps the code to the requested method.

## Run immediately

Python **3.9 or newer**; no third-party runtime or test dependencies. Run from the
extracted project directory. Execution was tested with Python 3.13.5 on Linux;
Python 3.9 grammar compatibility was checked, not execution on every version/OS.
Installation with pip is optional, not necessary for these commands.

```console
python -m unknot recognize examples/scrambled_unknot.json --certificate proof.json
python -m unknot verify proof.json --input examples/scrambled_unknot.json
python -m unknot show examples/scrambled_unknot.json
```

To exercise complete search rather than just the determinant filter:

```console
python -m unknot recognize examples/trefoil.json --no-determinant
python -m unknot recognize examples/determinant_one_knot.json --no-determinant
python -m unknot recognize examples/scrambled_determinant_one_knot.json --no-determinant
```

The determinant-one example is nontrivial. A determinant of one never triggers an
UNKNOT answer.

## Input format

The two marked column indices in each row, with rows ordered bottom to top:

```json
{"rows": [[0, 2], [1, 3], [2, 4], [0, 3], [1, 4]]}
```

Equivalently, give the X and O column positions in each row:

```json
{"x": [0, 1, 2, 3, 4], "o": [2, 3, 4, 0, 1]}
```

All indices are zero-based. Each row and each column must have exactly two
corners. Vertical segments pass **over** horizontal segments at crossings.
There must be exactly one link component. Every knot admits a rectangular
presentation, but this package does not convert arbitrary PD/DT codes, pictures,
or polygonal embeddings into this format. X/O orientation is not retained.

## Answers and resource limits

`UNKNOT` is accompanied by a legal monotone move path to the 2-by-2 rectangle.
`KNOTTED` is accompanied either by a non-unit exact determinant or by a finite
set closed under all non-increasing moves and containing no trivial diagram.
Certificates of the second kind can be exponentially large.

There is no default search limit. For controlled experiments:

```console
python -m unknot recognize examples/scrambled_unknot.json --max-states 1000 --timeout 10
python -m unknot recognize examples/scrambled_unknot.json --max-states 1 --no-determinant
```

A reached limit returns **UNKNOWN**, not KNOTTED. The second command intentionally
returns UNKNOWN. `--max-states` limits retained states, not bytes. `--timeout` is a
soft wall-time limit checked between operations; it does not interrupt a large
matrix operation or successor generation already in progress. A killed process
or exhausted memory does not supply a mathematical conclusion.

Exit codes: `0` for either conclusive answer, `2` for UNKNOWN, `1` for invalid
input/verification or an ordinary I/O error, and `130` for interruption. The JSON
verdict distinguishes the two conclusive answers. Use `--no-certificate` to omit
potentially large certificate data. `--output result.json` saves the full result;
`--certificate proof.json` additionally saves just the certificate. If UNKNOWN
is returned, no certificate is written and an existing certificate file is left
unchanged, with a warning on stderr.

The verifier does not call the recognizer. It independently enumerates candidate
moves and computes cyclic-shift representatives by exhaustive comparison, rather
than using the search's optimized enumerator and Booth canonicalizer. It still
shares the elementary move checker and determinant implementation. This is
replayable verification, not a Lean proof or a formally verified kernel.

## Polynomial components from the hierarchy approach

```console
python -m unknot pattern examples/pattern_theta.json
python -m unknot pattern examples/pattern_triangular_prism.json
python -m unknot normal examples/solid_torus.json
```

`pattern` checks a cubic spherical rotation system on the boundary of an
**already known 3-ball**. It does not recognize the ambient manifold as a ball.
Darts `2e` and `2e+1` form edge `e`; each vertex lists three darts in cyclic order.
Vertex-free circles are represented by a separate integer count.

`normal` accepts a simplicial tetrahedral complex with globally named vertices.
Without a supplied cocycle it computes a rational H^1 basis, represented by
integer cocycles, and converts the first class into compressed normal coordinates.
With an explicit `"cocycle": [[u,v,value], ...]`, it uses that cocycle instead.
Absent edge values are zero. This is not a face-pairing triangulation format.
The seven entries per tetrahedron are `T0,T1,T2,T3,Q01|23,Q02|13,Q03|12`.
The output does not certify manifoldness, extract a connected component, or cut
the manifold. A zero-dimensional H^1 produces the zero coordinate vector.

`unknot.potential.HierarchyPotential` implements the conditional base-(G+1)
complexity arithmetic. Supplying small G and L does not establish geometric
bounds or create a quasipolynomial recognizer.

## Reproduce validation

```console
python -m unittest discover -s tests -v
python -m tools.validate_exhaustive --max-size 6 --output docs/exhaustive-results.json
python -m tools.benchmark
```

The bundled run passed **40 unit tests**. The exhaustive run covered all **44,719
connected unoriented labelled grids of sizes 2 through 6**, using **1,285 cyclic-
shift orbits**. One representative per orbit was decided without the determinant
shortcut and every resulting certificate was verified. The benchmark also
includes nontrivial determinant-one examples. See the machine-readable reports
and `docs/test-output.txt`. These observations are not a complexity proof.

The fixture scrambler uses stabilizations only to manufacture test inputs; the
recognizer never increases grid size. Scrambling seeds are in
`examples/provenance.json`.

## Files

- `unknot/`: recognizer, verifier, exact determinant, cohomology, normal
  coordinates, spherical patterns, and conditional potential arithmetic.
- `tests/` and `tools/`: standard-library tests, exhaustive validation, fixture
  generation, and benchmark reproduction.
- `examples/`: input diagrams, spherical patterns, a solid torus, and saved
  certificates.
- `docs/`: technical report in PDF/LaTeX, source references, status audit, and
  actual test/experiment results.

All original code and documentation are supplied under MIT-0. Referenced papers
are credited in the report and are not redistributed in this archive.
