# Unknot recognition: exact baseline and hierarchy components

**Status: partial implementation. The requested general `n^O(log n)` worst-case
algorithm has NOT been implemented or proved here.** The runnable general
recognizer is complete and exact in the unlimited-resource mathematical model,
but its complete backend has an **exponential `2^O(n)` bound**. It explicitly
constructs `2^n` resolutions when that backend is used. This archive must not be
presented as Lackenby's quasi-polynomial algorithm.

The work also implements three actual components motivated by the supplied
February 2021 notes: compressed cocycle-to-normal-surface conversion, essential
boundary-pattern testing on a **known 3-ball**, and bounded lexicographic
accounting. They are individually executable, not placeholder callbacks. They
are **not connected into a complete hierarchy construction**.

## Run without installing anything

Use Python **3.10 or newer**, from the extracted `unknot_implementation` folder.
Only the Python standard library is required.

```sh
python -m unknotlab examples/trefoil.json
python -m unknotlab examples/torus_3_5.json --check-d2
python -m unknotlab examples/conjugated_unknot.json --check-d2
python -m unittest discover -s tests -v
python benchmark.py
python hierarchy_demo.py
```

Normal results have `status` equal to `unknot` or `knotted` and exit code 0.
A user-selected resource limit or inconclusive `--fast-only` run returns
`unknown` and exit code 2. Invalid input returns `invalid-input` and exit code 3.
**Unknown is not a negative answer.** No resource limit is set by default; large
inputs can exhaust time or memory. This is a reference implementation, not a
large-knot production solver.

```sh
python -m unknotlab examples/torus_3_5.json --fast-only
# unknown: determinant 1 is inconclusive

python -m unknotlab examples/torus_3_5.json --max-states 256
# unknown: the complete backend would require 1024 resolutions

python -m unknotlab examples/figure_eight.json --force-homology --check-d2
# knotted, reduced F_2 homology rank 5
```

`--force-homology` bypasses the fast certificates. `--check-d2` additionally
composes differentials on every generator and verifies that the result is zero.
`--max-generators` limits the total number of reduced chain generators.

## Input conventions

A planar diagram uses counterclockwise crossing tuples `(a,b,c,d)`, with
**underpass a--c and overpass b--d**:

```json
{"pd": [[1,2,3,4], [4,3,5,6], [6,5,2,1]]}
```

Arc labels must be positive integers and each must occur exactly twice. The
parser checks the rotation system is spherical and the diagram has one link
component. It rejects virtual diagrams, malformed incidences, and links.
`{"pd": []}` denotes **one** crossing-free circle, not the empty link; additional
crossing-free components cannot be encoded in this format. Positive integer
labels are normalized; complexity in the crossing count assumes the usual
O(log n)-bit labels, and otherwise includes the raw input length.

Alternatively, supply the closure of a braid read from top to bottom:

```json
{"braid": {"strands": 3, "word": [1,-2,1,-2]}}
```

Generator `i > 0` crosses the strand at position `i` over position `i+1`.
A negative generator reverses that crossing. Indices are one-based. The closure
must have one component. An optional `description` field is ignored.

## What the complete recognizer actually computes

It first looks for a descending-diagram witness, a sufficient unknot certificate.
Then it computes the Fox determinant using fraction-free integer elimination;
a value different from 1 certifies nontriviality. A value of 1 proves nothing.
The remaining cases use the **full reduced Khovanov chain complex over F_2**,
not merely its Euler characteristic or the Jones polynomial. Exact bit-packed
Gaussian elimination computes the total homology rank, and the answer is
`unknot` precisely when that rank is 1.

The mathematical detector is Kronheimer--Mrowka's theorem, together with the
universal coefficient theorem. The implementation's homological/quantum grading
is explicitly **unnormalized**; it is not a normalized knot-polynomial API.
No floating-point arithmetic, external CAS, knot table lookup, or unimplemented
topological operation occurs in the general recognition path. The results do
not include a geometric spanning disk or a Reidemeister-move sequence.

See `docs/implementation_report.pdf` and its LaTeX source for the mathematical
specification, correctness argument, complexity calculation, and source audit.
The argument relies on established mathematical theorems; it is **not a Lean
formalization** or a mechanically checked proof of all Python code.

## Implemented hierarchy components

`unknotlab.normal.Triangulation` accepts reciprocal tetrahedron face pairings,
checks orientability, excludes reversed edge identifications, and checks finite
sphere/disk vertex links. It computes integral cocycles whose classes form a
basis over Q and turns a cocycle into a compressed `7*t` normal vector using
half-integral levels of local vertex heights. It checks normal matching and
quadrilateral equations and computes Euler characteristic without expanding
disks. It does not return a saturated integral cohomology basis, extract a
connected component, or establish a low-genus bound.

`unknotlab.pattern.BallPattern` takes a spherical trivalent rotation system,
possibly with isolated simple-circle components. It either establishes
essentiality **assuming the ambient manifold is a 3-ball**, or gives an explicit
short dual-cycle obstruction (or reports disconnection). It does not recognize
3-balls or transport disks through a hierarchy.

`unknotlab.potential.HierarchyBudget` evaluates the exact base-`g+1` potential,
checks strict first-changed-digit decreases, and calculates a **conditional**
operation count. Passing these arithmetic checks does not supply any missing
geometric construction or prove bounds on its size.

## Verification actually performed

The delivered version passed **64 unittest test methods**, with many exhaustive
and randomized subcases. Tests include an independently structured dense
Khovanov calculation for small diagrams; `d^2=0`; braid relation, conjugation,
cancellation and Markov stabilization checks; determinant-one positive and
negative recognition cases; all 10,395 dart matchings for four-vertex cubic
patterns, keeping the spherical ones; and independent graph-connectivity
checks of boundary-pattern results.

Fifteen example diagrams, with 0--10 crossings in the supplied presentations,
were tested both through the default path and through full homology with
`d^2=0` verification. Six braid/determinant pairs were independently obtained
from Wolfram `KnotData`; their raw data and regeneration expression are included.
The runtime itself does not use Wolfram. The stored timings are small-case
measurements, **not evidence of a quasi-polynomial bound**.

`results/tests.log`, `results/benchmark.json`, and `results/benchmark.log` contain
actual outputs. `benchmark.py` regenerates the latter two. The normal-surface
stress test represents `3*10^1000` disks using seven integer coordinates.

## The unresolved requested implementation

The supplied notes announce the target bound, but the implementation still
needs simultaneous bounded-complexity hierarchical multisurfaces, compressed
cutting and pattern-compression with history, Cheeger-region recognition and
Heegaard-splitting modification, weak reduction, and a proof that the entire
process has logarithmic hierarchy depth and bounded bit cost including restarts.
These operations are **not implemented in this archive**. No function name,
callback contract, empirical timing, or appeal to the announced theorem is
being substituted for them. `STATUS.json` records this distinction explicitly.

## Layout and license

The Python package is `unknotlab/`; `tests/` is self-contained;
`examples/manifest.json` documents the supplied diagrams; `docs/` contains the
report and references. Optional installation is supported by `pyproject.toml`,
but is unnecessary for the commands above. The original code is supplied under
the MIT license in `LICENSE`. The user's slides and third-party papers are not
redistributed in this archive.
