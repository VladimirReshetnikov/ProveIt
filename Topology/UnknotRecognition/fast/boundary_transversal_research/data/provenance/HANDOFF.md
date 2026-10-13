# Boundary-transversal shortcuts: exact counterexamples

Both proposed universal shortcuts are false for the stated class of finite,
orientable, connected, one-vertex torus-boundary sources. No asymptotic lower
bound on the minimum resolving number h is established here.

## Reproduce

From the repository's `Topology/UnknotRecognition/fast` directory:

```sh
PYTHONPATH=. python -B -S /tmp/boundary-transversal-design/probe.py
PYTHONPATH=. /tmp/unknot-regina-env/bin/python -B /tmp/boundary-transversal-design/layer_refuter.py
PYTHONPATH=. python -B -S /tmp/boundary-transversal-design/replay.py
```

Only the middle command uses Regina, to generate three layerings on each
source. The last command replays retained exact maps and coordinates without
Regina, LP discovery, or the Q-cycle elimination model. It checks current
native/research source hashes against the generation snapshot at both ends.
`replay.json` has `passed=true`; `replay.txt` records its output. Full sources,
coordinates, and every intermediate gluing are in `layer-refuter.json`.
The initial retained witnesses are in the maintained
`euler_transversal_research/data/lower_witnesses.json` fixture file.
All hashes below use SHA256 of sorted-key compact JSON, as in the native
source-bound research records.

## Boundary-face tetrahedra: refuted on existing authenticated endpoints

A finite one-vertex torus boundary has two triangles, so its boundary-face
tetrahedron set has size at most two. On fixture `trefoil` (10 tetrahedra),
source hash
`515b94f650b5a7b0e8e09322ba31f59eb8cdb108fe33d9220994c43f148ca3fd`,
the boundary faces are `(6,0)` and `(9,0)`. Retained witness index 0 has
positive canonical formal Euler 1, Q support size 10, support rank 9, and
complete conflict set `{0,5}`, disjoint from `{6,9}`. In fact all eight
retained positive Q-extreme witnesses avoid these boundary-face tetrahedra.

On fixture `figure_eight` (13 tetrahedra), source hash
`1d03c1400d5168f3f862ddbccaa7551650a95f12d850d563fd9de653f0864c38`,
the boundary faces are `(7,0)` and `(9,0)`. Witness index 0 has formal Euler
2, Q support size 11, support rank 10, and conflicts `{3,8,12}`, disjoint
from `{7,9}`. Nine of the eleven retained witnesses avoid the boundary-face
set. These are genuine primitive positive Q root extreme rays, not merely
positive nonextreme formal points.

The original endpoint boundary-edge-star unions are all ten trefoil
tetrahedra and eleven figure-eight tetrahedra (all except 1 and 5).
Those original observations alone did not refute edge-star coverage.

## Boundary-edge stars: one explicit 11-tetrahedron refuter

Start with the trefoil fixture and witness index 0 above. Add tetrahedron
10 by replacing the two original boundary records as follows:

```
old tet 6, face 0 -> tet 10, permutation [3,1,2,0]
old tet 9, face 0 -> tet 10, permutation [2,3,0,1]
new tet 10 faces:
  0: boundary
  1: boundary
  2: tet 9, permutation [2,3,0,1]
  3: tet 6, permutation [3,1,2,0]
```

Every other old face pairing is unchanged. This layers on the original
local edge `(tetrahedron=6, edge_index=4)`, with local edge order
`01,02,03,12,13,23`. Leave every old normal coordinate unchanged and append
`[2,2,10,10,0,0,0]` on the new tetrahedron.

The resulting exact source hash is
`f6a05037099e93211b93a865e6ebca666d033e91dc04d9cb17475544206d5daa`.
It is finite, valid, orientable, connected, and has one vertex and torus
boundary. Its boundary faces are `(10,0),(10,1)`, and **all** tetrahedra
incident to any boundary edge are `{2,3,6,9,10}`. The extended canonical
formal vector still has Euler 1 and conflicts `{0,5}`. Its Q support still
has size 10 and rank 9, so it remains a positive primitive root extreme
ray. Its conflicts avoid the entire boundary-edge-star union.

Direct original-STANDARD rank replay retains all 44 triangle columns plus
the ten supported Q columns. The matching rank is 52, so this linear space
has dimension two. Its triangle-only kernel is the single vertex-link
line; the projected Q support therefore has dimension one. This proves
extremality without invoking the producer's Q elimination or any LP solver.

## Three-layer controls moving the boundary completely into the collar

The full retained construction flips each of the three original boundary
edges once. Every original tetrahedron then avoids every new boundary edge.
The trefoil steps use original local edge representatives `(6,4),(9,4),(6,3)`;
the figure-eight steps use `(7,4),(7,5),(7,3)`.

- Trefoil final source: 13 tetrahedra, hash
  `b2239d8ec0255f7de1740df91f74311086b2ac633f6c8793d8df8cecdf1fbdc1`.
  Boundary faces `(12,0),(12,1)`; boundary-edge tetrahedra `{10,11,12}`.
  Formal Euler 1, conflicts `{0,5}`, Q support/rank `12/11`.
  Direct standard restricted ranks at the three steps are `52,57,62`.
- Figure-eight final source: 16 tetrahedra, hash
  `509f35acd88e69016f930afb7f5439acfc6783b7d57e28164e36635bd3d16ece`.
  Boundary faces `(15,0),(15,1)`; boundary-edge tetrahedra `{13,14,15}`.
  Formal Euler 2, conflicts `{3,8,12}`, Q support/rank `13/12`.
  Direct standard restricted ranks are `65,70,75`.

Each new tetrahedron uses at most one Q type. Every step preserves the old
coordinates, canonicality, positive formal Euler, and the complete conflict
set. The generator enumerates the small local nonnegative extensions for
these fixed controls; no polynomial complexity claim is made for that
integer-value enumeration. The replay checks the actual saved results.

## What the replay proves, and provenance limits

For every step the independent native geometry reconstruction validates the
finite oriented manifold, sphere/disc vertex links, and single torus boundary.
The replay additionally verifies the exact two-face attachment, reciprocal
maps, the shared attaching edge with consistent oriented ends, unchanged
other old pairings, absence of any identification between distinct old edge
classes, and replacement of exactly the chosen boundary edge by one new
boundary edge. Thus the saved maps meet the local boundary-layering pattern;
validity alone is not being substituted for a homeomorphism theorem.

The applicable topological source is Jaco--Rubinstein,
*Layered-triangulations of 3-manifolds*,
https://arxiv.org/pdf/math/0603601v2, Lemma 9.2, printed pp.85--86
(PDF pages 84--85). It explains boundary layerings as diagonal flips changing
a triangulation in a boundary neighborhood while retaining the same compact
manifold and its one-vertex boundary triangulation. The exact attachments
above therefore have the collar interpretation; they preserve the manifold
represented by the original knot-exterior source. This is a theorem-based
homeomorphism inference, not an inference from Regina's validity flag.

The **new layerings are not supported operations in the maintained
crushing-chain certificate schema**. Thus these are supplied-source
counterexamples with explicitly checked collar maps, not claims that the
current diagram driver emitted these sources as authenticated successors.
The original sources are the exact endpoints retained in the previous
transversal audit. The new sources need no unproved negative-cone premise:
the counterexamples already have directly checked Q extremality. Nothing
here claims that their admissible canonical positive cone is empty merely
because their knot type is nontrivial.

## Consequence for the Euler-basis route

The Luo--Tillmann standard-solution basis (the primary reference retained in
`euler_transversal.tex`, https://arxiv.org/pdf/math/0510537v2, Theorem 6,
Lemma 7, and the subsequent Euler calculation) is a linear basis, with signed
coefficients. It does not impose a positivity decomposition whose conflicts
must touch the boundary. Canonical triangle subtraction is global over the
single vertex class. The examples above preserve all incompatible Q support
and formal Euler while changing which tetrahedra touch boundary edges.
Consequently that basis cannot imply either refuted coverage statement under
only finite orientable one-vertex torus-boundary hypotheses.

Three boundary edges also do not mean a bounded number of incident
tetrahedra. Repeated boundary layerings can keep one fixed boundary edge:
choose a different edge to flip at each step. That edge remains in both
boundary triangles and occurs in every newly attached tetrahedron. Its star
then grows linearly with the number of layers. This is a star-size example,
not a lower bound on h. It also need not survive source simplification.

A boundary-based search theorem would require extra canonicalization or
collar-removal hypotheses and a new coverage proof. Even then, a uniform
small h theorem remains separate. The present counterexamples refute the
unqualified boundary-face and boundary-edge-star shortcuts; they establish
neither a linear h family nor a general search lower bound.
