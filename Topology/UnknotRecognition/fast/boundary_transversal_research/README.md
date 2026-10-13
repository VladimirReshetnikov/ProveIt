# Boundary conflict-transversal counterexamples

This package refutes two proposed shortcuts for the positive root Q extreme-ray
conflict hypergraph. Neither boundary-face tetrahedra nor the union of all
boundary-edge stars is always a transversal, even for finite, connected,
orientable, one-vertex sources with torus boundary. It changes no native search
policy and makes no claim about a family with growing minimum transversal
number or general quasi-polynomial recognition.

From `Topology/UnknotRecognition/fast`, run the solver-free replay:

```sh
python -B -S -m boundary_transversal_research.replay --output /tmp/boundary-transversal-audit.json
python -B -S -m boundary_transversal_research.replay --check-evidence /tmp/boundary-transversal-audit.json --output /tmp/boundary-transversal-replay.json
python -B -S -m unittest boundary_transversal_research.test_replay
```

An optional fresh Regina construction reproduces the six retained layerings:

```sh
python -B -m boundary_transversal_research.generate --output /tmp/boundary-transversal-regeneration.json
```

The optional command requires Regina in that Python environment. The replay
does not import Regina, an LP implementation, a Q elimination implementation,
or another research package. It uses native manifold/source-incidence
validation, then computes all formal values and exact ranks from original
STANDARD matching equations. These are fixed correctness checks, not timings.
Run without Python's `-O` option because checks intentionally use assertions.
Store generated output outside this package.

The seven focused controls include rejection of noncanonical, nonprimitive,
nonintegral, and nonextreme matching vectors and a wrongly declared layering
edge. The nonextreme control is a canonical sum of two distinct retained rays,
so matching and canonicality alone cannot make it pass the extremality check.

## Retained data and pins

`data/lower_witnesses.json` is the byte-for-byte copy of the labelled endpoint
fixtures previously retained by `euler_transversal_research`.
`data/provenance/layer-refuter.json` retains every full source, coordinate
vector, local edge choice and intermediate gluing from the original discovery.
Its `source_sha256` map is a historical generation snapshot, not a statement
that current native files still have those hashes. The other files in
`data/provenance/` archive the original scratch scripts and outputs verbatim;
their absolute scratch paths are historical, and they are not the runnable
package interface. `data/provenance.json` binds all original inputs and scripts
by SHA256. The historical generation map additionally authenticates the exact
original endpoint fixture bytes.

Each new replay/regeneration pins every native Python file and all Python,
JSON, Markdown and text inputs in this package at both ends. A replayed saved
audit must equal the fresh result, including the current pins. This separates
fresh checking from retained, nonexhaustive root-ray discovery. No claim of
fresh or complete enumeration of root extreme rays is made.

## Exact evidence

The original trefoil endpoint has 10 tetrahedra, boundary faces `(6,0),(9,0)`,
and eight retained positive root Q rays that all avoid tetrahedra `{6,9}` in
their conflict sets. The 13-tetrahedron figure-eight endpoint has boundary
faces `(7,0),(9,0)`; nine of its eleven retained rays similarly avoid `{7,9}`.
Every one of these 19 rays is freshly checked.

One boundary layering on the trefoil endpoint gives the smallest retained
edge-star refuter. The resulting 11-tetrahedron source has canonical formal
Euler value 1, complete conflict set `{0,5}`, and boundary-edge tetrahedron
union `{2,3,6,9,10}`. Its Q support has size 10. Retaining all 44 triangle
columns and these 10 Q columns in original STANDARD matching gives rank 52;
the triangle-only block has rank 43. Thus the projected supported Q space has
dimension `54 - 52 - (44 - 43) = 1`, proving genuine root-ray extremality.
The replay explicitly checks first-step disjointness, every coordinate and
gluing, and this rank calculation.

The full controls add three layers to each endpoint. Their final sizes are
13 and 16 tetrahedra; their boundary-edge unions are respectively
`{10,11,12}` and `{13,14,15}`. All original conflict tetrahedra lie outside
those sets. Each extension leaves every original coordinate unchanged,
introduces at most one Q type in its new tetrahedron, and preserves canonical
formal Euler, the complete conflict set, and Q extremality.

## Topological and mathematical scope

The checker validates finite orientable connected sources with a single torus
boundary and one vertex. A layering attaches two faces of the new tetrahedron
to the two distinct old boundary triangles, consistently along their common
edge; other old pairings stay unchanged. The checker verifies that no old
edge classes merge and precisely the chosen boundary edge is replaced.

Jaco–Rubinstein, *Layered-triangulations of 3-manifolds*,
[§3, printed p.9, and Lemma 9.2, pp.85–86](https://arxiv.org/pdf/math/0603601v2),
identify this operation with a boundary diagonal flip preserving the compact
manifold. Their definition explicitly permits identifications between sides
of the boundary quadrilateral; an embedded attaching disk must not be assumed.
This collar theorem supplies the homeomorphism inference. A Regina validity
flag alone would not supply it.

The new layers are **not operations in the maintained crushing-chain schema**.
They are supplied-source counterexamples with checked collar maps, not claims
that a current diagram run emitted these authenticated successors. Original
endpoint labels match the retained previous diagram-bound evidence; this
package does not rerun diagram discovery or the earlier recognition chain.
Nor does it infer negativity of the admissible canonical cone from knot type.
The vectors are incompatible formal matching vectors, not embedded normal
surfaces; direct Q extremality makes a negative-cone premise unnecessary.

The companion article is `../../synthesis/boundary_transversal.tex`. The open
structural task remains a uniform resolving-set theorem under justified
additional hypotheses, or an actual growing-transversal counterfamily.
