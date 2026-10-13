# Reproducible normal-ray crushing audit

This research package compares the maintained normal-ray producer and its independent
checker with Regina's exactly numbered crushing quotient. Regina discovers fixtures and
serves as an external oracle. It is not imported by the maintained producer, verifier or
diagram-bound chain checker.

From `fast/`, using an interpreter with Regina installed:

```sh
python -B -m normal_crushing_research.audit --output /tmp/normal-crushing-audit.json
```

The development interpreter is `/tmp/unknot-regina-env/bin/python` (Regina 7.4).
The output retains complete sources, coordinates, native packets, independent oracle
observations and source hashes. It checks eighteen distinct retained witnesses (nine
rejected disc witnesses, nine accepted discs), 175 additional connected positive
surfaces, a non-vertex normal sphere with an erased six-face cycle, and one-tetrahedron
meridian/vertex-link controls. The additional edge-link surfaces are classified by
Regina's exact full matching-matrix support rank; nonextreme or triangle-only inputs
must be rejected by the strict maintained primitive-ray API.

Two additional chains start with the canonical twenty-tetrahedron exterior of the
crossing-free knot diagram and independently replay fifteen native boundary shellings.
One supplied ray crushes the resulting five-tetrahedron source to a ball. A second
chain crushes it to a one-tetrahedron torus and then to the empty quotient. Their final
packets are checked by `verify_crushing_chain`, including original diagram provenance.
Ray discovery in this audit uses Regina; this does not bound native discovery time.

## Why the one-tetrahedron terminal is sound

The primary source is Burton and Ozlen, *A fast branching algorithm for unknot
recognition with experimental polynomial-time behaviour*, [v3, pp. 8–10](https://arxiv.org/pdf/1211.1079).
Observation 3 identifies the surviving tetrahedra; Observation 4 lists possible
topological effects for crushing normal spheres or discs in an orientable manifold.
Neither observation requires more than one tetrahedron. Lemma 5 imposes that condition
because it replaces disappearance of the torus by a one-tetrahedron solid torus while
claiming strict reduction. Our terminal directly certifies the unknot when the torus
disappears. The deduction applies at one tetrahedron as well: a nonzero quadrilateral
removes the sole tetrahedron, and a nontrivial knot exterior cannot disappear through
the listed sphere cuts, trivial-boundary disc cuts or deleted components.

This reasoning requires authenticated knot-exterior provenance. The geometric packet
on a supplied compact orientable torus-boundary manifold alone is not a knot verdict.
Primitive full-source extremality implies connectedness: component coordinate vectors
lie on the same support ray, and primitiveness forces their positive proportionality
factors to be integers. Additional coordinate-zero restrictions are faces; arbitrary
unrelated extra linear restrictions would not justify this argument. Quadrilateral
content supplies strict progress. Triangle-only vertex links must be rejected.

## Cutting and destructive flattening differ

The first diagram fixture is a connected disc with trivial boundary. Native unit-ray
and weighted-orbit disc methods both return zero essential discs, with independently
replayed packets. Regina independently reports `isCompressingDisc() == False`.
Literal `cutAlong()` returns a solid torus and a ball; `crush()` returns only a ball.
This is a flattening side effect allowed by Observation 4, not a disagreement in
boundary essentiality. The audit retains both oracle component classifications and
the native topology proofs. It must not equate crushing with only cutting along the
selected surface.

## Graph and component edge cases

Face paths can revisit a tetrahedron through different entry faces. The directed
state is `(tetrahedron, entry_face)`. Quad-only cycles disconnected from retained
faces are valid erased regions: the isolated-cycle sphere fixture exercises one.
A repeated reachable directed state is different and must be rejected.

Complete quotients may contain a torus plus a ball or a closed component, several
balls, or no tetrahedra. The independent generic census checks every quotient
component; the unique torus-boundary component is extracted and renumbered for the
successor. Source-authenticated chains can discard the other components by the
crushing theorem without separately recognizing spheres. These are unmarked
successors: no annuli, sutures, cochains or peripheral markings are transported.

Strict descent bounds the number of successive crushing steps. General
quasi-polynomial positive-Euler discovery and its parameter bounds on all successors
remain open.

## Equivalent positive-query timing

`python -B -m normal_crushing_research.benchmark --output PATH` compares four
uncapped policies on the canonical circle and a negative Reidemeister-I curl.
Each query includes fresh source construction, native shelling, source replay,
search, independent positive replay, and result serialization. The existing
adaptive native discovery policy is the principal baseline. A second baseline
disables its Q-corner and matching-support preludes and is explicitly labelled
a standard-enumeration ablation. Two new arms use the maintained crushing
recognizer with its default diversified order and with canonical order as an
ablation. All measured calls must finish with a checked `UNKNOT` verdict.

The runner retains nine randomized paired repetitions and three adaptive A/A
pairs by default. It must be run after concurrent computational work has stopped.
Its two small positive fixtures support no timing claim about negative queries,
large triangulations, or the asymptotic complexity of global discovery.

`python -B -m normal_crushing_research.probe PATH` separately retains bounded
trefoil exploration with both traversal orders and a one-candidate diversified
checkpoint. It independently replays returned partial chains. Candidate caps
and cooperative cancellation produce incomplete outcomes, not knot verdicts.

`python -B -m normal_crushing_research.check_evidence` replays saved geometric
packets, checks source pins and timing arithmetic, and regenerates the article
table. After rebuilding the article, add `--publication` to pin the final PDF,
article, source, tests and evidence. This checker needs no Regina installation.
