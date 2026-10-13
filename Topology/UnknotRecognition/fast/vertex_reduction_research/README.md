# Expanded-edge vertex reduction audit

Run from `fast/` with Regina available:

```sh
python -B -m vertex_reduction_research.audit --output ../synthesis/data/vertex-reduction-audit.json
```

The audit reconstructs fresh labelled solid-torus triangulations using boundary
caps, interior subdivisions, Pachner moves and deterministic relabellings. It
also constructs the canonical circle, trefoil and figure-eight diagram
exteriors, checks the boundary shellings and follows every preprocessing crush.
Regina is an oracle for this research script and is absent from the native
recognition path.

For every multiple-vertex source, the audit independently checks the selected
edge's endpoint and boundary conditions, then compares the complete raw normal
coordinate vector with Regina's freshly computed `edge.linkingSurface()`.
Regina's own vertex identifications independently determine the canonical
peeling. Explicit surface components check that the raw and canonical vectors
consist of discs and spheres, including a non-vertex-link disc. The audit keeps
all labelled sources, vectors, components and removed link multiplicities.

The local coordinate bound is checked as `max coordinate <= 2` and `sum of
coordinates <= 4 * tetrahedra`. The fixed Pachner walk includes a control whose
expanded edge link has a double triangle coordinate and an actual vertex-link
sphere: its Euler characteristic drops from three to one during canonical
peeling. The audit records repeated occurrences of the selected global edge in
a local triangular face; counting distinct global edges would miss these
normalisation triggers.

Every extracted vector is checked against Regina's original standard matching
matrix for support rank, primitivity, positive Euler characteristic and
connectedness. Small selected sources additionally receive fresh complete
standard vertex-surface enumeration; the extracted vector must occur exactly
once. Each native crushing quotient is compared with Regina using the original
tetrahedron labels, gluings, component census and selected torus component.
Each entire diagram chain is replayed through the existing independent native
chain verifier. A terminal empty torus selection proves `UNKNOT`; a retained
one-vertex exterior is recorded as `REDUCED`, not a knottedness verdict.

The construction follows Burton and Ozlen, [Lemma 6 of arXiv:1211.1079](https://arxiv.org/pdf/1211.1079).
Its topology-preservation and completeness premises are those of a classical
knot exterior. Native source validation alone does not establish knot-exterior
provenance. The supplied solid-torus fixtures have separate construction
provenance; the diagram chains authenticate their own sources. Regina describes
the expanding normalisation semantics in its [edge-link documentation](https://regina-normal.github.io/7.1/engine-docs/classregina_1_1Face_3_013_00_011_01_4.html).

This preprocessing uses polynomial work and strictly decreases tetrahedron
count at every crush. The audit supports no general quasi-polynomial recognition
claim: quadrilateral-sector coverage and the exact simplex pivot bound remain
separate obligations. Historical evidence files are retained unchanged.

After all source edits and tests finish, run the timing experiments with other
CPU-intensive jobs stopped, then replay the saved evidence:

```sh
python -B -m vertex_reduction_research.benchmark --output ../synthesis/data/vertex-reduction-benchmark.json
python -B -m vertex_reduction_research.probe --output ../synthesis/data/vertex-reduction-probe.json
python -B -m vertex_reduction_research.check_evidence
```

The five-arm benchmark measures complete circle and negative-curl recognition:
adaptive disc search, the preceding fair Q and LP drivers loaded from pinned
commit `c7ebc2073`, and Q and LP with vertex preprocessing. Shared dependencies
use the current pinned sources. Nine randomized paired repetitions each batch
three whole queries; three adaptive A/A pairs measure repeat variation. Every
timed serialized result must match a separately replayed warm-up result.

The four-arm trefoil probe uses the same shared sector cap and separate Q/LP
resource limits before and after preprocessing. These single bounded profiles
record partial progress, not complete-recognition runtime. Independent replay
checks every returned chain; cancellation or inconclusiveness proves no knot
verdict. Source hashes cover native code, runners, and imported fixture code.

The checker replays saved source-bound crushing certificates and chains,
compares retained oracle records, recomputes counts and timing arithmetic, and
generates the article table. It does not rerun Regina discovery. After rebuilding
the article PDF, run `check_evidence --publication` to record the final source,
test, evidence and PDF digests.
