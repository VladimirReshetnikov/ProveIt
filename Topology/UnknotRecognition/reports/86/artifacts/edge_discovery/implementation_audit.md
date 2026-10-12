# Edge-weight defect implementation audit

The additive production module is
`Topology/UnknotRecognition/fast/fastunknot/normal_weight_defect.py`.
It changes no existing recognizer default, CLI option, or discovery schedule.
The public input is a supplied finite connected orientable triangulation
with exactly one torus boundary, one global vertex, and first Betti number one.
The existing manifold validator and exact primitive-cocycle producer enforce
these conditions. No diagram-to-triangulation correspondence is asserted.

## Implemented algorithms

`local_coordinates_from_weights` is the exact local edge-metric inverse.
It supports rational rays. The opposite sums are ordered as 01+23, 02+13,
03+12; the largest two must agree. Triangle coordinates are the minima of
the three corresponding face-corner arc counts. Scaling to a primitive
integral standard vector happens after all local reconstruction.

`build_weight_subspace`, `weight_subspace_rays`,
`enumerate_weight_subspace`, and `discover_in_weight_subspace` retain
the entire subspace W_F = span(b, unit_e for e in F), where b=|c|.
The coherent column is dropped exactly when its support lies in F.
Every standard vertex ray in W_F is recovered. Intersections can also be
extreme only after restriction to W_F, so emitted rays are not all claimed
to be unrestricted standard vertex rays. Every candidate's matching and
quadrilateral conditions are rechecked by the existing geometry module.

`weight_defect_search(max_defect=k)` enumerates all F of sizes 0 through k
and deduplicates all weight directions across spaces. `exact_size=True`
enumerates only size k; padding preserves the standard-vertex completeness
promise. The number of begun hyperplane intersections and the number of
entered subspaces have separate global caps. Exhaustion gives
`NO_VERTEX_DISC_UP_TO_EDGE_DEFECT`, explicitly limited to the specified
standard-vertex class. There is no independent exhaustion certificate.

`one_edge_defect_search` implements the sharper global sparse-row method
for k=1. It tests the coherent surface, constructs the global arrangement
once, and considers each nonzero row-edge incidence (L,e). It computes
delta=-L(b)/L_e and keeps positive even integers, as required for an actual
meridian with edge weights b+delta*unit_e. Every row involves at most four
global edges, so there are O(t) incidence attempts. If b is supported on
the exceptional edge, its entire ray was already tested as the coherent
surface. Otherwise a standard vertex meridian is an isolated point of the
affine slice and has such an active row with L_e nonzero.

Only tetrahedra incident to e are reconstructed for an offset candidate.
The Euler update is

    delta*(1 - f_e/2) + sum_t (new_normal_pieces_t - old_normal_pieces_t),

where f_e counts edge occurrences in one representative of each global
triangular face, including finite boundary faces. Positive candidates are
assembled as full binary normal vectors and checked again. This avoids
reconstructing all t tetrahedra for each rejected offset. The worst-case
number of local reconstructions is O(sum_e deg(e)^2); the code does not
claim universally linear total time. The general sparse matching bound
for k>1 is a theorem/proposed algorithm, not the optimized implementation.

Every successful public discovery call runs the existing native
compressing-disc observer and then its independent verifier. The returned
`certificate` is the existing `normal-disc-count-v1/v2` object and is
bound to both supplied triangulation and coordinate vector. All local
exhaustion statuses are inconclusive for global unknot recognition.

## New explicit result on the old coherent obstruction

The old eight-tetrahedron obstruction has a standard vertex meridian with
47 pieces and one exceptional interior edge, global root label 30. Its
weight changes from 1 to 5, giving cancellation multiplicity 2. The other
nine edge weights remain equal to b. The coherent surface has genus two,
and the intermediate delta=2 surface has genus one; delta=4 is the disc.
The three surfaces are connected, orientable, and have one boundary curve,
as independently checked by the native full surface-topology certificates.

This 47-piece meridian lies in the same allowed quadrilateral sector as
the original coherent vector. The old seeded Q-sector search already finds
it. It is therefore an escape from the coherent-height family and a new
parameterized discovery approach, not additional coverage over complete
seed-sector enumeration on this particular example.

The unrestricted search at k=1 uses 11 subspaces and 71 intersections before
finding the disc. The optimized global incidence method uses 39 begun bases
(the baseline plus 38 row-edge incidences), 6 distinct positive even offsets,
10 local tetrahedron reconstructions, and one positive native disc query.
Complete arrangement construction, without early stopping, gives:

| k | Subspaces | Intersections | Admissible rays | Standard rays | Disc vectors |
|---|---:|---:|---:|---:|---:|
| 0 | 1 | 1 | 1 | 1 | 0 |
| 1 | 11 | 73 | 2 | 2 | 1 |
| 2 | 56 | 5,634 | 5 | 5 | 2 |

The previously published 51-piece meridian, with exceptional edges 15 and
18, is recovered in the supplied three-dimensional subspace after all 105
two-hyperplane intersections are enumerated.

## Layered family and verification

The research driver appends boundary tetrahedra along the current smallest
boundary weight. Its face charts match the oriented shared edge with 01,
the attached faces with 012 and 013, and the new diagonal with 23. Each
transported height chart is checked to satisfy h0+h1=h2+h3. Coordinates are
extended by the coherent local vector and all face matching is rechecked.

For r layers the disc has F_(r+7)+34 pieces; the coherent surface has
F_(r+7)+28 pieces. Their Euler characteristics stay 1 and -3, respectively;
the only edge defect remains z_30=2. Native exact standard-extremality and
independent compressing-disc certificates pass at r=0,1,2,4,8,16,32.
The benchmark additionally verifies successful witnesses at r=64, where
the disc represents 308,061,521,170,163 normal pieces.

Regina 7.4 independently reconstructed 138 standard vertex surfaces across
eight triangulations with 1 through 8 tetrahedra. Twelve meridian vectors
satisfied the cocycle parity and lower-bound formula. Eleven supplied
subspace queries recovered the target standard vertex discs with defect
at most two; the optimized one-edge queries also passed whenever applicable.
Regina independently checked the layered family at r=0,1,2,4,8. Larger
surface-topology calls were intentionally omitted after consulting Regina's
installed documentation: isConnected/isOrientable explicitly expand normal
discs, isCompressingDisc may cut and retriangulate, and countBoundaries
expands boundary arcs. The native binary certificates remain fully checked
at the larger sizes. An initial unbounded external-family audit process
was terminated with exit code 137; its partial run is not counted as evidence.

## Clean paired benchmark

Seven measured rounds follow one excluded warm-up for each arm and fixture.
Arm order is shuffled by fixed RNG seed 261012084. Every positive discovery
time includes its own cocycle preparation, native observer, and internal
independent replay. A second fresh independent replay is timed separately.
The final retained timing run had no other heavy audit jobs from this task.

| Tetrahedra | Existing seeded Q-sector | All subspaces k=1 | Global one-edge | Supplied edge 30 |
|---:|---:|---:|---:|---:|
| 8 | 0.003947 s | 0.022281 s | 0.002839 s | 0.004663 s |
| 16 | 0.023683 s | 0.038538 s | 0.005050 s | 0.008571 s |
| 40 | 0.354871 s | 0.087642 s | 0.012730 s | 0.020739 s |
| 72 | 2.114322 s | 0.164222 s | 0.023326 s | 0.044324 s |

All four positive arms return exactly the same coordinate vector on every
fixture. The old sector matching nullity stays three while the number of
kernel variables increases from 16 to 208; the growth in old algebra/setup
cost is not attributed to increasing nullity. This is one structured family,
not a corpus-wide speedup or an asymptotic complexity proof.

## Retained artifacts

- `benchmark.json`: raw samples, fresh replay timings, counters, and witnesses.
- `regina-audit.json`: random-source reconstruction checks and full native
  layered-family sources, coordinates, construction records, and certificates.
- `enumeration.json`: complete k=0,1,2 arrangement counts and disc vectors.
- `cone-audit.json`: independent full topology certificates at delta=0,2,4.
- `first-witness.json`: the new 47-piece disc and native count certificate.

The standalone reproduction commands are exposed by
`python -m normal_orbit_research.weight_defect MODE --output PATH`, with
MODE `family`, `enumeration`, `benchmark`, `regina`, or `all`.
The production module has thirteen targeted unit tests in
`tests/test_normal_weight_defect.py`, covering rational reconstruction,
large binary coordinates, support degeneration, old and new explicit discs,
caps, caller cancellation, immutability, and producer-independent replay.
