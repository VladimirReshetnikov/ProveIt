# Native core top reduction: audit and implementation report

Baseline inspected: ProveIt commit `8cb7d9d25ac8cb64a9d147304e3441e98e94c7a4`.

## Implemented files

- New `fast/fastunknot/core_top_reduction.py`: independent source endpoint packet, linear queue planner, relative reduction producer.
- New `fast/fastunknot/core_top_reduction_verify.py`: independently reconstructs endpoint orientations from every local source edge and replays an arbitrary valid rooted schedule.
- Modified `fast/fastunknot/normal_cut_handlebodies.py`: applies source top reduction when three-handles occur, then runs the existing terminal paths with a version-6 wrapper.
- Modified `fast/fastunknot/normal_cut_handlebodies_verify.py`: authenticates both ORIGINAL source proofs before applying the top-reduction trace and replaying the nested existing terminal proof.
- New `fast/tests/test_core_top_reduction.py`: nine tests, including independent Regina construction of a five-interior-vertex source, a saved real interior-loop source, all ten original diagnostic cases, malicious certificate mutations, source-rank forgeries, scale invariance, and verifier independence.

The public queue helper `rooted_top_plan(incidence, *, check=...)` returns `(moves, surviving_original_two_ids, stats)`. It can be benchmarked independently of source reconstruction. `source_core_top_incidence` returns an ordered record for every source two-handle, with its original ID, canonical source edge, extreme rank, and two endpoints. `None` denotes a boundary end. Duplicate endpoints are retained: `[v,v]` is a loop, not one contact.

## Top certificate and wrapper

The top certificate is:

```
{
  schema: 'normal-core-top-reduction-v1',
  input_sha256: <source+normal-coordinate fingerprint>,
  moves: [[original_two_id, original_three_id], ...],
  surviving_two_handles: [ascending original_two_ids]
}
```

The reduced geometry retains every field except `core.handles2` and `core.handles3`. The latter becomes empty. Surviving two-handles are copied and densely renumbered, with all attaching-cycle records otherwise unchanged. Original zero/one IDs, ports, polygons, affine rank maps, source data, and boundary words are untouched.

The whole-cut wrapper has strict fields:

```
{
  schema: 'normal-cut-handlebodies-v6',
  parallelity: <original authenticated certificate>,
  boundary: <original authenticated certificate>,
  top_reduction: <top certificate>,
  terminal: {schema: <one of versions 1 through 5>, core/kernel/absorption/...},
  census: <the usual census>
}
```

The terminal object cannot contain its own source proofs or census, and cannot recursively be version 6. No-three-handle sources follow the old code path and retain their old schemas. The original summary remains an authenticated SOURCE summary: its handle counts describe the original core, while its Euler characteristic remains valid after equal numbers of index-2 and index-3 deletions.

## Exact endpoint theorem

For an interior source edge with canonical oriented endpoints `(a,b)` and normal weight `w`, the exceptional core handles have the following cap incidences. Write `iota(v)` for its source vertex three-handle if `v` is interior, and for a boundary marker otherwise.

| Case | Exceptional rank | Two cap endpoints |
|---|---:|---|
| `w = 0` | `0` | `[iota(a), iota(b)]` |
| `w > 0` | `0` | `[iota(a), boundary]` |
| `w > 0` | `w` | `[boundary, iota(b)]` |

The positive-weight external end is on the new cut boundary. This is true for one-sided normal components as well: the metric cut has boundary on both local sides, regardless of whether the global normal surface has an orientable normal bundle. The source validator already checks that vertex links are spheres or disks and prohibits edge reversal, so repeated global vertices do not erase oriented edge ends.

The endpoint producer reads the canonical root representative. The verifier instead scans every local source edge, reverses local endpoints according to source orientation parity, and checks consistency across all occurrences. It reconstructs the full expected extreme-rank inventory before interpreting a trace. It imports neither the endpoint producer nor the queue.

## Relative cancellation proof

Let `h` be a current two-handle having exactly one remaining three-handle contact, counted with multiplicity, with three-handle `B`. Its other belt disk is on the current exterior boundary. The union `h union B`, glued along their common belt disk, is a three-ball. Its attaching region to the remaining handles is the union of the lateral attaching annulus of `h` and the complementary disk in the attaching sphere of `B`; this union is one disk. Erasing a ball attached along a boundary disk is a relative homeomorphism. Every other two-handle remains with the same lower attaching cycle. Its cap disks formerly belonging to `B` become exterior disks. This is exactly the update "remove vertex B from the live endpoint multiset".

For a marked interface, it is essential that the actual interface rectangles are disjoint from the cancellation support. Merely saying "ports have dimension 0 or 1" would not suffice for an arbitrary handle presentation: a three-handle attaching sphere can include zero/one-handle boundary patches. The required separation follows here from the authenticated source product-rank construction. Selected prism, face-strip, and edge-cap product regions use strict interior stack gaps; they avoid original source vertex neighborhoods and exceptional end-gap belt disks. Their interface rectangles can be rounded simultaneously away from the exceptional two/three-handle support. Thus the homeomorphism fixes the labelled port rectangles and their charts. An arbitrary algebraic presentation cannot provide this hypothesis.

Collapsing all exterior ends to the same graph root is only a scheduling convention; no boundary components are identified topologically. A move always has exactly one live cap, and hence never joins two exterior roots. Loops retain both contacts and cannot pass the single-contact check.

## Completeness for inherited source cuts

Every connected component of the graph of zero-weight edges on interior source vertices has an external contact. Otherwise every edge incident to that component would have weight zero and remain inside it: a positive-weight incident edge would itself provide a normal-cut boundary contact, and a zero-weight edge to a boundary vertex would provide an old-boundary contact. This would disconnect the full source one-skeleton from its nonempty boundary, contradicting source connectedness. The rooted queue therefore removes every source three-handle, for every valid normal vector.

The default queue and retained source row set depend only on which source edge weights vanish. Positive scaling preserves both the selected original two-handle IDs and the cancellation order. Parent work strengthens this observation using one fixed source primal forest: choose a parent edge for each interior source vertex, process vertices by source-tree depth, and specialize the parent edge to its unique zero-weight gap or to the positive-weight extreme adjacent to the child. A single source tree then gives valid traces for ALL normal vectors without support enumeration.

## Cost

The queue scans each edge once for initialization and visits each vertex-edge incidence at most once. There are at most two such incidences per exceptional two-handle, so `incidence_visits <= 2*H2`. The graph portion uses `O(H2+H3)` operations, including survivor output by a linear scan of dense original IDs. Source reconstruction and fingerprinting are separate polynomial operations on the tetrahedral input and binary normal coordinates. Verification scans all local source edges and then the supplied `H3` moves, and never expands normal multiplicity. The certificate adds `O(T log T)` bits for source IDs and moves, apart from the existing source fingerprint.

These are local reduction and verification bounds. They do not bound useful normal-surface discovery, admissible hierarchy length, or the complexity of subsequent arbitrary marked transport. They therefore do not establish a quasipolynomial unknot algorithm by themselves.

## Verification performed

1. Nine new tests passed (`test_core_top_reduction.py`, approximately 7.1 seconds in this environment).
2. Seven existing whole-cut tests passed (`test_normal_cut_handlebodies.py`, approximately 8.7 seconds), including a 16,384-bit multiplicity, hexadecimal integer codec, shared discovery budgets, and false-valued cancellation callbacks.
3. Thirty-four existing tests passed from `test_core_handlebody`, `test_core_primitive_annuli`, `test_bundle_boundary_kernel`, and `test_source_handle_reduction` (approximately 40.8 seconds).
4. After factoring out `rooted_top_plan`, the independent-verifier test and the five-interior-vertex/dependent-order test passed again. These are repeat checks, not additional distinct tests.

Thus 50 distinct targeted tests passed. No native source files beyond the two assigned integration files were modified by this agent.

The ten pre-existing `core-three-handle-probe` cases all now have complete source-certified top reductions. Seven have COMPLETE whole-cut handlebody censuses, each independently replayed. They exactly match the diagnostic's saved Regina census. The remaining three still return INCONCLUSIVE:

- `pilot/finite_figureEight_interior/0`: raw cancellation stalled;
- `interior_2_3/mixed`: raw ball cancellation obstruction;
- `finite_trefoil_interior/mixed`: raw cancellation stalled.

The seven successes exercise nested whole-cut certificate versions 1, 2 and 3. The generic wrapper also composes with versions 4 and 5 by the same authenticated-reduction branch; the full corpus audit owned by the parent provides additional coverage.

The real loop fixture is a valid five-tetrahedron solid torus obtained from the one-tetrahedron solid torus by one 1-4 move and a 2-3 move, with isomorphism signature `fLHPccdedehspga`. Its interior edge with representative 14 has two endpoints at the same interior vertex. A forged trace treating it as a singleton is rejected independently.

The multi-vertex test performs five successive 1-4 moves, always choosing a tetrahedron with as few boundary vertices as possible. It produces 16 tetrahedra and five interior vertices, including a vertex with no direct boundary edge. The valid trace certifies the unchanged solid-torus census; moving a genuinely dependent cancellation to the front is rejected. Regina independently confirms that the source remains a solid torus.
