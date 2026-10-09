# Certified marked order on compressed normal boundaries

This contribution implements the missing cyclic-order interface for finitely
many attachment occurrences on a supplied compressed normal boundary curve.
The default implementation also reduces the endpoint weight dimension from
`2*p + 1` to **four exact integer coordinates**. The reference `one_hot` mode
is retained for controlled comparisons. This is a normal-boundary subroutine,
not a complete quasi-polynomial unknot recognizer.

## Mathematical status and source

The underlying deletion-and-weighted-orbit method is established. Marc
Lackenby's *The efficient certification of knottedness and Thurston norm*,
Advances in Mathematics **387** (2021), 107796, Theorem 9.2 and its proof in
Section 9.4, computes the order of core attachment pieces around vertical
annuli using weighted Agol–Hass–Thurston orbit counting. The relevant paragraph
is on pages 75–76 of the [November 2020 manuscript](https://people.maths.ox.ac.uk/lackenby/knp13nov20.pdf).
Theorem 9.2 begins on pages 72–73. The present contribution does not claim a
new marked-circle ordering theorem or a new orbit algorithm.

The computational advance is a concrete, independently certified native
interface, exact intervening lengths and unmarked cycle multiplicities, and
the lossless four-coordinate endpoint encoding below. The encoding is an
elementary consequence of the validated degree-two condition. It is not a
probabilistic fingerprint and does not solve a general set-encoding problem.

## Input and output contract

```python
from fastunknot.marked_boundary import normal_marked_boundary_order
from fastunknot.marked_boundary_verify import verify_normal_marked_boundary_certificate

answer = normal_marked_boundary_order(
    triangulation, coordinates, marks, record_certificate=True)
assert answer['status'] == 'COMPLETE'
assert verify_normal_marked_boundary_certificate(
    triangulation, coordinates, marks, answer['certificate'])
```

The lower-level functions `marked_boundary_order` and
`verify_marked_boundary_certificate` accept `(size, pairings, marks, ...)`.
Native normal-boundary point indices are exactly those returned by
`normal_surface_geometry.normal_arc_pairings(..., boundary=True)`. The native
wrapper retains that module's manifold and normal-coordinate validation.

A mark is a distinct integer point. Its occurrence identifier is its position
in the caller's list. Repeated semantic labels, such as a core-handle name,
must not collapse different attachment occurrences. The caller can associate
arbitrary labels with those occurrence identifiers. Duplicate geometric
marked points are rejected: any order of two attachments at the very same
point requires additional geometric information not present in this input.

An edge occurrence is `(raw_pairing_index, original_domain_point)`, and one
of its two ports is `(raw_pairing_index, original_domain_point, side)`, where
side 0 is its domain endpoint and side 1 its image endpoint. This preserves
two distinct ports of a self-loop and parallel edges between the same points.
The pairing list is ordered and certificate-bound because its row indices
are part of the occurrence identity.

A complete output contains:

* `ports`: exact descriptors, sorted first by input mark occurrence;
* `connections`: pairs of port indices and the number of intervening unmarked
  vertices, including direct marked-to-marked edges with count zero;
* `cycles`: marked occurrence order, outgoing port order, gap lengths, and
  total original vertices on each component containing a mark;
* `unmarked_cycles`: untouched component lengths and their exact multiplicities;
* `component_count`: the total number of boundary components.

Every cycle starts at its smallest occurrence identifier by default. The two
directions are compared lexicographically by occurrence word, with outgoing
port words breaking ties for one or two marks. `start_half_edge=(row,x,side)`
fixes the start and direction of that particular component. Other components
remain canonical. No ambient orientation is inferred from an unoriented
curve graph. A gap with `L` unmarked vertices has exactly `L+1` original edges.

`max_cycles` is passed to AHT. An incomplete calculation has status
`INCONCLUSIVE` and supplies neither cyclic-order claims nor a certificate.
Cancellation callbacks propagate. Integers and explicitly hexadecimal integer
strings are supported by the surrounding binary certificate transport.

## Why the reconstruction is correct

### 1. Preserve the multigraph before taking any orbit relation

Each point `x` in the domain of a raw interval pairing contributes one edge
from `x` to its image. A loop has two endpoint incidences; distinct raw rows
can give parallel edges. The degree at a vertex is therefore the sum of the
indicator functions of every domain and every range interval, counting both.
The producer validates that sum is exactly two on every constant interval
between endpoint events. It does not expand any point.

A finite degree-two multigraph is a disjoint union of circles, allowing
one-vertex loops and two-vertex parallel-edge circles. Identity pairings and
duplicate reflection arrows may subsequently be removed by the orbit
algorithm without affecting connectivity, but their marked incidences have
already been recorded and remain part of the reconstruction.

### 2. Delete marks and retain each half-edge identity

For each pairing, remove the source indices of edges incident to a mark:
marked source points and inverse images of marked target points. Split at
these finitely many events. Delete the marked vertices themselves by the
order-preserving rank map

\[
  r(x)=x-\#\{m\in M:m<x\},\qquad x\notin M.
\]

Each retained subinterval has no marked point in either its source or its
range, so this map preserves its width and its translation or reflection
type. Direct marked-to-marked edges are retained separately as pairs of
ports. This includes a loop at one mark.

Every residual component is a path, possibly a single vertex, or an unmarked
circle. A residual path has exactly two deleted-edge incidences. Those are
two different **ports**, even if they attach to the same mark or the same
residual vertex. An unmarked circle has none.

### 3. Four exact moments recover the unique two ports

Number the `2p` ports by labels `1,...,2p`. At the residual endpoint adjacent
to port `h`, add the weight

\[
 (1,h,h^2,0).
\]

At every residual vertex add `(0,0,0,1)`. Weighted AHT gives, for each residual
component, a vector `(c,s,q,L)` and its multiplicity. The last coordinate is
the exact number of its original unmarked vertices.

The degree-two proof gives only two possibilities:

* `c=0`: require `s=q=0`; the component is an unmarked circle of length `L`.
* `c=2`: there are two distinct incident labels `a,b`, so
  `s=a+b`, `q=a²+b²`, and

\[
 D=2q-s^2=(a-b)^2,\qquad
 \{a,b\}=\left\{\frac{s-\sqrt D}{2},\frac{s+\sqrt D}{2}\right\}.
\]

The producer checks exact squareness, parity, distinctness, and the range
`1 <= a < b <= 2p`. A component with two labels must have multiplicity one,
because every port label was inserted exactly once. The checker independently
derives candidate roots and rechecks their range, sum, and sum of squares.
It then verifies that every port, including direct-edge ports, belongs to
exactly one reconstructed gap.

These moments are injective on unordered pairs. They are not injective on
arbitrary sets: `{1,5,6}` and `{2,3,7}` both have cardinality three, sum twelve,
and square sum sixty-two. Consequently, checking the raw degree-two condition
is part of soundness, not an optional performance precondition.

The reference `weight_encoding='one_hot'` instead uses a separate unit-vector
coordinate for every port and a final length coordinate. Both modes return
the same full occurrence solution and are tested against each other.

### 4. Reconstruct the marked cycles

At each mark, its two ports form one fixed-point-free involution. The direct
edges and residual paths form a second fixed-point-free involution on all
ports. Alternating these two involutions follows the original circle from
one marked occurrence to the next. The two directions of each circle give
the two candidate cyclic words. The canonicalization rule above therefore
recovers exactly the circular order up to rotation and reversal, or the
specified directed order when a start half-edge is supplied.

## Binary complexity

Let `N` be the represented vertex count, `k` the number of interval pairings,
and `p` the number of explicitly supplied marks. Let `B` bound input endpoint
bit lengths. The marked vertices have `2p` incidences altogether, so at most
`2p` distinct edge occurrences are removed. Splitting at these occurrences
creates at most `k+2p` residual pairings. There are at most `2p+1` initial
weight intervals. None of these bounds depends on expanding `N`.

The producer's degree sweep and marked cut use sorted endpoint operations,
rank queries, and exact integer isometries. The independent checker uses a
separate endpoint partition and at most `O(kp)` elementary mark/pairing
incidence checks. Both are polynomial in the explicit source size and `B`.

The retained weighted AHT implementation has polynomial orbit-trace length
in its pairing count and `log(N+1)`. The new default always transports four
coordinates. Port moments have `O(log(p+1))` bits, and accumulated vertex
lengths have `O(log(N+1))` bits. A conservative global bound is `c<=2p`,
`s<=sum(h)`, and `q<=sum(h²)` over `h=1,...,2p`; nonnegative transport cannot
exceed those initial total masses. Thus intermediate moment magnitudes still
need only `O(log(p+1))` bits. Exact square-root decoding is polynomial in that
bit length.

The one-hot reference needs `2p+1` coordinates. The four-moment reduction
therefore removes the growing vector dimension and the quadratic initial
one-hot storage, without changing the orbit trace or introducing collisions.
It does not remove all dependence on `p`: there are still `2p` explicit ports,
`O(k+p)` residual intervals, and a larger AHT trace as marks are added. At zero
or one mark the reference dimension is one or three, below four, so no
universal constant-factor timing improvement is asserted.

## Certificate independence

`marked_boundary_verify.py` does not import or call the marked-order producer.
It independently validates degree, reconstructs the retained intervals by
partitioning at marked points and their inverse images, constructs the
endpoint weights, and invokes the maintained independent weighted replay
checker. Only after full replay succeeds does it decode path endpoints and
reconstruct the finite quotient. The proof binds the original size, ordered
pairing rows, mark occurrence list, selected direction, weight encoding, and
complete output solution. Statistics are not part of its mathematical claim.

## Reproduction and test scope

From the `fast/` directory:

```bash
python -m pytest -q tests/test_marked_boundary.py
python -m marked_boundary_research.benchmark
```

The test module covers 500 seeded signed interval-exchange multigraphs,
100 further cases run in both exact encodings, literal edge-occurrence
walks, every directed marked port of an adversarial example, adjacent marks,
singleton residual paths, identity loops, reflection fixed points, parallel
edges, the empty graph, all-marked graphs, native layered solid tori and
boundary caps, compatible sphere/disc/Möbius mixtures, 20,000-bit normal
multiplicity, exact hexadecimal transport, forged proofs and output orders,
and budget/cancellation behavior. If Regina is installed, eighteen native
normal-surface boundary counts are also checked independently.
The native-verifier cancellation regression checks the first and last native
geometry polls and the first subsequent replay poll, preserving the exact
callback exception object even when its type is `NormalOrbitError`.

`benchmark.py` uses supplied native normal meridians in layered solid tori,
with optional genuine boundary caps and binary multiplicity. It measures
native geometry validation, the marked-order producer with certificates,
independent replay, and the full supplied-normal-boundary wrapper separately.
The capped literal baseline follows every native arc using exact half-edge
identities. It is run only on primitive curves with at most 200,000 vertices;
omitted large cases have no extrapolated literal timing. `measurements.json`
records medians of three runs, with one literal walk per capped case, and
contains matched one-hot/moment rows at 0, 1, 8, 32, and 128 marks on the same
64-tetrahedron native boundary. `measurements_one_hot_initial.json` retains
the initial pre-optimization experiment for audit, not as the controlled
comparison used for the final performance claim.

### Earlier broad experiment

The controlled 64-tetrahedron fixture has 89,891,140,425,706 represented
boundary vertices and four original interval pairings. The same point and
mark inputs were used for both encodings. Times below are milliseconds.

| Marks | Moment producer | One-hot producer | Moment replay | One-hot replay | Replay speedup |
|---:|---:|---:|---:|---:|---:|
| 8 | 7.094 | 11.613 | 9.579 | 17.712 | 1.85x |
| 32 | 44.277 | 79.173 | 98.024 | 250.140 | 2.55x |
| 128 | 467.167 | 689.534 | 1,207.835 | 15,449.461 | 12.79x |

At 128 marks both modes use the same 4,215-event AHT trace. Their serialized
certificates are 344,445 bytes (moments) and 507,862 bytes (one-hot). The
remaining trace therefore limits the total certificate-size improvement
even though the weight dimension falls from 257 to four.

For a 22-tetrahedron primitive meridian, 150,050 boundary vertices and eight
marks, the moment producer took 2.197 ms, independent replay 3.121 ms, and
the full native wrapper 3.007 ms. The exact literal arc walk took 149.076 ms.
The 67.85x comparison is against the producer alone; including its independent
replay gives 28.03x. Tiny curves favor literal walking: at 26 vertices it took
0.046 ms versus 0.825 ms for the producer; at 1,220 vertices it took 1.058 ms
versus 1.495 ms. These are measured controls, not extrapolated asymptotics.

For the native 24-tetrahedron vector multiplied by `2**20000`, the graph has
`392836 * 2**20000` vertices (20,019 bits), four original and eight residual
pairings, and eight marks. The moment producer took 8.614 ms, replay 12.421 ms,
and native wrapper 10.158 ms. The output has three marked components and
retains the remaining unmarked components with exact multiplicity, totaling
`2**20000` components. Its certificate is 755,802 bytes with 108 AHT events.

The JSON also contains 101 interleaved repetitions of zero- and one-mark
controls. On the 26-vertex input with no marks, moment replay was 0.07024 ms
versus one-hot replay 0.06827 ms, about 2.9% slower. At one mark it was
0.09115 ms versus 0.09023 ms. Other tiny controls were effectively neutral.
The dimension reduction is valuable when the number of marks grows; it is
not a universal speed improvement for small inputs.

Measurements were made in CPython 3.12.14 on Linux x86-64 in the shared
research environment. They support this supplied-boundary kernel comparison
and do not measure a complete knot-recognition pipeline.

The observations in `measurements.json` were recorded before the native
marked-verifier callback-preservation fix. Their numerical rows and small
controls are retained unchanged and explicitly labeled with that source
phase. The separate final-source comparison is produced by:

```bash
python -m marked_boundary_research.matched_final
```

That driver runs only the matched 64-tetrahedron cases with 8, 32, and 128
marks: three paired trials per case, alternating which encoding runs first.
It retains every producer/replay wall and CPU time, combined times, exact
output and trace comparisons, serialized sizes, replayable reference
certificates, and hashes of the measured source files. The earlier literal,
native-wrapper, and small-control observations are copied with their original
provenance rather than rerun or relabeled as final-source measurements.

### Final-source paired encoding comparison

`measurements_matched_final.json` contains three alternating paired trials
for each mark count. All eighteen observations independently replayed, all
six outputs and full AHT proofs for each case were exactly equal, and the
hashed implementation files were unchanged during measurement. The same
64-tetrahedron native boundary and marking rule were used as above.

| Marks | Moment producer (ms) | One-hot producer (ms) | Moment replay (ms) | One-hot replay (ms) | Replay speedup |
|---:|---:|---:|---:|---:|---:|
| 8 | 6.482 | 7.693 | 9.987 | 15.086 | 1.51x |
| 32 | 32.110 | 51.145 | 72.514 | 260.093 | 3.59x |
| 128 | 462.465 | 710.939 | 1,062.141 | 15,035.489 | 14.16x |

The medians of each observation's combined producer-plus-replay time are
16.590 versus 22.566 ms at eight marks, 104.482 versus 311.239 ms at 32 marks,
and 1,524.606 versus 15,718.037 ms at 128 marks. These give combined speedups
of 1.36x, 2.98x, and 10.31x respectively. A median of paired totals need not
equal the sum of the two separately reported medians.

The data retain each wall-clock and process-CPU time, exact output and trace
sizes, the raw source triangulation and coordinates, and one replayable
reference certificate per encoding per case. Certificate sizes and trace
event counts match the earlier experiment. The file records source SHA-256
hashes for the producer, checker, driver, fixtures, and transitive numerical
kernels. Earlier literal, native-wrapper, and small-input controls remain
explicitly attributed to their original pre-callback-fix source phase.

## Integration boundary and next research questions

The interface orders supplied occurrences on supplied normal boundary curves.
It does not discover the geometric core attachments, identify the horizontal
side `F1` or `F2`, locate gaps meeting the exterior boundary, transport these
labels through a hierarchy, or construct the hierarchy itself. Lackenby's
Theorem 9.2 requires those additional geometric data. A normal component
profile without cyclic-order information cannot replace this interface.

Priority next steps are:

1. Produce attachment occurrence marks and their side labels directly from
   certified parallelity-bundle/core data, preserving the raw port identities.
2. Transport marked attachment data through certified simplifications and
   avoid repeatedly rebuilding boundary graphs that are unchanged locally.
3. Develop bounded-incidence analogues: for an established bound `d`, the
   first `d` power sums determine an endpoint multiset through Newton
   identities, but exact integer factorization and multiplicity validation
   must be included; first two moments alone do not suffice for `d>=3`.
4. Reduce the remaining AHT trace and independent replay costs at large `p`,
   now that dense endpoint vectors are no longer the dominant extra cost.
5. Integrate this interface into an actual geometric hierarchy construction,
   and only then establish a complete complexity recurrence for recognition.
