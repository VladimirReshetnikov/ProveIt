# Independent proof review: bounded-up Pachner search by local commitments

## Reviewed setting

Use the repository's generalized face-paired triangulations and the exact
`pachner_23` and `pachner_32` formal bipyramid replacements. These are relative
to the six formal boundary facets and permit global vertex identifications.
The 2-3 support contains two distinct tetrahedra; the 3-2 support is the full
degree-three star of an edge, containing three distinct tetrahedra and the
required consistent bipyramid labels.

This is important. If one instead imposes strict simplicial-complex legality,
such as forbidding an already-existing new edge with the same endpoints, two
tetra-disjoint replacements can interact through global vertex coincidences.
The theorem below does not silently include such extra global tests.

## Commutation lemma

Two legal replacements whose consumed tetrahedron sets are disjoint remain
legal after either is performed, and their composites are isomorphic by a
map that is the identity on all unchanged tetrahedra and on the formal
boundary. This holds even if support boundary facets are paired together.

Proof: remove both formal interiors, insert both new fillings, and retain
all original boundary-pairing maps. Either sequential order produces exactly
this simultaneous quotient. For a 3-2 move, its central edge has all its
occurrences in its three support tetrahedra, so a replacement with disjoint
support cannot alter its star. For a 2-3 move, its paired internal face and
both incident tetrahedra survive an outside replacement. The formal local
legality checks consequently remain true. The natural isomorphism records
the change in global tetrahedron numbering and, if local conventions differ,
the induced vertex permutations.

If a simplicial integral 1-cocycle is transported by leaving boundary values
unchanged and assigning a new diagonal by the two-edge path formula, the
same diagram commutes for the cocycle: each local extension is uniquely
determined by the unchanged boundary data. Thus final normal level-set
surfaces correspond under the endpoint isomorphism.

## Commitments and deterministic execution

A tetrahedron *incarnation* is born initially or as an output tetrahedron of
a replacement, and dies when consumed by a replacement. Exterior face
pairing changes do not create a new incarnation.

Assign each incarnation one symbol from an alphabet of eleven possibilities:

- idle;
- one of its six local edges (commitment to a 3-2 move);
- one of its four local faces (commitment to a 2-3 move).

A move is ready when it is legal and every tetrahedron in its support is
committed to its relevant local copy of the central edge or shared face.
All ready moves have disjoint supports: a tetrahedron has a single selected
port, and that local port identifies at most one such move. Execute ready
moves in any fixed deterministic order, giving fresh commitments to output
tetrahedra. Do not execute a 2-3 move after the total upward budget U is used.
Stop when no allowed ready move remains.

The deterministic order should be fixed from fully specified states. Exact
raw label equality between independent executions is unnecessary, but every
producer must transport surviving commitments alongside the survivor map.

## Completeness lemma (the substantive point)

Fix any finite target trace. Label each incarnation in that trace by the
local port through which it is eventually consumed; label all final
survivors idle. Any ready committed move at the current state is the first
future target move that touches its support.

To prove this, consider that first future touching move. A surviving local
face or edge retains its label until its tetrahedron is consumed. For a
2-3 support, the internal paired face remains unchanged until one support
tetrahedron is consumed. For a 3-2 support, the entire star of the committed
edge lies inside the support and cannot be changed without consuming a
support tetrahedron. The future touching move must use the selected local
port and therefore is precisely the presently ready move. All preceding
target moves have disjoint support and can be commuted past it.

Move this ready event to the beginning of the remaining target trace and
iterate. The tetrahedron and vertex relabellings from each commutation
transport all future commitments. The resulting deterministic execution
has the same endpoint up to the explicit induced isomorphism. It uses the
same numbers of upward and downward moves. Final idle commitments prevent
an unwanted extension past the chosen endpoint.

In particular, this proof does not assert confluence of unrestricted 3-2
reduction, and it covers every intermediate endpoint of arbitrary target
traces by regarding that prefix as the chosen complete target trace.

## Exact counting theorem

Begin with n tetrahedra and allow at most U total 2-3 moves. If a trace uses
u upward and d downward moves, then

    d <= n + u,   and   n + 3u + 2d <= 3n + 5U.

The second expression counts all tetrahedron incarnations. Enumerate all
eleven-symbol words of fixed length N = 3n + 5U; let a deterministic executor
consume these symbols in birth order, ignoring an unused suffix. Every
target endpoint appears among these executions. Hence at most 11^N words
are sufficient. One can instead enumerate the adaptive prefix tree, whose
number of nodes is bounded by (11^(N+1)-1)/10.

For purely downward traces the alphabet has seven symbols and at most 3n
incarnations, yielding at most 7^(3n) padded words.

Move execution and independent certificate replay are polynomial per word.
If the initial cocycle has maximum coordinate bit length B, a new diagonal
is a sum of two existing coordinates, and only 2-3 moves create a new edge.
Consequently all coordinate bit lengths are at most B+U+O(1). Each run has
at most n+2U moves. Include the endpoint oracle cost explicitly; do not call
it polynomial unless its own theorem establishes this. For any
isomorphism-invariant polynomial endpoint oracle the total running time is
2^O(n+U) poly(n+U+B). If an oracle is exponential in n+U it can still be
included in the singly exponential bound, with a different constant.

This improves the naive move-string upper bound
(O(n+U))^(n+2U) to a singly exponential bound. It is not a new globally
quasi-polynomial unknot-recognition theorem, and classical normal-surface
recognition already has exponential algorithms.

## Initial-footprint strengthening

Suppose only r initial tetrahedra are ever consumed. All other initial
tetrahedra are idle. Since at least n-r tetrahedra survive, d <= r+u. The
number of nontrivial initial/output incarnations is at most 3r+5U.
Enumerating the active initial subset and its commitments gives

    sum_{i=0}^r binom(n,i) 11^(3i+5U)

executions, times polynomial overhead in the entire input.

If the active initial set is connected in the initial face-adjacency graph,
the subset count is at most n*16^(r-1): choose a root and encode a
deterministic spanning-tree depth-first walk of length 2(r-1); the graph
has degree at most four. For at most c active components, an intentionally
coarse bound is n^c * 32^r. Hence the connected-footprint version takes
n * C^(r+U) poly(n+B+U), and the c-component version takes
n^c C^(r+U) poly(n+B+U), for an absolute constant C.

These bounds give quasi-polynomial *parameterized reachability*, for example
when c=O(log n) and r+U=O(log^2 n). No assertion has been proved that all
unknot inputs admit successful traces with such parameters.

One can implement this restricted search by tagging all initially selected
tetrahedra active and all other tetrahedra idle, permitting output
incarnations to be active. No dynamic geometric claim beyond support
preservation is needed to obtain the stated completeness within the
promised footprint.

## Adversarial checks and implementation caveats

1. Budget U counts total 2-3 moves. It is not excess height and is not the
   number of upward bursts. Reordering independent mixed-sign moves can
   change burst structure and maximum height.
2. Every participating tetrahedron must agree with the move, not merely
   one chosen root tetrahedron.
3. Symbols attach to local vertex indices of tetrahedron incarnations,
   never to ephemeral global edge indices.
4. Commitment transport is part of state transport; copy all surviving
   symbols with the exact survivor map, then append output symbols.
5. If endpoint deduplication is used, it must retain the transported marking
   or cocycle and budgets as needed. Unmarked manifold isomorphism alone can
   discard relevant marked states.
6. A heuristic endpoint oracle whose behavior depends on labelling may
   not inherit endpoint coverage. Use an invariant exact predicate or
   transport an actual normal-surface witness.
7. Reject/timeout/unknown is not a proof of knottedness. Exhaustion only
   proves absence of a selected successful endpoint in the bounded family.
8. A commitment executor may be much slower than conventional search on
   small cases because its safe counting constant is large. Practical
   improvement needs measured lazy branching, compatibility propagation,
   or a hybrid portfolio; do not infer it from the asymptotic bound.

## Primary literature positioning

- Lackenby, *Incompressible surfaces, hierarchies and unknot recognition*,
  arXiv:2607.23350v1 (25 July 2026),
  https://arxiv.org/html/2607.23350v1 . The paper establishes a new hierarchy
  algorithm, with polynomial cocycle-surface construction (Theorem 6.2),
  backtracking bound L(g+1)^L (Proposition 9.1), linear hierarchy length
  after bundle refinement (Proposition 10.2), and compressed cutting
  (Theorem 14.4, referring to earlier work for the proof). It does not claim
  the complete quasi-polynomial recognition bound.
- Lackenby's March 2021 author handout,
  https://people.maths.ox.ac.uk/lackenby/quasipolynomial-talk-oxford-compressed.pdf ,
  states 2^O((log n)^3), using multi-surfaces and Cheeger regions. Be aware
  that Oxford's short announcement instead says n^(c log n).
- Burton, *Simplification paths in the Pachner graphs of closed orientable
  3-manifold triangulations*, arXiv:1110.6080,
  https://arxiv.org/pdf/1110.6080 , Section 4.1/Theorem 4.5 already uses
  interchange of adjacent 2-3/3-2 moves and classifies overlapping cases by
  octahedron, pillow, and prism flips. Do not claim first use of commutation.
- Burton and He, *Connecting 3-manifold triangulations with unimodal
  sequences of elementary moves*, arXiv:2012.02398v3 (14 April 2025),
  https://arxiv.org/abs/2012.02398 . This proves a 2-3 then 2-0 route between
  eligible one-vertex triangulations; it does not establish the small total
  upward budgets needed here.

Literature search found no matching local-incarnation commitment bound, but
this is a bounded search and not a proof of historical novelty.
