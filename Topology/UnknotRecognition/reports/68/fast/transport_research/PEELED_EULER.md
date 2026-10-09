# Exact vertex-link-peeled scoring after a 3--2 move

**Status:** proved algorithmic lemma; not implemented or benchmarked here.
Whether its ordering improves disc discovery is an open empirical question.

## Setting and assumptions

Let `T` be a validated finite triangulation of a compact orientable
3-manifold, with manifold vertex links. In the current implementation its
boundary is one torus. Let `x` be an admissible integral normal vector.
For the proposed application, `x` is the coherent fibre of the supplied
global integral cocycle.

Consider all currently legal 3--2 moves. Each must satisfy the repository's
formal-bipyramid contract: three distinct tetrahedra, an interior degree-three
edge, consistent formal labels, and a valid relative-boundary replacement.
Global identifications among formal boundary vertices are allowed.

Every candidate's replacement vector `x'` must be specified in constant
local data, with all unaffected normal coordinates unchanged. Coherent
cocycle reselection provides exactly this condition: the five formal
heights determine the two new tetrahedral rows. The claim does not apply
to a procedure that also re-extracts a global tree gauge or changes
coordinates in tetrahedra outside the candidate region.

A local corner has a stable record identity `(tetrahedron, local vertex)`
within the current scoring pass. Different records remain distinct even
when they belong to the same global vertex or have the same coordinate.

## Vertex-link peeling

For a global vertex `v`, let `C_v` be its collection of local corner
records. Write `a_c` for the triangle coordinate at corner `c`, and put

    m_v = min { a_c : c in C_v }.

Let `L_v` be its normal vertex-link vector: one triangle at each corner
in `C_v` and zero elsewhere. The vector

    peel(x) = x - sum_v m_v L_v

is nonnegative and satisfies the same normal matching and quadrilateral
constraints. It removes the maximal collection of vertex-link components.
The usual normal-position reconstruction gives the geometric disjoint
vertex-link interpretation; the Euler formula also follows directly from
linearity of the normal cell count.

Write `lambda_v = chi(L_v)`. It is 1 for a boundary vertex, whose link is
a disc, and 2 for an interior vertex, whose link is a sphere. Therefore

    chi(peel(x)) = chi(x) - sum_v lambda_v m_v.

This operation is only vertex-link peeling. In particular, it does **not**
include the subsequent quadrilateral-gcd division used by the repository's
full `canonical_disk_core` routine.

## Lemma: thirteen retained corner records suffice

For every global vertex `v`, retain the first

    min(13, |C_v|)

corner records in increasing order of `(triangle coordinate, corner ID)`.
Also retain `m_v` and whether `v` is a boundary or interior vertex. These
records can be built in O(N) integer comparisons and O(N) storage for an
N-tetrahedron triangulation, using heaps of fixed capacity thirteen.

For a candidate 3--2 move, let `R` be the set of its twelve deleted old
corners. For every affected global vertex, remove the records of `R` from
its retained list and let `s_v` be the smallest remaining value. Define
`s_v=+infinity` if the list becomes empty. If `R'_v` is the collection of
new corners representing `v`, then the new link minimum is exactly

    m'_v = min( s_v, min { a'_c : c in R'_v } ).

The formal replacement has only eight new corners and at most five
affected global vertex classes. Hence all new minima and the exact change
in peeled Euler characteristic are obtained with O(1) integer operations
per candidate after the shared preparation.

### Proof

At most twelve old corner records are deleted in the entire move.
If any old corner of a given global vertex survives, its earliest surviving
record in the sorted order lies among the first thirteen: otherwise the
first thirteen records would all have been deleted, which is impossible.
Consequently, the smallest retained surviving record equals the minimum
over *all* surviving old corners. If there is no survivor, the retained
list is empty, and infinity is the correct temporary value.

All global vertices of a legal formal bipyramid survive its relative-boundary
replacement. Their boundary/interior types are also unchanged. Thus if no
old corner of an affected vertex survives, at least one new corner supplies
a finite value. The old-to-new formal labels identify which global vertex
receives each new corner. This argument permits repeated global vertices;
the bound counts distinct local records, not distinct global labels.

The minimum over surviving old corners and new corners is exactly the
minimum over the new global vertex link. There are at most five affected
classes, each needing at most thirteen retained-record checks plus the
constant number of replacement coordinates. Unaffected classes have
unchanged minima. This proves the stated cost and reconstruction.

## Exact peeled-Euler score

Linearity and preservation of the vertex-link types give

    delta_chi_peeled
      = delta_chi_raw
        - sum_(affected v) lambda_v (m'_v - m_v).

For transported coherent fibres, `delta_chi_raw=2g` in the 3--2 direction,
where `g` is the proved five-height gap. All ingredients of the displayed
expression therefore have O(1)-per-candidate evaluation after the shared
O(N) preparation. If B bounds the source and replacement coordinate bit
lengths, the local arithmetic uses
O(B+log N) bit work, under the usual fixed-size count of comparisons and
additions. Native triangulation validation is an additional shared cost.

The explicit connectivity counterexample in `splitting.py` illustrates the
distinction: its raw Euler gain is four, but it creates two vertex-link
spheres. Their Euler contribution is four, so the peeled gain is zero.

## Optional piece-count corollary

Let `d_v=|C_v|` and let `d'_v` be its value after the move. It is updated
from the twelve deleted and eight inserted corner records. Since a single
vertex link contributes `d_v` normal pieces,

    delta_P_peeled
      = delta_P_raw - sum_(affected v) (m'_v d'_v - m_v d_v).

This also takes O(1) integer operations per candidate. Its bit cost includes
multiplication of a coordinate by an O(log N)-bit corner count. For coherent 3--2 transport without global regauging, it is nonpositive.
The article proves this using nondecrease of global link minima, the two
apical corner-count losses, and the exact five-height piece formula.
This stronger sign conclusion does not extend the claim to arbitrary
locally rewritten normal vectors, and implies no peeled-Euler monotonicity.

## Limits and implementation obligations

The lemma concerns **one scoring pass on one fixed triangulation and
normal vector**. After committing a move, the thirteen-record summaries
must be rebuilt in O(N) time or maintained by a separately justified
dynamic ordered data structure. Deleting entries from the short lists
without replenishing them is invalid: a later move may need records that
were originally beyond rank thirteen.

The score does not remove non-vertex-link spheres or inessential discs,
classify essential components, or account for quadrilateral-gcd scaling.
It does not prove that the highest score leads to a disc, improves the
measured source corpus, or yields a complete downward closure. Those are
separate mathematical and experimental questions.

An implementation must independently audit: stable corner identities;
global vertex correspondence when several formal labels are identified;
boundary/interior link type preservation; coordinate reconstruction;
empty-survivor minima; and agreement with full post-move vertex-link
peeling. None of these new routines is claimed to be present in this package.
