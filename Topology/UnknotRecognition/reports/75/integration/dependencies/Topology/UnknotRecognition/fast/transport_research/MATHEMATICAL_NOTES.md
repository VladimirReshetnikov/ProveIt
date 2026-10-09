# Coherent cocycle transport and exact bistellar scores

Status: derived and locally exhaustively checked during the geometry audit.
No global completeness claim follows. The repository already implements
Pachner 2–3/3–2 moves but its `coherent_escape.py` search recomputes a rank-one
cocycle after each move. This memo concerns a different, local improvement.

## Local setup

Give the abstract five vertices of a bipyramid integral heights
`(C,D,E,A,B)`, where `C,D,E` are the belt and `A,B` are the two apices.
The old two tetrahedra are `(C,D,E,A)` and `(C,D,E,B)`; the new three are
`(A,B,C,D)`, `(A,B,D,E)`, and `(A,B,E,C)`. Boundary identifications are
permitted, as in the repository's formal-region Pachner contract. Integral
cocycle values on the old ball admit five such heights, unique up to a
constant, because they are exact on the abstract ball. Preserving these
heights on the replacement extends precisely the same boundary cochain.

Therefore the old and new global integral cohomology classes correspond
under the relative-boundary PL homeomorphism. In particular primitivity
and the meridional generator class survive. Heights can be recovered and
all changed normal coordinate rows reconstructed with a constant number
of arithmetic operations. Building an ordinary complete Python list still
requires copying the untouched rows, hence O(t), not O(1), total output work.

## Exact Euler jump

Put

    g = max(0,min(A,B)-max(C,D,E))
        + max(0,min(C,D,E)-max(A,B)).

Then under the 2–3 move

    chi(new) - chi(old) = -2*g.

The reverse 3–2 move increases Euler characteristic by exactly `2*g`.
All quantities have binary complexity polynomial in their bit length;
there is no iteration over the g layers.

Proof by integer coarea: use half-integer regular levels. At a level,
let r in {0,1,2} be the number of apices above, and s in {0,1,2,3} the
number of belt vertices above. The Euler jump is -2 exactly for
`(r,s)=(0,3)` or `(2,0)`; in all ten other cases it is zero. This follows
by counting new edge intersections, old/new internal face arcs, and
old/new tetrahedral normal discs. The number of exceptional half-integer
levels is g. Boundary cell terms cancel even when distinct formal
boundary cells are identified globally, since their identification data
are unchanged. The only changed interior cells are the old belt triangle,
the new apex edge, the three new internal triangles, and the tetrahedra.

An equivalent finite identity (suitable for an independent implementation
checker) writes `span(x)=max(x)-min(x)` and computes

    deltaF = sum(span(A,B,x,y) for (x,y) in [(C,D),(D,E),(E,C)])
             - span(A,C,D,E) - span(B,C,D,E)
    deltaA = sum(span(A,B,x) for x in [C,D,E]) - span(C,D,E)
    deltaV = abs(A-B)
    deltaChi = deltaV - deltaA + deltaF.

## Normal-disc monotonicity

The 2–3 move also never decreases the total number of coherent normal
discs. Per regular level, its jump is the following table, with rows r
and columns s=0,1,2,3:

| r | 0 | 1 | 2 | 3 |
|---|---|---|---|---|
| 0 | 0 | 0 | 1 | 1 |
| 1 | 2 | 1 | 1 | 2 |
| 2 | 1 | 1 | 0 | 0 |

Every entry is nonnegative; summing over levels proves the claim. This
also shows `deltaF >= g`. Thus a 3–2 collapse can be ranked first by g,
then by the exact normal-disc saving. The complete vector need only be
built for the selected move; evaluating all degree-three edge candidates
requires O(t) constant-size scores after local incidence construction.

There is a compact exact formula. Sort the belt heights as `x <= y <= z`
and the apex heights as `L <= U`. Then

    deltaF = max(U,y) - min(L,y)
             + max(0,min(U,x)-L) + max(0,U-max(L,z)).

The first term measures the levels between the apices plus the distance
of the median belt height from the apex interval. The last two terms
measure portions of the apex interval below/above the belt interval.
They are visibly nonnegative. Direct algebra also gives

    deltaF = span(L,U,y) + min(U,x)-min(L,x)
                        + max(U,z)-max(L,z).

Combining this with the independent relative cell-count formula reduces
the Euler jump to

    -abs(U-x)-abs(L-z)+(z-x)+(U-L)
       = -2*(max(0,x-U)+max(0,L-z)).

Thus there are two independent short proofs: the 12 binary profiles and
the min/max identity. This is an exact formula for the newly selected
coherent fiber after transporting the cocycle. It is not a claim that
ordinary topology-preserving normal-surface transport must change Euler.

## What this does and does not establish

* The class is preserved, but the coherent surface can change topology:
  the exceptional slabs replace two discs by an annulus (2–3), or perform
  the reverse compression (3–2). This is precisely the source of the
  Euler jump, rather than a contradiction to ambient manifold invariance.
  At each exceptional individual regular level the local change is
  annulus/two-discs. For many nested parallel annuli, do not claim all
  compression discs are disjoint from the entire original surface at
  once: an outer meridional disc can meet inner annuli. The local cell
  proof does not need this stronger geometric assertion.
* Connectivity is not preserved by this compression. A primitive class
  need not have a connected representative. In particular a transported
  cocycle with chi=1 cannot automatically use the repository's connected
  cocycle certificate. One must independently count/classify its
  components, or regauge and verify a zero-tree or minimum-span witness.
* A 3–2 sequence has length at most its initial tetrahedron count. No
  theorem says that a desired g>0 collapse exists. Some local optima
  require 2–3 expansions, and a positive g is only a useful search score.
* Consequently this yields a certified performance improvement for a
  restricted local search, not quasi-polynomial unknot recognition.

## Baseline audit observations

1. `maximize_cocycle_face_euler` already solves the entire minimum-span
   face in polynomial arithmetic complexity; merely proposing it again
   would duplicate the current repository.
2. `normal_seed_decide` does not invoke that optimizer, but this is
   deliberate experimental separation in recent reports: root extrema
   remain optional because previous measured pipelines had overhead.
3. `coherent_escape.py` greedily picks the first eligible degree-three
   edge and re-extracts the cocycle from scratch after collapsing. It has
   an explicit genus-two miss which is escaped by a 3–2 move.
4. `cocycle_euler.py` correctly rejects face-incidence degrees below two:
   otherwise the absolute-difference edge weights become negative and
   its convex min-cost-flow argument does not apply. Do not remove this
   restriction without a separate argument.

## Completed local check

The Euler identity was checked for all 4^5=1024 five-height tuples with
entries in {0,1,2,3}, using cell counts independent of the gap formula.
For a full contribution, add all 3^5 threshold profiles, binary-large
heights, random valid move sequences, source-bound positive replay, and
benchmarks against rank-one cohomology re-extraction.

## Implemented extension and further completed checks

The implemented scalar audit covers all 5^5=3125 tuples in {-2,...,2}^5.
The test suite checks 20,000-bit scaling, additive tetrahedral offsets,
strict certificate mutation rejection, cancellation, input immutability,
round-trip agreement with independently re-extracted one-vertex cocycles,
and every eligible collapse score after twelve random upward moves.

The first native/Regina audit uses four independent input families, each
with thirty mixed 2–3/3–2 moves. All 120 moves agree with Regina's Pachner
replacement up to isomorphism; the coherent Euler counts agree as well.

On the existing eight-tetrahedron genus-two obstruction the unique initial
candidate has five heights `(0,-1,1,3,4)`, gap 2, Euler gain 4, and piece
saving 5. Transporting without further H1 elimination gives six checked
collapses to a two-tetrahedron triangulation, total piece saving 33, and a
connected eight-piece normal disc. The native independent disc-component
certificate reports one compressing disc.

The natural canonical-source corpus (82 diagrams with at most sixteen
crossings) compares first-site/re-extracted-gauge, first-site/transport,
and score-selected/transport. All 246 runs complete. Each arm performs
144 collapses and finds exactly 15 supplied-vector compressing-disc
positives. Both transport arms' positives pass the full independent
diagram-to-exterior-to-moves-to-disc consumer. Final Euler characteristics
agree for every input, while normal piece counts differ on twelve inputs
due to representative or path changes. There is no coverage gain here.

## Binary coordinate growth under move sequences

Let `D` be the maximum absolute signed cocycle value on a global edge.
It equals the maximum local tetrahedral height span. A 3–2 move removes
one interior edge and creates no edge; hence `D_after <= D_before`.
A 2–3 move adds only the apex edge, whose value is the sum of the two
old oriented edge values along A–C–B, so `D_after <= 2 D_before`.
After u upward moves, `D <= 2^u D_initial` independently of the number
of intervening collapses. With every height row normalized at its first
corner, its entries have magnitude at most D, so bit length is at most
`B_initial + u + O(1)`. Accumulated Euler/piece totals add only O(log t)
bits. Input parsing must still pay for arbitrary initial offsets.

This bounds one deterministic downward epoch polynomially in tetrahedron
count and initial bit length. It does not prove that a useful collapse
exists. If one explores every 2–3 site between fixed deterministic
downward epochs, there are at most `sum_{i=0}^u (2(t_initial+u))^i`
macro histories. This is quasi-polynomial when u=O(log t), provided the
other endpoint queries are polynomially bounded. It enumerates only this
macrofamily, not every move sequence with u upward moves: alternative
downward choices are omitted. A completeness hypothesis must explicitly
refer to this restricted macrofamily.
