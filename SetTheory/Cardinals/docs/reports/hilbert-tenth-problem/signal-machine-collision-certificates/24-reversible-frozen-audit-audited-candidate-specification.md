# Candidate: reversible binary four-particle quadratic clock

Status: construction and proof supplied for independent audit. The accompanying
checker is newly written; no upstream executable code is used.

## Finite local rule

For each row below, a raw key is a pair (row, integer anchor x). It is present
when the occupied sites in the inclusive translated read interval x+W are
exactly x+E0 or exactly x+E1. Sites outside x+W are ignored.

| Block | Row | E0 | E1 | W |
|---|---|---|---|---|
| A | AR | {0,1} | {0,2} | [-4,6] |
| A | AL | {0,4} | {0,3} | [-4,8] |
| A | AC | {0,1,6} | {-1,2,7} | [-5,8] |
| B | BR | {0,2} | {1,2} | [-4,6] |
| B | BL | {0,3} | {-1,3} | [-5,7] |
| B | BC | {-5,0,3} | {-5,0,1} | [-5,8] |

A raw key records row and anchor, not endpoint side. Its hypothetical swap
replaces the endpoint present with the opposite endpoint, leaving all other
sites alone. All endpoint supports are contained in [-7,7] and all read
intervals in [-8,8]. Set b=7, r=8, H=2(b+r)=30.

In either block select a raw key k=(row,x) exactly when:
1. There is no OTHER raw key, including another row at x, with anchor within
   H=30 of x.
2. Its hypothetical swap preserves every raw key of this same block whose
   anchor lies within b+r=15 of x.

Apply all selected swaps simultaneously. Define F=B composed with A.
These instructions are a finite binary local-rule specification, not a
promise restricted to legal four-particle configurations.

## Full-shift involution lemma and proof

Consider any finite family of endpoint swaps with equal endpoint weight,
write support in [-b,b], and endpoint-symmetric raw predicates of read radius
r >= b. Assume each hypothetical swap preserves its own raw key. Define
the parallel block by the preceding two tests with H=2(b+r).

A hypothetical swap at x can affect raw predicates only at anchors within
b+r of x. Thus the prospective local test is equality of the entire raw key
sets before and after that hypothetical swap.

Selected anchors have mutual distance greater than 2(b+r), so their write
windows are disjoint. A raw-predicate read window can intersect at most one
selected write window: intersection with windows at x and y would imply
|x-y| <= 2(b+r). If a predicate intersects no selected write, it is unchanged.
If it intersects one, the corresponding prospective test preserves it.
Therefore the simultaneous block preserves the entire raw key set.

This also preserves every isolation status. For an isolated raw key at x,
the prospective test depends only on [x-(b+2r),x+(b+2r)]. Every selected swap
at a different anchor lies outside this region, since the other anchor has
distance greater than H=2b+2r and its write radius is b. If the key is selected,
its own swap interchanges the two configurations compared by its prospective
test. If it is rejected, no own swap occurs. Consequently the selected and
rejected statuses of all keys are preserved. Applying the block twice selects
the same disjoint swaps and undoes each one.

This establishes an involution on EVERY bi-infinite binary configuration,
including malformed and infinite supports. Equal endpoint weights and
disjoint writes imply number conservation on every finite support. Vacuum
has no raw key and is fixed. Translation equivariance is immediate.
To decide output at a site one considers anchors within b; at each such
anchor isolation reads radius H+r=2b+3r, while prospectivity reads radius
b+2r. The block radius is at most 3(b+r).

For the six literal rows the hypotheses hold by direct inspection:
both endpoints have the same cardinality, lie inside their read interval,
and exact replacement interchanges their raw-predicate sides. Therefore A
and B are globally reversible number-conserving binary CAs of radius at
most 45, and F is one of radius at most 90, with inverse A composed with B.

## Complete legal orbit

For D >= 13 let C_D={0,5,6,D} and ell_D=2D-22. For 0 <= s < ell_D:

R phase (0 <= s <= D-11):
    F^s(C_D) = {0,5+s,6+s,D}.

L phase (D-10 <= s <= 2D-23):
    F^s(C_D) = {0,2D-18-s,2D-14-s,D+1}.

The endpoint after the cycle is F^ell_D(C_D)=C_(D+1).

Verification of every half-step:
- Before right contact, write p=5+s with 5 <= p <= D-7.
  AR sends {p,p+1} to {p,p+2}; BR sends that to {p+1,p+2}.
- At right contact p=D-6, AR is excluded by the particle at p+6.
  AC sends {D-6,D-5,D} to {D-7,D-4,D+1}.
  BL sends its pair to {D-8,D-4}.
- In the L phase write q=2D-18-s. For q>=6, AL sends {q,q+4}
  to {q,q+3}, and BL sends that to {q-1,q+3}.
- At the last state q=5, AL sends {5,9} to {5,8}.
  BL is excluded by the particle at 0=5-5.
  BC sends {0,5,8} to {0,5,6}, giving C_(D+1).

For all half-states, exactly one pair of particles has mutual distance
at most 4, and every other pair distance is at least 5. Every literal
endpoint row must use that unique close pair.

For A, pair gaps 1/2 can only use AR (gap 1 alternatively AC input);
gaps 4/3 can only use AL (gap 3 alternatively AC output). AC input has
its marker at close-pair-left+6, precisely excluded by the AR read window.
AC output has its marker at close-pair-left+8, precisely excluded by the AL
read window. During free flights the marker distances exclude AC.
For B, pair gaps 2/1 can only use BR (gap 1 alternatively BC output);
gaps 3/4 can only use BL (gap 3 alternatively BC input). BC has its
left marker at close-pair-left-5, excluded by the relevant BR/BL read window.
During free flights this left-marker distance excludes BC.
The stated bounds D>=13 ensure that the unused fourth particle is outside
each contact read interval. Thus each half-step and its hypothetical endpoint
have exactly the same ONE raw key. Isolation and prospectivity always pass.
This proves the displayed formulas for the actual globally defined F.

## Exact anchored hits and failure of eventual periodicity

Take pattern 1000011 on coordinates [0,6]. In the R phase its two adjacent
particles occupy 5 and 6 precisely at s=0. In the L phase the moving pair
has distance 4; the other particles are at 0 and D+1>=14, so the pattern
cannot occur. The required zeros at coordinates 1,2,3,4 hold at s=0.

Starting from C_d, d>=13, the hit times are exactly
    t_k = sum_{j=0}^{k-1}(2(d+j)-22)
        = k^2 + (2d-23)k,  k=0,1,2,...

Successive gaps are 2k+2d-22 and tend to infinity. An infinite eventually
periodic subset of natural numbers has bounded successive gaps, so this
hit-time set is not eventually periodic. In particular, d=13 gives the
exact quadratic set {k^2+3k : k>=0}.

## Source boundaries

The prospective-isolation mechanism is reported in the repository review:
https://github.com/VladimirReshetnikov/ProveIt/blob/main/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_parallel_particle_reports.md
(fetch SHA 30c7366beb6afa71ee2f72e87776c9781c77e1e2).

The already audited NONreversible four-particle clock is different:
https://github.com/VladimirReshetnikov/ProveIt/blob/main/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/17-four-mass-BINARY-INDEPENDENT-AUDIT.md
(fetch SHA 0aa7b9707374304f496dce793a1501c15d3c2f85).

Morita's 2012 primary paper concerns multistate RNCCAs and does not by itself
establish this binary, fixed-four-particle claim:
https://arxiv.org/html/1208.2760

No novelty or priority claim is made. Finite checker results supplement,
rather than replace, the full-shift proof above.

