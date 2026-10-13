# Conflict transversals under knot/tangle composition: exact obligations

Scratch handoff, 2026-10-12. No maintained source, frozen research package,
evidence or article was changed. No family with growing h, universal small-h
bound, or new recognition complexity bound is proved here.

The useful next experiment is a **single marked meridional splice with two
certified positive formal witnesses whose conflicts remain in separate blocks**.
The following criteria specify what such an experiment must check before it
can support an inductive family. In particular, one cannot infer a family by
copying two knot names, concatenating Q coordinates, or preserving knot type.

## 1. Exact setting and the relevant strength of a counterfamily

For a finite triangulation T, K(T) is the root nonnegative Q matching cone,
F is canonical formal Euler, and D(q) is the complete set of tetrahedra having
at least two positive Q types. The maintained parameter h(T) hits D(r) for
all incompatible root extreme rays r with F(r)>0.

If T_m has m positive root extreme rays with pairwise disjoint nonempty
conflict sets, h(T_m)>=m. If also t(T_m)<=c*m+c0, this is a linear lower
bound for that family. This implication is immediate and does not require
that the admissible canonical cone is negative.

However, a family that also has easily found admissible positive Euler
vectors may be rapidly reduced by the maintained crushing driver. Sphere or
boundary-parallel-disc gadgets can therefore enlarge h at a supplied source
without obstructing recognition. A useful counterfamily against a proposed
post-simplification theorem must additionally do one of the following:

* already have F<=0 on its admissible canonical cone; or
* survive the precisely specified simplification with independently retained
  witnesses and a quantitative lower bound on their conflict packing.

A statement about all one-vertex sources, a statement about negative terminal
sources, and a lower bound on the actual driver are different claims. No
transport theorem for h under arbitrary normal crushing or simplification is
available from the current results.

## 2. Proved obstruction to naive one-vertex annular gluing

**Lemma.** An embedded annulus cannot be a subcomplex of a one-vertex
triangulated torus.

**Proof.** Each of its two boundary circles is a nonempty one-dimensional
subcomplex, hence contains a vertex. Both must contain the unique vertex,
contradicting disjointness of the two boundary components. This reasoning
also applies to the generalized triangulations used here: an edge circle
still contains its vertex. QED.

This does not exclude embedded annuli transverse to the triangulation.
It means that a knot connected sum cannot be implemented by merely selecting
existing complete boundary faces in each of our one-vertex sources and
identifying an embedded meridional annulus. Boundary subdivision, a cut through
existing cells, or an appropriate truncated-cell model is required. Restoring
one vertex afterward is a separate coordinate-transport obligation.

Gluing along a boundary disk instead gives a boundary connected sum; for two
torus-boundary pieces its boundary has genus two, not one. Gluing whole
boundary tori closes them. Neither substitute is a knot connected-sum
construction in the required finite torus-boundary class.

The topological marking is material. A meridional annular composition can
produce the connected sum of knot exteriors; an arbitrary annular slope need
not do so. A primary description using the composing space W x S^1 and
explicit meridian/longitude gluing is Porti--Yoon, *The adjoint Reidemeister
torsion for the connected sum of knots*, Sections 3.1--3.2, PDF pp.9 and 14:
https://ems.press/content/serial-article-files/36936 . No torsion result from
that paper is needed here.

## 3. Proved original-STANDARD rank transport criterion

For a proposed Q support S retain **all triangle columns** and only Q columns
in S in the original STANDARD matching matrix M_S. Let

    V = ker M_S,
    L = {x in V : q(x)=0}.

For a finite source with v vertices, dim L=v: triangle-only matching equates
corner values exactly along each global vertex class. Hence the projected
supported Q space has dimension

    dim(V/L) = 4t + |S| - rank(M_S) - v.

A nonzero nonnegative Q vector with precisely that support is root-extreme
when this dimension is one. A signed triangle lift causes no problem: add
large enough vertex-link multiples to make all triangle coordinates
nonnegative. This is the same direct projection argument independently
checked by the boundary-transversal package.

**Transport lemma.** Let V',L' be the analogous spaces after a proposed
composition/refinement. Suppose a specified linear restriction or aggregation
map R:V'->V maps L' into L. It induces an isomorphism V'/L' -> V/L exactly when

    R(V') + L = V,        and        R^{-1}(L) = L'.

**Proof.** The first identity is surjectivity of the induced quotient map;
the second says its kernel is zero. QED.

Convenient stronger sufficient conditions are: R is onto, ker R is contained
in L', and R(L')=L. For two one-vertex sources with the natural vertex-link
vector mapped to its counterpart, these reduce to unique extension of every
supported STANDARD solution: R:V'->V is an isomorphism.

A gluing matrix can be written from the two pieces' internal matching rows
and equalities of interface trace rows. Its rank must be measured on the
**entire selected Q support plus all triangles**. Restricting the triangles
to those positive in the selected witness would prove only a smaller
STANDARD-face assertion and can falsely suggest Q extremality.

The rank condition does not establish nonnegative extension, positivity of
F, topology of the new source, or conflict locality. Those are separate checks.
A single finite successful rank calculation also does not prove the needed
rank identity for arbitrary repeated composition. For a family, one wants a
block elimination/Schur-complement proof of this identity, with coefficients
and tetrahedron count bounded uniformly per connector.

## 4. Triangle-only continuation versus conflict-local continuation

Let P_A be the exact linear normal trace map at the gluing port A. If the
receiving block is required to have q=0, its possible traces are

    P_A(L_other),

with nonnegative triangle coefficients when actual nonnegative lifts are
required. On an unrefined one-vertex piece, L_other is only the vertex-link
line. Thus a general incoming trace cannot be matched with triangle-only
coordinates; it must lie in this one-dimensional trace image. Following a
subdivision, there can be more vertex-link directions and the actual matrix
image must be recomputed.

For a geometrically specified meridional annulus avoiding a small vertex
neighbourhood, a sufficiently small vertex-link disc has zero trace on A.
A nonzero essential boundary component whose slope intersects the meridian
therefore forces nonzero trace and cannot continue into such a triangle-only
receiving block. Meridional essential components can instead be arranged
outside a thin parallel annulus, as can sufficiently small vertex-link
circles. Translating this geometric observation into a refinement whose
normal-coordinate spaces preserve the seed ray is still unproved here.

**Strict support locality** would require all Q coordinates outside the
active block to vanish. That is stronger than necessary. For h packing it
suffices that each extended witness have at most one Q type in every
nonactive tetrahedron: its Q support may run through a connector and even
through other blocks, while its complete conflict set stays in its own
active block. Different witnesses may use different singleton types at the
same connector tetrahedron. They need not be mutually admissible; each
individually needs its own nonnegative matching lift, rank-one Q support,
positive canonical Euler, and conflict-set check.

This weaker **conflict locality** is the appropriate next target. Requiring
strict support locality would discard potentially useful compatible Q
continuations before testing them.

## 5. Canonical Euler is an independent gluing condition

Let E_T(x) be the linear formal Euler functional from source incidences, and
let L_v be the vertex link. For any STANDARD matching lift x of q,

    F_T(q) = E_T(x) - sum_v chi(L_v)*min_{corners at v} x_corner.

This is an exact algebraic identity, also for incompatible formal vectors.
For a finite one-boundary-vertex source it is E_T(x)-min_triangle(x), since
the link is a disc. Vertex merging can change the minimum and the number of
link directions. Rank isomorphism alone consequently does not preserve F.

Where a gluing admits an actual compatible cell-level description of the
formal polygon traces Gamma on the interface, Euler inclusion-exclusion gives

    E_glued = E_left + E_right - chi_formal(Gamma).

For a matched one-manifold trace, each interval component contributes one to
chi(Gamma) and each circle contributes zero. This formula assumes the exact
interface subdivision/gluing has been specified; it is not a substitute for
constructing that data. Afterward the global vertex-link correction above
must still be subtracted. In the general experiment, directly evaluate E
from the resulting labelled source and take the new corner minima.

In particular, preserving F of each seed before gluing, or adding a
triangle-only solution with positive Euler on another block, is not by itself
a proof of positive F after gluing and global canonicalization.

## 6. Negative-cone variant and 0-efficiency

On a source already proved negative on every admissible canonical vector,
a positive nonextreme formal point q can also give a packing constraint:
write its normalized point as a convex combination of root extreme rays.
Convexity of F implies that some component has positive F. Negativity rules
out its being compatible. Nonnegative coordinate decomposition implies its
conflict set is contained in D(q). Thus pairwise disjoint D(q_i) force at
least as many pairwise disjoint positive extreme-ray conflicts. Without the
negative-cone premise, that positive component could be compatible, and this
argument fails.

For finite one-vertex triangulations of a knot exterior in S^3, 0-efficiency
is equivalent to negativity of the admissible canonical cone. In one
direction, 0-efficiency allows only vertex-linking normal discs and excludes
normal spheres; the exterior also contains no embedded projective plane.
A positive canonical admissible vector would scale to an embedded normal
surface with a positive-Euler component, forcing one of these exceptions;
canonicality excludes the vertex-link component. Conversely, a connected
non-vertex-linking normal disc is canonical and has Euler one, contradicting
negativity. (Closed RP^2 cannot embed in S^3, for example by integral Alexander
duality: reduced H_0 of its complement would be Z/2.)

Primary topology reference: Jaco--Rubinstein, *0-efficient triangulations of
3-manifolds*, https://arxiv.org/pdf/math/0207158v1 , Proposition 5.15 on printed
p.56 and Theorem 5.17 on printed p.61. The former gives absence of normal
spheres and one vertex per boundary component; the latter is an existence
result for compact orientable irreducible boundary-irreducible manifolds.
Neither statement supplies a small-h bound or preserves these incompatible
ray witnesses through the simplification. Assuming such a simplification
available for free would bypass a central search obligation.

Essential annuli have Euler zero and are not ruled out by 0-efficiency.
Consequently composite knot exteriors remain relevant to a prospective
negative-source counterfamily, but the required coordinates and rank
transport have not been constructed.

## 7. Small retained-fixture probe, and its exact limit

Files boundary_profiles.py, boundary-profiles.json and boundary-profiles.txt
in this directory derive boundary traces and an integral primitive H^1
cocycle directly from the retained source's oriented edge/face incidences.
Reproduction from Topology/UnknotRecognition/fast:

    PYTHONPATH=. python -B -S /tmp/conflict-composition-design/boundary_profiles.py

The probe performs no LP, Regina call, new ray enumeration, or composition.
It rechecks original matching and pins the input fixture, geometry module,
and its own script. The previous boundary publication supplies the retained
ray extremality checks; no fresh enumeration is implied here.

For trefoil witness 0 (source SHA256
515b94f650b5a7b0e8e09322ba31f59eb8cdb108fe33d9220994c43f148ca3fd),
the boundary traces have two vertex-link circles. Removing them leaves
edge intersection weights (edge17:8, edge18:0, edge39:8), hence eight parallel
essential curves of the edge18 slope. The primitive exterior cochain takes
values (edge17:2, edge18:1, edge39:3). Evaluation one does NOT prove that
edge18 is the meridian: every slope mu+k*lambda has that evaluation.

Figure-eight witness 0 has one boundary vertex-link circle and two essential
curves parallel to edge3; that edge also evaluates to one. It has the same
meridian-marking ambiguity.

Across all 19 retained witnesses, only figure-eight witness 10 has no
boundary vertex-link circles. Its F is 1, Q support/rank is 11/10, and its
conflicts are {1,9,12}. Its boundary weights are

    edge3:4, edge58:10, edge29:14.

The weights have gcd two, so after dividing there are two parallel primitive
curves with weights (2,5,7). Edge29 is a primitive longitude: it is an
essential simple boundary edge and evaluates to zero under the exterior's
primitive integral cochain. Each primitive residual curve intersects it
seven times, so its meridian coefficient has absolute value seven. This
particular zero-vertex-link witness is therefore not meridional and cannot
have zero trace through a meridional annulus.

The other 18 witnesses all have positive numbers of boundary vertex-link
circles. A path in the boundary from the vertex to outside such a circle
must meet it. Therefore the most naive strategy of merging the summand
vertices along a boundary edge disjoint from every witness is also obstructed
for those retained rows. This is an obstruction to that specific zero-trace
transport, not a proof that a compatible Q continuation or an Euler-preserving
vertex reduction is impossible.

## 8. Concrete next experiment and missing induction theorem

Before attempting large composite diagrams, build ONE exact two-piece
meridional splice with a recorded peripheral marking. Test two candidate
witness extensions, one active in each piece, allowing singleton Q types in
all nonactive tetrahedra. For each verify:

1. finite oriented manifold source, torus boundary, and authenticated
   connected-sum topology with its actual meridian gluing;
2. nonnegative matching and the exact global canonical Euler formula;
3. rank(M_triangle) and rank(M_S) with all triangle columns retained;
4. nonempty disjoint complete conflict sets (not merely disjoint seed labels);
5. either an already negative admissible canonical cone, or explicitly only
   a supplied-source result vulnerable to positive crushing;
6. the actual one-vertex restoration and transport maps, not just a final
   tetrahedron count or isomorphism signature.

A promising finite subtask is to find a connector whose matching rows give
unique supported STANDARD extension modulo vertex links and whose singleton
Q continuation carries the required annular trace with positive final F.
Success on two copies is only a pilot. The missing family theorem must prove
this same connector identity for arbitrarily many copies, preserve conflict
locality, and give t=O(m), while establishing negativity or controlled
simplification survival. Failure of one pilot only rejects that connector.

This memo supplies exact obstructions and testable sufficient conditions. It
neither proves polylogarithmic h after simplification nor constructs a growing-h
family. Boundary-layer counterexamples stay published separately and frozen.
