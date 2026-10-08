# Independent review of cocycle seed minimization

Reviewed the current `fastunknot/cocycle_seed.py`, its focused tests, and
`Topology/UnknotRecognition/audit_notes/cocycle_theory.tex` independently of
the implementation author. No substantive mathematical counterexample or
implementation/proof mismatch was found in the reviewed claims.

## Deletion closure

For a cooriented normal surface, restriction to each triangular face gives
cooriented normal arcs. Their algebraic endpoint counts cancel around the
oriented face boundary, so the signed global-edge intersection cochain is
closed. Edge coherence identifies unsigned edge weights with absolute
signed weights; it survives deletion of any union of connected components.

The map from local normal coordinates (four triangles, three quadrilaterals)
to the six unsigned local-edge weights has rank six, with kernel generated
by `(1,1,1,1,-1,-1,-1)`. For example, comparing opposite edge equations
forces the four triangle entries of a kernel vector to be equal, then the
remaining equations force all three quadrilateral entries to be their
negatives. Two distinct nonnegative coordinate vectors on this affine line
cannot both satisfy the at-most-one-quadrilateral-type constraint: one
would have all three quadrilateral coordinates positive. Thus admissible
coordinates are uniquely recoverable from the unsigned edge weights.

The local-height construction for the signed intersection cocycle therefore
recovers the coordinates of the deleted-component complement. This is the
critical closure fact required by the optimization theorem; mere homology
equivalence without this fact would have been insufficient.

## Nullhomologous component unions and connectedness

For a validated finite compact orientable three-manifold, integral
Poincaré–Lefschetz duality identifies relative surface class zero with
cohomology class zero. Consequently the signed cocycle of a nullhomologous
component union is an integral coboundary. Deleting it changes only the
global vertex potential and strictly lowers the number of normal discs.
This contradicts global optimality, and proves the no-zero-union claim.

A connected cooriented separating properly embedded surface has relative
class zero, so each remaining component is nonseparating. In a connected
ambient manifold, any connected two-sided nonseparating surface has a
closed transverse loop meeting it algebraically once: join opposite sides
through the connected complement and cross the surface once to close.
Its relative class is therefore primitive. When H^1 is Z, every component
is a signed generator. Opposite signs produce a forbidden zero-class union;
equal signs and primitive total class permit exactly one component.

The rank-one and integral-primitivity hypotheses are essential. The
arbitrary-height optimization API alone does not establish geometric
hypotheses, manifold validity, rank, or primitivity. No incompressibility,
genus-minimality, or hierarchy-complexity consequence follows from this
argument alone. If the first theorem allows disconnected M, 'nonseparating'
is understood within the component of M containing the surface component.

## Optimization and exact bit cost

The primal span inequalities form a difference-constraint LP. The stated
layered transshipment is its dual, with unit supplies/demands. A feasible
flow is immediate from matching each tetrahedron through any own corner.
All original internal arcs have capacity T+1, so they remain forward-
residual after the total T units are routed. Standard successive shortest
augmentations maintain optimality, starting from the acyclic zero-flow
network. Original internal flows are zero or one because each lower node
has total outgoing flow at most one and each upper node has total incoming
flow at most one.

At optimum the internal residual reward graph has no positive cycle.
Longest distances from an added zero source give integral feasible
potential inequalities, with equality on every used arc. The matching
certificate independently proves weak duality and checks equality, so the
returned optimum also holds over real potentials.

The implementation performs T augmentations on O(T) nodes and arcs, using
O(T^3) Bellman–Ford integer relaxations, followed by O(T^2) residual
potential extraction. Costs have B bits, and simple-path distances have
O(B+log T) bits. The claimed O(T^3(B+log T)) bit bound follows for binary
addition/comparison, with vertex indexing and I/O costs separately included.
Very large global vertex labels affect indexing/I/O, not network size;
the theory explicitly allows this qualification. Binary disc weights need
a general polynomial min-cost flow algorithm and are correctly excluded
from the current unit-augmentation implementation.

## Archive primitivity check

The archive02 method uses a maximal-tree gauge, then obtains integral
vectors in the kernel of its integer face matrix. Its `integer_nullspace`
clears denominators and divides each vector by its coordinate gcd. A
one-dimensional rational kernel is a saturated integral rank-one lattice,
so this normalization yields an integral generator in that specific case.
The same observation does not certify a saturated lattice basis when rank
is greater than one; the article and archived code correctly avoid that
claim.

