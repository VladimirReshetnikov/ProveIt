# Initial conditional matching feasibility has a linear-algebra test

This scratch experiment is separate from the immutable sufficient-closure
experiment in `/tmp/conditional-type-elimination`. It changes no maintained
source, article, or evidence. It tests only the full initial quadrilateral
mask on six previously diagram-authenticated, fixed-U1 endpoints.

## Local matching identity

Fix a tetrahedron s. Give each of its four triangle types coefficient -1 and
each of its three quadrilateral types coefficient +1, with every coordinate
outside s zero. On each face and at each normal arc type, exactly one of these
triangles and one of these quadrilaterals contributes. Their sum is zero.
Consequently this signed STANDARD vector has zero trace on every face and
satisfies every original matching equation, even for global identifications
or self-attachments. Its Q projection is the vector r_s with all three Q
coordinates in s equal to one and all other Q coordinates zero.

This is a matching identity only. The signed STANDARD vector is not asserted
to be a nonnegative normal surface, and no Euler value is used here.

## Complete feasibility test at the full initial mask

Let a be one Q type in a tetrahedron tau. Let J_a keep a alone in tau and all
three Q types in every other tetrahedron. Write L_a for the linear space of Q
matching solutions on J_a. There exists a nonnegative STANDARD matching
vector whose Q projection is supported in J_a and whose a coordinate is
positive if and only if some vector in L_a has nonzero a coordinate.

The forward implication is projection. For the converse, divide a suitable
rational basis vector by its nonzero a coordinate to obtain q_a=1. For each
s different from tau, add max(0,-min(q_s0,q_s1,q_s2))*r_s. This preserves
matching and the three Q coordinates at tau, while making all other Q
coordinates nonnegative. Every r_s used is supported in J_a because the
other blocks are full. A rational triangle lift exists by the definition of
L_a, or equivalently by the triangle-potential elimination used in the
producer. On each global vertex, subtract the minimum of its triangle
coordinates; this adds a multiple of a triangle-only vertex-link matching
vector and makes every triangle nonnegative. Clearing denominators gives
the claimed integer STANDARD witness. The producer additionally divides
the common gcd; this is optional for feasibility.

This proof does not require a one-vertex triangulation; the retained six
sources happen to have one vertex. It requires the ordinary finite normal
matching system and its vertex-link triangle kernel, as validated by the
existing source preparation. It has no knot-type premise.

If every nullspace basis vector has a coordinate zero at a, the coordinate
functional e_a belongs to the equation row space. In reduced row echelon
form the pivot equation for a is exactly q_a=0: all free coefficients vanish.
The native sufficient closure's recovered RREF therefore detects this unit
equation immediately. Thus at the full initial mask a complete LP support
query cannot find additional target-coordinate zeros that this linear
test/unit-row check misses. This statement does not assert completeness of
the general one/two-row sign closure on arbitrary masks.

All construction steps have polynomial exact arithmetic and bit complexity
in the source size. The matching matrix has O(t) rows and columns with
bounded integral entries. Rational elimination coefficients are ratios of
minors, with polynomial bit lengths; block repair, triangle potentials,
O(t) denominator clearing, and gcd reduction retain polynomial bit length.
This memo gives no empirical timing claim and does not equate explicit
callback counts with bit operations.

## Why subsequent masks differ

The argument requires all blocks other than tau to remain full. After a
global deletion, the required block-ones vector may leave the retained mask.
There can then be a nonzero linear target coordinate but no nonnegative
matching vector with that coordinate positive.

For an exact abstract illustration, use blocks (a,b,c) and (d,e,f) with
equations a-b=0 and -a-b+2c+d-e=0. Each equation has coefficient sum zero in
each block, so both local block-ones directions belong to the kernel.
Initial single-type tests delete a and b by linear unit constraints. After
these deletions, the conditional mask for d is {c,d}, and its equation is
2c+d=0. A linear vector can have d nonzero (take c=-d/2), whereas nonnegative
coordinates force d=0. This is an algebraic counterexample to extending
the proof using block-ones directions alone; it is not claimed to be a
realizable triangulation or a native geometric fixture.

## Scope of the retained witnesses

The independent checker derives every J_a from the full source and tested
type. It checks literal nonnegative integer coordinates against the original
STANDARD matching equations, q_a>0, and both competing Q coordinates at tau
equal to zero. Other tetrahedra may have incompatible Q coordinates. It
does not use producer nullspaces, potentials, block repair, or any LP.
Construction metadata is diagnostic; its derivation is not part of the
independent mathematical acceptance test.

No Euler sign, ray extremality, global quadrilateral compatibility, normal
embedded surface, or recognition verdict follows from these witnesses.
They refute only the proposed conditional matching-zero elimination on
these initial masks. There are no global deletions in this experiment.
ZERO_LINEAR_TARGET, if returned, is a producer diagnostic unless accompanied
by an independently checked original-row proof; this experiment makes no
infeasibility claim from it. Capped sources cannot claim full-type coverage.

For a fixed source, restricting nested masks gives h_J' <= h_J by
coordinate-face extreme-ray inheritance. It does not change the full-source
h(T), and a negative tree on a reduced mask does not alone bound h(T).
No uniform resolving-set theorem or general quasi-polynomial recognition
bound is proved here.

## Reproduction and resource scope

    python -B /tmp/conditional-type-witnesses/probe.py --max-checks 1000000 > /tmp/conditional-type-witnesses/probe.txt
    python -B /tmp/conditional-type-witnesses/replay.py > /tmp/conditional-type-witnesses/replay.txt

The producer allows at most 1,000,000 explicit check callbacks per source,
6,000,000 total. Independent replay is outside this construction-work cap.
There is no wall-clock cutoff and no LP, row-pair closure, ray enumeration,
or Pachner discovery. All attempted queries, including incomplete returns,
are retained. Current maintained source hashes are recorded at generation
and compared again after every source and at the end; original staged
generation pins remain historical inside the independently authenticated
archive.
