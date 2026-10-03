# A fully literal periodic three-dimensional router

This construction closes the geometric routing step in the literal sandpile
loader. It does not call a graph-embedding theorem, a path finder, or a routing
oracle. Every support coordinate is given by finite loops over axis-aligned
segments. The only use of Cairns, arXiv:1508.00161v2, Sections 2.2–2.3, is the
wire/diode/gate semantics; the periodic routing construction below is explicit.

## 1. Finite input and the complete primitive placement

For the nontrivial case there are N >= 1 primitive boxes, indexed j=0,...,N-1. Allowed kinds are AND,
OR, FORK, WIRE, and DIODE. Higher fanout is first expanded into a finite binary
fork tree. The circuit description contains M >= 1 edges, indexed e=0,...,M-1.
Each primitive port is incident to at most one external edge. Ports are distinct
incidences: a port is never simultaneously the source of one edge and the target
of another. This is ordinary circuit normalization, with fanout implemented by
FORK boxes rather than by repeated use of an output port.

An edge has records (a,ap,b,bp,k,d), from source primitive a/port ap in cell (x,t)
to target primitive b/port bp in cell (x+k,t+d). Either (k,d)=(0,0), for an internal
edge, or d=1 and -2 <= k <= 2. Internal edges may form the prescribed finite DAG.
The geometry does not rely on acyclicity. Each port type occurs in at most one
edge record, including source and target occurrences. Consequently 2M <= 3N.
Unused ports are harmless finite dead-end tails. If M=0, omit routing entirely
and use z-period 32; if N=0 the all-zero configuration with periods (1,1,1)
suffices. The formulas and implementation below target the nontrivial M>=1 case.

The following coordinates are relative to a primitive's center:

* Every primitive has height-5 support (u,0,0), -12 <= u <= 12.
* AND, OR, FORK additionally have support (0,v,0), -12 <= v <= -1.
* AND and OR have height 4 at (-4,0,0),(4,0,0), and height 5 at
  (-5,1,0),(-4,1,0),(4,1,0),(5,1,0).
* AND has center height 4. OR and FORK have center height 5.
* DIODE has height 4 at (0,0,0), and additional height-5 support
  (-1,1,0),(0,1,0). Its permitted signal direction is left to right.
* All other listed support has height 5; all unlisted lattice sites have height 0.

The AND/OR template is exactly the parent's checked gate with its three straight
tails extended from length 8 to length 12. Its ports are L=(-12,0,0),
R=(12,0,0), B=(0,-12,0). WIRE and DIODE use only L,R. FORK uses L,R,B.
The gate/diode support degree is at most 3 and off-support co-degree is at most 2.
The routing checker also checks these assertions as part of the full assembly.

Set B=48(N+1). Primitive j in cell (x,t) has center

    (Bx + 24 + 48j, Bt + 24, 0).

Its planar port coordinates relative to the cell are

    L: (12+48j,24),  R: (36+48j,24),  B: (24+48j,12).

Every port x-coordinate is distinct modulo B, and the cyclic gaps are at least 12.
All gate support is in local y in [12,25]. Distinct primitive boxes have horizontal
clearance at least 24. The seam between consecutive cell rows has still greater
clearance. Thus there are no unspecified port adapters or normalizations left.

## 2. The seven explicit axis-parallel segments for one edge

For edge e and source cell (x,t), put r=x mod 7 and s=t mod 4, using nonnegative
remainders. Set

    H(e,x,t) = 64 + 12 [ e + M(r+7s) ].

Write the source port as (u_a,v_a) and target port as (u_b,v_b), in the local
coordinates above. Set

    ax=Bx+u_a,        ay=Bt+v_a,
    bx=B(x+k)+u_b,    by=B(t+d)+v_b,
    Y=Bt+B/2.

The edge support consists of every integer point of the seven segments with
successive corners

    (ax,ay,0),
    (ax,ay,H),
    (ax+4,ay,H),
    (ax+4,Y,H),
    (bx+4,Y,H),
    (bx+4,by,H),
    (bx,by,H),
    (bx,by,0).

All these sites have height 5, including their shared height-5 primitive port
endpoints. No other sharing is permitted. To enumerate a segment, identify its
single varying coordinate and loop over every integer between its endpoints.
No geometric decision is delegated to an oracle.

## 3. Exact periods and finite table generation

The periods are

    Lx = 7B,   Ly = 4B,   Lz = 336M+84.

The maximum used routing height is Hmax=336M+52. Thus Lz=Hmax+32.
Generate all primitive support for source cells 0<=x<7, 0<=t<4. Generate every
edge route for those same source cells, even if a target lies outside that range.
Reduce every generated coordinate modulo (Lx,Ly,Lz), assigning its specified
height. Everything absent from this sparse list is zero. This is the complete
fundamental-domain table; it is then repeated on all Z^3.

This modular procedure includes seam-crossing edges; it never clips a route at
a cell or fundamental-domain boundary. It is equivalent to the infinite route
formula because translation by 7 cells in x or 4 cells in t preserves H.
The positive-support slabs in z have thickness Hmax+1 and have 31 intervening
all-zero planes. Hence a finite seed set in the slab with gate plane z=0 leaves
all other z-translated slabs inactive.

The dense table has exactly

    28 * [48(N+1)]^2 * (336M+84)

sites. This is a fully charged O(N^2 M) bound, or O(N^3) using 2M<=3N. Producing
the dense table takes one explicit visit per entry after the sparse supports
have been generated. The bit size of any coordinate is O(log(N+M)).

Each primitive uses at most 41 support sites. Each edge route has at most
2Hmax+4B+21 = 672M+4B+125 sites. (The bound allows endpoint overcounting.)
Therefore a sufficient sparse-generation bound is

    28 [41N + M(672M+4B+125)].

This is also an explicit bound on elementary site insertions. N and M are fixed
once the finite universal circuit cell has been fixed.

## 4. Separation proof

First consider the unquotiented support in one slab. The modular assertions then
follow by applying the same arguments to every translate.

### Distinct shafts and reserved lanes

Every vertical shaft stands on a primitive port. Distinct port types or x cells
have x-coordinates differing by at least12. Copies of the same port in distinct
time rows have equal x but y separation at leastB; thus their shafts are still
separated. All shaft comparisons below include this equal-x, different-y case. A y-running routing segment has
x-coordinate equal to a port x-coordinate plus 4. Its distance in x from every
shaft is at least 4; from a shaft belonging to a different port it is at least 8.
The short x-running terminal stubs have length 4. A stub is at horizontal
distance at least8 from a shaft of a different port/x cell. Shafts of the same
port in another time row instead have y separation at leastB.

Every long x-running routing segment has y=Bt+B/2. Shaft y-coordinates are
B*t'+12 or B*t'+24. Their distance from this corridor is at least B/2-24>=24.
This holds across the y-periodic seam as well.

Distinct routing heights differ by at least 12. Thus planar pieces belonging to
different edge labels or different residue pairs cannot meet or have adjacent
support sites. Intersections of their planar projections do not matter. All
shaft/planar-piece interactions were covered by the preceding clearance bounds.

### Copies at one routing height

At one fixed height, the edge label and residue pair are fixed. The only other
routes at that height are translates by (7aB,4bB,0), where (a,b) is a nonzero
integer pair. A route's x extent is less than 3B because |k|<=2 and its endpoint
local coordinates lie strictly inside the cell. Its y extent is less than 2B
because d is 0 or 1. Consequently distinct same-height copies have a positive
coordinate separation of more than 4B in x or more than 2B in y. They cannot
interact. This is the reason for residue coloring; an edge-label-only layer
would not provide this guarantee for neighboring translates.

### Self-separation, corners, and primitive attachments

The two endpoint port types of an edge are distinct. Their lane x-coordinates
therefore differ by at least 12, including across x-cell seams. Their short
terminal stubs are separated by at least 8 whenever they have equal y.
The corridor is at least 24 from either local endpoint row when d=0; when d=1,
it lies strictly between the source and target rows, again with margins at
least 24. The two bends on a terminal stub are 4 apart. Every other successive
pair of bends is at least 12 apart, and the initial shafts are at least 64 long.
These facts show that each route is induced, without self-adjacencies.

A shaft attaches only to the endpoint of a length-12 straight primitive tail.
The nearest gate branch or diode feature is at least 7 away. Its attachment
neighborhood is therefore exactly one ordinary right-angle wire bend. The gate
interior and every unrelated gate are clear of the new routing support.

Thus the only support adjacencies are the prescribed primitive adjacencies and
consecutive sites of one listed route. Every new routing vertex has support
degree 2; a primitive port acquires exactly one neighbor, going from degree 1
to degree 2. Maximum support degree in the whole assembly remains 3.

### Off-support sites

The clearance estimates are stronger than nonadjacency: distinct unjoined
pieces are separated by at least 4. Therefore an off-support vertex cannot be
adjacent to two unrelated pieces. Near one straight segment it has at most one
support neighbor. Near one right-angle bend it has at most two. The separation
between bends prevents a radius-one neighborhood from seeing two bends.
Inside or near one primitive its co-degree is at most 2 by the explicit template
check; at an attachment it sees only the ordinary bend just described.
Consequently every off-support site has at most TWO support neighbors throughout
the infinite periodically repeated construction.

## 5. One-shot and isolation lemma

Let S be this positive support, let the periodic base height b satisfy b<=5 on S
and b=0 outside S, and add seeds delta(v) in {0,1} only at finitely many support
sites in the chosen slab. Suppose there were a first exceptional event in a
legal toppling sequence: either an off-support topple or a second topple of a
support vertex. Before that event every support vertex has toppled at most once
and no off-support vertex has toppled.

An off-support vertex can then have received at most 2 chips and cannot topple.
A support vertex has received at most deg_S(v)<=3 chips in total, so its lifetime
available chip count is at most b(v)+delta(v)+deg_S(v)<=9<12. It cannot have
performed two threshold-6 topplings. Both exceptional events are impossible.
This proves the assertion for every legal finite prefix and hence every legal
sequence, including infinite sequences. The weaker sufficient conditions
co-degree<=5 and b+delta+degree<12 would also suffice.

Every unseeded z-translated slab starts stable. There is no support connection
to the seeded slab, and off-support vertices never topple, so no signal can enter
it. Thus exactly the selected slab can carry the finitely initiated computation.

## 6. Executable independent checks

`periodic_router.py` is a standalone Python implementation of the formulas. It
checks the *complete periodic torus*, not a clipped finite sample, including:

* consistency of all heights at overlaps;
* uniqueness of every external port incidence;
* support degree at every nonzero site;
* co-degree at every zero site adjacent to support;
* every adjacency against gate/edge ownership labels;
* inducedness of each individual route, including periodic seams.

`router_checks.json` records two completed tests:

1. Five WIRE primitives with five temporal edges covering all offsets -2..2:
   periods (2016,1152,1764), 345296 nonzero sites, maximum support degree 2,
   maximum off-support co-degree 2, and zero unintended adjacencies.
2. Six mixed WIRE/FORK/AND/OR/DIODE primitives, seven internal/temporal edges:
   periods (2352,1344,2436), 582652 nonzero sites, maximum support degree 3,
   maximum off-support co-degree 2, and zero unintended adjacencies.

The proof establishes the arbitrary finite-cell result; the finite tests catch
coordinate and seam implementation errors and do not replace that proof.
