# Linear height and binary length of the complete quartic witness

Status: standalone companion lemma for the fixed-horizon compiler. This packet
makes no change to the frozen/current compiler packet and is not a separate
report designation. The construction under audit is in
`parallel-diophantine-certificate-research-20261003/{compiler.py,circuit.py}`;
the exact input hashes are recorded in `audit-receipt.json`.

## 1. Statement

Fix a validated finite source s and particle count n >= 0. Set b = B3 from its
validated metadata. For either direction, let Cert(s,n,T) be the existing
fixed-horizon compiler, and suppose its canonical external endpoint pair (X,Y)
is accepted, with max_i |X_i| <= A; take this maximum to be zero when n=0.
Here A,T are nonnegative integers. The complete auxiliary tuple means EVERY
natural variable other than the 4n external signed-pair components, including
all comparison bits/slacks, signed-assignment components, Boolean registers,
padding selections, inactive lanes, rejected raw slots, unsuccessful prospective
passes, and both external sortedness checks.

There is a finite, explicitly computable integer C(s,n) >= 1, independent of
A,T and direction, such that every coordinate v of that unique complete tuple
satisfies

    0 <= v <= C(s,n) (A + T + 1).

Write w_E(s,n), w_P(s,n) for the actual numbers of witness variables emitted by
one complete E or P block on n fresh canonical signed input pairs, without
external-domain/endpoint checks. The compiler's exact witness count is

    W(T) = 4 max(n-1,0) + T (w_E + w_P).

With zero encoded by one bit, the sum of the ordinary binary lengths of the
witness coordinates is at most

    W(T) ceil(log_2(C(s,n)(A+T+1) + 2)),

and hence is O_{s,n}((T+1) log(A+T+2)). This is an upper bound, not a lower bound
or a Theta statement. No asymptotic inversion assertion is made. Source, n,
horizon and direction remain compiler syntax; the number of witnesses grows
with T. No unbounded-time fixed-arity representation is asserted.

## 2. What cannot be inferred merely from degree two

A generic `Circuit.integer(p)` permits any quadratic p. Iterating assignments
such as v <- v^2 would destroy the claimed linear height even though each
residual is quadratic. Consequently neither residual degree <=2 nor the
quartic sum-of-squares conversion by itself proves this lemma.

We instead audit the actual emitter's assignment expressions. All products
that can involve coordinate-dependent data are a Boolean mask times an affine
combination of such data. The other products use constants or bounded control
values. In particular, p*m=0 canonicality, b(b-1)=0, the comparator's bit/slack
product, and the squares in the final polynomial are constraints; they are
not extra natural registers holding those products.

The word affine here refers to data inputs with the control bits held fixed.
No assertion is made that the compiler's comparisons or complete piecewise
function are globally affine functions of the initial coordinates.

## 3. Exact Boolean invariants used in the audit

For every integer input to `ge`, its natural bit/slack equations uniquely force
b in {0,1}, with slack d when d>=0 and -d-1 otherwise. The slack is <=|d|.
The two `ge` bits used by `eq(x,y)` differ by exactly the zero-indicator of
x-y, so that `eq` is Boolean. `AND`, `OR`, `NOT`, and the `all`/`any` folds
preserve Booleans, including their empty-fold constants. Their actual uses
receive only such bits, 0/1 source-table entries, or the live payloads below.

`select(b,x,y)` computes x+b(y-x), with a Boolean selector in EVERY actual
emitter call. It therefore returns x or y, with a uniquely canonical signed
pair. When x and y are live bits, the selected signed value remains a bit.
The resulting positive component is that bit and the negative component is
zero. Hence the signed-pair storage of sorted live fields does not turn them
into arbitrary integer arguments to later Boolean operations.

The selectors are raw interval bits for travel masking, singleton bits for
guard classes, comparator bits for coordinate sorting, Boolean compare-exchange
bits for key sorting, or Boolean route bits for lane routing. Counts, ranks,
arity values, IDs and signed coordinates are compared to obtain bits; they are
never passed as untested selector values. This establishes all Boolean-output
bounds used below by induction in the actual source's topological order. The
argument holds even for unsorted or duplicate coordinate lists, independently
of later acceptance checks.

## 4. Exhaustive audit of operation-producing code

All functions listed here are in the actual current `compiler.py`. Helpers
`plus`, `times`, `sum_poly`, and polynomial `add/sub/mul` only build expressions;
all natural auxiliary variables are allocated by `Circuit.integer`, `ge`, or
`boolean`, including allocations reached through their wrapper methods.

### Raw candidate construction

- `gap=c.sub(h2,h)` and `distance=c.sub(h,z)` are affine data differences
- Source gaps, shifts, mode signs, travel endpoints, type bases, and metadata
  radii are finite source constants. Anchors, old sites, and prospective new
  descriptor sites are affine coordinate expressions plus such constants
- Travel `t0` is an affine signed difference. Its range comparison returns a
  bit. The materialized `t=select(ok,dummy,t0)` is a Boolean-masked affine
  assignment. The ensuing ID assignment is affine in t. In fact travel masking
  gives source-bounded IDs, but that sharper fact is NOT needed in the majorant
- Exactness interval tests and all endpoint/guard equalities are comparisons
  of affine data or already assigned linear-height registers. Counts sum bits
- Every E family (free, behind, ahead, dispatch, endpoint, commit, direct) and
  P family (phase-free, phase-near, phase-home), both orientations and all
  pair/marker/source indices, use exactly these operations. Finite loops change
  the count and constants but introduce no new kind of data product

### Guards, including rejected detector configurations

- Interval bounds are anchor plus source constants; their flags are Boolean
- Hit count is a sum of n bits and is <=n
- Each offset term is flag times `side*(x-u)-Z`, a Boolean mask times an affine
  expression. Summing all terms is affine in their assigned registers
- Singleton class selection is `select(singleton,J+1,offset)`
- Every source-table cell is scanned using equality bits and Boolean folds,
  including false cells, multi-hit/rejected classes and zero-hit classes

Indeed a flagged offset lies in [0,J], so the total offset is <=nJ. If the
count is one the class is in [0,J]; otherwise the class is J+1. The proof below
can conservatively tag these offset/class registers as coordinate-dependent;
it does not need these tighter semantic bounds.

### Sorting and lane selection

- Key sorting compares live bits and anchors. Each compare-exchange selector
  is Boolean; selects transport live fields, anchors and fixed slot indices
- Padding live/anchor/index fields are the fixed values 0,0,-1. They are
  included in all comparator and select operations
- Selected live fields remain Boolean by Section 3, while slot indices remain
  among finitely many source/n-dependent constants
- Isolation compares differences of adjacent anchors with fixed H
- Rank accumulation adds isolated bits; ranks are at most the finite padded
  slot count. Rank/slot/arity arithmetic has coordinate-independent height bounds
- Routing repeatedly selects either the previous fixed dummy/payload or one
  raw descriptor, using Boolean route bits. ID, anchor and endpoint data may
  conservatively have linear height; arities and slot indices are bounded

### Hypothetical transport, full prospective rediscovery, and final output

- `move` forms each hit as a Boolean fold of selected/present, arity comparison,
  and coordinate equality. Each displacement assignment is hit*(new-old)
- Each moved coordinate is the original coordinate plus the finite sum of
  these displacement registers. This is affine, including when the lane is
  absent or later rejected. No disjointness assumption is needed for its
  one-block linear-height bound
- The fixed coordinate sorting network compares two coordinates (with the
  literal +1 strictness shift) and uses Boolean selects; it introduces no
  coordinate-by-coordinate product
- Every hypothetical lane runs the entire raw circuit again. Its input
  coordinates are linear-height expressions from the preceding move/sort,
  so the same audit applies to all newly created scratch
- Prospective near/same/own/other tests only compare IDs/anchors and combine
  bits. The selected lane flags are Boolean. Final simultaneous `move` is
  the same fully audited construction with finitely many lanes

Thus EVERY assignment or comparison monomial has at most one factor that
needs a coordinate-dependent height bound. Products within Boolean formulas
have only uniformly bounded control factors. This remains true for
constant-false flags, rejected slots, missing lanes, padding, and full after
passes. No branch's defining equations or allocated variables are omitted.

## 5. An explicit source/n-computable affine majorant

The following deliberately conservative constants avoid leaving the main bound
solely as an enormous abstract circuit recurrence. Define

    ell = floor(n/2),     F = metadata.factors,
    K_E = binom(n,2)[4p + (14p+2a_s)max(n-2,0)],
    K_P = binom(n,2)[4p + (8p+2m)max(n-2,0)].

Here a_s is the source's number of direct branches, p its moving-branch count,
and m its control count. Let P_E and P_P be the least powers of two at least
max(1,K_E) and max(1,K_P), respectively. These P_B are PADDED OCCURRENCE
WIDTHS, not endpoint-type counts. F is the total endpoint-type count. Put

    H_star = 2[b + max(Z+J,3b+1)],
    alpha = 14 + 12 ell,
    beta = (10+6ell)b + Z+J + 2H_star
           + n(J+1) + F + P_E + P_P + 10,
    C(s,n) = (4b+1)(alpha+beta).

Everything in these expressions is computed by the validated source metadata
and the compiler's exact finite slot formulas. P_B is only the width of the
existing fixed sorting network; no enumeration of coordinate travel or all
endpoint templates is introduced.

We claim that, for either ONE COMPLETE BLOCK with canonical input-coordinate
magnitude <=R, every auxiliary natural coordinate is <=alpha R+beta. The claim
includes hypothetical/rejected/inactive scratch and does not assume that the
input is a source encoding or that a candidate passes its prospective check.

### Raw-pass bound at arbitrary input magnitude U

Validated metadata has |side|=1, |moving delta|=1, every gap <=D, S=2D+2,
L=3D+4 and b=4D+5. Inspection of every descriptor family gives

    |old site| <= U,     |new site| <= U+b,     |anchor| <= U+1.

For dispatch/commit, the largest new-site offset is S+D<=b. For the other
families it is at most D+1<=b. Reverse endpoint anchors shift by at most one.
These facts hold even for descriptors whose raw predicates are false.

Gap/distance registers have magnitude <=2U. Unmasked travel expressions have
magnitude <=2U+1; range comparators therefore have slack <=2U+b+1. Selected
travel is in its fixed admitted interval (or its dummy point), and IDs are in
[0,F-1]. Canonical natural components obey the same absolute-value bounds.

Every raw-pass comparator slack or non-Boolean register is covered by the
following list; all Boolean outputs are <=1:

- Gap/incidence/travel equality/range comparisons: <=2U+b+1
- Exactness interval comparisons: <=2U+3b+2
- Detector interval comparisons: <=2U+Z+J+1
- Counts and count comparisons: <=n+4
- Guard offset terms and summed offset: <=J and <=nJ, respectively
- Selected guard classes and table-cell comparisons: <=J+1 and <=J+2
- Materialized travel and IDs: <=b and <=F

An `eq` uses two comparisons, including its +1 shift; that shift is included
above. A convenient common bound, including signed descriptor values whenever
materialized later, is

    RawCap(U) = 2U + 3b + Z+J + n(J+1) + F + 6.

### Key sorting and routing

Boolean selects copy existing values. Sorted anchors and routed anchors stay
within R+1; old/new sites stay within R and R+b. Live values remain bits, arity
stays in {0,2,3}, IDs stay in [0,F-1] or the zero dummy, and the signed index is
-1 or one of the finitely many slot indices. Prefix ranks are <=P_B.

Anchor ordering slack is <=2R+3 and isolation slack is <=2R+H_star+2. All
index/rank/arity comparisons, with the strictness/equality shifts included, are
covered by P_E+P_P+n+2 or a fixed constant already dominated by beta. Thus
sorting/routing witness values are <=alpha R+beta. These are bounds on values,
not on unevaluated monomial magnitudes, so repeated selects do not inflate them.

### Hypothetical transport and rediscovery

For one lane each masked displacement has absolute value <=2R+b. With three
terms per particle, its unsorted coordinate has magnitude at most

    Q = R + 3(2R+b) = 7R+3b.

This bound uses only the Boolean masks and descriptor bounds, not disjointness,
presence, or prospective success. Coordinate sorting preserves this bound;
its comparator slack is <=2Q+1=14R+6b+1. Every raw witness in the COMPLETE
after-pass is <=

    RawCap(Q) = 14R + 9b + Z+J + n(J+1) + F + 6.

The after-anchor has magnitude <=Q+1 and the routed before-anchor <=R+1.
Consequently prospective near/equality comparisons have slack at most
8R+3b+H_star+3. ID-equality slack is at most F+1. The Boolean own/other/
selected folds add only values <=1. The bound includes a wholly absent lane,
whose downstream raw pass is still fully executed.

### Simultaneous final transport and external sortedness

There are ell lanes and three displacement terms per lane. Without using
isolation or disjointness, the final unsorted coordinate magnitude is at most

    Q_final = R + 3ell(2R+b) = (1+6ell)R + 3ell b.

Sorting preserves magnitude and has slack at most

    2Q_final+1 = (2+12ell)R + 6ell b + 1.

Hit/arity/equality gates and individual displacement registers have already
been bounded. External sortedness slack for coordinates of magnitude <=R is
<=2R+1. Every coefficient of R in this complete audit is at most
alpha=14+12ell; every remaining constant is at most the chosen beta. Hence all
block and relevant external-domain witnesses are <=alpha R+beta, as claimed.

No smallness claim is made about source constants, slot counts or this bound.
The following independent circuit-majorant algorithm also checks every actual
operation and pays every literal coefficient, without relying on these sharper
semantic interval/selection estimates.

## 6. Independently executable circuit-majorant construction

The following conservative coefficient algorithm supplies the promised
explicit dependence. It involves only finite emission and finite integer
arithmetic, so it works for each validated finite source and n. It does not
claim that emission, the resulting constant, or the source is small.

Emit one complete block B in {E,P} with fresh canonical natural input pairs
(p_i,m_i), representing coordinates of magnitude at most R. Put V=R+1.
For each natural input variable give a tag delta_i=1 and a weight h_i=1.
Maintain the invariant

    v_i <= h_i V^{delta_i},       delta_i in {0,1}.

Tags describe dependence of the HEIGHT BOUND on the coordinate magnitude, not
functional dependence of the value: a comparison bit may vary with coordinates
while having tag 0. In this proof, "coordinate-dependent factor" is shorthand
for a factor assigned tag 1; "bounded" means its height bound is independent of R.

For any assignment/comparison expression p=sum_m c_m prod_{i in m} v_i,
including multiplicities in m, calculate

    delta(p) = max over nonzero monomials m of sum_{i in m} delta_i,
    h(p) = sum_m |c_m| prod_{i in m} h_i.

The empty sum has delta=0,h=0; an empty monomial has product 1. Verify that
delta(p)<=1. Section 4 proves this verification succeeds for the actual
emitter for every source,n. For any such p,

    |p| <= h(p) V^{delta(p)}.

Process the actual `Circuit.ops` in topological order:

1. For `integer(p)`, assign both fresh natural components tag delta(p) and
   weight h(p). Canonical positive/negative parts are each <=|p|
2. For `ge(d)`, assign its bit tag 0, weight 1. Assign its slack tag delta(d),
   weight h(d), using slack<=|d|
3. For `boolean(p)`, Section 3 proves the fresh value is 0 or 1. Give it tag 0,
   weight 1. Its actual expression only uses bounded control predecessors;
   the executable audit also checks delta(p)=0

Let H_B be the maximum of 1 and all fresh-variable weights in this emitted
block. Then every natural auxiliary variable of B is <=H_B(R+1). This includes
ALL its hypothetical raw circuits; no substitution of a growing per-step bound
is needed inside this finite calculation. Constants from the source and every
coefficient of every assignment/comparison are paid literally by h(p).

This algorithm is intentionally loose. For example, it may treat a masked,
actually source-bounded ID as coordinate-dependent and may overcount the two
components of a signed pair. Those choices increase H_B but do not its height
degree. It relies neither on an unproved global polynomial identity nor on a
small coefficient assumption. `audit_bounds.py` implements exactly this
recurrence on the existing emitted operation stream and rejects any monomial
with two coordinate-dependent factors.

### Why a fresh-block audit applies to every block of a certificate

A block receives only its n current-coordinate expressions and fixed metadata;
it does not otherwise read old scratch. Each current coordinate is represented
by a single canonical signed pair: initially the external pair, and thereafter
the `integer`/`select` pair emitted by transport/sort, or the same old pair when
a zero-lane block returns its input. Renaming these pairs to the fresh inputs
therefore gives the same local construction. Previous blocks' discarded scratch
does not affect the bound or the operation count.

Set

    H = max(3, H_E, H_P),
    C_majorant(s,n) = (4b+1) H.

These are explicit finite computable integers, determined by the source parser,
n, two block emissions and the recurrence above. C_majorant is an alternative
to the substantially more transparent explicit C in Section 5. Neither
construction assumes that its constant is small or optimal.

## 7. Reset at true block boundaries; target checks

The established endpoint theorem identifies the unique accepted computation
with the true automaton orbit. Each genuine block admits transport of length
at most 2b per particle. Hence every true block-input support and the final
endpoint Y lie in magnitude at most

    R_* = A + 4bT.

Apply the explicit one-block bound alpha R+beta separately to each of the 2T
blocks with R=R_*. Do NOT recursively feed a coarse hypothetical-scratch bound
into the next block's bound: the next true support is bounded independently by
the geometry. This distinction prevents artificial exponential growth.

The external canonical-pair and final endpoint equations introduce no witnesses.
The two external sortedness scans each compare successive coordinates through
`ge(z_{i+1}, z_i+1)`. For either X or accepted Y, the signed difference d has
|d|<=2R_*+1. Its bit/slack witnesses are therefore also <=alpha R_*+beta. This
includes BOTH the initial and target-domain witnesses, even though the target
checks were emitted before the block computations.

All complete-witness coordinates are consequently bounded by

    alpha R_*+beta <= (alpha+beta)(R_*+1)
                   <= (alpha+beta)(4b+1)(A+T+1).

This proves the theorem with the explicit C from Section 5. Independently, the
recurrence in Section 6 yields H(R_*+1) and the alternative C_majorant, with
H>=3 covering the external comparator slacks. Both bounds are recorded in the
executable audit; the main result uses the explicit C.

The accepted-target hypothesis matters. An arbitrary wrong target can have
unbounded external magnitude while A,T stay fixed, and its pre-check sortedness
slacks can then be arbitrarily large. There is no accepted witness in that
case. The theorem makes no contrary claim about deterministic scratch for an
arbitrarily large rejected external target. Internal rejected candidates and
inactive lanes on an ACCEPTED endpoint fiber are fully included.

## 8. Binary length and edge cases

For every nonnegative integer v<=C(A+T+1), its ordinary binary length with one
bit for zero is <=ceil(log_2(C(A+T+1)+2)). Multiplication by the exact count W(T)
gives the displayed total bound. Since source and n are fixed, C,w_E,w_P are
fixed finite constants and W(T)=O_{s,n}(T+1), giving the stated big-O bound.
The claim is about the tuple's summed binary coordinate lengths; the circuit
is fixed syntax for each T, so component ordering is already prescribed. No claim about JSON bytes, delimiters, self-delimiting encodings, or a serialized
container format is included in this definition.

- n=0 or n=1: the pair loop is empty, no lane exists, all blocks are identity,
  and the external order scans are empty. W(T)=0 for every T. The complete
  auxiliary tuple is empty; the theorem is vacuous but valid
- T=0: there are no blocks, but both external domain/order scans and endpoint
  equality remain. W(0)=4max(n-1,0). Acceptance forces Y=X, so the same target
  bound applies. For n=T=0 the unique complete witness is the empty tuple
- Zero raw-slot count alone is NOT grounds to set a block's witness count to
  zero when n>=2. `raw` creates pair-gap signed registers before the source
  family loops, even if no family contributes any slot. Our construction uses
  the actual emitted w_B and H_B, and covers these scratch registers
- Empty or direct-only source families, p=0, and either block order need no
  change. Constants are computed for BOTH block kinds and are direction-free

## 9. Evidence and scope of the standalone audit

The proof above is structural and applies to every validated finite source and
n. Finite executable checks are corroboration and an implementation binding,
not a substitute for this induction.

The normal and optimized audit runs cover the eight available fixture sources,
n in {0,1,2,3}, plus the increment-right n=5 cascade, with both block kinds.
They inspect every emitted operation monomial, compute exact integer majorants,
verify both the explicit affine bound and the circuit-majorant bound, and
evaluate all residuals for sample block assignments (including duplicated
input coordinates, widely separated coordinates and translations of magnitude
10^40). Full accepted endpoint checks exercise both directions, T=0,1,2,
empty/singleton masses, moving and zero-slot sources, and target-domain witnesses.

The audit reads the original packet without modifications or bytecode writes.
It hashes all consulted source/fixture inputs before and after execution and
requires them to match. `audit-receipt.json` and its optimized counterpart record
the concrete constants, counts and test results. None of those finite examples
asserts a practical bound for an arbitrarily large source.
