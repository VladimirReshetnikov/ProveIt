# Reports 35 and 36: finite sandpile certificates and the real-exactness boundary

The finite-prism certificate and real-orthant upgrade pass the scoped proof
review below. The separate [shared-arithmetic packet](sandpile_shared_arithmetic35_36.md)
preserves their complete polynomials while saving **(V+4E) multiplications
and E additions** between two explicitly paid schedules. Its
[independent review](review_sandpile_shared_arithmetic35_36.md) passes.
These are useful cubic certificates with arity growing with the prism; they
do not lower the separately established **84-operation universal polynomial**.

A further consequence is restrictive: a fixed-arity ordinary-input polynomial
whose real-witness existence agrees with natural-witness existence at every
integer input can recognize only a finite or cofinite subset of the positive
integers. Thus a universal compression of these certificates must give up
that real-existence equivalence somewhere. This is a standard consequence of
real quantifier elimination, not a new theorem about sandpile dynamics.

## Authenticated sources and actual review scope

The incoming archives are read as inert data. No archived Python, release
verifier, predecessor builder or historical suite was executed.

| Archive under `docs/incoming/` | SHA256 |
|---|---|
| `Literal_Periodic_Sandpiles_and_Diophantine_Certificates_Package.zip` | `3202b1f0430353a3cd05f15ac6f34e9a797ed931d9a86e3580a110d97b01a12d` |
| `Real_Exactness_of_Binary_Sandpile_Certificates_Package.zip` | `72cfb3a88640020e97f9b6b62c4f7580f97d75ed4f957b8c604536119bcf96ac` |

The root review read Report 35's README, complete composition proof, actual
vertex/edge formulas and complete loader proof. It read Report 36's README,
complete real proof, independent mathematical review and real-certificate
source. The author and independent arithmetic reviewer separately read the
composition/real proofs and reconstructed the original polynomial formulas.
A further independent mathematical challenge found no gap in the real proof
or the fixed-arity consequence below.

The four composition/real proof/source member pins are recorded and checked
by both new helpers. Additional source pins used for this intake are:

| Member | SHA256 |
|---|---|
| `Research_Report35/evidence/loader/LOADER-PROOF.md` | `1791518f521a147b014ca7636910b7775df64fcfe799b6fcb5a0261de4f99d34` |
| `Research_Report36/evidence/real/real_certificate.py` | `073e164feadc6bd4850ed043043889c5755e27c809f3afcdd3b52a14b9a1a299` |

The root did **not** independently reconstruct the multimillion-node physical
graph, every routing seam, all cellular-automaton or universal-machine source
tables, the published program-to-tape encoder, or a giant universal prism.
The loader's source dependencies remain inherited. This intake approves the
stated certificate argument and its conditional composition, with that scope.

## Report 35: what the cubic represents

Fix a nonempty rectangular prism P in the threshold-six lattice Z³, with
natural initial heights and initially stable exterior. All finite additions
are inside P. If its side lengths are a,b,c, put

    V=abc, S=ab+ac+bc, E=3V−S, H=2S.

The H halo sites are the six exterior faces, each with exactly one inward
neighbor. Edge/corner sites outside those faces have no neighbor in P and
need no extra halo constraint. There are W=8V+6E+H natural witnesses and
8V+7E+H displayed nonnegative summands. At each vertex, the category
coordinates define u=k+c and r=k+2c+beta. Five edge indicators and one gap
coordinate encode all possible relative ranks.

A natural zero has binary u, a stable endpoint, and canonical earliest
parallel support-burning ranks. The success and preceding-round failure
inequalities determine those ranks; firing active vertices in increasing
rank is legal. Halo stability closes the finite construction in the infinite
lattice. Conversely, a global stabilization with binary odometer supported
in P supplies all these coordinates. The complete natural zero tuple is
unique when it exists. General nonbinary odometers are outside this theorem.

The literal loader described in the report has stable periodic background
heights in {0,4,5}, periods (1303671936,744955392,1955501604), 3,879,975
primitive vertices and 5,819,945 directed edges. Its one-shot construction
claims the required binary firing property for legal schedules. Halting is
equivalent to finitely many **total** topplings, not to finitely many topplings
at each individual site: the one-shot property also holds along a nonhalting
run. The conditional prism bound is

    V ≤ 5426111451172075939316367360 (n+T+1)²,

where the source run actually halts in T steps. It is not an a priori
computable halting bound. The ordinary-program-to-U15-tape encoding remains
a published dependency, rather than a freshly implemented loader here.
The general three-dimensional simulation context is consistent with
[Cairns's sandpile undecidability paper](https://arxiv.org/abs/1508.00161);
that reference does not verify the report's particular literal graph.

Allowing an unbounded external choice of P therefore supplies a family of
cubics. It does not supply a fixed finite list of witnesses and paid
arithmetic operations for universal unbounded computation.

## Report 36: real zeros become natural

Writing Q for the Report 35 polynomial, the upgrade is

    Qreal = Q + sum_v f_v(k_v+c_v),

implemented by replacing fg with f(g+u). It keeps the witness and displayed
summand counts and exact degree three. The report's collected support and
coefficient height are unchanged; the affected fk and fc coefficients grow
from 2 to 3, while an unaffected kc coefficient already equals 86. The new
packet independently checks the complete coefficient change, support and
height on its three declared fixtures.

The proof does not start by assuming integral ranks. Over the nonnegative
reals, the edge simplex and weighted residual squares force a single
indicator, because their five allowed difference regions are disjoint.
The vertex category equation and new fu term imply f+u=1 and fu=0, hence
u is 0 or 1. Inactive ranks are zero and active ranks are at least one.

For an active rank above one, c is positive. Its success/failure conditions
force B−A≥1, hence an adjacent active vertex has rank exactly one smaller.
Repeated predecessors strictly decrease rank and cannot revisit a vertex.
Finiteness forces the chain to terminate at rank one. All active ranks are
therefore integral and bounded by the support size; k,c and every remaining
coordinate then become natural. Thus the entire nonnegative-real zero set
is exactly Q's natural zero set, empty or a singleton for the fixed prism.
The archived linear-programming searches are unnecessary for this argument
and were not rerun.

As an exact regression, the old singleton polynomial at initial height 1
has the fractional zero z=0, ell=5, f=5/6, k=1/6, c=beta=g=h=0 and every
halo gap 29/6. The fresh helper verifies Q=0 and Qreal=5/36, in both paid
schedules. This is distinct from the three genuine legal stabilizations
used to test the complete zero maps.

## General shared arithmetic and bounded complete evidence

With d the rank difference and g=sigma+2, the five weighted edge squares
equal

    S*d² − 2*d*(g*(hi−lo)+(pos−neg)) + g²*(lo+hi) + neg+pos,
    S=lo+neg+eq+pos+hi.

This is an all-value polynomial identity. The four comparison counts can
share S by subtraction, without imposing S=1. The vertex identity
(f+k)beta+(f+k)h=(f+k)(beta+h) supplies the other saving. Signed moment
intermediates do not need to be individually nonnegative: equality of the
full polynomial transfers both original zero-set theorems.

The author and independent reviewer check 24 complete cubic arrays: three
prisms, base/real variants, direct/moment schedules, and natural/paid-positive
coordinates. All 8,788 gates and all supplied ports are live. The independent
review compares 38,012 collected coefficient entries and all final outputs,
and verifies 24 complete zero tuples from three distinct legal stabilizations.
Natural base costs are 54→53, 143→136 and 831→763 operations. These savings
are relative to the declared already-shared direct schedule, not to an
uncounted expansion or an asserted optimum.

Since u is shared, the real upgrade costs V extra additions in either new
schedule. Report 36's original affine evaluation convention instead charges
coefficient-1 multiplication; its ledger is a different convention.
Representing each natural coordinate w by a positive integer p with w=p−1
costs exactly W subtractions. For real coordinates this transfers the theorem
only to the box p≥1 componentwise, not to every p>0.

Both author and independent reviewer receipts passed fresh normal and
optimized replays from `/`. Their source and receipt pins are preserved in
the committed companion packets. No tiny fixture is presented as a literal
universal sandpile instance.

## Why real-exact existence cannot survive a fixed-arity universal collapse

Fix a polynomial F(n,y) with finitely many real witness coordinates y and
fixed program numerals. Suppose for every positive integer n that

    exists y in R_≥0^m: F(n,y)=0
        iff exists y in N^m: F(n,y)=0.

Apply real quantifier elimination to the left side, with n a real free
variable. It gives a Boolean combination of signs of finitely many univariate
polynomials. Past all their real roots, every sign is constant, so the
Boolean formula is constant. The recognized positive-integer set is therefore
finite or cofinite. The same argument covers any fixed finite polynomial
system and semialgebraic witness domain, including y>0 or y≥1.
This deduction uses the projection/quantifier-elimination theorem stated in
[Basu, Theorem 2.1](https://www.math.purdue.edu/~sbasu/raag_survey2011_final.pdf).

Agreement of existence only at integer inputs already suffices; equality
of whole real and natural fibers is stronger than necessary. In particular
even-number recognition is impossible under these premises, so a universal
ordinary-input representation cannot retain them for every fixed program.

An unbounded external prism choice is outside the fixed-arity premise.
Integer-only packing may introduce extra nonintegral real zeros and is not
excluded. Neither rational-only exactness nor external nonsemialgebraic
preprocessing is covered by this argument. An integer-quantified outer
selector also lies outside the all-real witness projection. The consequence
is a design constraint on a proposed collapse, not a contradiction of either
finite-prism report and not a lower bound on the 84-operation construction.

The next useful sandpile step is consequently a paid integer-only packing
interface for the unbounded prism family, with its input encoding and new
real zeros explicitly separated from the finite certificate's real theorem.
