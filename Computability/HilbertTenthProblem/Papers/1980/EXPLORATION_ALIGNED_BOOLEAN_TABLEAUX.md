# Aligned Boolean tableaux with implicit row geometry

This note continues `EXPLORATION_FINITE_UNIVERSAL_HISTORY_VERIFIERS.md`.
It proves conditional arithmetic components and accounts for their operations.
It does not construct a universal certificate below 90. In particular,
the finite zero-exterior Rule 110 runs below are not substituted for Cook's
prescribed periodic-background simulation theorem.

## 1. Geometry and notation

Let R=4. Assume the already verified geometry equations

    q=v*d, Q=q*q, W=v*v, Q-1=h*(W-1),

with positive variables and q>1 a power of two. Then, for integers m,t>=1,

    W=4^m, Q=W^t, h=sum_(j=0)^(t-1) W^j.

The separate schedule costs six operations: three multiplications for
v*d, q*q, v*v; two subtractions for Q-1,W-1; and one multiplication
h*(W-1). Reuse with a complete outer construction can change that count.
All counts below similarly concern the displayed components, not an
unaccounted aggregate universal system.

A row contains m base-four digits. For a list of t rows b_j, let
B=sum b_j W^j. In this note a Boolean row or plane has all its base-four
digits in {0,1}. Unless explicitly lifted in Section 5, these integers
are allowed to be zero; the published positive-unknown convention is
not silently imposed on them.

## 2. Temporal alignment costs four operations

Let B,Y be the center and successor history planes, and I,F the initial
and final rows. Assume

    0<=B,Y<Q, 0<=I,F<W.

The equation

    I+W*Y = B+Q*F                                      (T)

forces exactly the intended overlap. In base W, the low digit on the
left is I, the next t digits are the t rows of Y. On the right the low
t digits are the rows of B and the final digit is F. Thus B starts with
I, its rows 1,...,t-1 are Y's rows 0,...,t-2, and Y ends with F.
Conversely every sequence of t transitions has this decomposition.

The exact arithmetic is WY=W*Y, QF=Q*F, left=I+WY,
right=B+QF: two multiplications and two additions. The equality is free.
The displayed bounds are necessary: without them the equation is not a
unique decomposition into rows. They need not all be paid separately.
With nonnegative B,Y,F and the existing Y<Q, imposing the one-addition
positive bound I+alphaI=W gives I<W and

    Q*F=I+W*Y-B <= (W-1)+W*(Q-1)=W*Q-1.

Thus F<W follows. The equation supplies no input or halt semantics for
I and F. A conditional schedule that adds temporal alignment to existing
history bounds must therefore include four alignment operations and this
one initial-row-bound operation.

## 3. Spatial alignment with a checked zero halo

Suppose every row of B and Y has first and last digit zero. For m>=2
this is a zero halo of one cell at each edge; m=1 is also meaningful but
forces every row to be zero. Define neighboring-cell planes by

    A=4*B,       4*C=B.                                (S)

These cost two constant multiplications and free equality tests. They
give the exact left and right neighbors of each cell with zero exterior.
The bit that would cross a row boundary in either shift is zero by the
halo assumption. Also A<Q and C<Q, and both are Boolean planes.

Combining (T), (S), and the seven-operation local Rule 110 relation

    B+C=X+2D, A+D=Z+2E, Y+E=X+D

therefore verifies all t transitions of a single finite array. If the
array is extended by zeros outside its spatial interval, the same rows
are actual infinite-line Rule 110 configurations: cells immediately
outside the left edge see a zero right neighbor, and all other exterior
updates stay zero. This is a theorem about a finite zero-exterior run.
It does not say that the corresponding halting-pattern problem is the
universal problem established by the cited periodic-tail theorem.

### The halo has an explicit support mask

Supply V with 4*V=W, so V=4^(m-1), and define

    edge=h*(1+V).                                      (H)

For m>=2, edge has digit one exactly at the first and last column of
each row. For m=1 those positions coincide, and edge=2h. The condition
of zero halo can be stated as no common binary 1-bit between B and edge,
and between Y and edge, when m>=2. At m=1 the coefficient two would
test the wrong bit; therefore either enforce m>=2 or use the equivalent
two tests against h and V*h separately for all m. A convenient sufficient
width condition is v=2+v_extra with v_extra positive: since v is a power
of two, this implies v>=4 and m>=2, at the cost of one addition.

Constructing (H) costs three operations: 4*V, 1+V, h*(1+V).
The bit predicates and the width guard are additional costs. This
distinction prevents a coincident-mask error at width one.

Before width/range/digit/input/halt costs, the separate geometry,
temporal alignment, spatial alignment, local rule, and combined edge
mask schedules cost 6+4+2+7+3=22. Adding the simple width guard above
makes 23. This is a conditional inventory, not a proposed complete
23-operation verifier or a bound of 43+23 for universality.

### Rule-specific improvement: only the first-column mask is needed

The preceding two-edge design can be improved for Rule 110. Assume only
that B's first column is zero in every row, and keep A=4B, 4C=B and A<Q.
At a row's first cell the left-shift plane A may contain the previous
row's last bit instead of the intended exterior zero. But its center
bit is zero, and Rule 110 satisfies f(a,0,c)=c independently of a.
The discrepancy therefore has no effect. At a row's last cell C is
zero, since the next row starts with zero (or the global shift ends).
Thus all local updates still agree with a zero exterior.

In fact the last-column zeros follow automatically. At such a cell,
f(a,b,0)=b, so temporal alignment makes every pretransition last-column
bit equal. The bound A=4B<Q forces the highest digit of B to be zero,
and hence every last-column bit is zero. The first-column bit of Y's
final row may be one; it need not be forbidden because there is no
further transition to check.

Consequently the combined edge mask (H) and its width guard can be
replaced by a single first-column mask h. If m=1, this mask forces B=0,
so a positive supplied B excludes that degenerate width automatically.
The conditional inventory becomes 6+4+2+7=19 before bit/range/support
tests and input/output; the just-described bound on I adds one operation.
This is an improvement to the conditional components, not a complete-system
count.

### Only five planes require independent bit tests

It is sufficient to require B,D,X,E,Z Boolean. The equations A=4B and
4C=B make A and C Boolean. The first two local equations recover
d=bc and e=abc digitwise. The third gives

    Y=X+D-E,

which is automatically a Boolean plane because the resulting digits
are the Rule 110 outputs. No independent Boolean test on Y is needed.

The entire collection of ranges follows from a single positive bound

    A+(B+C)+alpha=Q, alpha>0.

The register B+C already occurs in the local schedule, so adding this
bound costs two additions. Indeed D<=(B+C)/2, X<=B+C,
E<=(A+D)/2, Z<=A+D, and Y=X+D-E<=X+D<=B+C. Each is below Q.
This range argument assumes only the supplied nonnegative or positive
domains and the displayed integer equations. It does not require the
bit predicates or the recovery of the local products.

For canonical histories with a zero last column, B<Q/12; hence
A+B+C=(4+1+1/4)B<7Q/16, and the new alpha can be chosen positive.

A useful variant of the support predicate is to require both B and B+h
Boolean, with B+h<Q. Since each raw digit of their sum is at most two,
no base-four carry occurs: Booleanity of B+h is equivalent to absence
of overlap at the row starts. The range follows from B<Q/4 and
h< Q/3. This uses an additional supplied plane and one addition, and
can be combined with a uniform bit test on six planes. Its packing
costs must be included in the full schedule.

### General boundary sequences cost more

For reference, let G0 and Gend be the actual first/last-column bits of
B, compressed to row starts, and Lext,Rext the desired exterior-neighbor
bits, also at row starts. The exact shift identities are

    A+W*Gend = 4*B+Lext,
    4*C+G0 = B+W*Rext.                                (Sgen)

They cost four operations each before any sharing. Merely supplying
G0,Gend does not prove that they extract B's edge bits. Their support and
extraction must be checked. In particular, leaving them free can admit
wrap-around or arbitrary boundary neighbors. This is why the zero-halo
case is cheaper only after the halo predicate is actually established.

## 4. Input and output interfaces

### Raw input via two Boolean tracks

For a multitrack machine with a four-symbol input alphabet, two Boolean
initial-row planes I0,I1 can receive a raw nonnegative query x by

    x=I0+2*I1.                                        (I)

Each digit on the right lies in {0,1,2,3}, so there are no carries.
Uniqueness of base-four digits proves that I0 and I1 are exactly the low
and high bits of each base-four digit of x. Conversely such planes exist
uniquely for every x. This costs two operations, with the plane bounds
and digit predicates still charged separately.

This avoids an unjustified binary-to-base-four bit-spreading map. It is
directly suitable for a multitrack Turing or tile model designed to read
four-symbol digits. Rule 110 has only one bit at each cell, so using (I)
there requires paired-cell lanes or a verified input transducer. The
source's universality theorem does not supply that arithmetic interface
for free.

An explicit possible delimiter position has a similarly short geometric
description. Supply positive s,d0,P,delta,zeta satisfying

    v=s*d0, P=s*s, x+delta=P, P+zeta=W.                 (Idelim)

Since s divides the power-of-two v, P is a power of four. The inequalities
x<P<W put a single delimiter at a row position beyond every nonzero
input digit and before the end of the row. These four displayed
computations cost four operations. A distinct Boolean delimiter track
can have value P. A machine can scan until that marker and ignore the
possible leading zero input digits. Equating this marker to an actual
initial track, reserving room for a head marker and workspace, and
adapting to a spatial halo remain part of the final boundary design.

### A fixed final prefix is inexpensive; a freely placed event is not

If a tile machine is designed to return its head to a fixed column on
halting, the required final prefix can have the form

    F=p+4^k*Tail,

for fixed k,p: one multiplication and one addition, plus the tail's
range. This is an interface a fixed machine can be designed to have.
It is not an assertion about the location of Cook's halting glider.

For a fixed pattern p of k cells at an existentially chosen position,
the natural decomposition is

    F=Prefix+Zpos*(p+4^k*Tail), 0<=Prefix<Zpos,

with Zpos a certified power of four and enough remaining row width.
The displayed expression costs four operations, in addition to obtaining
Zpos, the prefix/tail bounds, and zero-coordinate handling. A finite
pattern-recognition theorem must include these obligations.

## 5. Strict positivity: an exact affine lift and its paid headers

Boolean history planes can be identically zero. Requiring every such
plane to be a supplied positive unknown loses valid histories unless
an explicit witness transformation or padding argument is supplied.

There is an affine lift that preserves the seven-operation local schedule
without changing any of its equalities. Given 0<=A,B,C,Y,D,X,E,Z<Q, put

    Aplus=A+2Q, Bplus=B+Q, Cplus=C+2Q, Yplus=Y+Q,
    Dplus=D+Q, Xplus=X+Q, Eplus=E+Q, Zplus=Z+Q.           (P)

All eight lifted values are positive. Their header coefficients in the
order (A,B,C,Y,D,X,E,Z) are (2,1,2,1,1,1,1,1). These satisfy the same
three linear relations:

    1+2=1+2*1, 2+1=1+2*1, 1+1=1+1.

Consequently the original and lifted local equations are equivalent.
The local schedule still uses seven operations when the lifted values
are supplied directly. By contrast, shifting all eight planes by Q
would require two explicit Q corrections in the first two equations.

This is only a local positivity improvement. Each lifted plane must
have its specified leading base-four digit (one or two) and Boolean
lower digits, with no higher digits. A support mask alone can forbid
unwanted 1-bits but cannot force a leading 1-bit to be present. If the
unlifted values are explicitly materialized, all eight lifts/unlifts
cost operations; if they are not, the header and interval tests and
the modified tableau alignment equations must be counted. No free
positive-domain conversion is claimed.

Another possibility is to enforce fixed valid padding records. The
three local triples 111,010,100 make each of the eight corresponding
planes have at least one zero and one one, including the auxiliaries.
This suffices to ensure both a plane and its Boolean complement are
positive. But those padding records must be placed in the common
tableau, and their input/boundary interactions isolated. They are not
independent records that can simply be appended while retaining (S).

For the improved five-plane construction, an even shorter sufficient
condition is an interior occurrence of 1110 in the initial row. The
local triple 111 makes D and E positive; the following triple 110 makes
X and Z positive; B is already nonzero. Thus a correctly specified
initial row containing that motif handles every potentially zero local
auxiliary without an affine lift. It must appear at a permitted location
in the actual simulation, not be inserted at an uncontrolled boundary.
In particular, placing a fixed nonzero prefix immediately beside the
left halo bounds the possible running time and is not a valid universal
padding argument.

## 6. Noncircular preliminary bounds for the proposed six-plane packing

This paragraph requires only positive supplied integers and the arithmetic
equations; there is no assumption yet that Q or W is a power of four.
From 4C=B, A=4B and A+B+C+alpha=Q, positivity gives

    B>=4, C>=1, A>=16, Q>=22.

In particular q>1 follows from Q=q^2. The geometric equation rules out
v=1, so W=v^2>=4 and

    0<h=(Q-1)/(W-1)<Q/3, 0<B<Q/4, 0<B+h<Q.

The integer local equations and positivity give all the ranges proved
in Section 3, without interpreting digits. Thus each of the six fields
B,D,X,E,Z,B+h is strictly below Q. Their ordinary base-Q Horner
concatenation P lies strictly between zero and Q^6. The bound on I and
the temporal equation imply F<W at this stage as well.

For the proposed special-mask packing, set

    n0=Q^6, Lbig=Q^8, 3*lambda=Lbig-1,
    r0=(Lbig-P)*(Lbig-1)+2*lambda.                       (K)

This note does not prove the special-mask/binomial equivalence; that is
a separate component. Its numeric interface is nevertheless explicit:
P<n0 and Q>1 imply Lbig-P>n0, hence r0>n0. Since P>=1,

    r0 <= (Lbig-1)^2+2*(Lbig-1)/3 < Lbig^2=Q^16
       < Q^18=n0^3.

Also n0>=64. These are stronger than the preliminary bounds required
by the retained 43-operation first-Pell subsystem. They hold before
that subsystem proves the power-of-two and central-binomial conclusions.
If its no-carry consequence then proves Booleanity of the six packed
fields, the geometry and first-column arguments apply in the order
given above. The bit predicates must not be used to establish (K)'s
preliminary size bounds.

In a canonical Boolean construction, Q is a power of four. Booleanity
of B and B+h gives B's unit digit zero because h's unit digit is one.
Consequently P is even, Lbig is even, and (K) makes r0 even. This is
the parity needed by the retained half-parameter Pell necessity proof;
that proof does not require it in the soundness direction.

Canonical nonzero histories with the specified 1110 motif make the
five local supplied planes positive, while B+h is positive because
h>0. An initial nonzero finite Rule 110 configuration also has a
rightmost one that persists: at that location f(a,1,0)=1, and all
cells farther right remain zero. Therefore the final row F and the
successor history Y are positive. The possible zero-plane issue is
handled for these conditional histories rather than assumed away.

## 7. What remains before an operation comparison

The subsequent round39 integration now supplies the common arithmetic
implementation, preliminary bounds, and all positive witnesses described
below. Its exact 86-operation schedule and complete decidable relation are
proved in `EXPLORATION_RULE110_FIXED_INPUT_BOUND.md`; the separate periodic
mask proof is `EXPLORATION_PERIODIC_DIGIT_MASK.md`. The remaining universal
input and halt interface is a distinct obligation. The following inventory
records the requirements at this component's original stage.

The primary unresolved obligations are a single consistent arithmetic
implementation of digit/range/support predicates; a fixed finite
universal model compatible with the initial and final interfaces;
strictly positive witnesses for all auxiliary fields; and a packing
whose preliminary bounds imply the retained first-Pell hypotheses.

The retained 43-operation subsystem requires n>=64 and
n<=r<2n^3 before its exact-index argument. Its canonical positive
construction also needs even r, n a power of two, and central-binomial
divisibility by n^2. A new tableau code must prove these facts in the
correct order. None follows from the geometry and local equations alone.

The exact components here are intended to make those remaining costs
visible, and to distinguish a promising architecture from a complete
universal certificate.

## 8. Focused exact regression

Run `python -X utf8 Papers/verification/explore_aligned_boolean_tableaux.py`.
The companion JSON records 5,050 proposed Boolean histories at widths
2-5 and heights 1-3, of which 2,513 satisfy the shared numerical bound
and 16 satisfy temporal alignment. The checker compares the integer
equations with direct cell-by-cell zero-exterior evolution, including
the harmless row-start wrap and derived last-column zeros.

It additionally checks 682 first-column masks including width one,
768 positive affine lifts, 4,096 exact raw-input decompositions, and
eight canonical positive histories through height eight. The last group
checks the 1110 motif, initial/final row bounds, the shared numerical
bound, six-plane concatenation, and the polynomial packing's even parity
and preliminary Pell ranges. It does not test the separate binomial-mask
equivalence and does not claim a universal initial-input interface.
