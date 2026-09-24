# A counted 174-operation bounded ant history

The two ternary toggle cells do give an exact finite-history interface for
Langton's ant. With all field bounds, board edges, positive adapters and
initial/final words charged, the construction below uses **174 operations:
72 multiplications and 102 additions/subtractions**, five positive parameters,
61 positive unknowns and 48 equations. The local rule itself accounts for
only six additions.

This is a bounded-board endpoint relation, not a smaller universal
certificate. In particular, its initial parameter is an already encoded
board word. The periodic-background compiler, the finite input perturbation
as a function of the raw query, and an observable for simulated halting are
additional obligations. Sections 9-10 give concrete interfaces and costs
for those obligations rather than identifying them with free numerals.

The full arithmetic and fresh source-polynomial comparisons are in
`../verification/explore_ant_checkerboard_history.py`; the adjacent JSON is
its reproducible receipt. The construction uses the previously proved
49-operation base-three component, with its input length replaced by q^4.
It does not require a new Pell lemma.

## 1. Exact endpoint relation and layout

The five parameters are arbitrary positive integers

    InitialMemoryPlus, FinalMemoryPlus, InitialHead,
    FinalHead, FinalSignPlus.

Decode I=InitialMemoryPlus-1, FM=FinalMemoryPlus-1 and
FZ=FinalSignPlus-1. The relation asserts the existence of an odd width
w>=3, an even height h>=2 and a positive number of steps t such that:

* I and FM are ternary Boolean words on the w by h board, flattened in
  row-major order, with x increasing east and y increasing south.
* InitialHead=3^j is a board position with j even. The initial heading is
  north. FinalHead is the final position, and FZ is either zero or FinalHead.
* The ant performs exactly t ordinary turn/write/move steps, staying on
  the board throughout. Its final incoming heading has sign FZ/FinalHead:
  north/south on a black square, east/west on a white square.

Here a square is black when x+y is even. Since w is odd, this is also the
parity of its flattened index. Color zero turns right and becomes one;
color one turns left and becomes zero. The finite board has no special
reflection or wrapping rule. The certificate rejects any history that
moves beyond an edge. Every finite ant trajectory can be placed inside a
sufficiently large board of this shape after translating the initial
configuration and rotating its initial heading. Such a translation changes
the encoded input; it is not a free raw-input conversion.

Write W=3^w, Q=W^h and q=Q^t. Each history field has q as its bound and
contains t consecutive board words. The exponent at site (x,y) and time s
is x+wy+whs. The area wh is even, so checkerboard parity does not change
when a time block is added.

## 2. The two local toggle cells and four outgoing directions

Mask A,B,C,D,E,F,G and four outgoing direction fields GE,GW,GN,GS as
ternary Boolean words. A and B are the colors before and after the visit.
C is activity, Z is the incoming sign, and Zp is a provisional outgoing
sign. Compute

    Ce=GE+GW, Co=GN+GS, C=Ce+Co, Zp=GW+GN.          (1)

The static masks below permit GE,GW only at black sites and GN,GS only at
white sites. Since C is Boolean, (1) has no digit carry and permits only
one outgoing direction at any active site. Thus Zp is also Boolean and
is supported on C.

The two cells are

    C=D+E,       A+E=B+D,                            (2)
    D=F+G,       Z+G=Zp+F.                          (3)

Each pair costs three additions. Once Z is known to be Boolean and
supported on C, all raw sides have digits at most two. They are exact
digit equations in radix three. The unique solutions are

    D=A*C, E=(1-A)*C, B=A xor C,
    F=Z*D, G=(1-Z)*D, Zp=Z xor D,

where these displayed products describe digitwise Boolean semantics,
not uncounted arithmetic operations in the certificate.

At a black square the incoming axis is vertical, sign zero is north and
sign one is south. Hence the outgoing horizontal sign is Z xor A.
At a white square the incoming axis is horizontal, sign zero is east and
sign one is west. The outgoing vertical sign is 1 xor Z xor A. Accordingly
Zp=0/1 is east/west at black sites and south/north at white sites. This
explains the single expression Zp=GW+GN. The geometry of an ant step flips
both the heading axis and the position parity, so the convention remains
valid at every time.

Z does not need an independent Boolean mask. Its temporal equation and
the unique-head induction below prove its Booleanity before (3) is used.
A separate numeric bound 0<=Z<q is retained and charged.

## 3. Geometry and the four forbidden masks

Supply positive W,Q,q,uW,uQ,Gy,Gt and assert

    Q=W*uW, q=Q*uQ,
    Q-1=Gy*(W-1), q-1=Gt*(Q-1).                    (4)

These relations cost seven operations, including the three subtractions.
Add positive WidthOdd,HeightEven,K,Wp and

    W=8*WidthOdd+3,
    Gy=(W+1)*HeightEven,
    q-1=8*K,
    W=3*Wp.                                        (5)

Before power recovery, W>=11 and q>=Q>=W, so the base-three kernel has
a nontrivial positive input length. Once q is a power of three, its
positive divisors Q and W are powers of three too. The divisor identities
in (4) imply Q=W^h and q=Q^t. The first condition in (5) forces w odd;
its positive slack excludes w=1. Reducing Gy=1+W+...+W^(h-1) modulo W+1
shows that its divisibility by W+1 forces h even. Therefore

    WidthOdd=(W-3)/8,
    HeightEven=(Q-1)/(W^2-1),
    K=(q-1)/8, Wp=W/3.

K has digit one at every even global exponent; Odd=3*K has digit one at
every odd exponent. Compute

    VH=Gt*HeightEven, Eedge=Wp*VH,
    Nedge=Gt*WidthOdd,
    Sbase=3*Nedge+Gt, Sedge=uW*Sbase,

    ForbiddenE=Odd+Eedge, ForbiddenW=Odd+VH,
    ForbiddenN=K+Nedge, ForbiddenS=K+Sedge.           (6)

VH marks the black first-column sites, and Eedge the black last-column
sites. Nedge marks the white first-row sites. Since h is even, its last
row is odd; Sedge marks exactly that row's white sites. Each edge part is
disjoint from its wrong-parity part. Every forbidden word is consequently
Boolean and smaller than q.

Equations (5), the products in (6), and the four final sums cost seventeen
operations in total. Additionally compute and mask the four words

    TestE=GE+ForbiddenE, TestW=GW+ForbiddenW,
    TestN=GN+ForbiddenN, TestS=GS+ForbiddenS.         (7)

These are four additions. Because the two summands are Boolean, the
Booleanity of (7) is exactly the required disjointness. This proves the
parity and edge restrictions; it does not assume away carries in an
unbounded field sum.

## 4. Spatial and temporal wiring

Use four products for the spatial shifts:

    SE=3*GE, 3*SW=GW, SS=W*GS, W*SN=GN.             (8)

SW and SN are supplied nonnegative quantities, with positive adapters
charged below. The four masks ensure that these are shifts within the
board. An east/west move does not cross a row edge, and a north/south
move does not cross a board or time-block edge.

Compute

    NextC=(SE+SW)+(SN+SS), NextZ=SW+SS.              (9)

This costs four additions. West and south have sign one on the target
square; east and north have sign zero. The head equations are

    C+q*FinalHead=InitialHead+Q*NextC,
    Z+q*FZ=Q*NextZ.                                 (10)

They cost seven operations. The memory equation is

    A+q*FM=I+Q*B,                                  (11)

costing four operations. Finally impose

    I+BoundInitial=Q,
    InitialHead+BoundHead=Q,
    q=InitialHead*HeadQuot,
    InitialHead=HeadRoot^2,                         (12)

with positive slacks and quotients. These are four operations. After
q is a power of three, InitialHead is a power of three of even exponent,
and (12) places it on the board. The square is necessary: an arbitrary
power of three would not establish the initial checkerboard convention.

## 5. Bounds, one common mask, and complete arithmetic

The fifteen distinct masked fields are

    A,B,C,D,E,F,G,GE,GW,GN,GS,TestE,TestW,TestN,TestS.

For each of these and for Z assert field+BoundField=q, with a positive
slack. These sixteen additions give all numeric bounds before the mask
or any prime-power conclusion. The raw supplied nonnegative quantities
are A,B,GE,GW,GN,GS,D,E,F,G,Z,SW,SN. Represent each by a positive supplied
value minus one. Together with the three parameter adapters I,FM,FZ,
this costs sixteen subtractions. C and the four Test fields are computed
from nonnegative quantities and need no further adapters.

Append D once more to the fifteen-field list and form the sixteen-field
Horner packing P in radix q. This costs fifteen products and fifteen
additions. The established field bounds prove 0<=P<q^16 before decoding.
The repeated D needs no new bound or supplied variable.

Compute

    q2=q*q, q4=q2*q2, q8=q4*q4, L=q8*q8,
    D0=9*L, pP=3*P, gap=D0-pP, r=gap-1.             (13)

These eight operations, together with the retained 43-operation kernel,
are the 49-operation theorem in `EXPLORATION_BASE_THREE_PELL_KERNEL.md`
with its q replaced by the integer q^4. No prime-power assumption is
needed for this substitution. That theorem proves q^4, and therefore q,
is a power of three, and that all sixteen concatenated fields are ternary
Boolean. Its soundness implication does not require parity.

| Part | Operations |
|---|---:|
| Positive adapters | 16 |
| Extent geometry (4) | 7 |
| Checkerboard and forbidden masks (5)-(6) | 17 |
| Four disjointness sums (7) | 4 |
| Initial bounds, power and parity (12) | 4 |
| Local cells and head sums (1)-(3),(9) | 14 |
| Spatial shifts (8) | 4 |
| Head time wiring (10) | 7 |
| Memory time wiring (11) | 4 |
| Sixteen field bounds | 16 |
| Sixteen-field packing | 30 |
| Mask, powers and Pell kernel | 51 |
| Total | 174 |

The checker independently constructs all 48 source polynomials, compares
them with all 174 acyclic primitive instructions, and checks the same
single penultimate Pell residual adjustment as the inherited kernel.
It records 72 multiplications and 102 additions/subtractions. Fixed
numerals are free inputs; multiplying by one of them is counted.

## 6. Soundness without a hidden unique-head promise

First decode the geometry and bounded mask, in that order. Each source
board of C is Boolean, and the direction fields obey the static masks.
Their sum is C: no base-three carry occurs because the raw sum of the
two permitted directions is at most two. The four shifts in (8) are
therefore boardwise spatial shifts even before head uniqueness is known.

Reducing the first equation of (10) modulo Q gives the initial C board
equal to InitialHead. It has exactly one head. Its outgoing route is
unique, so the first NextC board is a single power of three, still less
than Q because outward moves are forbidden. In particular it produces
no carry into the following time block. Subtract this established board
identity from (10), divide mathematically by Q, and repeat. This proves
one head on every source board and identifies FinalHead with the last
shifted head. It also proves NextC<q and FinalHead<Q. This induction
does not rely on a global bound NextC<q before uniqueness is established.

NextZ is a subword of NextC. The second equation of (10), together with
the already charged bound Z<q, gives the initial Z board zero and each
following Z board equal to the previous NextZ board. Hence Z is Boolean
and supported exactly as a sign on the unique head. FZ is zero or
FinalHead. Now the carry-free local equations (2)-(3) can be decoded;
they yield precisely the eight ant transitions described in Section 2.

Finally A and B are bounded Boolean words. Equation (11), the bound I<Q,
and nonnegativity of FM give its ordinary base-Q digit recurrence. It
derives I's Booleanity, equates each later old-color board to the previous
new-color board, and identifies FM with the final Boolean board. No
Boolean promise on the five arbitrary positive parameters was used.

## 7. Parity and all-positive necessity

Conversely, take any bounded history in the endpoint relation. Populate
the fields with its colors, unique head, outgoing routes and the Boolean
solutions of the two local cells. All source equations then hold. Each
field is smaller than q, and each supplied nonnegative field becomes
positive after adding one. Every range slack is positive. Equations
(4)-(6) have the displayed positive integer witnesses because w>=3 is
odd and h>=2 is even. The power and square witnesses in (12) are positive.

It remains to check the parity needed by the positive Pell converse.
From (2), A+B+D+E is even as an integer. From (3), F+G=D. The four
direction fields have sum C; the four Test fields have sum C plus the
sum of the forbidden fields. Therefore the sum of the fifteen unique
fields is congruent to C+D+sum(Forbidden) modulo two.

In (6), the horizontal edge contribution VH*(1+Wp) is even. The vertical
edge contribution is congruent to Gt, because uW is odd and

    Nedge+Sedge = Gt*WidthOdd
                   + uW*Gt*(3*WidthOdd+1).

The wrong-parity contributions occur in pairs. Thus sum(Forbidden)=Gt
modulo two. There is one head on each of t source boards, so C=t modulo
two; and Gt=1+Q+...+Q^(t-1)=t modulo two. The fifteen-field parity is
exactly D. Appending D makes the sixteen-field packing P even because
q is odd. Equation (13) then makes r even as well.

The Boolean mask has the required exact three-adic valuation, and every
hypothesis of the existing positive Pell converse is now satisfied. Its
explicit canonical construction supplies all seventeen positive Pell
witnesses. This completes both directions of the endpoint relation.

## 8. Finite evidence and its scope

The independent geometry check evaluates 27 width/height/time choices
against literal checkerboard and boundary arrays. The local check covers
all six Boolean triples (color,activity,sign) with sign<=activity and
proves unique auxiliary outputs. The full outer regression attempts
840 finite prefixes and verifies all equations for 305 that stay within
their boards, including five prefixes on an initially blank board.
It independently computes the three-adic valuation of each resulting
central binomial coefficient from factorial valuations; it does not
merely trust the Boolean-field construction.

These are bounded tests of the complete outer equations and the exact
kernel inputs. The general argument above supplies arbitrary-integer
soundness and positive Pell necessity. The regression does not instantiate
the enormous Pell tuples, and genuine sample histories do not by themselves
prove rejection of every malformed integer tuple.

## 9. A paid periodic-background generator

The primary source contract is recorded in
`EXPLORATION_TOGGLE_ROUTER_UNIVERSALITY.md`: a fixed periodic hardware
background plus a finite input-dependent perturbation. It is compatible
with bounded visited rectangles, but that fact does not construct their
initial arithmetic words for free.

Here is an explicit generator for a fixed u by v tile with bits b_ij.
Choose w=1 modulo u and h=0 modulo v, in addition to the existing odd/even
conditions. These congruences still allow arbitrarily large boards. Put

    r_j=sum_(i=0)^(u-1) b_ij*3^i,
    A_tile(W)=sum_(j=0)^(v-1) r_j*W^j,
    B_tile(W)=sum_(j=0)^(v-1) b_0j*W^j.

The r_j are fixed free numerals. Supply positive Hx,Hy and assert

    Wp-1=(3^u-1)*Hx,
    Q-1=(W^v-1)*Hy.                                 (14)

All powers of variable W in (14) and the tile polynomials must be
constructed. Then the actual periodic board is

    Background=Hy*(Hx*A_tile(W)+Wp*B_tile(W)).         (15)

The last term supplies the one extra column after the repeated horizontal
tiles. This avoids incorrectly requiring an even tile width to divide
the already odd board width. Formula (15) has no overlapping digit sums.

Using an addition chain of length ell(v) for W^v and ordinary Horner
evaluation of the two fixed-degree polynomials gives the conservative
additional budget ell(v)+4v+4: two operations for the first equation in
(14), ell(v)+2 for the second, at most 4(v-1) for the two polynomials,
and four for (15). Constant or zero coefficients and already available
powers can reduce this bound. Linking I=Background costs only a free
equality for the unperturbed background. That system has no variable
simulated input and is not a universal recognizer.

A finite input perturbation may be written abstractly as

    I=Background+Anchor*Delta_input(W).               (16)

Once Anchor and the signed polynomial Delta_input are faithfully
constructed, (16) costs one product and one addition. Their construction
is not included in those two operations. Input-dependent placement,
positional dilation, background phase, and the prescribed initial head
within the perturbation are still paid work. The source's computable
finite-pattern map is not an uncharged polynomial or numeral in the raw
query. No universal total is inferred from (14)-(16).

## 10. Endpoint words versus a halting observable

The 174-operation component already verifies a complete final board and
head when those are supplied as parameters. If they are left existential,
it verifies an arbitrary finite prefix; that alone cannot recognize
simulated halting. The ant never loses its head or stops moving.

For scale, even a fixed contiguous row pattern needs an extraction
interface. If Z is an already verified power of three, a length-u pattern
with free numeral K can be extracted from FM using positive Rplus,Tplus,
alpha and

    FinalMemoryPlus=Rplus+Z*(3^u*Tplus+K-3^u),
    Rplus+alpha=Z+1.                                (17)

These six operations are equivalent to
FM=R+Z*(K+3^u*T), 0<=R<Z and T>=0. A v-row rectangle can use successive
anchors Z,WZ,... with v-1 additional products, for 7v-1 operations before
anchor placement and edge conditions. The board-width-dependent gaps are
not fixed free numerals. One must additionally certify that the rectangle
does not cross a row or board edge and choose the exact macro-pattern
whose occurrence is equivalent to simulated halting in the primary
construction. None of these last obligations is silently included in 174.

The complete counted endpoint interface is therefore much more expensive
than its two three-addition local cells suggest. It supplies a rigorous
test case for future sharing, while the current universal frontier is
unchanged.
