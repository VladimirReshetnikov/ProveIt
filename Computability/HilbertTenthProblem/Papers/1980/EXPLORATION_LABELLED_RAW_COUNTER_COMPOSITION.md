# A fully shared 132-operation labelled raw-counter composition

This note gives a complete baseline combining three ordinary numerical
counters with a fixed finite directed-graph controller. Every state fixes
the three counter signs and a subset of counters required to be zero
before that update. The complete system has **132 operations, 61 products
and 71 additions/subtractions**, with 46 positive unknowns and 34 equations.
The single positive parameter x enters directly as the initial value 2x
of the first register; the other two initial values and all final values
are zero. All three counters move by +/-1 at every step. The first
register's first sign is plus.

This is a checked upper-bound composition, not an improvement of the
90-operation universal frontier. It proves an exact labelled-register
history relation. A universal-machine compilation theorem is not included
in that statement. The source, all primitive instructions, and the exact
receipt are in `../verification/explore_labelled_raw_counter_composition.py/.json`.
The safe simultaneous 81-operation predecessor and fixed nondeterministic 68-operation router
remain unchanged.

The program table in the maintained arithmetic instance has three states.
It supplies nontrivial sign and zero-event tests and cleanup paths for
x=1 and x=2. The general proof and operation template below apply to any
fixed finite labelled graph after its numeral constants are compiled.

## 1. Fixed program data inside a variable counter frame

Take a fixed loop-free graph on m>=2 states, initial state i0, and final
state i1. Each state i carries labels

    s_i=(s_i0,s_i1,s_i2) in {-1,+1}^3,
    z_i=(z_i0,z_i1,z_i2) in {0,1}^3.

The meaning of z_ia=1 is that counter a must be zero at the source of
that step. The graph chooses an allowed successor. Self-loops can be
removed by the fixed phase split already used by the router, with the
endpoint phase included in the fixed endpoint specification.

Choose l>=2 with 3^l>m and set

    a_i=l*3^i, b_s=l*3^m, b_z=l*3^(m+1), d=b_z,
    S=sum_i 3^(a_i), g=3^d,
    h_s=3^(d+b_s), h_z=3^(d+b_z),
    Z_c=sum_(h=1)^(l-1)3^(d+h), I=3^(a_i0), F=3^(a_i1).

The constant K_0 contains all edge terms 3^(d+a_j-a_i), all count-marker
terms 3^(d-a_i), and the label terms

    3^(d+b_s-a_i) when s_i0=+1,
    3^(d+b_z-a_i) when z_i0=1.

For a=1,2, K_a contains the corresponding sign and zero label terms for
counter a, without edge or count-marker terms. The extended Sidon set
ensures all terms within each K_a have distinct nonnegative exponents.
Marker/edge collisions would require one positive power of three to
equal a sum of two; other target collisions are excluded by the ordinary
Sidon argument. These are fixed numeral constants.

Choose a fixed power of three Rmin strictly greater than

    K_0 S, K_1 S, K_2 S, gS, 2S+1, Z_c+h_s+h_z.

The integer R is the variable radix of one counter block and W=R^3 is
the radix of an entire time frame. Impose R=Rmin*z_R with positive z_R.
The variable program table is explicitly

    K(R)=K_0+R(K_1+RK_2).                            (1)

It costs two products and two additions. It is not a free fixed numeral:
its variable powers of R and their construction are paid. The bound on
Rmin will separate program products within every counter block and hence
within every time frame.

## 2. Complete outer source

Retain the positive outer unknowns of the safe three-register 81-operation system:

    q,J,W,H,v,T,F0,F1,G0,G1,FKplus,FKminus,alpha,alphaI,R,Htime.

Add the positive unknowns

    FZ,FZbar,alphaT,
    C,V,TestC,TestV,alphaP,NC,NV,NTC,NTV,z_R.

The source checker calls J `Jrep`, the four raw program variables
`PC,PV,PTC,PTV`, their native fields `PNC,PNV,PNTC,PNTV`, and z_R `zR`.
Also retain the seventeen positive unknowns of the fixed-sign 43-operation kernel,
including r. The following 23 equations are the outer source:

    q=2J+1, q=Wv,
    H(R-1)=2J, W=R^3, Htime(W-1)=2J,
    FKplus+FKminus=2J+H,
    F0+F1+alpha=q+J,
    G0=F0+T, G1=F1+T,
    2x+(W-1)(F0+F1-2J)+W(FKplus-FKminus)=0,
    2x+alphaI=R,
    6T=2(2J+H)+(R-3)(FZ-J),
    2T+alphaT=q, FZ+FZbar=2J+H,
    C+J=S Htime+TestC,
    TestV=V+Z_c Htime+(h_s+h_z)H,
    TestC+TestV+alphaP=q,
    NC=J+C, NV=J+V, NTC=J+TestC, NTV=J+TestV,
    R=Rmin*z_R,
    (WK(R)-g)C+gI=(gF)q+W[V+h_s(FKplus-J)+h_z(FZ-J)]. (2)

The mask word and its index are

    P=FKplus+qG0+q^2F0+q^3G1+q^4F1+q^5FKminus
        +q^6FZ+q^7FZbar+q^8NC+q^9NV+q^10NTC+q^11NTV,
    r=P, D0=q^12.                                  (3)

Equation r=P is the twenty-fourth outer comparison. Append all ten
equations of the fixed-sign 43-operation kernel with these r,D0, as stated in
`EXPLORATION_UNIT_TWO_TERNARY_KERNEL.md` and the safe 81-operation predecessor.
The total is 34 source equations. No kernel equation is dropped and
there is no extra variable exponent operation.

The sign and zero control expressions FKplus-J and FZ-J may be signed
before decoding. They are charged arithmetic intermediates, not supplied
nonnegative unknowns. Their needed ranges are proved in the order below.

## 3. Exact shared arithmetic count

Start from the safe simultaneous 81-operation certificate.

Replace its single operation 3T by the nine-operation block

    twoT=T+T, sixT=3*twoT,
    twoHead=(2J+H)+(2J+H), Rminus3=(R-1)-2,
    rawZ=FZ-J, spread=Rminus3*rawZ,
    topRhs=twoHead+spread,
    topBound=twoT+alphaT, zeroFlags=FZ+FZbar.

Compare sixT=topRhs, topBound=q, and zeroFlags with the existing register
2J+H. This is eight additional operations, one product and seven
additions/subtractions. It gives both the zero-test geometry and its
essential pre-mask bound. Appending its two native flag fields costs
four Horner operations.

The controller contributes exactly thirty more operations:

* Three for C+J=S Htime+TestC.
* Four for TestV=V+Z_c Htime+(h_s+h_z)H.
* Two for its shared positive bound.
* Four additions for its native adapters NC,NV,NTC,NTV.
* One product for R=Rmin*z_R.
* Sixteen for (1) and the last routing equation of (2). These include
  four operations for K(R), two for WK(R)-g, the product with C and
  its initial addition, the subtraction FKplus-J, two label products,
  two additions to V, the outer W product, and the final product/addition.
  The zero raw expression FZ-J is shared with the zero-test block.

Appending the four controller fields costs eight further Horner
operations. The chain q^2,q^4,q^6,q^12 takes four products, one more
than the predecessor's scale chain. The kernel itself remains 43 operations.
Therefore the complete count is

    81+8+4+30+8+1=132=61M+71A.

This is a full source and schedule count, rather than a sum of standalone
kernel-containing components. The checker expands every source residual
independently and verifies the existing acyclic correction of the
auxiliary Pell norm at its proper source position.

## 4. Noncircular pre-power bounds and native field recovery

The counter geometry and input bound give R>=3, q>=3, H<=J. The new
explicit slack gives 0<T<=J, regardless of the signed expression FZ-J.
The two native control pairs and the track bound give

    0<F0,F1,FKplus,FKminus,FZ,FZbar<3J,
    F0+F1<=3J, 0<G0,G1<4J.                          (4)

Thus the unchanged six-field bound for the safe 81-operation predecessor applies
to the low six-field word P6:

    q^5<P6<3(q^6-1)/2.

For the program, the paid time-frame geometry gives
J=((W-1)/2)Htime before powers are decoded. Since R>=Rmin>2S+1 and
W=R^3, the support equation gives C<TestC. Positivity gives V<TestV.
Their shared bound implies

    0<C<TestC<q, 0<V<TestV<q,
    TestC,TestV<=2J-1.

Consequently NC,NV,NTC,NTV are at most 3J-1 and positive. The two new
zero flags have the same upper bound. Appending these six fields to P6
therefore gives

    q^11<P
      <3(q^6-1)/2+q^6(3J-1)(1+q+...+q^5)
      <3(q^12-1)/2.                                (5)

In particular r=P,D0=q^12 meet the full general-scale kernel bounds
D0>=81,r>=27,r<2D0,D0<r^2. The kernel proves q is a power of three and
D0 divides binomial(2r,r). Its soundness does not assume even r.
The native unit-two mask in the enlarged window (5) makes P<q^12 and
all its ternary digits one or two, with unit digit two.

The first flag FKplus, being less than 3J, cannot carry into the next
q-chunk: its remainder would be smaller than J. Each adjacent pair
G_i,F_i then has the previously proved guard/base carry exclusion.
If G_i carried once, its native remainder would require G_i>=q+J;
F_i<3J would absorb that carry with F_i<=q-2, contradicting
G_i=F_i+T<=q+J-2. Every following field is at most 3J-1 and has no incoming
carry, so the same remainder bound decodes it directly. All twelve
supplied fields equal their native chunks.

Subtracting J from NC,NV,NTC,NTV shows that C,V,TestC,TestV are Boolean
words. No positivity or support of a native-derived control was assumed
to obtain these packing or field-recovery bounds.

## 5. Counter signs and exact source zero tests

Power recovery and the retained geometry give

    R=3^m, W=R^3, q=W^t,
    H=sum_(b=0)^(3t-1)R^b, Htime=sum_(j=0)^(t-1)W^j.

The decoded raw signs Kplus=FKplus-J and Kminus=FKminus-J are Boolean
and sum to H. Exactly one sign occurs at every counter-block head.
Likewise Z=FZ-J and its complement are Boolean and sum to H.

The new top equation now has the exact interpretation

    T=(R/3)H+((R-3)/6)Z.                            (6)

The coefficient (R-3)/6 is the Boolean ternary repunit on all positions
below the highest digit of one counter block. Therefore T is Boolean.
In every block its highest digit is one. If that block's Z bit is one,
all its lower digits are also one; otherwise all lower T digits vanish.
This proves T<=J from its intended interpretation after decoding, while
the separate slack had already paid for the pre-mask bound.

Native G_i=F_i+T forces the Boolean raw track A_i=F_i-J to be disjoint
from T. At the least overlap, digit two of F_i plus digit one of T would
produce zero and a carry, contradicting a native output. Hence both
tracks have zero top digits in every block, and both tracks vanish
entirely in a block selected by Z.

Their ordinary numerical sum A=A0+A1 consequently has block values
0<=a_b<R/3. It is zero wherever Z requests a source zero test. The exact
mixed time equation is the predecessor's equation

    2x+(W-1)A+W(Kplus-Kminus)=0.

Reducing successively in base R, with W=R^3, proves initial values
[2x,0,0], one +/-1 update per register per time frame, and final values
[0,0,0]. Every interior coefficient has absolute value at mostR/3<R;
the initial coefficients have absolute value less than R by the paid
input bound. Thus there are no carries between counters or time steps.
All counter values are nonnegative, so decrement from zero is excluded.
The unit-two first flag forces the first sign of the first counter plus.

## 6. Variable-table controller recovery and label consistency

The support relation C+J=S Htime+TestC makes C a Boolean subset of the
fixed source positions in each W row. The forbidden mask for V consists
of the count-marker high digits in the first block and the two label
targets in each of the three blocks. Those supports are disjoint and
Boolean by the paid R bound. Thus Boolean TestV forces V to avoid all
of them.

Reducing the routing equation modulo W gives the initial row C0=I:
its other extra output terms are multiplied by W, and gS<R<=W makes
the usual cancellation modulo W/g exact in the known interval. Define
Next=(C-I+qF)/W mathematically. It consists of the later rows of C and
the fixed singleton final row. The routing identity becomes

    K(R)C=g Next+h_s Kplus+h_z Z+V.                 (7)

Each row of the left side separates into three blocks K_a C_row,
each smaller than R by Rmin>K_a S. There are no carries between blocks
or time rows. Within a block, all raw program exponents lie on the
l grid and every coefficient is at most m, since each K_a has distinct
exponents. Thus normalization cannot carry between successive grid
positions.

The three non-junk terms on the right have disjoint Boolean supports:
state outputs occur in the first block at the state targets, signs occur
at the sign target of each block, and zero labels at the separate zero
target. Adding Boolean V gives digits at most two, so there are no
ternary carries on that side either.

At the full length-l count-marker block, (7) is exactly the same
one-head test as in the fixed nondeterministic 68-operation proof. It forces each
source row to contain at most one state. Empty rows propagate through
the nonnegative equation to the fixed nonempty final row, so every row
has exactly one state. The ordinary state target proves the chosen
successor is an allowed edge.

At each sign target, the forbidden V digit is zero, and the table digit
is precisely the fixed sign label of the source state. Thus Kplus emits
that sign in each of the three counter blocks. The zero target similarly
identifies Z with the source state's zero label. Section 5 then proves
every labelled zero condition on the actual counter value. Neither
label consistency nor the numerical zero condition is treated as free.

## 7. Positive converse and parity of the shared word

Take any finite path in the fixed labelled graph whose prescribed counter
updates and zero tests are valid, starting from [2x,0,0], ending at all
zero, and obeying the first-plus convention. Choose R as a sufficiently
large power of three divisible by the fixed Rmin. Its bound may be
increased arbitrarily without changing the path. Set W=R^3,q=W^t and
the two geometric masks as above.

Split each raw counter value into two Boolean ternary tracks with a
zero top digit. This is an ordinary digit split of the value itself.
Form Kplus,Kminus and Z from the labels, their native counterparts,
and T from (6). Every labelled zero block has both tracks zero, so the
two guard fields are native. The track bound gives alpha>=1 and the
choice of R gives alphaI>=1. Also T<=J, so alphaT=q-2T>=1, including
the extreme case T=J. All zero flags remain positive after adding J.

Use the actual program path to define C and Next. Set V by (7), and
define the two raw Test fields from (2). Each selected sign, zero, and
successor output is removed from a digit one without borrowing. The
remaining V is Boolean, and the count-marker unit digit remains one,
so V>0. Every forbidden output digit is empty in V, making TestV
Boolean. TestC is Boolean by source support. Both are positive and at
most J, so alphaP>=1. The four native adapters are positive and native.
Every one of the 24 outer comparisons now holds.

The duration t is even, since each physical register starts at an even
value, ends at zero, and moves by +/-1 each time. Consequently J is even,
Htime has an even number t of odd terms, and H has an even number 3t of
odd terms. The sum of the original six native counter fields is even.
The new zero-flag pair sums to 2J+H and is even. Finally

    NC+NV+NTC+NTV
      =2(C+V)+5J+(Z_c-S)Htime+(h_s+h_z)H

is even. Since q is odd, the entire twelve-field word P is even. It is
native, below q^12, and has unit digit two. The full fixed-sign 43-operation
positive converse therefore supplies all sixteen remaining kernel
auxiliaries for the already fixed r=P,D0=q^12. The soundness proof had
not required this parity in advance.

## 8. Verification scope and cheaper variants

The maintained instance verifies all 132 primitives and all 34 expanded
source equations. Its canonical full outer tests use x=1 and x=2,
including genuine selected source zero tests, and verify every one of
the 24 outer residuals, all twelve native fields, the complete packed
word, exact central-binomial valuation, and the full positive-kernel
extension hypotheses. The packed words have 78,056 and 117,084 bits;
the exact valuations are 49,248 and 73,872. The enormous Pell coordinates
themselves are supplied by the proven converse, not numerically built.

The general proof gives the exact relation for arbitrary fixed labelled
graphs. This receipt is a full arithmetic check and two complete
canonical examples; it is not an exhaustive search over malformed
twelve-field assignments or a universal-machine compilation test.

The baseline deliberately retains the predecessor's complete time-frame
geometry. A serial controller operating once per base-R counter block,
with the lane number stored in the finite program state, can use a fixed
table rather than (1) and a single shared block-head forbidden mask.
That is a separate proposed reduction. Changes to the counter geometry,
the sign interface, or a raw universal-machine compiler likewise need
their own source and proof checks before being included in a smaller
claimed total.
