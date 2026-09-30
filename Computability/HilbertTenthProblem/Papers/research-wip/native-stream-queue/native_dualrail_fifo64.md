# An exact native dual-rail FIFO in 64 operations

This component costs **64=33M+31A**, with17 equations and22 strictly
positive auxiliaries beyond seven positive parameters. It retains every
native FIFO run with initial queue **6x**, a positive first append rail,
and empty final queue. Three aggregate bounds replace four individual
field bounds. A possible field carry is excluded by the initial queue's
low-order zero, with no extra arithmetic operation.

Using the final equality directly gives an exact **conditional73** general
filtered carry architecture, or **conditional72** when its fixed endpoint
carries coincide. A particular existing serialized controller costs seven
additional operations, giving **conditional71**. No universal controller, raw-input
loader or accepting compiler is supplied; the established complete
universal bound remains76.

## 1. Exact source and projection

The positive parameters are x,W,q,F0,F1,F2,F3. Define paid registers

    Q=q-1, D0=q^4, P=F0+qF1+q^2F2+q^3F3,
    A=F0+F1-Q, D=F2+F3-Q, I=6x.

Supply the seventeen retained Pell coordinates and five more positive
coordinates alphaP,alphaA,alphaD,beta,L. Impose

    r=P, r+alphaP=D0,
    A+alphaA=q, D+alphaD=q,
    D=I+WA, I+beta=W, q=WL,                             (1)

together with the ten retained ternary Pell equations at scale D0,
exactly as in the [four-field55 proof](native_controller_four_fields55.md).
There are no equations Fi+alpha_i=q. A,D are intermediate registers,
and are not assumed nonnegative before typing has been proved.

The exact parameter projection is: q=3^t,W=3^m for integers t>=m+1,
m>=2; 0<I=6x<W; and Fi=H+Bi for H=(q-1)/2 and four length-t Boolean
ternary words Bi. The first two are append planes, the last two read
planes. Their scalar trits

    a_j=b0_j+b1_j, d_j=b2_j+b3_j

give a t-step FIFO run

    N_0=I, N_t=0,
    d_j=N_j mod3,
    N_(j+1)=floor(N_j/3)+(W/3)*a_j,                     (2)

and b0_0=1. Trit1 can use either rail orientation; no additional label
selection or finite controller is implicit.

## 2. Bounds before any power or digit assumption

The width equations give W>I>=6 and q>=W, hence q>=7. The packed
bound supplies

    q^3+q^2+q+1<=r=P<q^4=D0<r^2.

The two aggregate bounds give

    F0+F1<=2q-2, F2+F3<=2q-2,
    1<=Fi<=2q-3<2q.                                    (3)

Thus the pre-power kernel bounds are stronger than those explicitly
checked in the55 source: D0>=7^4, r>=400, X,Y>=D0,
XY>=D0^2>r+1, a>=D0(D0+1)>2r+1 and

    6r/a<6/(D0+1)<1/2.

Its rank, first-index, ratio, direct exponent recurrence and rounding
arguments use these bounds, not separate Fi<q assumptions. They yield

    q=3^t, X=3^(2r+1), D0 divides binom(2r,r).

The same generic signed **positive-branch** theorem forces r even:
the retained classification has p=2r+1,c=psi_(a+3)(p)>2p,
f=chi_(a+3)(u)>2c,c dividing u,u>=2p, and the two positive congruences
for the normalized auxiliary root. These are the hypotheses already
audited in55. In particular parity is necessary for every positive
solution, not assumed from a canonical choice of witnesses.

## 3. Aggregate bounds recover every individual field

Now put q=3^t,H=(q-1)/2. Because P<q^4, maximal valuation forces all
4t trits of P to lie in{1,2}, with units trit2. Normalize its supplied
fields by

    Fi+c_(i-1)=Gi+q*c_i, c_(-1)=0, 0<=Gi<q.

The bounds(3) make c_i either0 or1. The packed bound makes c3=0,
and the normalized chunks satisfy

    G0>=H+1, G1,G2,G3>=H.                               (4)

For the append pair,

    F0+F1=G0+G1+(q-1)c0+q*c1<=2q-2=4H.

If c0=1, the lower bound is4H+1; if c1=1, it is at least4H+2.
Both contradict the aggregate bound. Thus c0=c1=0, and both append
fields are genuine native chunks. In particular A>=1 and its first
trit has b0_0=1.

For the read pair, only c2 can remain:

    F2+F3=G2+G3+(q-1)c2<=4H.

If c2=1, (4) forces G2=G3=H, and then D=F2+F3-2H=q-1. The
transport and q=WL imply I congruent to -1 modulo W. Since 0<I<W,
this would give I=W-1. But W divides the recovered power3^t and
W>I>=6, so W is a positive power of3. Hence W-1 is2 modulo3,
contradicting I=6x. Therefore c2=0 as well.

All supplied fields are now native and strictly below q. Subtracting
H gives the four Boolean planes. The exact transport D=I+WA with
0<=A,D<q proves FIFO causality and its empty endpoint by the usual
successive reduction modulo3. W=3^m with m>=2. Since A>=1,
D=I+WA>W and D<q, so t>=m+1. This proves the entire stated projection.

The initial scaling is essential to this argument. With q=27,W=9 and
fields(14,14,40,12), one gets P=265748<q^4, the required valuation,
even P, A=2 and D=26=q-1. This gives old initial I=8=2*4=W-1,
while F2 exceeds q. It satisfies all three aggregate bounds but fails
I=6x. Thus aggregate bounds cannot be silently treated as independent
Boolean typing without the retained FIFO/input argument.

## 4. Positive converse for every stated FIFO run

Given a run (2) and any of its Boolean rail splittings with b0_0=1,
set Fi=H+Bi. The fields are positive native words; their packing has
all4t doubling carries and units trit2. Telescoping gives D=I+WA,
and odd W with even I gives

    sum_i Fi=4H+D+A=0 modulo2.

The complete55 converse therefore supplies every retained positive
Pell coordinate. Choose

    alphaP=q^4-P, alphaA=q-A, alphaD=q-D,
    beta=W-I, L=q/W.

All are positive. Every equation(1) follows. No padding of a controller
path or absorbing terminal state is assumed: the converse covers every
FIFO run in the stated projection.

The bare FIFO still accepts every positive x. Choose the least W=3^m
greater than6x, put t=m+1 and q=3W, append1 first and then0 for the
remaining steps. The read stream consists of the m trits of6x followed
by1. Splitting each read trit arbitrarily and splitting the initial
append1 as(1,0) gives positive witnesses. This is a fixed injective
ordinary-input transformation, not a sparse encoding or an exponent.
A universal compiler would still have to handle that initial format.

## 5. Ledger and conditional controller

The literal schedule computes the packing by six Horner operations,
q^2 and q^4 by two multiplications, r+alphaP by one addition and
Q=q-1 by one subtraction. It then uses the unchanged43 kernel, the
nine FIFO instructions from65 with `initial=6*x`, and the two additions
A+alphaA and D+alphaD. This gives64=33M+31A and17 equations.
There are22 positive auxiliaries, or29 positive coordinates including
the seven parameters.

For the general fixed carry constraint, let the local equation be

    3*k_(j+1)=k_j+h+c0*b0_j+c1*b1_j+c2*b2_j+c3*b3_j.

For arbitrary
fixed weights ci, offset h and endpoint carries cs,cf, put K=sum(ci)
and lambda=(h-K-2cf)/2. After doubling all fixed carry data if needed,
lambda is integral, and its source is

    sum_i ci*Fi + lambda*Q + cs-cf=0.

The historical literal ten-instruction schedule in the
[65/75 architecture](native_dualrail_fifo67.md) computes four products,
their sum, lambda*Q, the sum of those five variable terms and finally
the fixed constant cs-cf. It gives74=38M+36A here. The final addition
is unnecessary: compare the sum of the five variable terms directly
with the fixed numeral cf-cs. Thus the exact general schedule costs
**9=5M+4A**, giving **73=38M+35A** and18 equations.

If cs=cf, split the variable terms across the free equality instead:

    c0*F0+c1*F1+c2*F2+c3*F3 = (-lambda)*Q.

Four products and three additions compute the left side, and one
product computes the right side. This costs **8=5M+3A**, giving
**72=38M+34A**. The common fixed carry need not be zero. Both versions
retain exactly the same positive coordinates as64. Negative constants
are fixed numerals; forming -lambda is not an operation on a variable.

These equalities encode the entire Boolean-filtered carry graph. Indeed,
telescoping the local equation gives the displayed packed constraint;
conversely, reducing it successively modulo3 recovers an integer carry
at every step and the prescribed final carry. Doubling all fixed
weights, h and both endpoints is exact if needed to make lambda integral:
an initially even carry remains even at every integral step, since
division by3 preserves parity. Dividing all carries by2 recovers the
original graph. No universal coefficient choice or code filter is supplied.

## 6. A seven-operation specialized controller

The smaller [two-step Rule110 experiment](native_controller_rule110_serialization.md)
uses read weights(-88,-40), append weights(8,4), h=27 and endpoints0.
Its conditional coded transducer is proved there, together with an
uncoded escape. Double the carry data. In the field order used here,
the coefficients become(16,8,-176,-80), h=54 and lambda=143. The source is

    16F0+8F1-176F2-80F3+143Q=0.                         (5)

The FIFO has already paid for S=F0+F1. Compute

    U=S+F0, V=8U,
    T0=176F2, T1=80F3, T=T0+T1,
    C=143Q, E=V+C,

and impose the free comparison E=T. These are exactly **7=4M+3A**
additional operations: the combined source has **71=37M+34A**,18 equations
and22 positive auxiliaries. With Fi=H+Bi and Q=2H, (5) becomes

    16B0+8B1-176B2-80B3+54H=0,

which is precisely the doubled whole-stream carry equation. The parity
argument above gives an exact equivalence to the original integer graph.

This counts the **unfiltered** controller, including its known unwanted
paths. It does not count a Rule110 compiler. The required two-trit code,
ordinary-input loading, phase alignment and terminal cleanup are not
enforced. In particular the continuously nonzero code from that experiment
cannot cover the all-zero append suffix required by an empty final FIFO.
The lower conditional count does not repair these semantic obligations.

## 7. Evidence and comparison with a joint bound

The [source](native_dualrail_fifo64.py) independently checks all17
polynomial residuals and the exact auxiliary-norm correction, then the
combined74 literal reference and optimized73,72,71 schedules. It verifies
their expanded controller residuals and the specialized coefficient
normalization. Its [receipt](native_dualrail_fifo64.json) scans
1,338,042 positive field tuples through t=3 under the three aggregate
bounds. Every valuation-admitted tuple is either genuinely native or
one of the40 all-two read exceptions; none of those exceptions survives
the initial6x condition. Four hundred positive outer maps cover the
first200 ordinary inputs and both choices of read-trit1 orientation.
The enormous complete Pell extension is proved parametrically.

A separate possible64 variant replaces A<q and D<q with the stronger
joint bound A+D<q, costing two additions with one positive slack. Along
with P<q^4, this gives sum(Fi)<=6H; any normalized field carry would
instead make that sum at least(4H+1)+2H=6H+1. It therefore derives
typing without the initial residue exclusion. Its exact FIFO projection
has the additional joint bound. Enlarging q can repair that bound for
bare runs, but arbitrary controller endpoints need not permit padding.
The present separate-bound source preserves the unrestricted run
interface and keeps the residue-based proof explicit.

Run `python native_dualrail_fifo64.py` for a fresh receipt comparison.
Independent complete proof/source/default review passed, including all
three optimized controller schedules, the overflow exclusion and every
positive converse coordinate. No Lean formalization or improved complete
universal bound is claimed.
