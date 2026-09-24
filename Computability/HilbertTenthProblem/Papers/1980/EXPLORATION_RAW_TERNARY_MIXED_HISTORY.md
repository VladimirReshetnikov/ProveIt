# Raw numerical counter histories from two ternary tracks

This construction represents ordinary nonnegative integer counter values,
not binary values dilated into ternary bit positions. Each time row changes
its counter by either +1 or -1, chosen by a typed Boolean control flag.
Intermediate counter values may be zero; decrementing zero is excluded by
the history equations. The raw initial value is a direct parameter.

The complete certificate has **82 operations: 42 multiplications and 40
additions/subtractions**, before any program lookup or halting construction.
Its independently verified exact schedule and finite receipt are in
`../verification/explore_raw_ternary_mixed_history.py/.json`.
All 22 expanded source equations and the complete primitive list pass.
This is a bounded component,
not an improved universal operation bound. The variable finite width is
existential and can grow with the computation.

## 1. Complete interface and the raw input

Let I be a nonnegative raw input parameter and Fplus a positive parameter;
the intended final value is F=Fplus-1. A positive user input x may be supplied
directly as I=x. A counter initialized at zero may instead use the literal
fixed numeral zero. No x-to-binary-track dilation or exponential loader is
involved. All existential unknowns below are strictly positive.

Use positive outer unknowns

    q,J,W,H,v,T,F0,F1,G0,G1,FKplus,FKminus,alpha,alphaI,

and the eighteen positive kernel unknowns from
`EXPLORATION_PARITY_FREE_PELL_KERNEL.md`. Define mathematical abbreviations

    S=F0+F1, A=S-2J, delta=FKplus-FKminus,
    P=G0+qF0+q^2G1+q^3F1+q^4FKplus+q^5FKminus,
    L=q^6, D0=3L.

The checker calls the guard fields G0,G1 by T0,T1 and the native control
fields FKplus,FKminus by FKp,FKm. These are only register-name changes.

A and delta are signed arithmetic intermediates before decoding; they
are not additional supplied positive unknowns. The eleven outer equations are

    q=2J+1,                                      (1)
    q=Wv,                                        (2)
    H(W-1)=2J,                                   (3)
    FKplus+FKminus=2J+H,                          (4)
    3T=2J+H,                                     (5)
    F0+F1+alpha=q+J,                             (6)
    G0=F0+T, G1=F1+T,                           (7)
    I+(W-1)A+W delta+q=q Fplus,                   (8)
    I+alphaI=W,                                  (9)
    r=3P+2.                                     (10)

Equation (7) consists of two equations, so the displayed outer block has
eleven comparisons. The remaining eleven comparisons are the complete
parity-free base-three kernel with inputs D0,r. No separate promise about
q, the digits of any field, the flags, or the sizes of the raw row values
is used.

The plus-q term in (8) pays for the output offset Fplus=F+1. Equivalently,

    I+(W-1)A+W delta=qF.

There is no input offset, so I=0 and I=x are both available directly. If a
surrounding convention instead insists on a positive input parameter
Iplus=I+1, the equivalent time equation uses Iplus and +2J in place of
I and +q; the raw query-to-Iplus addition is then an additional operation
unless the surrounding system already computes it.

## 2. Paid bounds and power recovery

Before digit decoding, positivity in (1)--(3),(9) gives q>=3, W>=2 and
0<=I<W. In particular H(W-1)=2J>0 excludes W=1 even when I=0.
Since q is odd and W divides it, W is odd and W>=3. Consequently
(3) gives 0<H<=J. From (4),(5),(6),

    0<F0,F1,FKplus,FKminus<3J,
    F0+F1<=3J, FKplus+FKminus=2J+H<=3J,
    0<T<=J, 0<G0,G1<4J.                          (11)

These bounds do not assume A>=0; this is essential for a noncircular
bootstrap. The positive fields give P>q^5. To bound P above, group its
guard/base pairs:

    P=(q+1)F0+(q^3+q^2)F1+T(1+q^2)
        +q^4FKplus+q^5FKminus
     <=(3J-1)(q^3+q^2)+q+1+J(1+q^2)
        +(3J-1)q^5+q^4
     <3(q^6-1)/2.                               (12)

After J=(q-1)/2 is substituted, the last strict upper-bound gap is

    (q-1)(5q^4+q^2+7q+4)/2>0.

Thus D0=3q^6 and r=3P+2 satisfy

    D0>=2187, r>3q^5>=729,
    r<3D0/2<2D0, D0<r^2.

These imply every hypothesis of the general-scale parity-free kernel.
It recovers U=3^(2r+1) and D0 dividing binomial(2r,r). Since q^6 divides
U, q is a power of three. Equations (2),(3) then give

    W=3^m, q=W^t, m,t>=1,
    H=1+W+...+W^(t-1), J=((W-1)/2)H.             (13)

The standard divisibility proof applies: if q=3^ell and W=3^m, then
W-1 divides q-1, and reducing ell modulo m proves m divides ell.

## 3. Native masking and guard/base carry exclusion

The native positive ternary mask from
`EXPLORATION_NATIVE_TERNARY_OVERFLOW.md` applies with L=q^6, r=3P+2,
D0=3L and the strict window (12). It forces P<L and every one of its
6log_3(q) ternary digits to be one or two. The argument for this mask does
not require r even; only the old kernel's converse did. Here the fully
parity-free kernel supplies both directions for either parity.

Every q-chunk of P is consequently native and belongs to [J,q-1].
Consider the adjacent low pair G0,F0. If G0>=q, then G0<4J<2q and its
native remainder forces G0>=q+J. A carry one enters F0. Since F0<3J,
F0>=q would leave a remainder at most J-1, and F0=q-1 would leave zero.
Thus F0<=q-2 and the carry is absorbed. But T<=J implies

    G0=F0+T<=q+J-2,

contradiction. Therefore G0<q, and F0<3J with no incoming carry forces
F0<q as well. Apply the identical argument to the next adjacent pair
G1,F1. The final flag fields are each less than 3J and have no incoming
carry, so both are below q. All six supplied fields equal the native
chunks. This proof handles the initial larger range G_i<4J without an
unpaid guard bound.

## 4. The tracks encode unrestricted small ternary row values

Define raw Boolean ternary words

    A0=F0-J, A1=F1-J,
    Kplus=FKplus-J, Kminus=FKminus-J.

Equation (4) becomes Kplus+Kminus=H. Raw digit sums are at most two, so
this equality is digitwise: exactly one of the two controls is present
at every row head, and neither has any other occupied position. Thus

    delta=sum epsilon_j W^j, epsilon_j in {-1,+1}.

Since H(W-1)=2J, equations (3),(5) imply

    3T=WH, T=(W/3)H.                             (14)

This is the Boolean mask of the highest ternary digit in each row. The
native guard G_i=F_i+T forces A_i to be zero at all these positions.
Indeed, at the least overlap of A_i and T, the native F_i digit is two
and addition of T produces digit zero with a carry. There is no incoming
carry, because every earlier sum is at most two. That zero contradicts
native G_i. Conversely, absent every overlap, adding T just changes a
native digit one to two and creates no carry.

Let a_j be the jth base-W row of A=A0+A1. Each A_i row is a Boolean word
whose highest ternary digit is zero. Their sum represents an ordinary
ternary integer, allowing digits zero, one, and two without a carry. Hence

    0<=a_j<=2(1+3+...+3^(m-2))=W/3-1.           (15)

For m=1 this says a_j=0. There is no binary interpretation here: the
integer a_j itself is the counter value. Every nonnegative integer smaller
than W/3 admits such a two-track representation by splitting each ternary
digit two as 1+1 and each one as 1+0. Different splits of digit one do not
change the represented counter or its transitions.

## 5. Exact mixed transitions from one time equation

Write A=sum a_j W^j, delta=sum epsilon_j W^j for j=0,...,t-1, and
F=Fplus-1>=0. Equation (8) expands as

    (I-a_0)
    +sum_(j=1)^(t-1)(a_(j-1)+epsilon_(j-1)-a_j)W^j
    +(a_(t-1)+epsilon_(t-1)-F)W^t=0.             (16)

The unit coefficient has absolute value less than W by 0<=I<W and (15).
Since (16) is zero modulo W, that coefficient must be zero: a_0=I.
After division by W, each interior coefficient has absolute value at most
W/3, hence strictly less than W. Induction therefore gives

    a_j=a_(j-1)+epsilon_(j-1),
    F=a_(t-1)+epsilon_(t-1).                     (17)

Every a_j and F is nonnegative, so no decrement from zero is accepted.
There is no modular wraparound and no carry into another time row.
No positivity restriction was added to the counter values themselves.

The exact interpretation is a positive-length walk by +/-1 from raw I
to raw Fplus-1, whose intermediate values have a finite existential bound.
The two native flag fields preserve the chosen sign at every time. Without
a separate program controlling those flags, this endpoint relation is
decidable. The contribution is a counted raw numerical history interface,
not a universal program.

## 6. Positive converse and arbitrary finite width

Take any finite nonnegative walk n_0=I,n_1,...,n_t=Fplus-1 with
n_(j+1)-n_j in {-1,+1}. Choose m large enough that every n_j<W/3 for
W=3^m, and set q=W^t,H,J,v,T as in (13),(14). Split the ternary digits
of each input row n_j into two Boolean tracks with zero top digit.
Form the two control masks at row heads and their native fields.

All six masked fields are positive, including tracks or controls that
are identically zero before the native offset. Both guards are native by
the zero top digits. Moreover

    A=sum n_j W^j<=(W/3-1)H<=J,
    F0+F1=2J+A<=3J.

Thus alpha=q+J-F0-F1>=1. Also alphaI=W-I>=1. Every outer equality holds,
including (8) with the positive output offset. The packed word is native
and below q^6. Its native ternary mask supplies D0-divisibility, and the
general-scale hypotheses follow from (12). The parity-free positive
converse supplies all remaining positive Pell witnesses for the new
r=3P+2,D0=3q^6. No parity selection, variable exponent operation, or
large-witness numerical test is being treated as free.

## 7. Count and scope of a future program composition

The straightforward schedule charges: five operations for (1)--(3), two
for the head pair (4), one product for (5), three additions for the shared
bound (6), two additions for the guards, one subtraction to form A from
the shared F0+F1, seven operations for the mixed time equation (including
the output-offset term), and one input-bound addition. Six-field Horner
packing takes ten operations; q^2,q^4,q^6,D0=3q^6,r=3P+2 takes six.
Together with the 44-operation kernel, this totals 82. All intermediate
names denote charged registers or algebraic abbreviations, not free
computation.

The exact receipt checks 8,315 positive pre-power tuples and 48,684 complete
finite outer candidates, with 39 accepted. Its 3,382 canonical histories
include 47 zero-input cases, 45 zero-output cases, 28 cases with the final
value W/3, and both packed-index parities (1,141 odd and 2,241 even).
These tests supplement the proofs; they do not instantiate enormous Pell
coordinates or supply a universal machine.

A common program relation could reuse the geometry, the typed control
fields, and the global mask rather than concatenate two entire kernels.
Several registers might also share one word by using smaller counter
blocks within a time row. Those possibilities still require complete
boundary, control, and zero-branch proofs. The present theorem asserts
only the raw numerical +/-1 history described above.
