# A special periodic digit mask with a smaller binomial scale

This note gives an exact arithmetic realization of a local Boolean
base-four word predicate. It does not assert a complete universal
machine encoding or a new bound for the published universal system.
All displayed variable powers are accounted for by explicit products.

## 1. Exact popcount identity, including addition overflow

Let N>=1, L=4^N, M=2(L-1)/3, and let P be any integer with
0<=P<L. Thus M has base-four digits all equal to two and
popcount(M)=N. Define

    r=(L-P)(L-1)+M.

Write c=popcount(P)+popcount(M)-popcount(P+M). This is the number
of binary carry events in the addition and is nonnegative; c=0
exactly when P AND M=0. If P+M<L, the two base-L digits of r are
L-P-1 and P+M, giving

    popcount(r)=3N-c.                         (1)

If P+M>=L, then P>0 and the normalized digits are L-P and P+M-L.
Using popcount(P-1)=popcount(P)-1+v2(P) gives instead

    popcount(r)=3N-c-v2(P).                   (2)

In this case c>=1, so equality with 3N is impossible. It follows,
without assuming carry-free addition, that

    popcount(r)<=3N,
    popcount(r)=3N iff P AND M=0.             (3)

By the central-binomial valuation identity, (3) is equivalent to

    2^(3N) divides binom(2r,r)
       iff every base-four digit of P is zero or one. (4)

The bound 0<=P<L is an explicit hypothesis. No assertion for
negative P or P>=L is hidden in this lemma. Parity is also exact:
r=P modulo two, since L and M are even.

## 2. A power scale suitable for six bounded planes

Suppose the surrounding construction gives a positive q and
nonnegative integer P with P<Q^6, where Q=q^2. Use

    L=Q^8, D=Q^12, N0=Q^6,
    3lambda+1=L,
    r=(L-P)*(3lambda)+2lambda.                (5)

The positive supplied lambda makes q>=2 and Q>=4. Before any
power-of-two conclusion, all these are ordinary integer relations.
The assumed bound gives

    N0^2<r<Q^16<N0^3,

because (Q^8-Q^6)(Q^8-1)>Q^12 and r<L^2. In particular
N0>=64 and N0<=r<2N0^3. If the retained first-Pell kernel uses
U=wD,Y=sD, positivity gives U,Y>=D=Q^12. Hence

    UY>=Q^24>r+1, a=Y(U+1)>Q^24>2r+1,
    4r/a<4/Q^8<1/2.

These establish its preliminary index and ratio hypotheses without
assuming a Boolean P, any binary carry statement, or that q is a
power of two. The retained exact-index argument, lower ratio and
first exponent congruence then prove U=2^(2r+1), as in the base-two
Pell proof. Since U=wQ^12, q and Q are powers of two. No second
fixed-index/exponential block is needed just to establish that fact.

After this conclusion, write Q=2^k. Then L=Q^8=4^(4k), so N=4k
and D=Q^12=2^(3N). The kernel's conclusion D divides binom(2r,r)
is therefore exactly the predicate (4).

This local necessity construction requires the retained kernel's
parity condition. Since r=P modulo two, the published half-parameter
positive construction is available when P is even. The popcount
lemma itself is valid for odd P as well, but it does not establish
the missing positive auxiliary witnesses for that case.

## 3. Explicit outer operations

The following six multiplications construct every needed power if
N0 is explicitly retained as a register:

    Q=q*q, Q2=Q*Q, Q4=Q2*Q2, L=Q4*Q4,
    N0=Q4*Q2, D=N0*N0.

The geometry uses two operations: three_lambda=3*lambda and
L_check=three_lambda+1, with free equality L=L_check. The packed
integer uses four operations:

    gap=L-P,
    product=gap*three_lambda,
    M=2*lambda,
    r=product+M.

This is 12 operations: nine multiplications and three additions.
Equivalently r=lambda*(3*(L-P)+2), also four operations.

If the retained Pell kernel uses only D=N0^2 and does not require
N0 itself as a register, compute D=L*Q4 directly. This replaces
the last two power multiplications by one. N0=Q^6 remains legitimate
proof notation, without being a free variable exponent in a
certificate. The resulting outer schedule has 11 operations:
eight multiplications and three additions. Its applicability
depends on that precise kernel interface.

For comparison, the direct general-mask construction at packing
base L constructs Q,Q2,Q4,L,L^2 in five multiplications. Computing
three_lambda,L_check,M takes three operations; the generic packing

    P*(L^2-L)+(M+1)*(L^2-1)

uses another six operations with L^2 shared. That explicit schedule
has 14 operations, nine multiplications and five additions. Thus
the special mask saves two operations with an explicit N0, or three
when only D is needed. These are comparisons of specified schedules,
not lower bounds on arbitrary implementations.

## 4. A sixth plane can impose a low-bit row-edge condition

Suppose a history compiler already supplies five nonnegative planes
below Q, including a word Bword. Suppose h is a Boolean row-start
word of the same length. Testing Bword and Bword+h as Boolean
base-four words is equivalent to requiring Bword Boolean and
Bword AND h=0: every raw digit of their sum is at most two, so
there is no radix-four carry to invalidate this argument.

For the proposed geometry Q-1=h(W-1), W=v^2, the additional source
relation q=v*d is important. Once q is a power of two, positive
integer v divides q and is also a power of two. Hence W is a
power of four, and the integral quotient h is the genuine Boolean
row-start word. The geometric equation alone would not suffice.
For example Q=4^12,v=118,h=1205 satisfies that equation, and
Bword=80,Bword+h=1285 are both Boolean even though h is not.
It is excluded by q=v*d, since 118 does not divide q=4096.

If the existing range proof gives 4*Bword<Q, then h<Q/3 and
Bword+h<Q. Appending Bword+h as the sixth Horner-concatenated
plane costs one addition to form the word, followed by one
multiplication and one addition to append it: three operations.
All six planes fit below Q, so their concatenation P<Q^6. The
fixed L=Q^8 already has room for them, and no additional power is
needed. Since Q is a power of four, the plane boundaries align
with base-four digits and one periodic mask tests all six planes.

The row-start word has unit digit one. Therefore the edge condition
forces Bword's unit digit to vanish. Choosing Bword as the least
concatenated plane makes P even, supplying the auxiliary parity
condition in Section 2 without another arithmetic operation.

The range proof for the planes, the equation q=v*d, and the complete
machine transition encoding remain requirements of the surrounding
construction; they are not supplied for free by this local lemma.

## 5. Focused exact verification and scope

`../verification/explore_periodic_digit_mask.py` verifies (1)--(4)
for every 0<=P<4^N, N=1..8: 87,380 exact cases, including the
overflow branch. It checks representative pre-power bounds using
both power-of-two and non-power-of-two q, and 196 Boolean edge-plane
cases. It constructs no universal machine certificate. The general
proof and the specified operation lists are the substantive results;
the finite receipt only corroborates them.

## 6. Independent round39 integration audit

The integrated checker `round39_1980_boolean_history_components.py`
independently passes 86 primitives (46 multiplications and 40 additions),
31 positive unknowns, and 21 source equations. Its retained 43-operation
Pell kernel reads only the computed squared scale D=q^24; n0 is proof
notation. The preliminary history equations give each of the six planes
strictly below Q before any digit argument, so Section 2's Q^12<r<Q^16
bounds justify the exact index, first exponential, and binomial rounding
in that order. The resulting Q-power conclusion aligns the six fields;
q=v*quot makes the row-start mask genuine. In necessity, that mask forces
the lowest B digit zero, hence P and r even, which supplies the positive
half-parameter auxiliary construction. No second exponent is needed.
All source equations and positive Pell witness obligations pass this
independent audit. This is a finite-history component result, not a
universal bound: for fixed nonzero raw I, the zero-exterior leftmost one
moves left each step and the first-column condition bounds the number
of transitions by v4(I). The complete history equivalence and that
limitation are treated in the companion aligned-history work.
