# Exact scope of the 86-operation finite Rule 110 history system

**The round39 system defines a decidable finite-history relation. It is
not a universal representation below 90.** For a fixed positive initial
row I, its running time is at most valuation_4(I), independently of the
chosen rectangle width. This note gives both directions of that
characterization and accounts for the positive supplied auxiliaries.

The arithmetic is `../verification/round39_1980_boolean_history_components.py`
and its JSON receipt: 86 operations, consisting of 46 multiplications
and 40 additions/subtractions, with positive parameters I,F, 31 positive
unknowns, and 21 equations. Equality tests and fixed numerals are free.
The exact residual checker was independently rerun. No source equation
is silently discarded in the characterization below.

## 1. The complete source system

The 14 outer unknowns are

    q,v,quot,hrow,B,C,Y,D,X,E,Z,alpha,alphaI,lambda.

The 17 kernel unknowns are

    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,gamma,y_aux.

All are positive integers. Capital B,C,Y,D,X,E,Z here name the source
variables Bw,Cw,Yw,Dw,Xw,Ew,Zw. This avoids confusing a local word
with a Pell coordinate. The following are mathematical abbreviations
for explicitly counted straight-line registers:

    Q=q^2, W=v^2, L=Q^8, D0=Q^12, Aword=4B,
    P=B+Q*(D+Q*(X+Q*(E+Q*(Z+Q*(B+hrow))))).

The eleven outer equations are

    q=v*quot,
    Q-1=hrow*(W-1),
    B=4C,
    B+C=X+2D,
    4B+D=Z+2E,
    Y+E=X+D,
    4B+B+C+alpha=Q,
    I+alphaI=W,
    I+W*Y=B+Q*F,
    3lambda+1=L,
    r=(L-P)*(3lambda)+2lambda.                         (O)

For the retained kernel put

    U=w*D0, Yp=s*D0, A=a+2, Dpell=A^2-1,
    K=Dpell*(f^2-1), u=2r+1+jc.

Its ten equations are

    U*Yp^2*(U*Yp^2+1)*k^2=tau*(tau+1),
    c=Yp*k+eta,
    k=eta+zeta,
    k=r+1+h*U*Yp,
    a=Yp*(U+1),
    d=U+a*c+gamma*(4a+3),
    d^2=1+Dpell*c^2,
    (i*c^2)^2=Dpell*(f^2-1),
    K*(u^2-y_aux^2)=1-y_aux^2,
    u=c+o*f.                                          (K)

The source uses K in the penultimate equation. Its straight-line
implementation reuses (i*c^2)^2, justified by the preceding equation;
the checker verifies the exact residual correction. It materializes
only D0=q^24, not a separate square-root scale. The outer and kernel
schedules each contain 43 instructions.

The kernel's soundness and positive construction are the applicable
parts of Sections 1-6 of `BASE_TWO_PELL_90_PROOF.md`, with every second
index/exponent equation omitted. The scale used in that proof is
N0=Q^6, so N0^2=D0. The required interface is established below; it is
not inferred from an already decoded history.

## 2. Noncircular decoding of every solution

Positivity and the first outer equations give B>=4, C>=1, Aword>=16,
Q>=22, and q>1. The geometry excludes v=1, so W>=4 and

    0<hrow=(Q-1)/(W-1)<Q/3, B<Q/4.

The local integer equations give

    D<=(B+C)/2, X<=B+C,
    E<=(4B+D)/2, Z<=4B+D,
    Y=X+D-E<=X+D<=B+C.

Hence B,D,X,E,Z,Y and B+hrow are all below Q before any Boolean or
power-of-two interpretation. Their Horner concatenation satisfies
0<P<Q^6=N0. The positive bound on I gives I<W, and the temporal
equation then yields

    QF=I+WY-B <= (W-1)+W(Q-1)<WQ,

so F<W as well.

Writing L=Q^8 and 3lambda=L-1, the last outer equation implies

    N0<r<L^2=Q^16<N0^3, N0>=64.

These are stronger than the retained kernel's preliminary hypotheses.
Its exact-index, ratio, and first-exponential proof therefore applies
and gives

    U=2^(2r+1), D0 divides binom(2r,r).

Since U=wq^24, q is a power of two, and Q=q^2 is a power of four.
The special periodic-mask theorem in `EXPLORATION_PERIODIC_DIGIT_MASK.md`
then identifies this binomial divisibility exactly with Boolean base-four
digits of P. Because all six fields were already bounded below Q and
Q is a power of four, this restricts each field B,D,X,E,Z,B+hrow.

The positive divisor v of q is also a power of two. The geometric
equation consequently gives

    W=4^m, Q=W^t, hrow=1+W+...+W^(t-1)

for integers m,t>=1. Booleanity of B and B+hrow forces B's first
column to vanish in every row. Width m=1 would make B=0, and is
therefore excluded by positivity without a separate equation.

The local equations now recover D=bc, X=b XOR c, E=abc, Z=a XOR bc
at each digit, and Y is exactly Rule 110's output. The shift words
Aword=4B and C=B/4 provide the actual neighbors except possibly the
left neighbor at row starts. There the center bit is zero, so the rule
f(a,0,c)=c ignores the spurious value. The right neighbor at every row
end is zero. Temporal alignment gives exactly a sequence of t updates
with initial row I and final row F.

At a row end f(a,b,0)=b. Thus temporal alignment makes every source
row's last bit equal. Aword<Q forces the highest one zero, so all
last-column bits vanish. Extending every row by zeros outside the
rectangle gives a genuine infinite-line Rule 110 run through the final
time. The final first-column bit can be one; there is no further update
requiring it to remain zero.

## 3. Leading and trailing fronts

For a nonempty finite binary configuration on the integer line, let
ell be the position of its leftmost one and k the position of its
rightmost one. One Rule 110 step has leftmost one exactly ell-1 and
rightmost one exactly k.

Indeed, the cell at ell-1 has neighborhood 001 and becomes one;
all cells farther left have neighborhood 000 and remain zero. The
rightmost one has neighborhood a10 and remains one, while every
cell farther right has neighborhood a00 or 000 and remains zero.
This proof uses no assumption about the configuration between its ends.

For the decoded positive Boolean base-four word I, the initial left
position is ell=valuation_4(I), and the right position is its largest
nonzero digit index k. At time j these fronts are ell-j and k. All t
source rows have zero first column. Therefore

    1<=t<=ell.                                         (F)

This bound is independent of m and Q. At final time,

    valuation_4(F)=ell-t.

For fixed positive I,F, even the proposed height is uniquely determined:
t=valuation_4(I)-valuation_4(F). Increasing the number of blank columns
on the right cannot change a trajectory: the rightmost one never moves
right. Increasing the padding on the left would multiply I by a power
of four, and therefore change the fixed parameter I.

## 4. Exact positive-domain characterization

For positive integers I,F, the complete system (O),(K) is solvable
in its 31 positive unknowns if and only if the following finite condition
holds:

1. I is a Boolean base-four word.
2. For some integer 1<=t<=valuation_4(I), the infinite-line Rule 110
   evolution of I, initially zero outside its encoded support, has
   encoded final word F after t steps.
3. A block 111 occurs in at least one of the source configurations at
   times 0,...,t-1.

The source proof just given establishes the first two conditions. The
third is exactly positivity of E: it sums the local products abc over
the source tableau. It is necessary, not merely a convenient motif
assumption.

For the converse, take a finite run satisfying these conditions, and
choose an integer width m>k+1. Put

    W=4^m, Q=W^t, q=2^(mt), v=2^m,
    quot=2^(m(t-1)), hrow=(Q-1)/(W-1).

Pack the source rows as B and successor rows as Y, and form their
correct local auxiliary planes D,X,E,Z. Condition (F) makes the first
column zero in every source row, and m>k+1 supplies a zero last column
and an additional cell to the right of the rightmost one.

Every required word is positive. B is nonzero, C=B/4 is positive,
and Y and F are nonzero because the rightmost one persists. The
occurrence of 111 makes E positive and also makes D positive. At each
rightmost one, the pair bc is 10, so X is positive. Immediately to its
right, the triple is 100, so Z is positive. The sixth word B+hrow
is positive because hrow>0. No separate 1110 motif is required.

All six packed fields, and therefore their base-Q concatenation, are Boolean
base-four words.
The zero highest digit gives

    B <= (Q/4-1)/3 < Q/12,
    4B+B+C=(21/4)B<7Q/16<Q.

Thus alpha=Q-(4B+B+C) is positive. Also I<W and
alphaI=W-I is positive. Temporal alignment and all local equations
hold by construction. Form P from the six words, set
lambda=(L-1)/3 and r=(L-P)(L-1)+2lambda. These are positive integers,
and P<Q^6. Boolean P and the special-mask theorem give D0 dividing
binom(2r,r). Since B's unit digit vanishes, P is even and hence r is
even. Moreover N0<r<N0^3 and N0 is a power of two.

The retained kernel's positive necessity construction now applies:
choose U=2^(2r+1), w=U/D0,
Yp=floor((U+1)^(2r)/U^r), s=Yp/D0, and the canonical main and
first Pell coordinates. Its ratio estimates give positive eta,zeta;
its index and exponential congruences give positive h,gamma,tau.
The relaxed auxiliary and half-parameter construction at this generic
base supplies positive i,f,j,o,y_aux because r is even. These are
exactly the remaining variables in (K). This proves the full converse,
not just existence of an outer Boolean history.

## 5. Decidability and the universal-interface limitation

The characterization is decidable by direct finite computation. First
reject non-Boolean I or F. Compute ell=valuation_4(I) and the only
candidate t=ell-valuation_4(F); reject unless 1<=t<=ell. Simulate those
t steps, compare the result with F, and check whether a source row
contains 111. Every simulated row lies between positions zero and k,
and t<=k. A straightforward implementation therefore runs in time
polynomial in the bit lengths of I and F.

In particular, declaring I to be the raw universal query input, with
F fixed or subject to a decidable final-pattern test, does not provide
an undecidable halting relation: only finitely many bounded steps are
available. An initial row containing an appropriately placed 1110
motif is a sufficient positivity device, but does not change this bound.

An unbounded padding witness that changes I, or another computation
model with a different boundary interface, is a substantive new task.
For Cook's universal simulation one must additionally encode the required
periodic-tail initial configuration and a sound finite halt-event cone.
The 86-operation result is a verified arithmetic description of the
decidable relation above, not a new universal certificate.

## 6. Finite corroborating checks

`../verification/explore_rule110_fixed_input_bound.py` exhausts nonempty
Boolean words of bounded length. It checks both front identities, the
unique candidate time, equivalence of accumulated auxiliary positivity
with a source occurrence of 111, and the complete eleven outer equations
for the positive cases using the chosen width. It also checks the
special packing's ranges, even parity, and popcount valuation threshold.
It does not materialize the enormous canonical Pell witnesses. Their
existence is established by the general retained-kernel construction
used in Section 4, not inferred from this finite regression.
