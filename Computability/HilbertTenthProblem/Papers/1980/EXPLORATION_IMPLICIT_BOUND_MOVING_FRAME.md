# An 82-operation finite history system with an implicit bound

**This is an exact improvement of the finite moving-frame history
relation, not a universal certificate below 90.** The full arithmetic
is `../verification/round42_1980_implicit_history_bound.py` and its JSON
receipt: 82 operations, comprising 45 multiplications and 37
additions/subtractions, with positive parameters I,F, 30 positive
unknowns, and 20 source equations. The source and all primitive
residuals were independently read and rerun successfully.

The new packing obtains the necessary bounds from the existing positive
variable r. A vacant interval of digit positions separates the top
field from the lower four fields, and accommodates an extra top digit
of Z. This separation is essential to the proof.

## 1. Exact system and counted changes

Use the same variable names as in
`EXPLORATION_RULE110_FIXED_INPUT_BOUND.md`, except that alpha is
deleted. The 13 outer unknowns are

    q,v,quot,hrow,B,C,Y,D,X,E,Z,alphaI,lambda,

and the 17 positive Pell unknowns remain

    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,gamma,y_aux.

Put

    Q=q^2, W=v^2, L=Q^8, D0=Q^12,
    T=B+hrow,
    P=D+Q*X+Q^2*E+Q^3*Z+Q^7*T.                     (1)

These powers are explicitly computed by the schedule, not treated as
free exponentiation. Its outer equations are

    q=v*quot,
    Q-1=hrow*(W-1),
    B=4C,
    B+C=X+2D,
    4B+D=Z+2E,
    Y+E=X+D,
    I+alphaI=v,
    I+W*Y=C+Q*F,
    3lambda+1=L,
    r=(L-P)*(3lambda)+2lambda.                      (2)

The ten retained Pell equations are exactly (K) of
`EXPLORATION_RULE110_FIXED_INPUT_BOUND.md`, with U=wD0 and
Ypell=sD0. They are unchanged from round41. The independent full
source checker verifies their algebra and the one triangular residual
correction. Their precise proof interface is the first-index,
first-exponential and rounding portions of `BASE_TWO_PELL_90_PROOF.md`,
Sections 1-6, with the second index/exponent omitted.

Relative to round41, delete the two additions computing
4B+(B+C) and then adding alpha, and delete their equality to Q.
In the five-field Horner packing, replace the product Q*T by Q^4*T;
Q^4 is already available. After the three later Horner multiplications,
this puts T at Q^7 instead of Q^4. No instruction is added. The
outer schedule therefore has 39 instructions and the retained kernel
43, totaling 82. Removing alpha leaves 30 positive unknowns and
removing the bound equation leaves 20 equations.

## 2. Preliminary bounds from positivity alone

All assertions in this section concern arbitrary positive integral
solutions, before any power-of-two or Boolean conclusion. The input
bound implies v>=2, so q=v*quot>=2, Q>=4 and W>=4. Put H=hrow
and Aword=4B. From B=4C, one has B>=4. The last equation of (2)
can be written

    r=(L-P)(L-1)+2(L-1)/3.

If P>=L+1 its right side is negative. Hence r>0 forces P<=L.
All five packed summands are positive, so

    Q^7*T<P<=Q^8,
    0<T<Q, 0<B<T<Q.                                (3)

The three local integer equations and positivity give

    D < (5/8)Q,
    X < (5/4)Q,
    E < (37/16)Q,
    Z < (37/8)Q.                                   (4)

For example, B+C=5B/4 and X+2D=B+C, giving the first two;
then Z+2E=4B+D gives the last two. Define the lower packed part

    R=D+Q*X+Q^2*E+Q^3*Z.

Since Q>=4, (4) implies

    0<R<(141/16)Q^4<Q^7.                           (5)

Thus T is exactly floor(P/Q^7), despite the absence of the old
individual field bounds. Moreover T is an integer below Q, so

    P=Q^7*T+R <= Q^7*(Q-1)+R < Q^8=L.             (6)

This excludes P=L before invoking any Pell or popcount theorem.
There is no exceptional endpoint left for the digit-mask lemma.

Let N0=Q^6 be proof notation; only its square D0=Q^12 is computed.
From positive integral P<L,

    r>L-1>N0, r<L^2=Q^16<N0^3, N0>=64.             (7)

The upper bound follows from P>=1:
r<=(L-1)^2+2(L-1)/3<L^2. Consequently (7) supplies the original
retained kernel hypotheses N0<=r<2N0^3, even though the stronger
old lower bound N0^2<r need not be available. Neither Booleanity
nor a binary carry statement was used to establish them.

## 3. First Pell decoding and isolation of all five fields

The retained kernel now applies in its established proof order:
exact main and first indices, the lower ratio estimate, first
exponential decoding, and exact binomial rounding. It yields

    U=2^(2r+1), D0 divides binom(2r,r).

Since U=wq^24, q is a power of two and Q=q^2 is a power of four.
The periodic-mask theorem in `EXPLORATION_PERIODIC_DIGIT_MASK.md`,
with P<L from (6), says exactly that every base-four digit of P
is Boolean.

The gap bound (5) identifies T as its complete top base-Q field.
Therefore T is Boolean, and

    T< Q, T<=(Q-1)/3, B=T-H<Q/3.                  (8)

Reusing the local inequalities with this stronger B bound gives

    D<5Q/24<Q,
    X<5Q/12<Q,
    E<37Q/48<Q,
    Z<37Q/24<2Q,
    Y<=X+D<=B+C<5Q/12<Q.                        (9)

These bounds identify the lower fields exactly. The first three
base-Q digits of R are D,X,E, so each is Boolean. The remaining
quotient floor(R/Q^3) is the entire Z, and therefore it too is
Boolean. There is no separately packed field at Q^4 that could
absorb an overflow of Z. Its possible extra base-four digit at Q
lies in the empty interval before Q^7*T, and is tested as part of
Z. In particular, the proof does not assume or incorrectly conclude
Z<Q.

The equation q=v*quot makes v a power of two. The geometric equation
then gives

    W=4^m, Q=W^t, H=1+W+...+W^(t-1)

for positive integers m,t. If m=1, H is the largest Boolean word
below Q, and Boolean T=B+H<=H contradicts B>0. Thus m>=2,
v>=4, and the input bound gives I<v<=W/4. These deductions still
precede any conclusion that B itself is Boolean.

Finally, I<v<W and Y<Q imply F<W from the temporal equation:

    QF=I+WY-C<I+WY<WQ.

## 4. Causal recovery of B with the larger Z field

The subtraction lemma in `EXPLORATION_FIVE_PLANE_MOVING_FRAME.md`
applies verbatim to B=T-H. At every row start, a B digit is in
{0,2,3}, never one. A zero start resets the borrow and makes every
digit in that row Boolean. B=4C supplies the initial zero start.

Writing b_j,c_j,y_j for the base-W rows, temporal uniqueness gives

    c_0=I, c_(j+1)=y_j for j<t-1, y_(t-1)=F.

Since I<W/4, the next B row starts with zero. This starts the same
prefix induction as in the five-plane proof: on the already processed
prefix, Aword,B,C are Boolean; D,X,E,Z are Boolean by (9) and the
gap extraction; the three local equations give the exact Rule 110
output prefix. The next c row is Boolean, its highest digit cannot
be a row-start one, so it is zero. That resets the next subtraction
borrow and extends the induction.

The fact that Aword=4B and Z may have an extra digit above Q does
not affect the induction. It works with equality modulo successive
powers of W; higher digits cannot alter the already normalized
Boolean prefix. E<Q and Y<Q have already been proved. At completion
every B digit is Boolean, every first-column digit is zero, and Y
is precisely the Boolean Rule 110 output plane.

## 5. The final row can extend one cell beyond the stored width

The spatial argument no longer requires 4Y<Q or Aword<Q. At each
row start the center bit is zero, so f(a,0,c)=c ignores any wrapped
left-neighbor bit. At each row end the right-neighbor bit is zero,
because the next B row begins with zero, or the complete word ends.
Thus every y_j is the actual zero-exterior Rule 110 update of b_j.
Outside the row on the right the neighborhood is (a,0,0), whose
output is zero even when the last source bit a is one.

The temporal identity now says exactly

    b_0=4I,
    b_(j+1)=4*Rule110(b_j) for j<t-1,
    b_t=4F=4*Rule110(b_(t-1)).                     (10)

For nonfinal steps, c_(j+1)=y_j has its last digit zero because the
following source row begins with zero. Hence those raw successors
fit below W/4, and their shifted next source rows fit below W.
For the last step F is only required to be below W. Its highest
digit may be one, and the physical final row 4F may extend to
position m, one cell beyond the stored width. It is nevertheless
the genuine moving-frame successor: the unshifted exterior cell is
zero, and shifting the last in-row output creates precisely that
one new boundary cell.

This is a change in the permitted final rectangle boundary, not in
the infinite-line trajectory or the fixed endpoint relation. It is
not sound to retain the old assertion 4F<W for every solution.

## 6. Exact endpoint relation and all-positive converse

For positive parameters I,F, the system is solvable if and only if:

* I is a Boolean base-four word;
* for some positive integer t, the infinite moving update
  b -> 4*Rule110(b), starting from 4I, reaches 4F in t steps;
* a source row before that final step contains 111.

Soundness follows from the decoding above, and the last condition
is necessary because the positive supplied E is the plane of
products abc. Conversely, choose such a finite run and enlarge m
until m>=k+t+2 and 2^m>I, where k is the initial rightmost position.
This supplies enough blank space for every represented local cell;
there is no need to exploit the optional final extension. Choose
v=2^m, q=2^(mt), quot=2^(m(t-1)) and the geometric H.

The round40 local definitions supply B,C,Y,D,X,E,Z. B,C,Y,F are
positive because the nonempty configuration's rightmost one persists;
111 supplies positive D,E; the rightmost 10 pair supplies X and its
following 100 triple supplies Z. The new input slack alphaI=v-I
is positive. T=B+H is Boolean, because all source rows begin with
zero; it is positive and below Q. D,X,E,Z are Boolean and, with
this sufficiently wide choice, below Q as well.

Define the new sparse P by (1). The four lower fields occupy
positions below Q^4, and the top field T is below Q at position
Q^7. Therefore P<L, and P is Boolean. D's unit bit is zero,
because B's unit bit is zero. Thus P and r are even. The periodic
mask theorem supplies D0 dividing the central binomial coefficient,
and (7) supplies the retained kernel's size hypotheses. The usual
positive necessity construction, including its generic relaxed norm
and half-parameter auxiliary witnesses, now supplies all 17 Pell
unknowns. It requires no removed alpha or second exponent block.

This proves the same fixed I,F relation as round41. In particular,
the rightmost-front identity forces the unique possible height

    t=floor(log_4 F)-floor(log_4 I).

It remains a decidable exact-endpoint relation. With F allowed to
vary, every positive Boolean I supports all durations t>=3: its
rightmost run develops 111 within two updates. Neither fact supplies
a universal raw-input or periodic-tail halt interface.

## 7. Independent arithmetic and finite evidence

The round42 verifier checks the exact 39+43 schedule, all 20 fresh
source residuals, all primitive instructions, the declared variable
set after deleting alpha, the sparse packing expression, and the
unchanged computed squared scale q^24. Its independent rerun passes
82=45M+37A with 30 positive unknowns.

`../verification/explore_gap_packed_moving_frame.py` enumerates 38,874
Boolean T words without assuming B Boolean or imposing the deleted
range bound. It examines 18,678 positive B candidates and finds ten
positive aligned histories. All ten satisfy the proven Boolean
recovery, local evolution, parity and exact popcount threshold.
Seven actually require the extra top digit of Z and the one-cell
final extension. For example, width four and height two admit I=5,
F=69, B=21524 and Z=83028, with Q=65536 and 4F=276>W=256.

These finite tests corroborate the general gap/causality proof and
exercise the changed boundary. The general positive Pell construction
establishes existence of the huge kernel witnesses; the finite checker
does not materialize them. No universal operation bound below 90 is
claimed by either receipt.
