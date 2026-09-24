# An exact Boolean mask in every power-of-two radix

This note generalizes `EXPLORATION_PERIODIC_DIGIT_MASK.md` and gives
an explicitly counted radix-sixteen interface to the retained
43-operation Pell/binomial kernel. It proves a local digit predicate.
It supplies neither a complete Life constraint encoding nor a new
universal-system certificate. Numeral constants have no construction
cost; multiplying a variable by a numeral still costs one operation.

## 1. The exact identity, with overflow included

Let k>=2 and N>=1 be integers, and put

    R=2^k, L=R^N, J_R=(L-1)/(R-1), M=(R-2)*J_R.

Thus M has N base-R digits equal to R-2. Each digit has k-1 binary
ones followed by a zero, so popcount(M)=(k-1)N. For an arbitrary
integer 0<=P<L define

    r=(L-P)(L-1)+M,
    c=popcount(P)+popcount(M)-popcount(P+M).

The nonnegative integer c counts binary carry events. In particular,
c=0 if and only if P AND M=0. No absence of carries is assumed.

If P+M<L, the normalized base-L expression is

    r=(L-P-1)*L+(P+M).

Since L is a power of two, L-P-1 is the bitwise complement of P in
kN bits. Consequently

    popcount(r)=(2k-1)N-c.                         (1)

If P+M>=L, then P>0 and the normalized expression is

    r=(L-P)*L+(P+M-L).

Here 0<L-P<L, P+M<2L, and

    popcount(L-P)=kN-popcount(P-1),
    popcount(P+M-L)=popcount(P+M)-1,
    popcount(P-1)=popcount(P)-1+v2(P).

It follows that

    popcount(r)=(2k-1)N-c-v2(P).                  (2)

Overflow implies c>=1. Indeed, if c=0, all the forbidden bits of P
vanish, its base-R digits are zero or one, and P<=J_R. Then
P+M<=(R-1)J_R=L-1, contradicting overflow. Equations (1)--(2)
therefore prove the sharp statement

    popcount(r)<=(2k-1)N,
    popcount(r)=(2k-1)N
        iff P AND M=0
        iff every base-R digit of P is zero or one.       (3)

For completeness, the central-binomial valuation follows directly
from v2(n!)=n-popcount(n):

    v2(binom(2r,r))=2*popcount(r)-popcount(2r)=popcount(r).

Thus (3) is precisely

    2^((2k-1)N) divides binom(2r,r)
        iff every base-R digit of P is zero or one.       (4)

The domain 0<=P<L is essential and remains an explicit obligation
of any surrounding compiler. Also, L and M are even and L-1 is
odd, so

    r=P modulo 2.                                      (5)

The lemma itself applies to both parities of P.

## 2. The radix-sixteen Pell interface before power decoding

Suppose the surrounding integer equations establish q>=4 and
0<=P<L, and supply a positive lambda with

    L=q^8, D0=q^14, 15*lambda+1=L,
    r=(L-P)*(15*lambda)+14*lambda.                       (6)

Write N0=q^7 as proof notation only; the arithmetic interface supplies
D0=N0^2 and need not construct N0. These equations are interpreted
as ordinary integer equations before any power-of-two conclusion.
Because P<=L-1 and 0<14*lambda<L,

    N0=q^7 < L-1 < r < L^2=q^16 < q^21=N0^3.            (7)

For the lower inequality r> L-1, use L-P>=1 and lambda>0.
For the upper inequality, use
r<=L(L-1)+14(L-1)/15<L^2. In particular N0>=64 and the
retained kernel's size hypotheses N0<=r<2N0^3 hold. The conclusion
does not require a small packed word such as P<q^5 or P<q^6.

The kernel supplies positive U=w*D0 and Y=s*D0. Hence U,Y>=D0,
and with E=UY and a=Y(U+1),

    E>=q^28>r+1,
    a>q^28>2r+1,
    4r/a<4/q^12<1/2.                                  (8)

These are the preliminary inequalities used by the retained exact
index, ratio, and first exponential arguments. Applying that kernel
in the proof order established in `BASE_TWO_PELL_90_PROOF.md` gives

    U=2^(2r+1), D0 divides binom(2r,r).

Since D0=q^14 divides U and q is a positive integer, q is a power
of two. Write q=2^e, where e>=2. Then

    L=q^8=16^(2e), N=2e,
    D0=q^14=2^(14e)=2^(7N).

Equation (4), now with k=4, proves that P is Boolean in radix
sixteen. This establishes the scale and threshold without assuming
the conclusion of the digit test during the preliminary bounds.

Conversely, for an admissible power-of-two q and a Boolean radix-
sixteen P<L, equation (4) gives the required central-binomial
divisibility. If P is even, (5) gives even r and 2r+1=1 modulo 4.
The positive necessity construction of the retained kernel then
applies with N0=q^7 and D0=q^14: choose U=2^(2r+1), take Y as the
integer part of the usual binomial approximation, and use the
positive Pell and half-parameter witnesses from
`BASE_TWO_PELL_90_PROOF.md` and `HALF_PARAMETER_PELL_92_PROOF.md`.
The scale bound (7), the binomial divisibility, and even r supply
their hypotheses. In particular 2r+1 is larger than the binary
exponent of D0, so D0 divides U; the binomial congruence supplies
D0 dividing Y. No unproved positive auxiliary construction for odd
P is asserted here. Evenness must come from the surrounding encoding
or be imposed with its arithmetic cost accounted for.

## 3. Field alignment is a separate consequence of geometry

The local digit predicate in Section 2 needs only q to be a power
of two: q^8 is automatically a power of sixteen. However, extracting
independent radix-sixteen words from a concatenation with base-q
field boundaries requires q itself to be a power of sixteen.

One sufficient integer geometry is

    W=v^4, q=v*quot, q-1=H*(W-1), v>=2,

with H and quot positive. It gives q>=W>=16 before any Pell
argument. After that argument, q=2^e and v divides q, so v=2^m
for an integer m>=1. Divisibility of q-1 by W-1 is now

    2^(4m)-1 divides 2^e-1.

Euclidean reduction of e modulo 4m shows that 4m divides e. Thus
q=W^t=16^(mt) for a positive integer t, and

    H=1+W+...+W^(t-1).

The field boundaries are aligned and H is the actual row-start
indicator. This proof must precede any inference that separate
base-q fields are independently Boolean. The arithmetic of this
geometry, including W=v^4, is additional to the local mask schedule
below; it is not supplied at no cost by this note.

## 4. Eleven explicit operations and their exact interface

Construct the powers in five multiplications:

    q2=q*q,
    q4=q2*q2,
    q6=q4*q2,
    L=q4*q4,
    D0=L*q6.

The scale D0 is exactly q^14; N0=q^7 remains proof notation.
The mask geometry requires two more operations:

    fifteen_lambda=15*lambda,
    L_check=fifteen_lambda+1,

with the free equality test L_check=L. Finally construct r in four
operations:

    gap=L-P,
    product=gap*fifteen_lambda,
    M=14*lambda,
    r=product+M.

The total is eleven operations: eight multiplications and three
additions/subtractions. Every variable power in the interface is
produced by the displayed multiplication chain. The inputs are q,
P, and lambda; positivity, P<L, field geometry, parity, and the
43-operation Pell system are separate surrounding obligations.

For the direct-length radix-four interface used in round43, the
power chain q2,q4,L=q^8,D0=q^12 has four multiplications, while its
mask geometry and r use the same two and four operation counts.
That specified outer schedule costs ten operations, seven
multiplications and three additions. The radix-sixteen interface
therefore adds one multiplication to that component. This is an
exact comparison of the two displayed schedules, not an optimality
claim and not an operation count for a complete Life encoding.

## 5. Focused exact checks

`../verification/explore_general_radix_boolean_mask.py` checks both
branches of the exact popcount formula, the Boolean equivalence,
and parity for every P in bounded complete ranges for radices
4, 8, 16, and 32. It also checks direct central-binomial valuations
in smaller ranges, verifies the eleven-register schedule symbolically,
and tests the pre-power bounds at admissible values of q including
non-powers of two. Separate finite geometry checks corroborate the
alignment implication. The JSON receipt reports their exact scope.
These finite checks support the proof above and do not test a full
Life or universal-machine system.

## 6. Six radix-sixty-four fields need only the q^11 scale

For six nonnegative words F0,...,F5 individually below q, the usual
concatenation P=F0+q*F1+...+q^5*F5 satisfies P<q^6. Its construction
uses five multiplications and five additions, separately from the
mask component. Put

    L=q^6, D0=q^11, 63*lambda+1=L,
    M=62*lambda, r=(L-P)*(63*lambda)+M.                    (9)

Five products suffice for the powers:

    q2=q*q, q3=q2*q, q5=q3*q2, L=q3*q3, D0=L*q5.

The two geometry operations and four operations constructing r are
unchanged in count. This local mask again costs eleven operations,
eight multiplications and three additions/subtractions. These costs
do not include the ten operations concatenating six previously
available fields, their bounds, or their construction.

There is an apparent square issue: D0=q^11 need not be a square
before power decoding. No square is in fact required by the retained
arithmetic kernel. Its only scale input is D0, used in U=w*D0 and
Y=s*D0. To audit the proof, let n=q^5 be an integer used only in
inequalities. For q>=4 and 0<=P<L,

    n=q^5 < L-1 < r < q^12 < q^15=n^3,
    D0=q^11 > n^2,
    U,Y>=D0>n^2>=4096.                                  (10)

The published exact-index argument uses n only to obtain the
inequalities E=UY>r+1, a=Y(U+1)>J=2r+1 and the lower bounds on
the Pell indices. These hold here, with the explicit stronger bounds

    E>=q^22>r+1, a>q^22>J,
    4r/a<4/q^10<1/2.

The first norm's index congruence, relaxed auxiliary rank argument,
and half-parameter recovery involve r,E,A,c and their stated
bounds; none invokes n^2 dividing an integer. The ratio argument
then gives Y>=U^r. As U>=4096 and r>=64, the first exponential
criterion again has

    2^(3J)=8*64^r<U^(r+1)<a,
    U^3<=U^r<a.

It follows that U=2^J. This proves q is a power of two from q^11
dividing U. Finally the exact rounding proof produces
Y=binom(2r,r) modulo U. Because D0 divides both U and Y, its
conclusion is D0 divides binom(2r,r), directly. At no stage does
one replace D0 by n^2 or assume D0 was a square.

Write q=2^e after this conclusion. Now L=64^e, so N=e and
the required threshold is 2^(11N)=q^11=D0. Section 1 applies.
For necessity, D0 is a power of two and D0<r^2<U=2^J, since
r>L-1=q^6-1. Hence U/D0 is positive integral. Central-binomial
divisibility and the same rounding expansion give positive integral
Y/D0. The remaining positive witnesses are exactly the retained
kernel construction, with even P supplying even r for its original
half-parameter signs. This supplies both directions of the scale
interface without a pre-power square hypothesis.

For independent radix-64 fields, geometry W=v^6, q=v*quot and
q-1=H*(W-1), with v>=2, proves q=W^t=64^(mt) after q becomes
a power of two. The divisibility proof is the one in Section 3 with
6m in place of 4m. Computing W can use
v2=v*v, v4=v2*v2, W=v4*v2: three multiplications. Those are
additional geometry operations, not part of the eleven-operation
mask schedule.

If seven through twelve independently bounded fields are needed,
the conservative interface L=q^12,D0=q^22 is also valid. Six
products construct its powers, for example

    q2=q*q, q4=q2*q2, q6=q4*q2,
    q10=q6*q4, L=q6*q6, D0=L*q10.

The corresponding mask costs twelve operations, nine multiplications
and three additions/subtractions. It has the direct square scale
D0=(q^11)^2. This is a separate capacity choice; adding unchecked
fields to the six-field interface would invalidate its range premise.

## 7. Selecting a different bit and the radix-128 odd-index option

The same proof works for any fixed bit b with 0<=b<k. Replace M by

    M_b=(R-1-2^b)*(L-1)/(R-1).

It still has popcount(M_b)=(k-1)N. Equations (1)--(2) are unchanged
with M_b in place of M, since their derivation only uses that
0<=M_b<L and its popcount. In the overflow case, carry-free addition
would imply P+M_b=P OR M_b<L, again a contradiction. Therefore

    2^((2k-1)N) divides binom(2r,r)
        iff every base-R digit of P is zero or 2^b,
    r=M_b-P modulo 2.                                   (11)

For b=0 this is the preceding Boolean lemma. For b>0, M_b is odd
and every accepted P is even, so every accepted r is odd. The
same-cost kernel in `EXPLORATION_ODD_INDEX_PELL_SIGNS.md` uses
u=jc-J=of-c to supply the positive auxiliary witnesses for odd r;
its sufficiency proof permits either parity of a putative r. This
is the appropriate kernel for the selected higher-bit option.

In particular choose radix 128, b=1, and up to seven fields:

    L=q^7, D0=q^13, 127*lambda+1=L,
    M_1=125*lambda, r=(L-P)*(127*lambda)+M_1.

Again five products suffice:

    q2=q*q, q3=q2*q, q6=q3*q3, L=q6*q, D0=L*q6.

The local mask cost is still eleven operations, eight multiplications
and three additions/subtractions. For q>=4, proof-only n=q^6
gives n<r<q^14<n^3 and D0=q^13>n^2. The scale proof of Section 6
applies word for word with these exponents. Once q=2^e, L=128^e
and the required threshold 2^(13e) is exactly D0. Six fields fit
with spare capacity, P<q^6<q^7. Positive necessity uses the odd-r
signs just described; it does not need an independent parity test.

Field alignment can use W=v^7, q=v*quot and q-1=H*(W-1).
Four products construct W, for example v2=v*v, v3=v2*v,
v6=v3*v3, W=v6*v. After power decoding, divisibility gives
7m dividing e and q=128^(mt). This W construction costs one more
multiplication than W=v^6. Multiplying an already packed P by two
would also cost a multiplication; no such conversion is included
in the eleven-operation mask count.

The homogeneous Life local relation in
`EXPLORATION_LIFE_LOCAL_ARITHMETIC.md` may instead be interpreted
directly on fields with digits zero or two. Dividing its scalar
equation by two gives exactly the original Boolean relation. Its
nonnegative side bounds become 98 and 62, below 128; the inclusive
neighbor-sum variant has bounds 100 and 64, also below 128. Thus
the local predicate itself permits this native scaling without
changing its listed operations. A complete compiler would still
have to encode the target, row marker, shifts, bounds and possible
zero planes in that representation. No saving for a complete
system is inferred from the mask or this local scaling observation.

## 8. Extended regression scope

The accompanying script additionally checks the selected-bit formula
for every bit position of radices 4 through 128 in complete bounded
word ranges. It verifies the q^6/q^11, q^12/q^22 and q^7/q^13
power schedules symbolically, checks their pre-power inequalities
at admissible non-powers of two as well as powers of two, and checks
the relevant geometry divisibilities. These are local interface
checks, not construction of a full torus or of its large Pell
witnesses. The nonsquare-scale argument is the general proof in
Section 6, not a conclusion drawn from the finite tests.
