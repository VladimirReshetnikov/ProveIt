# An 80-operation Rule 110 history component in radix eight

This note proves a finite moving-frame history relation using 80
arithmetic operations, 46 multiplications and 34 additions or
subtractions, with two positive parameters I,F, 29 positive unknowns,
and 19 equations. It is not a universal certificate below 90.

The complete schedule and independent fresh source residuals are
`../verification/round44_1980_two_auxiliary_history.py` and its JSON
receipt. All 19 source comparisons, the auxiliary norm correction,
and the primitive counts pass. The system uses radix-eight words;
it is not a claim of numerical equivalence to the old radix-four
endpoint relation for unchanged integers I,F.

## 1. A scalar local relation with only two auxiliaries

For Boolean a,b,c,y, Rule 110 is the relation

    y=b+c-bc(a+1).

It is equivalent to existence of Boolean u,v satisfying

    2a-b-c+4y=2u+3v.                              (1)

This has a complete six-row verification, grouping the symmetric
inputs b,c by their sum s:

| a | s=b+c | Required y | 2a-s+4y | u | v |
|---|---|---|---|---|---|
| 0 | 0 | 0 | 0 | 0 | 0 |
| 0 | 1 | 1 | 3 | 0 | 1 |
| 0 | 2 | 1 | 2 | 1 | 0 |
| 1 | 0 | 0 | 2 | 1 | 0 |
| 1 | 1 | 1 | 5 | 1 | 1 |
| 1 | 2 | 0 | 0 | 0 | 0 |

Changing y to its other Boolean value gives a number outside
{0,2,3,5} in every row. The auxiliary bits are unique and equal to

    u=a XOR (bc), v=b XOR c.                       (2)

They are the old Z and X fields. Eliminating the old D,E from its
three local equations also gives (1) directly.

For radix-eight words A,B,C,Y,U,V that are already Boolean, the
packed version is

    2A+4Y=B+C+2U+3V.                              (3)

The nonnegative raw digits on its sides are at most six and seven,
respectively, so there are no radix-eight carries. With A=8B,
equation (3) is

    15B+4Y=C+2U+3V.                               (4)

This regrouping avoids computing A: the counted schedule uses one
multiplication by 15 instead of separately forming A and 2A-B.
Its soundness is proved using (3), not by assuming that 15B itself
has carry-free digits. Output Booleanity will be explicitly masked.

## 2. Exact system and count

The twelve outer positive unknowns are

    q,v,quot,H,B,C,Y,U,V,alpha,alphaI,lambda.

The seventeen retained positive Pell unknowns are

    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,gamma,y_aux.

To avoid confusion, U and Y without a subscript denote local word
planes. The large Pell quantities will be named U_pell,Y_pell.
Put

    W=v^3, L=q^6, D0=q^10,
    T=B+H,
    P=U+qV+q^2Y+q^3T.                            (5)

The nine outer equations are

    q=v*quot,
    q-1=H(W-1),
    B=8C,
    15B+4Y=C+2U+3V,
    C+2U+3V+alpha=q,
    I+alphaI=v,
    I+WY=C+qF,
    7lambda+1=L,
    r=(L-P)*7lambda+6lambda.                      (6)

The other ten equations are exactly the retained Pell equations (K)
in `EXPLORATION_RULE110_FIXED_INPUT_BOUND.md`, now with

    U_pell=wD0, Y_pell=sD0.

Their 43-operation schedule is unchanged. In particular the main
Pell parameter is still a+2, and the first decoded exponent still
has base two. The local radix eight does not change that exponent.
The full source polynomials are displayed and verified in the new
checker, rather than inferred by renaming an older source.

The outer arithmetic is counted as follows:

| Part | Operations |
|---|---:|
| q^2,q^4,L=q^6,D0=q^10 | 4 |
| v*quot,v^2,W=v^3,q-1,W-1,H(W-1) | 6 |
| B=8C and the local equation (4) | 8 |
| Reuse its right side and add alpha | 1 |
| I+alphaI | 1 |
| Moving-time equation | 4 |
| T=B+H | 1 |
| Four-field Horner packing | 6 |
| 7lambda+1=L and construction of r | 6 |
| Total outer arithmetic | 37 |
| Retained Pell arithmetic | 43 |

The shared bound costs only one addition because C+2U+3V is already
computed by (4). This bound is essential: (4) alone does not give
separate upper bounds on U,V,Y. All multiplications by numerals in
the table are counted. There are 46 multiplications and 34 additions
or subtractions in the complete 80-instruction schedule.

## 3. All pre-Pell bounds follow from positive source equations

Consider an arbitrary positive integer solution. The input bound
gives v>=2. Since H>=1, the geometry gives q>=W=v^3>=8. Write
Rlocal=C+2U+3V. The positive slack equation gives Rlocal<q, and
equation (4) gives Rlocal=15B+4Y. Consequently

    0<B<q/15, 0<Y<q/4,
    0<U<q/2, 0<V<q/3.                            (7)

Also H=(q-1)/(W-1)<q/7, so

    0<T=B+H<(1/15+1/7)q=22q/105<q.               (8)

All four packed fields are positive integers below q. Thus

    0<P<q^4<L=q^6.                               (9)

Only ordinary positive integers have been used; no power or digit
claim enters (7)-(9).

Let n0=q^5 be proof notation, so D0=n0^2 is the computed scale.
Since 7lambda=L-1 and 6lambda is between zero and L,

    r>(q^6-q^4)(q^6-1)>n0,
    r<L^2=q^12<n0^3,
    n0>=64.                                      (10)

The displayed lower estimate follows from (9); for q>=8 its last
inequality is immediate, and it is stronger than the retained
kernel's required n0<=r. Therefore the original hypotheses
n0<=r<2n0^3 hold. In addition

    U_pell,Y_pell>=q^10,
    U_pell*Y_pell>=q^20>r+1,
    a=Y_pell(U_pell+1)>q^20>2r+1.

These are the same preliminary index and ratio margins used by
the retained kernel. There is no square-free-scale issue here:
D0=q^10 is exactly the square of the integer n0=q^5.

## 4. Decode the powers, geometry, and four Boolean fields

Apply the first-index, first-exponential, and exact rounding parts
of `BASE_TWO_PELL_90_PROOF.md`, in their established order. They give

    U_pell=2^(2r+1),
    q^10 divides binom(2r,r).                     (11)

Since U_pell=wq^10, write q=2^e. The retained divisor equation
q=v*quot gives v=2^m with m>=1. As W=v^3 and W-1 divides q-1,

    2^(3m)-1 divides 2^e-1.

Reducing e modulo 3m proves 3m divides e. Thus for an integer t>=1,

    W=8^m, q=W^t=8^(mt), H=1+W+...+W^(t-1).     (12)

This establishes that all base-q field boundaries align with
radix-eight digits before extracting any fields.

Now L=q^6=8^(2e). The general periodic-mask lemma in
`EXPLORATION_GENERAL_RADIX_BOOLEAN_MASK.md`, with k=3 and N=2e,
uses the mask word 6(L-1)/7 and threshold

    2^((2k-1)N)=2^(10e)=q^10.

It applies to (9), (11), and the final equation of (6). Hence P is
Boolean in base eight. Bounds (7)-(8) identify its four complete
base-q fields as U,V,Y,T, each therefore Boolean.

If m=1, H=(q-1)/7 is the largest Boolean radix-eight word below q.
But the Boolean T=B+H is strictly larger than H, a contradiction.
Thus m>=2, v>=4, and

    I<v<=W/8.                                    (13)

Moreover C=B/8<q. The temporal equation, I<W and Y<q imply F<W:
as integers I<=W-1,Y<=q-1,C>=1, one has
qF=I+WY-C<Wq.

## 5. Causal recovery now uses the explicitly masked output

Subtract the geometric row-start word H from the Boolean word T.
At every row start, the resulting normalized B digit is in
{0,6,7}, never one. Indeed, the subtracted H digit is one and the
incoming borrow is zero or one, while the T digit is zero or one.
A zero row-start digit can occur only with T digit one and incoming
borrow zero. It resets the borrow. All subsequent positions in that
row have H digit zero, so they are Boolean and no new borrow starts.

The relation B=8C gives the first row-start digit zero. Thus the
first B row is Boolean. Let c_j,y_j denote base-W rows. Using the
already established ranges, the temporal equation has the unique
row expansion

    c_0=I, c_(j+1)=y_j for j<t-1, y_(t-1)=F.     (14)

The bound I<W/8 forces the next B row start to vanish: that digit
is the highest digit of c_0. Every later c_j is a row of the masked
Boolean Y. Its highest digit is therefore zero or one. The
corresponding next B row start is also in {0,6,7}, so it must be
zero. All row starts vanish, and the subtraction argument proves
that every row of B is Boolean.

This avoids a circular local-rule argument. Boolean Y was extracted
directly from the mask; it is not being assumed as a consequence of
the still-unproved local rule. The first row comes from the input
guard and initial zero digit, and all subsequent rows follow from
(14) and the row-start subtraction property.

## 6. Recover the actual finite Rule 110 evolution

Now B is Boolean, as are U,V,Y. Both shifted neighbor words
A=8B and C=B/8 are Boolean. From (7), A<q as well. Rewriting the
source local equation as (3), its raw digit bounds six and seven
prove the scalar equation (1) at every packed position. Hence Y
is the Rule 110 update word, and (2) identifies its unique local
auxiliaries.

The packed shifts connect two adjacent rows at their seam, but the
first B digit of every row is zero. At a row start the local rule
f(a,0,c)=c is independent of the wrapped left bit. At a row end,
the right bit is zero, being the next row start or the end of the
complete word. The exterior cell immediately beyond a row has
neighborhood (a,0,0), whose output is zero. Thus each y_j is the
actual zero-exterior Rule 110 update of the corresponding finite
source row b_j.

Equation (14) says precisely

    b_0=8I,
    b_(j+1)=8*Rule110(b_j) for j<t-1,
    8F=8*Rule110(b_(t-1)).                        (15)

For intermediate rows, the next row-start zero gives y_j<W/8,
so the shifted successor fits in its stored row. The final source
also has zero last digit: B<q/15<q/8 prevents a Boolean digit at
the highest packed position. The local rule at that final position
then gives final output digit zero. Thus F<W/8 here, and even the
final physical row fits below W. The optional one-cell final
extension of the older implicit-bound construction is unnecessary
under the new bound.

For clarity, positivity of U,V imposes no extra 111 condition.
If ell is the highest occupied position of the complete B word,
then ell is below its last position because B<q/8. At ell,
b=1,c=0 gives v=1. At ell+1, the neighborhood is (1,0,0), giving
u=1. Therefore both planes are nonzero for every nonempty source
word. The output is nonzero as well, since the rightmost source one
has right neighbor zero and persists in the raw update.

## 7. All-positive necessity and complete Pell witnesses

Conversely, let I,F be positive Boolean radix-eight words, and
suppose the moving update b -> 8*Rule110(b), starting at 8I,
reaches 8F after t>=1 steps. Let k be the rightmost occupied position
of the initial word 8I. Choose m large enough that

    m>=k+t+2, m>=2, 2^m>I.

Set v=2^m,W=8^m,q=W^t,quot=q/v=2^(3mt-m), and use the geometric
H from (12). Every source and raw output row has at least two
blank high columns, because the rightmost position increases by
one only after the moving shift. Their row-major words satisfy

    0<B<q/(7*64), 0<Y<q/(7*64).                  (16)

For example, each such row is at most
(8^(m-2)-1)/7. Multiplying this by H and using H(W-1)=q-1 proves
(16) strictly. Put C=B/8, and define the Boolean local U,V by (2).
The zero first and last columns give exact packed shifts and (4).
All B,C,Y,U,V,H are positive, by the rightmost-boundary observations
in Section 6. Set

    alpha=q-(C+2U+3V)=q-(15B+4Y),
    alphaI=v-I.

Both are positive integers. In particular (16) gives
15B+4Y<19q/448<q, proving the new bound without requiring an
extra multiplication in the certificate. T=B+H is Boolean because
the row-start digits of B vanish. All four fields are below q,
so P is Boolean and P<q^4.

Choose lambda=(q^6-1)/7 and r=(L-P)(L-1)+6lambda. At the unit
cell, a=b=0 and y=c, so (1) has value 3c. Its unique solution has
u=0. Thus the least digit of U, and hence of P, is zero. The
periodic-mask parity identity gives even r. The mask theorem also
gives q^10 dividing binom(2r,r).

All hypotheses of the positive retained Pell construction are now
available, before selecting any of its witnesses: n0=q^5>=64,
n0<=r<2n0^3, even r, and D0=n0^2 dividing the central binomial
coefficient. For explicit witness names, put

    J=2r+1, U_pell=2^J,
    Y_pell=floor((U_pell+1)^(2r)/U_pell^r),
    w=U_pell/D0, s=Y_pell/D0,
    a=Y_pell(U_pell+1), A_pell=a+2,
    c=psi_(A_pell)(J), d=chi_(A_pell)(J),
    k=psi_(2U_pell*Y_pell^2+1)(r+1).

Power-of-two and central-binomial divisibility make w,s positive
integers. The strict ratio bounds give positive
eta=c-Y_pell*k and zeta=k-eta. The odd-parameter norm and first
index congruence supply positive tau,h; the first exponential
congruence supplies positive gamma. Finally the positive relaxed
and half-parameter construction supplies i,f,j,o,y_aux, using
even r. These are exactly the proved constructions in
`BASE_TWO_PELL_90_PROOF.md` and `HALF_PARAMETER_PELL_92_PROOF.md`;
no second index or exponent equation is required here.

This supplies every one of the 29 positive unknowns. In particular,
there is no assumption that a possibly zero local auxiliary can be
used as a positive witness, and no odd-r auxiliary existence is
being asserted without its hypothesis.

## 8. Exact endpoint meaning and remaining scope

The system has a positive solution for positive I,F if and only if
I,F are Boolean radix-eight words and, for some positive height,
the finite zero-exterior moving update b -> 8*Rule110(b) reaches
8F from 8I. There is no 111 filter. The change of radix and removal
of that old positivity condition are explicit changes in the
numerical endpoint predicate.

Every nonempty finite source keeps its rightmost one under the raw
Rule 110 step. The moving shift then advances that position by one.
Consequently any endpoint height must equal

    floor(log_8 F)-floor(log_8 I).

This gives a finite decision procedure: first check the Boolean
digits and a positive height difference, then simulate that many
steps. Arbitrarily long histories exist when F varies, but that
does not establish a universal input or halt interface. The
published universal certificate bound remains 90.

## 9. Independent checks and their evidence boundary

The independent finite audit
`../verification/explore_two_auxiliary_history_audit.py` and its JSON
receipt check 19,724 complete candidate T words, yielding 17 positive
outer tuples, of which 15 have no source occurrence of 111. They also
check 30 canonical histories with heights through 16. Every accepted
tuple is compared with the actual moving Rule 110 evolution, not just
the local arithmetic equation. The checks include the source bounds,
field Booleanity, boundary conditions, parity and exact special-mask
popcount.

The complete scalar table proves the local relation. Sections 3-7
establish the general soundness and all-positive converse. The finite
audit is supplementary evidence for those arguments; it does not
construct the enormous Pell witnesses or substitute sampled histories
for the general proof. The separate exact source checker verifies all
19 polynomial residuals and every one of the 80 primitive operations.
