# A complete 53-operation ordinary-input exponent component

For every positive integer input `x`, the [literal source](pell_fixed_affine_exponent.py)
has positive witnesses, and its computed register `Q` has exactly the value

\[
                         Q=8^{32x}.
\]

The complete polynomial costs **53=31M+22A**, with **52 certificate
operations, one comparison, 12 positive existential coordinates**, and
**total degree54**. Its only supplied parameter is `x`; `Q` is a computed
output. A squared finalizer costs54 and has degree108. This is an exponent
component for subsequent composition, not a universal compiler bound.

The [receipt](pell_fixed_affine_exponent.json) records every paid row.
In particular, multiplication by48,4 and `2^31` is charged. No
comparison, exponentiation, odd multiplier, checksum, mask predicate,
or source register is supplied for free.

## 1. Source and the positive output projection

Supply positive integers

    x; delta,s,eta,zeta,g,gamma,f,i,j,o,y,h.

Compute the following graph; these displayed formulas describe the
literal straight-line source, not additional equations:

    r=48x+15, Q=x+delta, X=2^31 Q, Y=s,
    E=XY, k=eta+zeta, c=kY+eta, a=E+Y=Y(X+1),
    H=4a+3, Delta=a²+H=(a+2)²−1,
    L=X+gamma H, D=L+ac,
    t=ic², V=of−c, K=k−hE.

There are exactly six integer factors:

    N0=g²+4E(kY)(g−k),
    N1=D²−Delta c²,
    Ns=f²−Delta t²,
    N3=Delta² t²(V²−y²)+y²,
    Nk=K−r,
    Nl=V−jc+2K.                                      (1)

The single polynomial is

    F=N0 N1 Ns N3 Nk Nl−1.                           (2)

It is unnecessary to supply a separate `Q` coordinate or compare it
with a quotient. Before any equation, positivity gives

    r>=63, Y>=1,
    X−(4r+6)=(2^31−192)x+2^31 delta−66>=2^32−258>0.         (3)

Thus the stronger bound `X>4r+6` is paid by the two definitions `Q=x+delta` and `X=2^31 Q`.
Conversely the target `Q=2^(96x)` is greater than x, so its delta is
positive. This output projection avoids a separate size slack for X
and an external comparison `X=2^31 Q`.

The [power-two43 component](pell_kernel_power_two43.md) proves that a
supplied q is some positive power of two. It does not link that exponent
to an ordinary input x. Here the affine index and positive projection
make that link exact, without importing any native AND geometry.

## 2. All norm signs and the pre-index bounds

At an integer zero of(2), each factor is+1 or−1. Each of the first four
factors excludes−1 modulo4. For N0 the cross term is divisible by4.
For N1 and Ns, Delta is0 or3 modulo4, so a difference of the indicated
square and Delta times a square never equals3 modulo4. The coefficient
of `V²−y²` in N3 is the square `(Delta t)²`; modulo4 its value is
therefore either y² or V². This does not presume that V is positive.
Consequently

    N0=N1=Ns=N3=1, Nk=epsilon, Nl=lambda,
    epsilon,lambda in{−1,1}, epsilon lambda=1.        (4)

Write `A=a+2`, `P=2XY²+1`. From(3), before identifying any Pell index,

    E>=X>4r+6>2r+3,
    P>A>2.                                          (5)

The last inequality follows directly from X>=64,Y>=1:
`P−A=XY(2Y−1)−Y−1>0`. Positivity of
eta,zeta supplies the strict ratio `kY<c<k(Y+1)`.

N0=1 implies g odd, and

    tau=XY²k+(g−1)/2>0,
    (g+2XY²k)²−(P²−1)k²=1.

The ordinary Pell classification therefore gives `k=psi_P(n)`, n>=1.
Since P=1 modulo E, `k=n mod E`. From Nk and(5),

    K=k−hE=r+epsilon, 0<K<E, n>=r−1.                (6)

N1 gives `c=psi_A(p), D=chi_A(p)`, p>=1. Monotonicity in both the
index and the parameter, P>A and c>k imply p>n, hence p>=r>=63.
Elementary Pell growth now gives the three bounds

    c>A Delta², c>2p,
    c>k=hE+r+epsilon>E>2(2r+3).                          (7)

For example `psi_A(p)>=(2A−1)^(p−1)>A^5>A Delta²`.
Here h>=1 and r+epsilon>0; the last bound uses the index factor
after its unit sign is known. It does not assume a Pell index in advance.
This proves the large-index hypotheses from the paid input bound;
no preliminary packed-width bound such as r<q^4 is used.

## 3. Recovering both exact indices before exponent decoding

The retained strong equation is the full normalized equation Ns=1.
Set `T=Delta t`. Then

    T²=Delta(f²−1), c² divides T, T>0.

The generic integral-rank/divisibility argument in the
[relaxed auxiliary proof](../../1980/PELL_RELAXED_AUXILIARY_PROOF.md),
applied with(7), gives

    f=chi_A(m), T=Delta psi_A(m), c divides m,
    m>=c>2p.                                       (8)

The theorem is generic in A>1. In particular it does not require the
historical packed field definitions. It uses the full c² divisibility;
no weakened strong equation is substituted here.

Thus `f>chi_A(2p)=1+2Delta c²>2c`, and V=of−c is positive. Set

    Jnew=2K−lambda.

Equations(4),(6),(7) give

    V=jc−Jnew=of−c,
    0<2r−3<=Jnew<=2r+3<c/2, 0<p<c/2.              (9)

The local odd-index and signed step-down argument of
[native coupled units, Section2](native_binary_index_coupled_units.md#2-bounds-and-the-common-rank-argument-before-typing)
therefore applies with exactly these hypotheses. To specify its use:
N3 is `(TV)²−(T²−1)y²=1`; its positive Pell index ell is odd. The
odd-index quotient polynomial gives

    V=(-1)^((ell−1)/2) psi_A(ell) mod f,
    V=(-1)^((ell−1)/2) ell mod c.

Together with V=−c mod f and the full index divisibility(8), signed
step-down yields `ell=+p or−p mod m`. The second congruence then yields
`Jnew=+p or−p mod c`. The strict bounds(9) exclude the negative
representative and nonzero multiples of c. Hence

    p=Jnew=2K−lambda.                               (10)

This invokes only the individual rank and signed-index lemmas, with
all their size and positivity hypotheses checked in(5)--(9). It does
not invoke the complete AND theorem or any bit interpretation.

Now p<=2r+3<E and n<p. The congruence n=K mod E identifies n=K
exactly. If lambda=−1, (10) would give p=2n+1. But with
`A2=2A²−1`, direct substitution gives A2>P and2A>Y+1. Duplication and
monotonicity imply

    psi_A(2n)=2A psi_A2(n)>k(Y+1).

Then c=psi_A(2n+1) contradicts the upper ratio. Therefore lambda=1.
Because there is no checksum or other potentially negative factor,
(4) also gives epsilon=1. We have proved

    n=r+1, p=2r+1, K=r+1.                           (11)

## 4. The lower ratio supplies the modulus size

Put `xi=(X+1)^(2r)/X^r`. At the indices(11), the elementary Pell bounds
from [power-two43, Section3](pell_kernel_power_two43.md#3-lower-ratio-first-then-the-direct-exponent-recurrence)
are

    c/k >= xi(1+3/(2a))^(2r)(1+1/(2XY²))^(−r)>xi,
    c/k < xi(1+2/a)^(2r).                           (12)

These inequalities follow directly from the usual lower and upper
bounds `(2A−1)^(p−1)<=psi_A(p)<(2A)^(p−1)` and their counterparts
for P. The strict lower factor follows from6XY²>a, valid already for
X>=64,Y>=1. No Y divisibility or minimum16 is needed.
Use this inequality first. The supplied upper ratio gives xi<Y+1;
since xi>X^r and Y is an integer,

    Y>=X^r, a>X^(r+1)>2^(2r+1).                    (13)

For the last inequality X>=64 and r>=63 are more than sufficient.
The sequence `chi_A(v)−a psi_A(v)` starts with1,2 and obeys the same
second-order recurrence as the Pell sequences. Modulo H=4a+3 it agrees
with `2^v`, since `4−4A+1=−H`. The definition D=X+ac+gamma H gives

    X=2^p mod H.

Both X and2^p are strictly between0 and H by(11),(13), so

    X=2^p=2^(96x+31), Q=X/2^31=8^(32x).            (14)

This is a direct recurrence plus an independently proved no-wrap
bound. It does not assume an exponent criterion requiring a stronger
initial bound on r.

### Signed-unit projection for guarded composition

A separate necessary conclusion holds if the product of the six factors
is either+1 or−1. All six factors are then integer units, the four norm
signs are still positive, and Sections2--3 through the proof `lambda=1`
remain valid. With epsilon=Nk, define `r*=r+epsilon−1`. The exact indices
are

    n=r*+1, p=2r*+1, r*>=61.

Repeat(12)--(13) with r* in place of r. Their only relevant lower bounds
are X>=64,Y>=1,r*>=61, which hold independently of either sign. The
same recurrence and no-wrap argument therefore give

    Nk=+1: Q=2^(96x),
    Nk=−1: Q=2^(96x−4),
    Nl=+1 in both cases.                            (18)

This is a necessary signed projection, not an assertion that an
arbitrary negative-product tuple extends. There is no
additional sign-excluding factor. Thus a composition may not merge
this product into an unrelated signed-unit product and simply retain
the standalone conclusion(14). It must retain the product=1 comparison
or prove that its own paid constraints exclude the negative branch of(18).

## 5. Positive extension for every input

Fix any positive x and define

    r=48x+15, p=2r+1, X=2^p, Q=2^(96x),
    delta=Q−x>0,
    Y=floor((X+1)^(2r)/X^r).

The binomial expansion gives exactly

    Y=sum_(j=0)^r binom(2r,r+j)X^j,
    0<xi−Y<1/4,
    Y=binom(2r,r) mod X.                            (15)

Take s=Y, which is a positive integer by(15). No central-binomial
divisibility or parity constraint is needed for this source. The receipt
also records the familiar valuation `v2(Y)=popcount(r)=popcount(3x)+4`
as a check of its actual x=1 binomial construction; it is not a hypothesis
of the theorem or a justification for an uncounted source operation.

Define a,A,Delta,E,H as in Section1, and

    c=psi_A(p), D=chi_A(p), k=psi_(2XY²+1)(r+1).

The same estimates(12) prove the strict ratio in the canonical case.
Indeed a>X^(r+1) implies4r/a<1/2, so the upper estimate gives
`c/k<xi(1+8r/a)`. Since xi<Y+1<2Y,

    0<c/k−xi<16r/(X+1)<1/2.

Together with(15), this gives `Y<c/k<Y+3/4`. Hence all the following
coordinates are positive:

    eta=c−kY, zeta=(Y+1)k−c,
    g=chi_(2XY²+1)(r+1)−2XY²k,
    h=(k−r−1)/E,
    gamma=(D−X−ac)/H.                               (16)

For g, the exact difference is `psi_P(r+1)−psi_P(r)>0`.
For h, the first Pell residue makes the quotient integral and growth
makes the numerator positive. The recurrence of Section4 makes gamma
integral; its numerator is positive because
`D−ac=2c−psi_A(p−1)>c>X`.

It remains to provide all five normalized auxiliary coordinates.
Since p=2r+1 is3 modulo4, use

    m=2cp, f=chi_A(m), i=psi_A(m)/c²,
    T=Delta psi_A(m), y=psi_T(p), V=chi_T(p)/T,
    o=(V+c)/f, j=(V+p)/c.                           (17)

The multiple-index identity proves c² divides psi_A(2cp). More
explicitly, `psi_A(pn)=c psi_D(n)` and
`psi_D(n)=nD^(n−1) mod c`; take n=2c. The odd-index quotient is
integral, and the usual quotient polynomial identities give
`V=−c mod f` and `V=−p mod c`, because p=3 mod4. These are the same
canonical congruences used in the complete native coupled proof;
there are no restrictions on an outer bit geometry in(17).
All five quotients/coordinates in(17) are positive. The norms Ns,N3
are1, V=of−c=jc−p, and(11) gives Nk=Nl=1. N0=N1=1 follows from the
chosen first and main Pell coordinates. Thus(16),(17) construct all
12 positive coordinates and make(2) zero for every positive input x.

## 6. Literal count, degree and reproducible evidence

`build()` returns the sole canonical packet. `polynomial_source()`
accepts only that packet and returns all53 paid rows; `sum_of_squares`
adds one final square. `interfaces['power']` names the computed Q.
For composition the52 certificate rows end in the product of six
factors, with the comparison of that product to1 explicitly recorded.
Any external use of Q must keep this complete certificate and its
positive domain. This packet does not provide an arbitrary-host rewrite.

The exact factor degrees are respectively

    N0:5, N1:7, Ns:14, N3:22, Nk:3, Nl:3.

For N1 only, the source's all-integer cancellation is used:

    (L+ac)²−(a²+H)c²=L²+2Lac−Hc².

The checker expands each literal factor and verifies its total degree.
The nonzero product therefore has degree54; subtracting1 cannot change
that degree. All52 certificate gates and the final subtraction are
ancestors of the output. The source contains31 multiplications and22
additions/subtractions; the certificate omits only the last subtraction.

Run `python pell_fixed_affine_exponent.py` for a fresh exact receipt
comparison. The author audit verifies six symbolic factor identities,
the main cancellation,512 complete ordinary/squared output evaluations
on256 assignments (128 signed),512 mod-four norm cases,258 pretyping
and valuation bounds, and640 pairs of modular recurrence checks.
It materializes the actual first/main coordinates for x=1, checks their
strict ratio, positivity and equations, and separately materializes six
small canonical normalized auxiliary blocks. Those blocks are local
fixtures; they are not mislabeled full zeros of the x>=1 gadget.
No enormous full auxiliary tuple is numerically materialized. Its
existence for every x is the proof in Section5.

Author generation and a separate fresh default replay pass for the final
53-operation source. The one-M saving from its initial form uses Y=s
and the stronger bound in(3),(7).
An independent full review of the initial source passed without
findings, including the sign/rank order, lower-ratio-first argument,
positive extension and separate signed classification. Its own symbolic
oracle verifies the six factors and their exact degrees; its separate
manual executor checks320 assignments (160 signed), yielding640 complete
outputs (320 signed). Additional checks cover404 pretyping tuples,
1,312 main-root recurrences,128 affine valuation/delta cases, an actual
x=1 first/main block and eight separate normalized auxiliary blocks.
All six local links resolve. These finite checks corroborate the proof;
they do not materialize a full giant auxiliary tuple.

The same reviewer identified the now-applied Y=s saving and completed
an independent final proof/source/fresh-default review of the53-operation
source without findings. The six symbolic factor identities, exact degree
bounds and320 manual assignments/640 complete outputs were rerun against
the final source. An expanded4,040-case pretyping oracle covers Y=1,2,3
and both index signs. The final proof retains the separate signed-branch
statement; no old Y>=16 hypothesis is used. All six local links and the
whitespace check pass. Source and receipt are frozen after these checks.
