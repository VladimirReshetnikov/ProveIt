# A 52-operation positive ordinary-input exponent component

The [literal source](pell_fixed_affine_exponent52.py) computes an output
`Q` with the exact positive-zero projection

    Q=8^(32x),  x>0.

Every positive integer x has a positive extension. The complete polynomial
costs **52=31M+21A**, with **51 certificate gates, one comparison and12
positive existential coordinates**. Its total degree is **54**. The sole
supplied parameter is x; Q is computed. Squaring the final output costs53
and has degree108. This is a paid exponent component, not a universal
compiler operation bound.

The [53-operation parent](pell_fixed_affine_exponent.md) remains unchanged.
This successor removes its affine index offset and reverses both auxiliary
congruence signs. It proves the same input/output projection using fresh
positive Pell coordinates; it does not claim that old supplied tuples or
arbitrary-point polynomials are unchanged. The
[receipt](pell_fixed_affine_exponent52.json) records the full new source.

## 1. The exact source and its unconditional bounds

Supply the same positive integers

    x; delta,s,eta,zeta,g,gamma,f,i,j,o,y,h.

Compute

    r=48x, Q=r+delta, X=2Q, Y=s,
    E=XY, k=eta+zeta, c=kY+eta, a=Y(X+1),
    H=4a+3, Delta=a²+H=(a+2)²−1,
    L=X+gamma H, D=L+ac, t=ic²,
    V=of+c, K=k−hE.

The six literal integer factors are

    N0=g²+4E(kY)(g−k),
    N1=D²−Delta c²,
    Ns=f²−Delta t²,
    N3=Delta² t²(V²−y²)+y²,
    Nk=K−r,
    Nl=jc−V+2K.                                      (1)

Let U be their product. The complete source polynomial is U−1.
Every numeral multiplication is charged. Relative to the canonical
parent, its two rows `48x` and `48x+15` become the single row `r=48x`;
Q and X each retain one paid gate, and both sign reversals retain one
addition/subtraction. The source saves exactly one addition.

Before any equations, put A=a+2 and P=2XY²+1. Positivity alone gives

    r>=48, X>=2r+2>=98, Y>=1,
    E>=X, A>=X+3>=2r+5,
    P−A=XY(2Y−1)−Y−1>0.                             (2)

The positive slacks give `kY<c<k(Y+1)`. Unlike the parent, it is not
necessary to prove E>2r+3 before the equations. Section3 supplies the
needed first-index argument without that stronger bound.

## 2. Norm signs and the plus-congruence rank argument

We prove a stronger signed statement: suppose U is either+1 or−1.
Every factor in(1) is an integer unit. The same unconditional modulo4
arguments as the parent give

    N0=N1=Ns=N3=1, Nk=epsilon, Nl=lambda,
    epsilon,lambda in{−1,1}.                         (3)

For N0 the cross term is divisible by4. For N1 and Ns, Delta is0 or3
modulo4. For N3 its coefficient `(Delta t)²` is a square, so its residue
is either y² or V². These exclusions use no auxiliary sign or parity
assumption about Y.

The positive first-root inverse gives

    (g+2XY²k)²−(P²−1)k²=1,
    k=psi_P(n), n>=1, k=n mod E.

Since `K=r+epsilon` lies strictly between0 and E by(2),

    n=K+vE, v>=0, n>=r−1.                           (4)

The main norm gives `c=psi_A(p), D=chi_A(p)`. Because P>A and c>k,
p>n and p>=r>=48. Therefore

    c>A Delta², c>2p,
    c>=psi_A(2)=2A>4r+6.                            (5)

The first inequality follows from `(2A−1)^(p−1)>A^5>A Delta²`.
The third uses the much larger main index already proved, not a
presumed linear sign or a size assertion about Y.

For clarity, the normalized strong equation permits a direct integral
rank argument here. Ns=1 gives

    f=chi_A(m), psi_A(m)=ic², m>0.

Strong divisibility of psi implies p|m. Write m=pb. The multiple-index
binomial expansion gives

    psi_A(pb)/c = b D^(b−1) mod c.

The left side is divisible by c and `gcd(D,c)=1`, so c|b and **pc|m**.
In particular m>2p+1, c divides m, and

    T=Delta*psi_A(m),
    f>2chi_A(2p)>2c, T>1.                            (6)

These are stronger than the generic rank conclusions used in the parent.
All conclusions follow from the full normalized norm; no weakened
strong-divisibility premise is introduced.

Set `J=2K−lambda`. The reversed linear factor says

    V=jc+J=of+c,
    0<2r−3<=J<=2r+3<c/2, 0<p<c/2.                  (7)

V is positive directly from its graph definition. The auxiliary norm is
`(TV)²−(T²−1)y²=1`, so it has an odd positive Pell index ell, with
`TV=chi_T(ell)`. An even ell is excluded by
`chi_T(2z)=(-1)^z mod T`. The odd quotient polynomial gives

    V=(-1)^((ell−1)/2) psi_A(ell) mod f,
    V=(-1)^((ell−1)/2) ell mod c.                   (8)

These follow by writing `chi_T(2z+1)=T L_z(T²)`, where
`L_0=1,L_1=4Z−3` and `L_(z+1)=(4Z−2)L_z−L_(z−1)`.
The same recurrence proves `L_z(0)=(-1)^z(2z+1)` and
`L_z(1−A²)=(-1)^z psi_A(2z+1)`. Here T is divisible by c and
`T²=1−A² mod f`.

The changed congruence is V=+c mod f. Squaring it in(8) gives exactly
the same `chi_A(2ell)=chi_A(2p) mod f` as a negative congruence.
The strict signed step-down can be stated directly. Choose a nearest
multiple of m, writing `ell=+z+km` or `ell=−z+km` with0<=z<=m/2.
The Pell pair at2m is `(-1,0) mod f`, hence

    chi_A(2ell)=(-1)^k chi_A(2z) mod f.

If2z=m, the right side is zero modulo f, whereas
`0<chi_A(2p)<f/2`. Otherwise `chi_A(2z)<=chi_A(m−1)<f/3`,
since A>=3. Odd k would make a positive sum smaller than f divisible
by f. Even k identifies the two small chi coordinates, hence z=p.
Thus ell=+p or−p modulo m, and therefore modulo c by(6).
Combining with the second congruence of(8) and V=+J mod c gives
`J=+p or−p mod c`. The strict bounds(7) force

    p=J=2K−lambda.                                  (9)

This explicitly verifies that reversing both congruence signs retains
the rank conclusion; it does not assume the parent's minus-congruence
linear comparison. The underlying quotient and step-down identities are
also recorded in [the auxiliary sign proof, Section2](complete75_weakened86_auxiliary_sign_lift.md#2-two-quotient-identities-and-a-strict-step-down).

## 3. The exact first index does not require p<E

From(9), p<=2r+3. If v>=1 in(4), then

    n>=r−1+E>=3r+1>2r+3>=p,

contradicting n<p. Therefore n=K exactly. This argument matters at the
smallest formal corner: r=48, X=E=98, K=49 and candidate p=99 obey
the signed preliminary formulas, so p<E is not an available premise.
Their first wrapped index would be147, which the displayed inequality
correctly excludes. This is a pretyping boundary fixture, not a Pell zero.

If lambda=−1, then p=2n+1. Put A2=2A²−1. Direct substitution gives
A2>P and2A>Y+1. The duplication identity implies

    psi_A(2n)=2A psi_A2(n)>k(Y+1),

contradicting c=psi_A(2n+1)<k(Y+1). Consequently

    Nl=1, n=r+epsilon, p=2r+2epsilon−1,
    U=epsilon.                                      (10)

No checksum or other potentially negative factor is present.

## 4. Exact ordinary and signed power projections

Set `r*=r+epsilon−1`. Then r*>=46, n=r*+1 and p=2r*+1.
The parent lower-ratio argument applies with only X>=98 and Y>=1:
for `xi=(X+1)^(2r*)/X^r*`, the elementary Pell bounds give

    c/k >= xi(1+3/(2a))^(2r*)(1+1/(2XY²))^(−r*)>xi,
    c/k < xi(1+2/a)^(2r*).                           (11)

The strict lower factor follows from6XY²>a. The supplied upper ratio
and integrality give `Y>=X^r*`, hence

    a>X^(r*+1)>2^(2r*+1), X<a.

The recurrence for `chi_A(v)−a psi_A(v)` has initial values1,2 and
agrees with2^v modulo H=4a+3. The paid definition D=X+ac+gamma H
therefore gives X=2^p modulo H. Both representatives lie in(0,H), so

    X=2^p, Q=X/2=2^(96x+2epsilon−2).                 (12)

In particular U=1 forces `Q=2^(96x)=8^(32x)`. On U=−1 the necessary
output is still `Q=2^(96x−4)`, exactly the negative branch of the
53-operation component. A containing compiler must preserve U=1 or
exclude this branch using its own paid comparisons before merging signed
unit products. The source itself does not hide such an exclusion.

## 5. All positive converse coordinates, including their signs

For any x>0 and epsilon in{−1,1}, let

    r=48x, r*=r+epsilon−1, p=2r*+1,
    X=2^p, Q=X/2, delta=Q−r,
    Y=floor((X+1)^(2r*)/X^r*), s=Y.

Here p=1 modulo4 on both branches, and delta>0. For the latter,
`2^(96x−4)>48x` holds at x=1 and is preserved when x is increased by1.
There is no required divisibility of Y. The full binomial expansion has
positive fractional tail less than1/4. The upper estimate(11), using
`4r*/a<1/2`, gives

    0<c/k−xi<16r*/(X+1)<1/2

at the canonical indices. Therefore `Y<c/k<Y+3/4`.

Choose a,A,Delta,E,H as in Section1 and define

    c=psi_A(p), D=chi_A(p), k=psi_P(r*+1),
    eta=c−kY, zeta=(Y+1)k−c,
    g=chi_P(r*+1)−2XY²k,
    h=(k−r−epsilon)/E,
    gamma=(D−X−ac)/H.                                (13)

Both ratio gaps are positive integers. The first-root gap is exactly
`psi_P(r*+1)−psi_P(r*)>0`. The first-index congruence makes h integral,
and growth makes it positive. The power recurrence makes gamma integral;
its numerator is positive because `D−ac=2c−psi_A(p−1)>c>X`.

For the five auxiliary coordinates choose

    m=2cp, f=chi_A(m), i=psi_A(m)/c²,
    T=Delta psi_A(m), y=psi_T(p), V=chi_T(p)/T,
    o=(V−c)/f, j=(V−p)/c.                            (14)

The multiple-index expansion in Section2 makes i a positive integer.
Odd p makes V integral. Since p=1 modulo4, the two polynomial identities
in(8) give **V=+c mod f and V=+p mod c**. Thus o,j are integers.
Their positivity is also explicit:

    V>=chi_T(3)/T=4T²−3>T>f>c>p.

Indeed `T²=Delta(f²−1)>f²`; all parameters here are positive and
Delta>=3. This proves positivity of both subtractive quotients in(14),
not merely their integrality. The normalized strong and auxiliary norms
are1, and `V=of+c=jc+p`. Since n=K=r+epsilon, (1) gives Nl=1 and
Nk=epsilon. The first and main norms are1 by construction. Thus U=epsilon.
This supplies all12 positive coordinates on both signed branches and,
in particular, proves completeness of the actual polynomial U−1.

## 6. Counted source, guards and evidence

`rewrite(old)` accepts only the entire literal canonical53 packet:
source, domains, comparisons, factors, exports and metadata are checked.
It verifies the six affected rows and that the deleted `r_scaled`
prefix has only its expected consumer. The replacement emits `r=48x`
in that slot, deletes the old r-offset row, and updates Q, X, V and the
linear gap. The output interface still names the live computed Q and r.
`polynomial_source` likewise accepts only the new canonical packet.
There is no general table or unsupported host API.

The source retains31 multiplications and removes one addition, giving
52=31M+21A and51 certificate gates. Every emitted gate is an ancestor
of the output. Both finalizers and every supplied variable are audited.
The literal factor degrees are5,7,14,22,3,3; their sum54 is the exact
product degree. The sole degree cancellation is the unchanged all-integer
identity

    (L+ac)²−(a²+H)c²=L²+2Lac−Hc².

No solution-set identity is used to lower a formal degree.

Run `python pell_fixed_affine_exponent52.py`; `--write` regenerates the
receipt. The author checker verifies six symbolic source/factor identities,
the exact factor degrees, the main cancellation,512 complete outputs on
256 assignments (128 signed),1,560 pretyping corners including Y=1,2,3,
32 plus-quotient recurrence identities, and nine rejected mutated packets.
It materializes actual x=1 first/main coordinates on both signed branches
and three small full plus-congruence auxiliary blocks. These separate
fixtures are not claimed to be full giant x=1 Pell tuples; the complete
positive existence theorem is Section5.

Author receipt generation and a separate fresh default replay pass.
An independent full proof/source/fresh-default review passes without
findings. It checks the direct pc|m rank argument, sign-insensitive strict
step-down, wrapped-index exclusion, both signed power branches, and
positivity of the two subtractive auxiliary quotients. Its independent
manual executor checks320 assignments (160 signed), yielding640 complete
outputs (320 signed), plus six symbolic factor identities, the exact
degrees, both live finalizers and4,040 pretyping bounds. A separate binary
Pell oracle checks four full small plus-auxiliary blocks,289 exact quotient
identity pairs,60,360 signed step-down modular cases, and actual x=1
first/main blocks for both signs. These are distinct component fixtures,
not claimed full giant source zeros. All four local links and the whitespace
check pass. The source and receipt are frozen after this review.
