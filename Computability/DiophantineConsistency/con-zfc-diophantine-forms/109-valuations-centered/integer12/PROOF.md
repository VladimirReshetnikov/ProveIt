# Twelve unrestricted integer variables: fixed prime-three separation

## Result and exact scope

All variables in this note range over **unrestricted integers**. The supplied
whole source34 coefficient tuple is unchanged. There are three explicit ordinary
integer polynomials, with every multiplication and binary addition/subtraction
paid in their literal DAGs:

| Variant | Variables | Operations | Exact degree |
|---|---:|---:|---:|
| Integer auxiliary radical | 12 | 209 | 2848 |
| Rational auxiliary radical, denominator cleared | 12 | 215 | 2336 |
| Rational auxiliary radical with integral center translation | 12 | 216 | 2304 |

Each has an integer zero if and only if the inherited source34 generalized
signed kernel has a witness, hence if and only if ZFC has a finite refutation.
Consequently the ordinary argument, composed with the explicitly inherited
calibration, is formalizable in ZFC and proves the requested unsolvability
biconditional. A new checked Lean theorem or an encoded internal ZFC proof is
**not** supplied. We do not claim global minimality or historical priority for
prime-adic radical separation or for intersective polynomials.

The previous twelve-integer points were 248 operations/degree4832 and
223 operations/degree16000. Every new point improves both operation count and
degree over both of those points, with identical variable domain and whole
coefficient tuple. Nine-positive and ten-integer families remain different
tradeoffs. The novel contribution within the inspected snapshot is the
composition of the existing full-residue interpolation theorem with constant
prime-three weights, including the smaller carrier scale and exact centered
clearing argument.

## 1. Literal front and fixed coefficients

The variables are

    j,C,z,h,r,v,w,T,c,n,t,s.

The exact six fixed coefficients are beta,K0,MC,MF,cone_A,cone_B in
coefficients/BINDING.json and its gzip binary payloads. In particular
beta=2^1064921-1, MF is already shifted by beta, cone_A=2^1113,
cone_B=2^666104. The original coefficient recipe and original dependency ZIP
are included; no unspecified machine index or consistency-dependent value is
used. Define

    J=6j+1, q=beta J+1, W=12w+4,
    X=qW, Y=(2v+1)q^3, E=XY,
    a=E+Y, H=4a+3, Delta=a^2+H,
    F=(K0+W)C-z(q-1), alpha=q-F-C,
    R=(q(q-F)-C)(q^2-1)+(MC+q MF)J,
    k=R+1+hE, eta=c-Yk, zeta=k-eta,
    G=(cone_A F)(cone_B C)-(q-cone_A F-cone_B C)^2,
    P=G eta zeta-(t^2-G-eta zeta+1)^2,
    Dg=(3P-4)s^2+1,
    I=src^2, Df=1+Delta I^2,
    Q=Delta^2 I^2, delta=Q-1,
    V=Df(c-R+4IT)-c, Cy=QV^2-1, Da=delta Cy,
    ell=XY^2, Dt=1+ell(ell+1)k^2,
    Dm=1+Delta c^2, b0=X+ac, u=HT-b0.

The builder uses the exact factorization Dt=1+(ell k)(ell k+k).
All abbreviations are polynomial definitions, not additional unknowns.

## 2. A cheap intersective quintic

Use

    pi(x)=(x^2+3)(x^3-19).

It has a root modulo every nonzero integer, but no zero in any real extension
of Q of degree at most two.

For local solvability at an odd prime p other than3, there are two cases.
If p=1 mod3, quadratic reciprocity gives (-3/p)=1, so x^2+3 has a simple
root modulo p. If p=2 mod3, the cube map on F_p is bijective. Since the only
prime dividing19 is19=1 mod3, the cubic root in this latter case is nonzero
and has nonzero derivative3x^2. Both cases lift by the ordinary simple-root
Hensel lemma. At2 the cubic has the simple odd root modulo2. At3 put

    x=1+3u,
    x^3-19=9(3u^3+3u^2+u-2).

The bracket has the simple root u=2 modulo3, since its derivative is1
modulo3. Lifting that root gives cubic roots modulo every power of3.
CRT now gives a root modulo every nonzero integer.

The quadratic factor has no real root. The cubic is Eisenstein at19 and
is irreducible over Q; a degree-three element cannot belong to a field of
degree at most two. This proves the real-quadratic nonvanishing statement.

Reduce the homogeneous quintic in d^2=Dm:

    A+B d = ((u+d)^2+3H^2)((u+d)^3-19H^3).

A short division-free evaluation is

    Q0=u^2+Dm+3H^2,
    C0=u(u^2+3Dm)-19H^3,
    C1=3u^2+Dm,
    A=Q0 C0+2u Dm C1,
    B=Q0 C1+2u C0.

Equivalently

    B=5u^4+10u^2 Dm+Dm^2+9H^2u^2+3H^2Dm-38H^3u.

B need not be positive. Positivity is not needed in this construction.
For comparison, three additional supplied DAGs keep the old monotone carrier
(x^2+31)(x^3+x+1). They use one more operation, have the same degrees, and
satisfy the same proof below. This transparently separates the main weight
reduction from the optional one-gate carrier improvement.

## 3. Final equations

Put S=srH^5 and S2=S^2. This is the deliberately reduced scale; the previous
interpolation proposal used I H^5=src^2H^5.
Let N32(Z;d0,...,d4) denote the polynomial

    product over epsilon in {−1,+1}^5 of
        (Z−sum_i epsilon_i sqrt(di)).

Sign invariance makes this a polynomial with integer coefficients. The literal
five_square_norm.py evaluator uses only +,-,* and supplies the ordinary
polynomial, without radical gates or hidden root unknowns.

The 209-operation variant is

    N32(Sn−A;
        B^2 Dm, S2 Da, 9 S2 Df, 81 S2 Dt, 729 S2 Dg)=0.        (I)

The 215-operation variant is the division-free polynomial obtained from

    delta^16 N32(Sn−A;
        B^2 Dm, S2 Cy/delta, 9 S2 Df, 81 S2 Dt, 729 S2 Dg)=0. (R)

The rational expression here only specifies a polynomial identity. The actual
DAG uses cleared_norm5 and contains no division. Its denominator-clearing
exponent is exactly16.

The 216-operation variant replaces the center of (R) by

    S(n+V)−A.                                                  (C)

Because n ranges over all integers, this is an integral bijective translation
of the center, with inverse n_old=n_new+V. It preserves the complete zero set
up to this translation. In particular it has no additional completeness
condition.

## 4. Unconditional facts and exclusion of S=0

These are facts about every integer assignment, before the final equation.
J is nonzero and odd. Since beta is odd and larger than17, q is even,
|q|>=16, and W is a nonzero multiple of4. Thus |X|>=64 and |Y|>=4096.
As a=(X+1)Y, H is nonzero and Delta=(a+2)^2−1>1. Consequently Dm,Df>=1.
Also ell(ell+1)>=0 for every integer ell, so Dt>=1.
Q is either0 or greater than1, and hence delta is never0. If I=0 then
Q=0,delta=−1,Cy=−1,Da=1 and Cy/delta=1. If I is nonzero, then
|I|>=c^2 and c is nonzero. Therefore Df>|c|+1. Writing b=c−R+4IT,
if b=0 then |V|=|c|>=1; otherwise |V|>=Df−|c|>1. Hence Cy>0 and
both Da and Cy/delta are positive.

At S=0, s=0 or r=0 because H is nonzero, so I=0 and delta=−1.
All scaled radicands except B^2 Dm vanish, and either literal polynomial
specializes to

    (A^2−B^2 Dm)^16.

It is nonzero: either A+B sqrt(Dm) or A−B sqrt(Dm) being zero would give a
root of pi in a real extension of degree at most two. Thus every zero of
(I),(R),(C) has S nonzero, and in particular s,r nonzero.

This bootstrap does not assume c nonzero. The c=0 case is handled below.

## 5. Prime-three separation without sign assumptions

Because the exponent1064921 is odd, beta=1 modulo3. The literal front gives

    q=2, W=1, X=2, a=0, H=0, Delta=0, u=1  (mod3),
    Dm=Df=Dt=Da=Cy/delta=1                 (mod3),
    B=1                                  (mod3).

For Dt, ell=2Y^2 modulo3, so ell(ell+1)=0 modulo3. For B the surviving
terms are 5u^4+10u^2Dm+Dm^2=16=1 modulo3, for either quintic.
Thus B is nonzero, even though it need not be positive.

At a polynomial zero choose a vanishing conjugate linear factor and divide
it by nonzero S. Its left side is rational. The five squared radical terms
on the right have 3-adic valuations

    −2 v3(S), 0, 2, 4, 6+v3(Dg),

with the last term omitted when Dg=0. Here v3(S)>=5 because3|H.
The first four valuations are distinct even integers; the fifth is at least6,
and may be odd. Negative Dg is allowed at this stage.

For completeness, the required algebraic lemma is as follows. Group a rational
linear combination of radicals sqrt(d_i), for nonzero rational d_i, by their
classes in Q*/Q*^2. Distinct square classes have linearly independent radical
representatives over Q; this follows by character projections in their finite
multiquadratic Galois extension. Within a class write each term a_i sqrt(d)
with a_i rational. If the squared terms have distinct valuations, the a_i
have distinct valuations and their signed sum cannot vanish: the unique
least-valued summand remains a unit after clearing denominators. In our
application every class containing an old root has a unique least valuation.
A class containing only the guard has a single nonzero term. Consequently
no nontrivial square class can occur in the rational total sum.

Therefore **all five roots are rational**. This proof includes negative
radicands and dependent square classes, and does not presume the guard.
Since Dg is an integer rational square, Dg>=0. With s nonzero,
P<=0 would imply Dg=(3P−4)s^2+1<=−3, impossible. Hence P>0.
The inherited elementary joint-positivity lemma gives G>0 and eta*zeta>0.
If c=0, however,

    eta*zeta=−Y(Y+1)k^2<=0,

contradiction. Thus c is nonzero. Combined with s,r nonzero this gives
I nonzero and Q>1, at the point where those facts are needed.

## 6. Integer roots and the main quotient

Rational roots of the integer radicands Dm,Df,Dt,Dg are integral. In (I),
sqrt(Da) is integral and y=sqrt(Da)/delta is initially rational. In (R),(C),
y=sqrt(Cy/delta) is initially rational. In both cases

    Q V^2−(Q−1)y^2=1, Q>1, V in Z.

The source's adjacent-coefficient descent makes y integral. One direct proof
is retained in the unchanged dependency: in lowest terms y=a/b, b^2 divides
Q−1, and multiplication by the fundamental unit2Q−1+2sqrt(Q(Q−1)) reduces
|V| while preserving b, eventually reaching |V|=1 and |y|=1. All signs are
removed by absolute values for that descent.

Write the signed main root as d. Since every other signed term in the
vanishing factor is now S times an integer, the factor equation implies

    S divides A+B d=H^5 pi((u+d)/H).

In particular H^5 divides the homogeneous quintic at x=u+d.
If p^e divides H exactly and v_p(x)=b<e, the leading term x^5 has
valuation5b and every lower term has larger valuation: the other terms are
3H^2x^3,−19H^3x^2,−57H^5. Thus H^5 divisibility is impossible.
This proves H|x, hence

    gamma=(d−b0)/H is an integer.

The original31 carrier satisfies the identical monic valuation argument.

## 7. Source restoration and noncircular completeness

The strong and main equations give

    f^2−Delta I^2=1, d^2−Delta c^2=1,
    d=X+ac+gamma H.

Set rho=Delta I and recover the two old CRT quotients by integer formulas

    o=f(c−R+4IT),
    j_aux=Delta s^2 r^2 c^3(c−R)+4src Df T.

Then V=fo−c=c j_aux−R, and the auxiliary equation becomes
rho^2 V^2−(rho^2−1)y^2=1. The first Pell equation, transport and index
identities, determinant and strip guards are exactly the generalized
signed kernel in the original INTERPOLATION12.md, Section5. Its proof
allows an even strong multiplier, and establishes the source34 native
finite-refutation endpoint. This is the sole inherited semantic reduction
at this step; we do not claim that every new tuple is literally an old
quintic-norm tuple.

For the reverse implication use the unchanged canonical witness family and
full-residue interpolation theorem (original Section6). First choose the
native outer data and t with P>0; choose a nonzero guard Pell witness s.
The interpolation theorem fixes I,f with 4s c^2|I, so r=I/(sc^2) is a
nonzero integer, **before** any residue of T is requested. It then supplies
an auxiliary witness T in any prescribed residue class modulo this same I.

By intersectivity choose a residue a with I|pi(a+gamma). Request T=a moduloI.
Then I|pi(T+gamma), and since sr|I,

    S=srH^5 divides H^5 pi(T+gamma)=A+B d.

All remaining roots are integral. Choose n last using the vanishing factor:
for (I), the auxiliary term is delta*y; for (R), it is y; for (C), subtract
V from that integer value of n. The weights1,3,9,27 introduce no new residue
condition. There is no circular dependence: native data, t, s, then I/f/r,
then a residue and T/y, and finally n.

## 8. Exact degrees and exhibited nonzero coefficients

For total degrees with the six coefficients held fixed, use the original
front degrees

    deg a=6, deg I=4, deg V=25, deg delta=32,
    deg Df=20, deg Dt=34, deg Dg=46, deg Dm=14,
    deg A=35, deg B=28, deg S=32,
    deg Cy=82, deg Da=114.

For (I) the radicands have degrees70,178,84,98,110 and the center has
degree35. The unique highest contribution to N32 is (S^2 Da)^16.
Hence the exact degree is2848.

For (R), after clearing delta^16, the unique highest expression is the
sixteenth power of the auxiliary numerator S^2 Cy, of degree146. The
other cleared radicand contributions have degrees at most142 and the
cleared squared center has degree102. Thus the exact degree is2336.

For (C), pair the two choices of the auxiliary radical. Write

    Wc=Sn−A,
    L=epsilon0 B sqrt(Dm)+epsilon2 3S sqrt(Df)
      +epsilon3 9S sqrt(Dt)+epsilon4 27S sqrt(Dg).

The exact paired factor is

    delta[(S V+Wc−L)^2−S^2 Cy/delta]
      =delta[2 S V(Wc−L)+(Wc−L)^2]+S^2(1−V^2).

This identity proves that the cleared product is the product of these16
paired factors. The unique leading contribution in each is the term from
the guard part of −2 delta S V L, with degree

    32+32+25+55=144.

Indeed the competing square term has degree32+110=142, while all other
cross terms are smaller. Thus the product has exact degree16*144=2304,
and its leading form is

    2^16 delta_top^16 S_top^16 V_top^16 (729 S_top^2 Dg_top)^8.

It is nonzero. The guard leading form is negative, but its eighth power
is positive, so there is no sign cancellation.

Explicit leading monomials provide uniform certificates using beta only.
Let q0=6beta j, Y0=2v q0^3,

    a0=2^7*3^5*beta^4*j^4*w*v,
    I0=src^2, b=4I0 T−R_top,
    S_top=2^10*sr*a0^5,
    Dg_top=−3s^2 Y0^4 h^4 a0^4.

The following coefficients are strictly positive:

| Variant | Monomial | Coefficient |
|---|---|---|
| (I) | j^1408 w^352 v^352 s^192 r^192 c^320 T^32 | 2^2848 3^1760 beta^1408 |
| (R) | j^1152 w^288 v^288 s^160 r^160 c^256 T^32 | 2^2400 3^1440 beta^1152 |
| (C) | j^1248 w^288 v^320 h^32 s^128 r^112 c^160 T^16 | 2^2512 3^1592 beta^1248 |

The sums of the displayed exponents are2848,2336,2304. Taking the maximal
T-power in b^32 or b^16 makes each coefficient selection unique. The same
leading forms apply to either quintic because both are monic of degree5.
The finite line-specialization checks supplement these exact arguments.
