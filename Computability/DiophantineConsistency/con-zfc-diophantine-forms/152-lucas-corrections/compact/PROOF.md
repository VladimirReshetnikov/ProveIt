# Second-order Lucas correction permits the scale Y = q s

## Result and inherited boundary

The principal candidate is `equation_bV.json`: one ordinary polynomial over
ten independently strictly positive integers, evaluated in 87 live binary
additions, subtractions and multiplications, with exact total degree 304.
The square-transport control `equation_V2.json` has 86 operations and degree
410. The control is dominated by known earlier endpoints and is not promoted
as a frontier improvement. Fixed scalar multiplications and squares are charged.
The complete four-number directly indexed BFS943 coefficient tuple is retained
from the pinned `Centered_Residues` incoming package. The new correction is
independent of those numerals except for their inherited port box and calibration.

The mathematical statement, after composition with that identified ordinary
native/refutation theorem, is that ZFC proves absence of a strictly positive
zero iff syntactic Con(ZFC). This is not a proof of either side, a global
minimum theorem, a literature-wide priority claim, or a new end-to-end formal
proof-assistant object. The new part is the second-order index correction and
its complete signed-transport, denominator, and positive-completeness proof.

The latest inspected incoming `Residual_Bases_Denominator_Engineering` package
explicitly rejected a q-linear scale because the visible first-index modulus
was only q^3 while the rank bound was q^4. The correction below repairs that
specific obstruction. It leaves no binomial coefficient, variable exponent,
division, or bounded-quantifier primitive in the polynomial itself.

## 1. Complete definitions

The ten variables are

    J,F,alpha,i,T,w,s,n,eta,zeta > 0.

The four fixed ports beta,K0,MC,MF are the whole coherent tuple in
`parent/coefficients`, satisfying

    beta >= 31 odd, K0 > 0, 0 < MC < beta < MF < 2 beta.

Define polynomial abbreviations, not additional variables:

    h=beta J, q=h+1, C=q-F-alpha,
    X=wq, Y=qs, k=eta+zeta, c=kY+eta,
    A=Y(X+1)+1, Delta=A^2-1, H=4A-5,
    v=XY^2, E=1+v(v+1)k^2,
    R=[h(q-F)+alpha](q^2-1)+(MC+q MF)J,
    B=(K0+w)C-F,
    U=ic^2, a=Delta U^2 E, F0=1+a, G=E F0,
    Fs=1+4a F0, Q=Delta(Fs-1),
    b=cT-R, V=Fs b-c, K=X(3c-2X)+2,
    e6=6(k-R-1)-v(R+1)(R-1)(R+3),
    D6=6q^6,
    M=h D6 H,
    Z=h D6[H(n-LB)+K]-H[D6 B+h(e6-6q^4 s)],
    RG=M^2 G,
    P=Q(Z^2-RG V^2)+(RG-Z^2).

The principal uses L=bV. The control uses L=V^2. The equation is P=0.
The literal circuits compute v using the existing XY product and compute
(R+1)(R-1)(R+3) as (R+1)((R+1)^2-4). Their other sharing is explicit.

For proof only, put

    t=B/h, W=1+hL, kappa=K/H, sigma=s/q^2,
    ebar=e6/6, rho=ebar/q^6, z=Z/M.

Then, without assuming any divisibility,

    P=(Q-1)Z^2-M^2 G(QV^2-1),
    z=n+kappa+sigma-Wt-rho.                         (1)

In particular ebar need not initially be asserted integral. All denominators
in (1) are nonzero at positive inputs. The polynomial uses e6, never ebar.

## 2. Root extraction and early folding

The retained elementary root extraction uses only positivity, so it applies
unchanged at Y=qs: q>=32, X,Y>=q, k>=2, c>kY, A>=3, Delta>0,
U>=c^2, a>0, Fs>2c, Q>1, M>0. For every integer b,
V=Fs b-c is nonzero and |V|>1. Identically

    Fs=(1+2a)^2, Q=4 Delta^2 U^2 G.

Thus G is coprime to Q-1 and QV^2-1. At a zero of P, division by
M^2 gives (Q-1)z^2=G(QV^2-1). Prime valuations force G=g^2
for an integer g>0. Since gcd(E,F0)=1, E=tau^2 and F0=f0^2
for positive integers tau,f0, with g=tau f0. Then y=|z|/g satisfies

    QV^2-(Q-1)y^2=1.                               (2)

The adjacent-Pell descent in the retained parent forces y integral.
In brief, writing y=r/m reduced gives m^2|Q-1. For |V|=u>1,
u<y<Qu/(Q-1), and

    u'=(2Q-1)u-2(Q-1)y,
    y'=(2Q-1)y-2Qu

has a nonzero integral first coordinate with |u'|<u and preserves the
reduced denominator m of the second coordinate. Reflection and descent
reach u=y=1; hence m=1. Therefore z=epsilon g y is integral.

Put f=1+2a and I=2Ug. These obey

    f^2-Delta I^2=1, Q=(Delta I)^2, c^2|I,
    V=f^2(cT-R)-c.                                 (3)

The retained signed all-index folding theorem, which does not require a
sign for V or R, applies to (2),(3), c<=I and V=-c mod f. It gives
c=psi_A(p) for a positive odd p. The first norm gives

    k=2 psi_(2v+1)(n0), n0>=1.

If n0=1, k=2, eta=zeta=1 and c=2Y+1 lies between the first two main
ordinates 1 and 2A. Thus n0>=2 and

    k>=8v+4, c>kY>8XY^3>=8q^4, c>X, K>0.           (4)

No sign of C,B,R,b,V or ebar was assumed.

## 3. Absolute transport estimate with only Y >= q

If b=0, (2) gives y^2-c^2=(c^2-1)/(Q-1), strictly between zero and
one, impossible for integers. Thus b!=0 and sign V=sign b. Put
D0=Delta U^2. The identity

    a^2/g^2=D0*a/(1+a)>D0/2>9

gives a>3g. Also Fs>2c and Fs-c>a, so |V|>3g, |V|>|b|,
and y<(3/2)|V|. Consequently gy<V^2/2 for the control.

For the principal, exclude p=3. If c=4A^2-1 and n0>=3, then
k>32v^2, whereas A<2XY and Y>=32 give
c<16X^2Y^2<32X^2Y^5<kY<c. Thus n0=2 and k=8XY^2+4.
With u=X+2-2Y, the exact equality is

    eta=4Y^2(Xu+1)+8Y(X+1)+3-4Y.

If u<=-1, this is negative because Y(X-1)>2(X+1). If u>=2,
subtracting k gives at least 4Y^2+8Y(X+1)-4Y-1>0. Both contradict
0<eta<k. Thus u is 0 or 1, implying 2Y-X is 2 or 1, contrary to
q|X,Y and q>=32. Therefore p>=5 and c>c3=4Delta+3.

Pell classification of (2) gives |V|=chi_S(j)/S for odd j>=1,
where S=Delta I and S^2=Q. Index one gives |V|=1, excluded. Index
three gives |V|=4Q-3 and would give one of

    Fs(b-4Delta)=c-c3,  Fs(b+4Delta)=c+c3.

Both right sides are strictly between 0 and 2c<Fs, impossible.
Thus j>=5, |V|>=16Q^2-20Q+5>8Q^2, and Q>Fs>2c yields

    |b|>(8Q^2-c)/Fs>4Fs>4g.

Hence L=bV=|b||V|>0 and gy<(3/8)L<L/2. For either L we have

    L>0, gy<L/2, |b|/q^6<L/2.                     (5)

The degree reduction has not used an invalid inverse of a positive
coordinate shift. T is the original positive input throughout.

## 4. New signed-transport proof for the cubic correction

Let e0=k-R-1 and B_R=(R+1)(R-1)(R+3). Since
b-e0=cT-k+1>0, one has

    rho < b/q^6 - v B_R/(6q^6).

If B_R>=0, then rho<|b|/q^6. If B<=-1, Wt<-L, and (1),(5),
with positive kappa and sigma, force n<0. This is a contradiction.

The only integer ranks for which B_R<0 are R<=-4 and R=0. They
require a separate argument; ignoring them would be a soundness gap.
Write Pmask=(MC+q MF)J>0. The exact outer relation is

    R=(hC+q alpha)(q^2-1)+Pmask.                    (6)

For R=-r<=-4, (6) gives C<0 and

    |C| > r/[h(q^2-1)] > r/q^3.

Moreover B=-(K0+w)|C|-F <=-1-w|C|, so
Wt<-(1+w|C|)L. The adverse correction is

    delta0 = v(r-1)(r+1)(r-3)/(6q^6)
           < w s^2 r^3/(6q^3),                    (7)

because v=wq^3s^2. Here b=cT+r>r and b>c, so
V=Fs b-c>(Fs-1)b. In either choice of L,

    L>(Fs-1)r^2.

Since Delta>Y^2>=s^2 and Fs-1=4a(1+a)>s^2, equations (6),(7)
give w|C|L>delta0. Substituting into (1), then using (5), gives

    n < L/2-(1+w|C|)L+|b|/q^6+delta0 < 0.

For R=0, (6) again gives C<0 and |C|>=1. The adverse term is only
delta0=v/(2q^6)=w s^2/(2q^3). Now b=cT>=c and
V>= (Fs-1)b, whence L>(Fs-1). Thus
w|C|L>w(Fs-1)>delta0, giving the same contradiction.

All integer ranks have been covered. Hence every positive zero has
B>=0. Since F>0, its defining formula forces C>0. The inherited
mask bound is now licensed:

    3q<R<q^4-2.                                    (8)

By (4), c>2R, so b,V>0. The retained normalized rank and signed
auxiliary-index theorems have all their premises (3), c>2R,c>2p,
V=-c mod f and V=-R mod c. They give p=R. Therefore R is positive
odd; the unchanged mask parity also gives even q and odd J.

## 5. Second-order index recovery, including primes 2 and 3

The Lucas sequence psi_(1+2v)(m) has the finite polynomial expansion

    psi_(1+2v)(m) = sum_(j=0)^(m-1) (4v)^j binom(m+j,2j+1).

This identity follows from the recurrence or its generating function.
For m>=1 it gives the exact integer equality

    2 psi_(1+2v)(m)
      =2m+8v binom(m+1,3)+32v^2 Z_m,               (9)

where Z_m is a nonnegative integer (zero for m=1,2). Binomial
coefficients appear only in this proof, not in the final polynomial.

Let r0=(R+1)/2, an integer by Section 4. Then
B_R=8r0(r0^2-1)=48 binom(r0+1,3), so ebar=e6/6 is an integer and

    ebar=k-2r0-8v binom(r0+1,3).                   (10)

Since z is integral, (1) cleared through hH gives
6q^6 | hH(e6-6q^4s). Cancelling the literal integer factor 6 in
this divisibility, now that ebar is integral, gives

    q^6 | hH(ebar-q^4s).

But h=q-1 and H=4Y(X+1)-1=-1 mod q because Y=qs. Thus
gcd(q,hH)=1 and

    q^6 | ebar-q^4s, hence q^4 | ebar.              (11)

No invertibility of 6 modulo q was used.

Set d=2n0-R-1=2(n0-r0). Both (9) and (10) reduce modulo 4v to
ebar=d. Since q^3|v, (11) implies q^3|d. The exact difference
identity obtained from (9),(10) is

    6(ebar-d)
      =v d[(2n0)^2+(2n0)(R+1)+(R+1)^2-4]
        +192v^2 Z_(n0).                            (12)

Both terms in (12) are divisible by q^6. For every prime ell|q,
write a=v_ell(q)>=1. Because v_ell(6)<=1, divisibility q^6|6(ebar-d)
implies v_ell(ebar-d)>=6a-1>=4a. Hence q^4|ebar-d, even when q is
divisible by 2 or 3. Combining with (11) gives q^4|d.

The first base P0=2XY^2+1 is larger than A. If n0>=R, monotonicity
in base and index would give k/2>=psi_A(R)=c, contrary to c>k.
Thus 1<=n0<R, and (8) gives |d|<R<q^4. Therefore

    d=0, n0=(R+1)/2.                              (13)

Only after (13) return to (9),(10): ebar=32v^2 Z_(r0), so

    q^6 | ebar, rho=ebar/q^6 is a nonnegative integer.  (14)

This is the repaired order of deduction. A second-order correction first
improves the usable congruence, identifies the bounded index, and then
restores the entire denominator.

## 6. Delayed q^2 divisibility, projection, and source restoration

Equations (11) and (14) immediately give q^6|q^4s, hence q^2|s.
Thus sigma=s/q^2 is integral and q^3|Y=qs has been restored before
projection. The integer carrier (1) now gives kappa-WB/h integral,
and clearing h gives H|hK.

With (13), the parent's uniform ratio lemma applies at scale one.
Writing R=2r+1, (8) gives r>=48. It yields Y>X^r/3 and
X^(r+1)<3Y(X+1)<H.

The inherited polynomial Pell projection and its entire-product height
bound give

    H | h(X-2^R)(2^R X+1),
    |h(X-2^R)(2^R X+1)|<H.

Consequently X=2^R and kappa=K/H is integral. No possibly nonunit
factor of the displayed product was cancelled. The remaining carrier
gives h|WB. Since W=1 mod h, h|B. Thus

    q^3|Y=qs, t=B/h is a nonnegative integer.        (15)

The fixed-minus parity, half-binomial rounding and fresh original-source
reconstruction now have their full inherited hypotheses. That reconstruction
uses the source base Y(X+1)+2, not our auxiliary A. The retained whole-tuple
native/refutation theorem yields a finite syntactic ZFC refutation.

## 7. Positive completeness

A finite refutation supplies the parent's canonical outer data:
q^3|Y, X=2^R, R=3 mod4, R>3q, t=B/h>=0 integral, with the exact
half-binomial interval. Set the new positive input s=Y/q. Then
sigma=s/q^2=Y/q^3 is integral and at most Y.

Using the scale-one bases, set c=psi_A(R),
k=2psi_(2XY^2+1)((R+1)/2), tau=chi_(2XY^2+1)((R+1)/2),
eta=c-kY, zeta=k-eta. The retained uniform ratio estimate gives
eta,zeta>0. By (9),(10), rho is nonnegative integral.
Projection gives positive integral kappa<Xc.

A positive multiple of a finite Pell matrix period modulo c^2 tau supplies
one seed pair (f0,I0) with c^2 tau|I0. Set i=I0/(c^2 tau)>0 and double
the pair exactly as in the parent. This yields (3), G=(tau f0)^2 and the
canonical positive auxiliary pair V,y with unshifted
T=(V+c+Rf^2)/(cf^2)>0 integral. The same pair is retained throughout.

Now f0>(A-1)I0>2Xc, while kappa<Xc and sigma<=Y<Xc. Hence
g=tau f0>kappa+sigma. Define

    n=gy+(1+hL)t+rho-kappa-sigma.

This is a strictly positive integer, and its carrier is exactly z=gy.
Thus P=0. Every independent coordinate has been constructed positively.
Together with Sections 2--6 this proves both existential directions.

## 8. Exact degree and the finite verification scope

The changed registers have degrees Y2,c3,A4,Delta8,v6,E14,U7,a36,
Fs72,Q80,G50,b4,V76,M11. The corrective cubic has degree 18,
well below the leading transport part. For L=bV, deg Z=93 and
-Q M^2 G V^2 is the unique dominant term, of degree 304. For L=V^2,
deg Z=165 and QZ^2 uniquely supplies degree 410.

Put q0=beta J, k0=eta+zeta, C0=q0-F-alpha and
B0=k0 s T-q0^2(q0-F). The entire highest homogeneous forms are

    [P_bV]_304 = -9*2^12 q0^128 w^34 s^78 i^14 k0^44 B0^2,
    [P_V2]_410 =  9*2^16 q0^166 w^46 s^104 i^20 k0^60 B0^4 C0^2.

In particular they have respective nonzero coefficients
-9*2^12 beta^128 and 9*2^16 beta^166 at

    J^128 w^34 s^80 i^14 eta^46 T^2,
    J^166 w^46 s^108 i^20 eta^64 T^4 F^2.

The checker binds every actual DAG row to independent exact polynomial
cuts, checks liveness and costs, propagates the complete leading forms,
authenticates every coefficient byte, and rejects actual gate corruptions.
It verifies (12) as a polynomial identity and supplements the unbounded
Lucas proof with finite recurrence controls. Such finite controls do not
prove consistency or replace the ordinary unbounded proof above.

## Sources and attribution

The source parent is the compact component of
`docs/incoming/ConZFC_Centered_Residues_2026-10-25.zip`, inspected at
ProveIt commit 3ecd6a6cf53d47519228328567f45fb7ee9781d9. Its retained
proof sources identify the product-square extraction, adjacent descent,
signed all-index folding, normalized rank, universal projection,
scale-one ratio, parity, and native/refutation calibration. The retained
files provide the inherited arithmetic proofs and interfaces used here;
they are not all transitive native-calibration proofs or a standalone
proof-assistant build. The former
q^3 modulus obstruction is recorded in the inspected incoming
`ConZFC_Residual_Bases_Denominator_Engineering_2026-10-25.zip`,
`compact/PROOF.md`, Section 8. The q^2 partial-scale predecessor in
`ConZFC_Coprime_Products_and_Positive_Centers_2026-10-25.zip` is also
credited for retaining a positive fractional carrier and recovering its
missing divisibility at the end. New analysis and artifacts here were
prepared with AI assistance; independent reviews mean separate checks
within that workflow, not outside human peer review.
