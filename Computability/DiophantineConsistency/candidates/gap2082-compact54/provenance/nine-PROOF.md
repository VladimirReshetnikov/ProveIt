# A refined free-carrier nine-positive equation

This component combines a positive-gap source, degree-separated coefficient
packing, a leading-block-free carry test, a free carrier, and the polynomial
quotient majorant from round8. It defines ordinary integer polynomials in
exactly nine positive variables b,g,h,s,w,C,i,j,n. All named registers below
are abbreviations, not additional existential variables. The literal arithmetic
DAG is the authoritative fully specified equation. Every power is fixed and
is expanded into charged binary multiplication gates.

The parent/source compiler and Jones ratio theorem are inherited. The present
argument establishes their new composition; it does not independently prove
their end-to-end formalization or assert global minimality. All four original31
coefficient ports are retained together, including the shifted MF_source.

## 1. Exact source and calibrated block

Read source.json, layout.json and kernels.json from the selected data/H*/
directory. The source first
performs rho14=r14+r2 and rho15=r15+r3, then replaces old P by P+eta+zeta
and old N by N+1 (H2068,H2057), or old N by N+q (H2082), where
q=1+beta J. These substitutions are positive-zero-set bijections:
old P−eta−zeta=E(c−eta)>0 and old N=q³>q>=2 on every parent root.
The accompanying source proof gives the reverse implications as well.

For the 31 distinct positive weights w_i and 22 targets q_j, let

 D_d(B)=sum_(terms of degree d) coefficient * B^exponent,
 ell=sum B^w_i, Targets=sum B^q_j, W=max w_i,
 Hc=max_d(deg D_d+dW), Ec=Hc+W+2.

The exact degree-separated isolation certificate proves

 [T^q_j](D2(T)U_y(T)^2+D1(T)U_y(T)+D0(T))=2rho_j(y),
 U_y(T)=sum y_i T^w_i.

Coefficients are explicit signed integers computed from the authenticated
whole original31 tuple. Their magnitudes are below M=2^2134927. Put

 kappa=2134939, B=2^kappa b², N0=B^(W+1),
 Us=ell+g, Gs=(D2(B)Us+D1(B))Us+D0(B),
 Mask=N0−1−(b−1)ell,
 Jcode=2Gs+Targets,
 Scode=g+N0 Jcode, Tcode=Mask+N0(B−2)Targets.

The two unreflected layouts have positive leading coefficient1 in D2 and
deg D2+W−deg D1>=3, deg D2+2W−deg D0>=3. Since Us>=B^W,
the leading quadratic contribution dominates both lower-degree kernels:
D2(B)>B^degD2/2, and each competing kernel has magnitude less than
2M times its leading power. Thus Gs>0 unconditionally for b,g>=1.
The complete actual gaps are recorded in each packing certificate.
The reflected H2057 layout instead reverses row2 and has independently
positive leading coefficients (2K0,2,beta) in (D0,D1,D2). The elementary
leading-term bound makes each kernel positive separately, so Gs>0 with no
layer gap assumption. Its quadratic and linear leading heights tie; the
leading coefficient of Gs in B is beta+2, not beta. The final degree
certificate includes this positive sum.

On g<4bB^W, Us<6bB^W. The inherited explicit bounds, now with smaller
kernel support, give 2Gs/B^(Hc+1)<1/32. The actual targets lie at least
two places below Hc, so Targets/B^(Hc+1)<1/64 and
(B−2)Targets/B^(Hc+1)<1/64. Consequently

 0<=Scode,Tcode, and Scode+Tcode<B^Ec.

For b=2^k, B=2^v, v=kappa+2k, the low mask forces
g=sum z_iB^w_i with 0<=z_i<b. Us then represents y_i=z_i+1.
Every convolution coefficient has magnitude below993Mb²<B/4.
At each target, adding1 and masking B−2 tolerates the incoming borrow
of either0 or−1 precisely when the target residual is zero. Thus

 Scode AND Tcode=0 iff g encodes a positive common source zero.

The all-one source tuple is not a zero (row5 has value1), so a genuine
source witness gives g>0 and g<bB^W for every sufficiently large binary b.

Let Hp=Ec+W+23, delta=(Hp−15) mod2, lp=(22−Hp*kappa) mod2, and put

 eN=(Hp−15−delta)/2,
 e2=((15+delta)kappa+lp−22)/2,
 L=2^lp b B^Ec, N=2^e2 b^delta B^eN,
 R=L(Scode+Tcode+1)−Scode−1, capbase=bB^W, Gcap=32capbase.

These divisions are fixed integer definitions, not variable divisions.
For binary b the two disjoint blocks give

 pop(R)=log2(L)+pop(Tcode)−carry,
 pop(Tcode)=(W+23)v−31k−22,
 log2(L)+pop(Tcode)=Hp*v−30k+lp−22=2log2(N).

Legendre's factorial valuation therefore gives
N² | binomial(2R,R) iff Scode AND Tcode=0. The bound above makes both
blocks valid. Before any binary-base hypothesis R,N>=8 and b<=R,N.
The endpoint b=1 cannot produce a final zero because the low mask then
forces g=0, contrary to its positive domain.

## 2. Free-carrier ratio registers

Set j0=j−1>=0 and define

 U=N²w, Y=N²s, M0=RY, P=2M0²U,
 K=R+1+h(P−1), A=M0(U+1), B1=2R+1, W1=bw,
 J=4A−5, Q=3W1C−2(W1²−1),
 D=(A²−1)C²+1, k0=iJC, E=k0DC,
 F=(A²−1)E²+1, Lambda=CD+1−A,
 G=A+F Lambda, H=C+F(B1+j0 C), I=(G²−1)H²+1,
 a0=(P²−1)K²+1, a1=DFI,
 m=K²(4capbase−g)−16capbase(C−KY)²,
 Omega=Jm, E0=J(n+W1²)+Q, V0=PK.

All radicands are positive even for C=1. In particular A>=33280,
D>=A², D>C², F>=A², G>A and H>1. Also A>W1. The identity

 E0=Jn+(J−2)W1²+3W1C+2>0

replaces the former assumption Q>0. The normalized margin is exactly
one eighth of the inherited ratio margin. If m>0, then
|C−KY|<K/2, and hence C>2K>2R+1+W1. Thus the required old carrier
range follows from the margin rather than an input substitution.

The exact CRT reparameterization is unchanged: F=1 modulo both J and C.
An old positive H_old=B1+j_old C with F dividing H_old−C yields
(H_old−C)/F=B1+j0 C with j0>=0, once the carrier range is recovered.
The divisibility condition is F|(H_old−C), not F|H_old.
Conversely j_old=1+((F−1)/C)B1+Fj0 is a positive integer. No unproved
cofinality in j_old is used. The inherited ratio predicate is therefore
equivalent to a0,a1 being squares, J dividing Q, and m>0.

## 3. Refined unconditional majorant and the single equation

With B8=8D²−4D−1 and Ns=2G+Lambda, define

 T6=k0[128B8 Ns−k0²(16(B8+D)−8)Lambda+C(14k0²−192)],
 T=T6+i³[C(C(576A−2151)−(896A²−4256A+8442))+1024]+288i+2048,
 V1=TH, qscale=2048²,
 Theta=E0−Omega(V0+V1),
 F9=(Theta²−Omega²(a0+qscale*a1))²−4qscale*Omega⁴*a0*a1.

The equation is F9=0. The retained round8 quotient-majorant proof assumes
only A>=729,C>=1,i>=1, so it applies to the free carrier without change:

 T>2048 sqrt(DF)G>0,
 V1>sqrt(qscale*a1), and V0>sqrt(a0).

For completeness, that proof expands a seventh-order rational comparison
polynomial, performs exact division of J³ by A+1 and A²−1, and bounds the
remaining terms; no analytic asymptotic assertion is being substituted for
an inequality. The full proof and exact703-term defect are retained.

If F9=0 and m=0, then E0⁴=0, impossible. Otherwise the real two-root norm
factorization gives

 E0/J=m(V0+V1+r0+r1), r0²=a0, r1²=qscale*a1.

The left side is positive, and the strict majorants make the parenthesis
positive for every choice of signs. Hence m>0 first. This recovers the old
carrier range, then a1>a0. The signed sum r0+r1=Theta/Omega is rational
and nonzero; the latter follows since qscale*a1>a0. Squaring isolates each
root, so both are rational, then integral. The rational root r1/2048 of the
integer a1 is also integral. The displayed identity now implies J|Q.
All inherited ratio conditions follow, yielding the source zero and a finite
syntactic ZFC refutation.

Conversely choose the ratio witnesses from a source zero, transform the CRT
coordinate, and choose positive roots r0,r1. Set

 n=m(V0+V1+r0+r1)−W1²−Q/J.

It is an integer. Since m>=1, A>W1, D>=A² and D>C²,
W1²+Q/J<2D. The refined majorant has V1>2048D, so n>0.
One norm factor vanishes. This gives a positive zero of the stated polynomial.
Negating the existence equivalence establishes in ZFC that the equation has
no positive solution iff Con(ZFC).

## 4. Exact degree, not a syntactic upper estimate

Write r=deg R, nu=deg N, c0=2W+1 and a=r+4nu+2. Free C has degree1.
Then

 deg H=8a+r+10, deg V1=23a+r+29,
 deg Omega=5r+20nu+c0+12, deg V0=4r+12nu+7.

The exact polynomial T²−2048²DFG² has coordinatewise exponents at most
(15,18,6) in (A,C,i); its unique term attaining all three maxima is
9*2^18 i^6 A^15 C^18. The independent symbolic expansion checks all703
coefficients. Consequently, with Delta1=V1²−qscale*a1,

 Delta1=H²(T²−qscale*DFG²)+qscale*DF(H²−1),
 deg Delta1=31a+2r+44.

In the exact cancellation-resolved identity

 Theta²−Omega²(a0+qscale*a1)
 =E0²−2E0 Omega(V0+V1)
  +Omega²[(K²−1)+Delta1+2V0V1],

Omega²Delta1 uniquely dominates. Its square also dominates the final
subtracted term. Thus

 deg F9=86r+328nu+4c0+260.

If the leading constants of R,N,capbase are rho,sigma,tau, the diagonal
leading coefficient is 81*2^88*tau^4*rho^86*sigma^328, which is positive.
For the source layouts here r=4Ec−1, nu=2eN+delta. This proves both upper
and lower degree bounds for the actual integer coefficients.

The cheaper companion retains V1=k0(8D²−4D−1)GH and qscale=64.
Its inherited strict-majorant proof gives the same equivalence. Its exact
degree is104r+400nu+8W+316. These are honest cost/degree tradeoffs.

## 5. Arithmetic-circuit accounting and reproducibility

Every addition, subtraction and multiplication, including multiplication
by an integer constant, costs one operation. Reused nodes count once;
fixed integer construction is outside this arithmetic-circuit measure.
A global backward addition-chain plan shares the required B powers across
all kernels, masks and thresholds. It changes no polynomial. Every power
in the emitted DAG consists solely of ordinary charged multiplications.

Run build_nine.py and verify_nine.py; check_defect_exact.py uses SymPy for
the independent exact local identity. Verification binds the whole tuple,
all fixed coefficient recipes and the source hash, checks live-gate counts,
replays1080 actual-coefficient modular assignments against separately written
register formulas, and checks the cancellation-resolved exact degree argument.
These finite checks supplement, not replace, the mathematical proof above.

### Erratum in inherited majorant reference

The retained `REFINED_MAJORANT_PROOF.md` gives 1719 for the sum of the seven negative coefficient magnitudes of `t7`. The exact sum is 1619 = 1024+256+128+80+56+42+33. The printed value is an overestimate, so its strict positivity argument remains valid without any change to the majorant.
