# Strong-Pell growth pays for a smaller transport guard

## Result and status

The explicit polynomial in `p11_positive_degree213.json` has eleven
strictly positive integer unknowns, exact degree 213, and 112 live binary
arithmetic operations. Its two-residual system costs 109 operations.
Compared with the incoming Joint Guards centered equation (257 / 114),
both degree and arithmetic-operation count decrease. Compared with that
packet's cheaper 277 / 111 equation, this is a degree/cost tradeoff.

This document proves the new transformation by ordinary mathematics,
formalizable in ZFC. It inherits the compact44 native coefficient
calibration and the normalized Pell source interface from packages 61,
65, and 70. It does not assert a fresh Lean/Rocq certificate or reprove
the complete native compiler. No consistency assumption is made.

The distinctive step is a conditional bound obtained from the *strong
Pell equation itself*. Its index divisibility makes the already present
witness i enormously larger than the outer parameters. The polynomial
i^3 can therefore replace a much higher-degree bound involving q Df.
Centering at both the auxiliary root and a polynomial approximation to
the strong root then cancels the corresponding leading norm terms.

## 1. Literal equation

The eleven unknowns, all strictly positive integers, are

    j, F, alpha, i, T, X, Y, n, eta, zeta, gamma.

The four fixed integers beta, K0, MC, MF are the *whole compact44 tuple*:
beta = 2^590069 - 1, with the already shifted MF port. The files under
`coefficients/` specify these actual integers by authenticated compressed
little-endian payloads. MF must not be shifted again. Every other symbol
below is a polynomial abbreviation, not an additional unknown.

Define

    J=3j+1, q=beta J+1, C=q-F-alpha, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y, Aparam=a+2,
    H=4a+3, Delta=a^2+H=Aparam^2-1, ell=EkY,
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J,
    M=q^3(q-1), Bt=(q K0+X)C-qF,
    Dtau=ell(ell+k)+1,
    I=i c^2, Df=1+Delta I^2, Q=Delta^2 I^2, delta=Q-1,
    V=Df(cT-R)-c, fbar=Aparam I,
    hstar=i^3+cT, W=1+(q-1)hstar,
    Zbar=M(ell+k+n+cT+V+fbar)+(q-1)Y-q^3 W Bt.

The unchanged adaptive main carrier is

    v=k-R-1, S=4qY, U=qS=4q^2Y,
    Dstar=U(X+ac)+H(U gamma+SX-v),
    A1=Dstar^2-U^2(1+Delta c^2).

Define the scaled radicands and the octic norm by

    Ar=M^2 Dtau, Br=M^2 Df, Cr=M^2(QV^2-1),
    Tn=delta^2 Ar Br, Rn=delta Cr,
    Jn=delta(Zbar^2-Ar-Br)-Cr,
    Nc=Jn^2-4[Tn+Rn(Ar+Br)],
    N8=Nc^2-64 Tn Rn Zbar^2.

The required polynomial is

    P=N8+A1+N8 A1.

There are no divisions, variable exponents, or unquantified auxiliary
registers in this definition. The DAG uses only integer constants and
binary addition, subtraction, and multiplication. Scalar products and
squaring are charged; fixed leaves and register reuse are free.

## 2. Inherited source theorem, stated precisely

The weighted/adaptive normalized source interface used by package 70 and
the incoming Joint Guards packet has the four residual equations

    Z^2-M^2 Dtau=0,
    A1=0,
    f^2-Delta(i c^2)^2-1=0,
    (V+u)^2-Delta(f^2-1)u(2V+u)-1=0,

where V=f^2(cT-R)-c and

    Z=M(ell+k+r)+(q-1)Y-q^3 W Bt,
    W=1+(q-1)hstar.

All its supplied coordinates are positive. Its soundness holds for every
positive integer hstar, including a value computed from the other
coordinates. A positive solution yields a finite refutation in the fixed
ZFC calculus. Conversely a finite refutation supplies canonical outer
and strong/auxiliary Pell witnesses. After these are chosen, hstar may
be computed and the first transport witness may be set to

    r=W t0+tau-ell-k-s,
    t0=Bt/(q-1)>=q, 0<s=Y/q^3<k, ell<tau<ell+k.

Consequently r>qW-2k. The canonical main carrier supplies positive
gamma. This is an inherited existence theorem, not a finite-test claim.

The complete compact44 tuple also satisfies beta>=15, K0>=1,
0<MC<beta, 0<MF<2beta. Thus

    0<(MC+q MF)J<(q-1)(1+2q)<2q^2.

Once F, alpha, C are positive and q=F+alpha+C, the same authenticated
source bounds imply 3q<R<q^4-2. The native compiler and K215/refutation
calibration are the unchanged semantic endpoint of this companion.

## 3. What the three-root norm supplies before C is positive

For every positive input, I>=c^2, c>=3, Delta>=15, and

    1<Dtau<Df<Q,  |V|>1.

Indeed ell<ac and k<c imply ell(ell+k)<a(a+1)c^2<Delta I^2.
Also Df>c. For b=cT-R in Z, b=0 gives V=-c; b>=1 gives
V>=Df-c>1; b<=-1 gives V<=-Df-c<-1.

Put Dy=(QV^2-1)/(Q-1), used in the proof only, and let t,f,y be
the positive square roots of Dtau,Df,Dy. We have

    Dy=V^2+(V^2-1)/(Q-1)>V^2>1.

The three radicands are pairwise distinct. The first two are already
ordered. If Dy equalled either integer D in {Dtau,Df}, then
Q(D-V^2)=D-1, impossible because 0<D-1<Q.

No signed sum of t,f,y is zero. If b=0, y<c+1 whereas
f-t>(a+1)c(c-1)>c+1. If b is nonzero, then
y>|V|>=Df-c>2f>f+t. These inequalities use only I>=c^2,
not C>0, R bounds, or any source equation.

The exact octic identity is

    F8(x;A,B,C)=[(x^2-A-B-C)^2-4(AB+AC+BC)]^2-64ABCx^2.

It is the product of x-e1 sqrt(A)-e2 sqrt(B)-e3 sqrt(C) over the
eight sign triples. Our N8 is delta^4 F8(Zbar;Ar,Br,Cr/delta).
Thus N8=0 gives signed roots tau*,f*,y* with

    Zbar/M=tau*+f*+y*,
    tau*^2=Dtau, f*^2=Df, y*^2=Dy.

The elementary three-root extraction lemma applies: three distinct
positive rational radicands, with no vanishing signed sum, have all
their square roots rational whenever one signed sum is rational. For
completeness, for signed roots x1,x2,x3 with rational nonzero sum t0,
write a_j=x_j^2,

    u0=(t0^2-a1-a2-a3)/2,
    v0=(u0^2-a1a2-a1a3-a2a3)/(2t0).

Then u0=x1x2+x1x3+x2x3, v0=x1x2x3, and

    x1=a1(a1+u0)/(a1 t0+v0).

Its denominator is x1(x1+x2)(x1+x3), nonzero by distinctness of
the squared roots. The cyclic formulas finish the argument.

Consequently tau* and f* are integers, being rational square roots of
integers. The adjacent-coefficient Pell descent proves that y* is an
integer from QV^2-(Q-1)y*^2=1, since Q>1 and V is an integer.
That descent is recalled in the retained incoming proof: if y=a/m is
reduced, m^2 divides Q-1, and the unit transformation

    V'=(2Q-1)V-2(Q-1)y,
    y'=(2Q-1)y-2QV

preserves the denominator m and strictly decreases abs(V) when abs(V)>1.
At abs(V)=1 the denominator is 1.

We now have M|Zbar. Reducing modulo q^3 gives q^3|Y; reducing modulo
q-1, using W=1 mod(q-1), gives q-1|Bt. Neither deduction uses C>0.
Set s=Y/q^3>0. Also A1=0 makes Dstar/U an integer square root of
1+Delta c^2. Classify its absolute value and t=abs(tau*) by Pell theory:

    c=psi_Aparam(p), g=chi_Aparam(p), p>=2,
    k=2 psi_(2XY^2+1)(m1), t=chi_(2XY^2+1)(m1).

The case m1=1 would give k=2, eta=zeta=1, c=2Y+1, contrary to
c>=2Aparam>=4Y+4. Thus m1>=2 and

    c>kY>=4(2XY^2+1)Y>8XY^3>=8q^9.

Every statement in this section precedes and is independent of the sign
of C. This order is essential.

## 4. The strong-Pell growth lemma

**Lemma.** Suppose q>=2, Y>=q^3, A>=2Y+2,
Delta=A^2-1, c=psi_A(p)>=6, and positive integers f,i satisfy

    f^2-Delta(i c^2)^2=1.

Then

    i>8q Delta c^4,
    i^3>6q f^2,
    i^3>q^2,
    A i c^2<i^2,
    i^3-A i c^2>k whenever 0<k<c.

**Proof.** Pell classification gives f=chi_A(m),
I=i c^2=psi_A(m), m>=1. The sequence psi has strong divisibility,
so c|I implies p|m. This standard identity follows directly from
psi_A(r+s)=chi_A(r)psi_A(s)+chi_A(s)psi_A(r) and
gcd(chi_A(r),psi_A(r))=1: the Euclidean algorithm on indices yields
gcd(psi_A(r),psi_A(s))=psi_A(gcd(r,s)). Strict growth then gives p|m.

Write m=pv and g=chi_A(p). Composition gives

    i c=I/c=psi_g(v).

Modulo c, g^2=1 and the recurrence gives
psi_g(v)=v g^(v-1) mod c. Since g is a unit modulo c and c divides
the left side, c|v. Thus v>=c>=6.

For g>=2 the positive recurrence gives psi_g(v)>g^(v-1) for v>=2.
Hence i c>g^5. Since g^2=1+Delta c^2 and
Delta>(2Y)^2, we obtain

    i>g^5/c>Delta^(5/2)c^4
       >8Y^3 Delta c^4>=8q^9 Delta c^4>=8q Delta c^4.

All inequalities are strict where needed. Put H0=Delta c^4. Since
H0>=15, i^3>8q H0 i^2>6q(H0 i^2+1)=6q f^2.
Also i>q and i>A c^2, so i^3>q^2 and A i c^2<i^2.
Finally i>c>k and i>=2 yield i^3-i^2>k. This proves the lemma.

At a zero of our two residuals, Section 3 supplies its hypotheses with
A=Aparam and f^2=Df. Thus

    i^3>6q Df, i^3>q^2, fbar<i^2,
    i^3>fbar+k.

In addition fbar>f, because

    fbar^2-Df=I^2-1>0.

These are conditional consequences of the recovered equations. They are
not claimed for arbitrary positive inputs.

## 5. Positivity bootstrap with the low-degree weight

We prove C>0 before invoking the positive source interface. Suppose
instead C<=0. Put d=-C>=0 and Bneg=-Bt>0. Then

    Bneg=(qK0+X)d+qF,
    R=[q(q-F)+d](q^2-1)+(MC+qMF)J.

Using the fixed mask bounds from Section 2 gives

    R<q Bneg+q^4+q^2.

If R<0, the same formula gives

    -R<qF(q^2-1)<q^3F<=q^2 Bneg.

The radical equality becomes

    tau*+f*+y*=ell+k+n+cT+V+fbar+s+W Bneg/(q-1).

Its left side is at most t+f+y, where t<ell+k. We show that its
right side exceeds this upper bound.

First note delta>Df and

    0<y-abs(V)=(V^2-1)/(delta(y+abs(V)))<abs(V)/delta.

If V>0, the integer b=cT-R is positive, and
y-V<V/delta<b. Therefore

    cT+V+fbar-f-y>cT-b=R.

When R>=0 this already suffices. When R<0,
W Bneg/(q-1)>hstar Bneg>=i^3 Bneg>q^2 Bneg>-R.
Again the sum is strictly positive, a contradiction.

If V<0, then b<=0, hence R>=cT>=c>8q^9. Thus
q^4+q^2<R/2, and the preceding bound implies R<2q Bneg.
Moreover abs(V)<Df R and y-abs(V)<R, so

    cT+V+fbar-f-y>-(2Df+1)R>-3Df R.

But

    W Bneg/(q-1)>hstar Bneg>=i^3 Bneg
                    >6q Df Bneg>3Df R.

This is the same contradiction. V=0 is impossible. Therefore C>0.

## 6. Soundness and completeness

Now C>0, and the fixed source bounds give 3q<R<q^4-2.
As c>8q^9, we have c>2R and V=Df(cT-R)-c>1.
The positive-root gap estimate in Section 5 gives

    cT+V+fbar-f-y>R>0.

Recover

    f_old=f, i_old=i, u=y-V,
    r=n+cT+V+fbar-f*-y*.

The auxiliary equation gives u>0, and the last strict inequality gives
r>n>0 for every possible sign choice of f*,y*. Subtracting
M(f*+y*) from Zbar shows that the first source register Z equals
M tau*. Thus the first, strong, auxiliary, and main source equations
all hold with positive supplied coordinates. The inherited soundness
theorem yields a finite ZFC refutation.

Conversely begin with canonical source witnesses for a finite refutation.
Choose their strong pair and positive auxiliary T,u,y, then compute
fbar, hstar=i^3+cT, and W. Section 4 applies to these source witnesses
and gives hstar>cT+fbar+k. The inherited weighted construction provides

    r>qW-2k>cT+fbar.

Set

    n=r-cT-fbar+f+u>0.

Then Zbar=M(tau+f+y), so N8=0; the canonical main carrier gives
A1=0. No additional congruence or divisibility restriction on the
strong pair has been imposed. The order of witness choices is acyclic.

Finally N8 is a square modulo 4, and A1 is a square modulo 4 because
4|U. Thus P=(1+N8)(1+A1)-1 vanishes if and only if both residuals
vanish: the only integer unit possibilities are (1,1) and (-1,-1), and
the latter would make each residual -2, impossible modulo 4.

We have proved, with the identified inherited source calibration,

    exists a strictly positive integer zero of P
       iff a finite refutation in the fixed ZFC calculus exists.

Negating this ordinary arithmetic equivalence gives the requested
equivalence, provable in ZFC, between absence of positive zeros and
Con(ZFC). It establishes neither of those two equivalent assertions.

## 7. Exact degree and why double centering matters

The strong radicand obeys the exact identity

    Df=fbar^2-e, e=I^2-1.

Write z=Zbar-M(V+fbar) only for the degree calculation. Its degree is 9,
and its leading form is

    z0=-q0^4 (i^3+k0 Y T) Bt0,
    q0=3 beta j, k0=eta+zeta,
    Bt0=(K0 q0+X)(q0-F-alpha)-q0F.

In the universal norm substitute

    x=M(V+t)+z, A=M^2 D, B=M^2(t^2-e),
    Cnum=M^2(QV^2-1), delta=Q-1.

As a polynomial in Q,V,M,t,z,e,D, its exact expansion has 1110 terms.
With weights 18,18,4,7,9,10,8, respectively, its highest weight is 200
and its leading form is exactly

    64 M^6 Q^4 V^4 t^2 z^2.

`verify.py` multiplies this polynomial out in an exact sparse integer
ring and checks that leading form. This check captures cancellations
that naive gate-degree propagation misses.

For the source substitutions,

    Q0=i^2 k0^4 X^4 Y^8,
    Df0=i^2 k0^4 X^2 Y^6,
    R0=q0^3(q0-F), V0=-Df0 R0,
    fbar0=i k0^2 X Y^3, M0=q0^4.

The leading form of A1 is

    32 q0^2 k0 X^2 Y^4
       [4q0^2 Y gamma+q0^3(q0-F)],

of exact degree 13. Consequently P has degree at most 213. In its
degree-213 part, the coefficient of

    j^48 i^24 eta^37 X^30 Y^67 F^4 alpha^2 gamma

is exactly

    2^13 (3 beta)^48 > 0.

To see uniqueness, the gamma term fixes the displayed main-carrier
summand; the minimum q0 degree selects F^4 from (q0-F)^4 and
X^2 alpha^2 from Bt0^2. The i^24 term selects i^6 from
(i^3+k0YT)^2. This coefficient is independent of K0,MC,MF, so it
cannot disappear on the actual coefficient slice. It proves exact
degree 213 rather than merely a generic upper bound.

## 8. Verification boundary

The package verifies exact register identities, the octic norm identity,
both norm-center cancellations, the selected leading coefficient,
operation count, input liveness, literal rebuild, and coefficient bytes.
Small Pell examples check the growth estimates and integrality formulas;
they supplement the proof and do not establish an unbounded theorem.

The new part requiring mathematical review is Sections 4--6. The copied
incoming source proofs and their hashes are retained under `provenance/`
to make inherited assumptions inspectable. The checker does not test
ZFC consistency, run K215 to completion, or replace the compiler proof.
