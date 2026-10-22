# Twenty-six unrestricted integer unknowns

## Result and exact scope

The monic merger below, together with the signed-core argument, gives a
polynomial in exactly **26 unrestricted integer unknowns**. Its explicit
division-free circuit uses **169** binary additions, subtractions, and
multiplications (96 multiplications and 73 additions/subtractions), and its
exact total degree is **2993**. The corresponding three-equation system uses
164 operations and has residual degrees 13, 4, and 2976.

All fixed ports must come from one authentic blank-input native compiler
tuple. The original package-06 tuple works; the T4 tuple and the new
5252-tile backend also work after their separate adapters establish the same
interface. For the signed completeness step, the backend's exponent d_base,
canonical width and height are powers of five. In particular the new backend
has d_base=5^16, which is odd. The four ports are beta=Bbase-1, K0, MC,
and the shifted MF=MF_native+Bbase-1. No individual ports may be mixed across
backends.

The proof is ordinary mathematics formalizable in ZFC. The Diophantine
compiler and signed Pell core remain mathematical dependencies, not newly
kernel-checked results. The existing K215 calibration then gives the
equivalence between existence of an integer zero and finite ZFC refutability.
Consequently ZFC proves that absence of zeros is equivalent to Con(ZFC).

## 1. Exactly twenty-six supplied integers

For each v in {J,F,alpha,z,s,eta,zeta}, supply three independent integers
v_x,v_y,v_z and set

    v = 1+v_x^2+v_y^2+v_z(v_z+1).

These are seven positive ports represented by 21 unrestricted integers.
Supply five further integers h,T,u,r,b, and set

    i=2r+1, w=b^2.

Thus there are exactly 26 independent integer unknowns. Every positive
integer is represented by the displayed positive map: Legendre's
three-square theorem applied to 4n-3 gives one odd square and two even
squares, which yield n=1+x^2+y^2+z(z+1). The map is positive on every
integer triple because z(z+1)>=0.

Define substituted polynomials

    q=beta J+1, Cw=q-F-alpha, X=wq, Y=sq^3, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y, H=4a+3, Delta=a^2+H,
    R=[(q-1)(q-F)+alpha](q^2-1)+(MC+q MF)J,
    Nk=k-hE-R,
    Nt=(K0+w)Cw+q-F-z(q-1),
    L0=E(kY), A=1+L0(L0+k).

For the eliminated strong root put

    I=ic^2, D=1+Delta I^2, Q=Delta(D-1)=(Delta I)^2, d=Q-1,
    v0=cT, Z0=c+RD,
    P=QD v0^2, Z=Q Z0^2, e=P+Z-1, a0=PZ,
    M=2(kI^2+T^2), N=dM^2 A.

The symbol d here is the auxiliary Pell coefficient Q-1, not the fixed
compiler exponent d_base. All the preceding quantities are polynomial
abbreviations; none is a further unknown.

Consider the monic degree-eight polynomial in an eliminated indeterminate v:

    H8(v) = [v^4-2d(N+e)v^2+d^2((N-e)^2+4a0)]^2
            -16a0 d^2[v^2+d(N-e)]^2.

Set

    B=1+Delta c^2, W=X+ac+Hu, p=Hc,
    Rstar=Res_v(H8(v),(W-pv)^2-B).

The single equation is

    Nk Nt(1+Rstar)-1=0.

The system is Nk=1, Nt=1, Rstar=0; its circuit compares the two terms of
the final norm directly, hR^2=B hI^2, saving the subtraction. The resultant notation only describes
an ordinary polynomial. It is implemented by this division-free norm circuit:

    r0=W^2+B, r1=2W, dp2=d*p^2, d2p4=(dp2)^2,
    S=N-e, ell=2dp2(N+e), vc=d2p4(S^2+4a0),
    vR=r0^2+B r1^2-ell r0+vc,
    vI=r1(2r0-ell), uR=r0+dp2 S, coef=16a0d2p4,
    hR=vR^2+B vI^2-coef(uR^2+B r1^2),
    hI=2(vR vI-coef uR r1),
    Rstar=hR^2-B hI^2.

The identity in the quadratic algebra is

    hR+hI sqrt(B)=p^8 H8((W+sqrt(B))/p).

Multiplication by the conjugate gives exactly the resultant; the factor
p^16 is precisely the usual leading-coefficient contribution from the
degree-two polynomial, not an extra zero-producing factor. Since a,c>0,
p=Hc is nonzero at every tuple in the stated domain.

## 2. Unit extraction and the monic integrality argument

At a zero, Nk,Nt,1+Rstar are integer units. Since hI is even, Rstar is
a square modulo four. Thus 1+Rstar cannot be -1; necessarily Rstar=0
and Nk=Nt=epsilon with epsilon in {+1,-1}.

The zero resultant supplies a common complex root v. Since H8 is monic
with integer coefficients, v is an algebraic integer. The other equation
gives

    v=(W+/-sqrt(B))/(Hc).

Here X>=0, Y>0, a>0 and c>0, so B>0. If B were nonsquare, conjugation
would give another algebraic integer v' and

    Norm(v-v')=-4B/(H^2c^2).

But

    H^2c^2-4B=(12a^2+8a-3)c^2-4>0.

The norm would lie strictly between -1 and zero, contradicting its being
an integer. Therefore B is square. It follows that v is rational and
algebraically integral, hence v is an integer. Consequently

    gamma=u-cv

is an integer and the common-root equation restores the exact main norm

    (X+ac+gamma H)^2-Delta c^2=1.                 (Main)

This conclusion uses no positivity of u or gamma. Put t=v/d, provisionally
a rational number. The task below is to prove that this rational t restores
the eliminated integer roots without allowing extraneous solutions.

## 3. Exclude the square-scale boundary before outer bounds

The auxiliary multiplier i=2r+1 is never zero. Also Delta>0 and c>1, so
Q>1 and d>0 even before w is shown positive.

If b=0, then X=0 and a=Y. In (Main), the left root is ac+gamma H and
Delta=a^2+H. Reduction modulo H would give 0=1 mod H, impossible
because H=4Y+3>1. Hence b!=0 and w>0. In particular X>=q.

Weak transport gives Cw>=0. Indeed

    q-F-z(q-1)=1-F-(z-1)(q-1)<=0,

and Cw<=-1 would make Nt<=-(K0+w)<=-2. The authentic shifted-mask
bounds now give

    q>=16, R>3q+1, R<q^4-2,
    E>=q^4>R+2, a>R+2, Y>=q^3>=4096.

One must retain the possible Cw=0 boundary at this stage. It disappears
only after the final index-sign argument.

Although h is signed, it is forced nonnegative. For h<=-1,
k=R+epsilon+hE<=R+1-E<0, contrary to k=eta+zeta>0. Therefore
k>=R-1, R<2k, and k>48. Positivity of eta,zeta gives

    kY<c<k(Y+1).

## 4. A signed lower-weight domination bound

This step replaces the positive-h proof in the twelve-positive-variable
construction. It is essential: signed h only gives h>=0 and does not give
k>E.

Write Aparam=a+2. Classify (Main):

    c=psi_Aparam(j), |X+ac+gamma H|=chi_Aparam(j), j>=1.

Here chi_Aparam(j)+psi_Aparam(j)sqrt(Aparam^2-1) is the j-th power of
Aparam+sqrt(Aparam^2-1). Since c>1, j>=2. If j=2, c=2a+4 and
the absolute main root is 2a^2+8a+7. For the positive main root,
root-ac is 4 modulo H. For the negative root, root-ac is 3a+2 modulo H.
But root-ac is also X modulo H, and 16<=X<a<H. Neither residue is
possible. Thus j>=3.

It follows that c>=4(a+2)^2-1>4a^2. Together with c<k(Y+1),
Y+1<2Y and a>=XY, this gives

    k>2X^2Y.

Now L0=kXY^2 and Aparam<2XY, so

    L0>2X^3Y^3>12 Aparam^2,
    L0>Aparam c/4.

Consequently

    A>144 Aparam^4,     A>Aparam^2 c^2/16.       (Bounds)

Let M0=kI^2+T^2; our actual M=2M0. Since I^2>1,

    D<Aparam^2 I^2, M0^2>=4kI^2T^2, M0^2>=k^2I^4.

The second bound in (Bounds), with k>48, gives

    A M0^2>12 Dv0^2.

Also c<I^2 and R<2k give Z0<3k Aparam^2 I^2. The first bound in
(Bounds) gives A M0^2>16 Z0^2. Splitting into two halves yields

    A M0^2>4(Dv0^2+Z0^2),

and the same strict inequality holds for M=2M0. As d>=Q/2, define
C0=N-e. Then

    C0>Q(Dv0^2+Z0^2)+1>|B0|sqrt(D),
    B0=2Qv0Z0.

These bounds permit signed T. They have been established before recovering
f,tau,y or assuming t is integral.

## 5. Rational auxiliary Pell saturation

We need the following elementary lemma, including for the T=0 exception.

**Lemma.** If S>=2 and V are integers and y is rational with

    S^2 V^2-(S^2-1)y^2=1,

then y is an integer.

Write S^2-1=b0^2 D0 with D0 positive squarefree. Put x=S|V| and
z0=b0|y|. Squarefree valuations in x^2-D0 z0^2=1 force z0 to be an
integer: a reduced denominator squared would have to divide squarefree D0.
Let F+G sqrt(D0) be the fundamental positive norm-one unit with integer
coefficients. Pell classification supplies positive indices e0,m with

    S=chi_F(e0), b0=G psi_F(e0),
    x=chi_F(m), z0=G psi_F(m).

Because S divides x, chi_F(e0) divides chi_F(m). The addition identities
give chi_F(m+2e0) congruent to -chi_F(m) modulo chi_F(e0), and
chi_F(2e0-r) congruent to -chi_F(r) modulo chi_F(e0). Reducing the
index modulo 2e0 and reflecting it gives 0<=r<=e0. If r<e0,
strict growth gives 1<=chi_F(r)<chi_F(e0), a contradiction. Thus m is
an odd multiple of e0. The multiplication identity gives
psi_F(e0)|psi_F(m), so |y|=psi_F(m)/psi_F(e0) is integral.

This argument does not assume S^2-1 is squarefree, which would be false
for many admissible S.

## 6. Restore all three integer roots, including T=0 and t=0

Put

    Ct=d t^2+N-e,
    Ut=Ct^2+4(a0-d t^2 N),
    Rt=Ut^2-16 Ct^2 a0.

Direct expansion gives H8(dt)=d^4 Rt. Since t=v/d and H8(v)=0,
we have Rt=0. The bound in Section 4 shows Ct=C0+dt^2>0 for rational
t. If t=0, then

    Rt=(C0^2-4a0)^2=(C0^2-D B0^2)^2>0,

a contradiction. Thus t is nonzero.

If T=0, then B0=a0=0. The identity Rt=0 gives
Ct^2=4d^2t^2M^2 A. Hence tau=Ct/(2dtM) is rational with
tau^2=A, so tau is an integer. Put y=t-Mtau. Expanding Ct gives

    Q Z0^2-(Q-1)y^2=1.

Because Q is an integer square, the saturation lemma makes y an integer.
But 1<Z0<Q. To check the upper bound, note Delta>R and
D=1+Delta I^2:

    Q-Z0=(Delta-R)D-Delta-c
         >=D-Delta-c
         =1+Delta(I^2-1)-c>0.

The norm would imply (Q-1)(y^2-Z0^2)=Z0^2-1>0 and therefore
|y|>=Z0+1. Since Q-1>=Z0, this gives

    Z0^2-1 >= (Q-1)(2Z0+1) >= Z0(2Z0+1)>Z0^2-1,

impossible. Thus T!=0 and B0!=0. This explicit exception check is
required before dividing by B0.

Now define

    f=-Ut/(2Ct B0).

Since 4a0=D B0^2, Rt=0 gives f^2=D. Thus f is a nonzero integer.
The definition of Ut then gives

    (Ct+B0 f)^2=4d^2t^2M^2 A.

Therefore tau=(Ct+B0 f)/(2dtM) is rational with square A and is an
integer. With y=t-Mtau, expansion gives

    Q(v0 f-Z0)^2-(Q-1)y^2=1.

The saturation lemma again makes y an integer, and then t=Mtau+y is an
integer as well. Because f^2=D,

    v0 f-Z0=c(Tf-1)-Rf^2,
    f^2-Delta i^2c^4=1.

The original normalized first, strong, and auxiliary norms have therefore
all been restored. Neither tau nor y is zero: A>1 and Q>1 exclude these
cases directly.

## 7. Finish soundness through the signed core

The reconstructed tuple has precisely the signed-core hypotheses:

- J,F,alpha,z,s,eta,zeta are positive;
- i is odd and nonzero, and w is a positive square;
- h,T,gamma,f,tau,y are integers;
- the main, first, strong and auxiliary norms are +1;
- Nk=Nt=epsilon in {+1,-1}.

For completeness, the inherited arithmetic argument proceeds as follows.
The first norm classifies k=2psi_(2XY^2+1)(n), and the index congruence
gives n>=(R-1)/2. The main norm gives c=psi_(a+2)(j); the size ratio
implies j>n and c>2j,2R. The normalized strong norm gives
|f|=chi_(a+2)(m) with jc dividing m, by strong divisibility followed by
the binomial expansion modulo c. In particular c divides m and m>2j.

Classifying the absolute auxiliary Pell root while retaining its sign, the
two congruences V=-c modulo |f| and V=-R modulo c imply
R=+j or -j modulo c. The strict bounds 0<R,j<c/2 force j=R.
Then E>R+2 removes wrap in the first-index equation. The ratio
kY<c<k(Y+1) excludes epsilon=-1 by Pell duplication, so Nk=Nt=1.
Transport now excludes the previously retained Cw=0 boundary.

The signed-gamma proof uses the lower ratio estimate to show
0<X*2^R<a<H-1. A negative main root would imply X*2^R=-1 modulo H,
contradicting that interval. The positive main-root congruence therefore
gives X=2^R exactly. Standard half-binomial extraction, inverse population,
mask synchronization and the native local relation recover an accepting
blank K215 tableau. These are precisely the signed-core arguments in
package 14, whose proof does not assume positive h,T,gamma or f.

Thus the new integer equation produces no additional halting claims beyond
the authenticated signed compiler interface.

## 8. Completeness with the two restricted ports

If the blank machine halts, choose canonical width and height that are
sufficiently large powers of five. With d_base a power of five, the exponent
d_base*Ncells in q=2^(d_base*Ncells) is odd. The final tuned rank R is
3 modulo four and therefore odd. The canonical

    w=2^(R-d_base*Ncells)

has positive even exponent and is a square. At the canonical witnesses,
c=psi_(a+2)(R) is odd. Choose the auxiliary index m=cR rather than
2cR. The binomial expansion gives c^2|psi_(a+2)(m), and this quotient
i is positive and odd, because m and c are odd. Thus i=2r+1 and w=b^2
are both admissible without changing the accepting tableau.

Take the resulting positive normalized witness. Put

    t=M tau+y, v=d t, u=gamma+c v.

The root identities give H8(v)=0 and the main norm gives
(W-pv)^2=B. Hence Rstar=0 and Nk=Nt=1. All seven positive ports have
preimages under the three-integer positive map. This gives a zero of the
26-integer polynomial.

The canonical square-w and odd-i restrictions preserve existence; they do
not claim that every old positive solution already has those properties.

## 9. Uniform exact degree and audited operation count

The twelve-port product circuit has 117 operations. Seven positive
parametrizations cost 7*7=49 operations, i=2r+1 costs two, and w=b^2
costs one. Thus the integer circuit has 117+52=169 operations. Its three-
equation version removes the four-gate product finalizer and compares the
two norm-square terms directly, saving one further subtraction. It has
164 operations: 94 multiplications and 70 additions/subtractions.

Give the positive ports J,F,alpha,z,s,eta,zeta and w weight two,
h,i,T,u weight one, and fixed ports weight zero. Then

    deg(c,a,Delta,R,A,I)=(10,12,24,8,44,21),
    deg(D,Q,d,P,Z,e,a0,M,N)=(66,90,90,178,238,238,416,44,222),
    deg(B,W,p)=(44,22,22).

In the norm circuit, vR has the unique degree-744 top term
d^2 p^4 e^2; vI has degree394, uR degree372 and coef degree684.
Consequently hR has unique top term d^4 p^8 e^4 of degree1488, while
hI has degree1138. The final norm has exact degree2976 with top form
d^8 p^16 e^8. Its competing term B hI^2 has degree2320.

Nk has degree13, Nt degree4, and their top forms are nonzero. Thus the
single polynomial has exact degree 13+4+2976=2993. These leading terms
are uniform for every authentic beta>0. Substitution by the seven disjoint
positive quadratics cannot annihilate them, since specializing two members
of each triple to zero gives the injective monomial map v->v_x^2; the
odd multiplier has nonzero linear leading term 2r and w has leading b^2.

The emitted artifacts check all live ports/gates, independent signed
evaluation of the quadratic-algebra norm, exact weighted degree bounds,
and a modular univariate specialization attaining the degree. These finite
checks do not claim a K215 halting witness or an end-to-end formal proof.

## 10. Sources and boundary of the claim

- New twelve-coordinate monic merger: the accompanying merger_proof.md
  and its explicit emitter build_mergers.py.
- Package 09's normalized root core and authentic weak bounds:
  09-combined13/proofs/ROOT_AMALGAMATION_PROOF.md and
  upstream/compiler/06_fixed_blank_67_proof.md.
- Seven-positive-port signed soundness and odd-i/square-w completeness:
  14-integer29/proofs/signed_domain_proof.md.
- Coefficient adapters are separate proofs; all four ports must bind to
  the same adapter instance and to the literal K215 table.

The upstream source pin is
f0ae4e0991ca44a7bb4e5671d42e33d775e48035. This improves the provided
collection's explicit unrestricted-integer count from 29 to 26, at a
substantial degree and operation cost. It asserts no global minimum and
does not supersede lower-degree alternatives when those are the objective.

