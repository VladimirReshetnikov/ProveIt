# An auxiliary offset and two root centers give degree 211

## Result and comparison

One explicit fixed-coefficient polynomial in eleven strictly positive integer
unknowns, exact total degree **211**, with **112** live binary arithmetic
operations. Its two-residual system uses 109 operations. The earlier centered
eleven-positive equation in the incoming `ZFC_Diophantine_Joint_Guards_2026-10-24.zip`
has degree 257 and 114 operations; the uncentered descent equation
has degree 277 and 111 operations. These are relative, measured improvements,
not a proof of global simplicity or worldwide priority.

The key new choice is very small: replace the auxiliary coordinate by

    T_old = T + F + alpha.

The first and main Pell equations already force c>8q^9 before transport
positivity is known. This translation consequently makes the auxiliary
quantity V positive at exactly the stage when it is needed. It removes the
large exceptional-negative-V weight. Centering the strong root at (a+2)I and bounding the remaining auxiliary
gap gives a degree-two transport weight.

The fixed compact44 tuple and the native/compiler/refutation interface are
inherited. The new local transformation has the ordinary proof below; this
packet is not a new end-to-end Lean/Rocq or internal object-ZFC certificate.

## 1. Complete polynomial

The eleven unknowns, all strictly positive integers, are

    j, F, alpha, i, T, X, Y, n, eta, zeta, gamma.

The fixed ports are the coherent compact44 tuple beta,K0,MC,MF, with
beta=2^590069-1 and MF already shifted. Actual payloads and their finite
generator are included. Every other symbol in this section abbreviates a
polynomial, not an additional quantified variable.

Define

    J=3j+1, q=beta J+1, C=q-F-alpha,
    E=XY, k=eta+zeta, c=kY+eta,
    a=E+Y, Aparam=a+2, H=4a+3, Delta=a^2+H=Aparam^2-1,
    ell=EkY, I=i c^2, M=q^3(q-1),
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J,
    Rhat=q^3(q+F+alpha), Bt=(q K0+X)C-qF,
    Dtau=ell(ell+k)+1,
    Df=1+Delta I^2, Q=Delta^2 I^2, delta=Q-1,
    T_old=T+F+alpha, C_f=Aparam I,
    V=Df(c T_old-R)-c,
    L=k T_old, W=1+(q-1)L,
    Zbar=M(ell+k+n+L+V+C_f)+(q-1)Y-q^3 W Bt,
    r0=k-R-1, S=4qY, U=qS,
    Dstar=U(X+ac)+H(U gamma+SX-r0),
    A1=Dstar^2-U^2(1+Delta c^2).

Set

    A=M^2 Dtau, Bf=M^2 Df, Cnum=M^2(QV^2-1),
    Tn=delta^2 A Bf, Rn=delta Cnum,
    Jn=delta(Zbar^2-A-Bf)-Cnum,
    Ncenter=Jn^2-4[Tn+Rn(A+Bf)],
    N8=Ncenter^2-64 Tn Rn Zbar^2.

The single equation is

    P11=N8+A1+N8*A1=0.

The literal division-free graph is `p11_positive_degree211.json`. Fixed
numerals and reuse are free in its operation metric; scalar multiplication,
squaring, addition, and subtraction each cost one binary operation.

## 2. Radical recovery is independent of the new positivity argument

The following source70 argument applies with any positive integer T_old;
neither the new transport weight nor positivity of C enters it. Write

    t=sqrt(Dtau), f=sqrt(Df), Dy=(QV^2-1)/(Q-1), y=sqrt(Dy).

All three radicands are positive. They are pairwise distinct, and no signed
sum of their square roots vanishes. Here is the explicit separation argument.
For Z=XY^2, t<ell+k=k(Z+1), while f>(a+1)I>t; indeed
I>=c^2 and c>kY make the latter inequality immediate. Put b=cT_old-R.
If b=0, V=-c. Since Q>c^2, y<c+1, whereas
f-t>(a+1)c(c-1)>c+1; thus f>t+y. If b is a nonzero integer, then
|V|>=Df-c. The bounds f>3c^2 and f>t give
y>|V|>=Df-c>2f>f+t. Either case proves strict dominance by one root.
Also Dy cannot equal Dtau or Df: for either such positive integer D,
Q(D-V^2)=D-1 is impossible because 0<D-1<Q. Finally Dtau<Df.

For positive pairwise-distinct rational radicands with no zero signed
three-root sum, a rational signed sum forces all three roots rational.
One elementary proof writes the signed roots x1,x2,x3, their nonzero
rational sum s, and a=x1^2,b=x2^2,c=x3^2. Then

    u=(s^2-a-b-c)/2,
    v=(u^2-ab-ac-bc)/(2s),
    x1=a(a+u)/(as+v),
    as+v=x1(x1+x2)(x1+x3).

The denominator is nonzero by distinctness; the cyclic formulas recover
the other roots. All these identities are checked exactly in `audit.py`.

The universal conjugate norm is

    F8(x;a,b,c)=[(x^2-a-b-c)^2-4(ab+ac+bc)]^2-64abc x^2.

It is the product of x minus all eight signed sums of the three roots.
Our N8 is delta^4 F8(Zbar;A,Bf,Cnum/delta). Thus N8=0 gives

    Zbar/M=tau_*+f_*+y_*,
    tau_*^2=Dtau, f_*^2=Df, y_*^2=Dy.

All three signed roots are rational by separation. The first two are
integers because their squares are integers. The adjacent-coefficient
Pell descent from source69 makes the third an integer as well:

    QV^2-(Q-1)y_*^2=1, Q>1, Q,V in Z  =>  y_* in Z.

For clarity, write y_*=a/m in lowest terms. Then m^2 divides Q-1.
For |V|>1 the norm-preserving transformation

    V'=(2Q-1)V-2(Q-1)y_*,
    y'=(2Q-1)y_*-2QV

has integral first coordinate with 0<|V'|<|V| and preserves the reduced
denominator m. Strong induction reaches |V|=1, where y_*=+/-1.
Signs can be made positive before each descent. This proves integrality.

## 3. The outer Pell growth is available before C>0

Since M divides Zbar, reduction modulo q^3 and q-1 gives

    q^3 divides Y,   q-1 divides Bt.

This uses W=1 modulo q-1 and gcd(q,q-1)=1. It uses no sign of Bt or C.
The equation A1=0 gives an integral root g_*=Dstar/U. Its sign is not
needed: |g_*|^2-Delta c^2=1.

Positive Pell classification gives indices m1,p>=1 with

    |tau_*|=chi_(2XY^2+1)(m1), k=2 psi_(2XY^2+1)(m1),
    c=psi_(a+2)(p).

Here chi and psi are the standard Pell sequences, initialized by
chi_A(0)=1,chi_A(1)=A and psi_A(0)=0,psi_A(1)=1, each satisfying
z(n+2)=2A z(n+1)-z(n). The first classification is the elementary Pell
classification for tau^2-XY^2(XY^2+1)k^2=1.

Because c>=3, p>=2. If m1=1, then k=2, eta=zeta=1 and c=2Y+1, but
c>=2(a+2)>=4Y+4. Hence m1>=2 and

    c>kY>=4(2XY^2+1)Y>8XY^3>=8q^9.                 (1)

Everything up to (1) precedes transport positivity and any bound on R
that depends on C. This dependency order is essential.

## 4. The new offset makes V positive

The actual fixed masks satisfy 0<MC<beta, 0<MF<2beta. The elementary
source70 estimate is unconditional in positive F,alpha:

    |R|<q^3(q+F+alpha)=Rhat.

For reference, the mask term is less than 2q^2, and expanding the other
term gives |R|<q^4+Fq^3+(alpha+2)q^2<Rhat; q>=16 and alpha>=1 suffice.
Put h=F+alpha>=2. Since

    q^3(q+h)<=q^3(q/2+1)h<q^4 h,

(1) implies c h>Rhat. Consequently

    cT_old-R=cT+c h-R>cT>=c,
    V>Df*c-c>1,

In particular V>0 is now
known without assuming C>0. This is the new implication that replaces
the exceptional-negative-V branch in the degree-257 construction.

The same bound Rhat<c h also gives

    0<cT_old-R<c(T+2h),  0<V<Df*c(T+2h).

Moreover

    delta-(Delta-1)Df=Delta(I^2-1)>0,
    c=kY+eta<k(Y+1),   Delta-1>2(Y+1).

The second strict bound follows from a>=2Y and Y>=1. Therefore the
auxiliary norm gives the sharper positive-gap estimate

    0<y-V=(V^2-1)/(delta(y+V))<V/delta
         <c(T+2h)/(Delta-1)<k(T+2h)/2<k(T+h)=L.

Also f<C_f=Aparam I, because C_f^2-Df=I^2-1>0. Hence

    L+C_f+V-f-y>0.                                  (2)

This L has degree two. The polynomial centers V and C_f absorb the two
large radicals themselves; only the much smaller gap enters the weight.

## 5. Recover transport positivity and the source witnesses

Write s=Y/q^3>0 and b=Bt/(q-1), an integer. The norm equality is

    tau_*+f_*+y_*=ell+k+n+L+V+C_f+s-Wb.

If b<=0, its right side is strictly larger than
|tau_*|+|f_*|+|y_*| by |tau_*|<ell+k and (2), a contradiction. Hence
Bt>0, which implies C>0. The ordinary native mask bounds now give

    3q<R<q^4-2.

Recover positive integers

    f_old=|f_*|, i_old=i, u=|y_*|-V,
    r=n+L+V+C_f-f_*-y_*.

Equation (2) gives r>n>0, and u>0 follows from the auxiliary norm.
The transport with weight hstar=L becomes exactly the first carrier
M*tau_*. The strong equation f_old^2-Delta I^2=1, the auxiliary
norm, and the adaptive main equation all hold.

These are the weighted source70/source61 interface with positive T_old.
Its soundness for every positive integer transport weight hstar yields
the pinned native zero and then a finite syntactic ZFC refutation. The
source proof is retained in `upstream/70-residue-orientation__eleven__PROOF.md`;
its weighted-interface derivation, ordinary rank recovery, fixed native
compiler, and K215 calibration are inherited, not finite-test conclusions.

## 6. The positive offset is compatible with canonical completeness

A finite refutation gives the canonical compact source. It has
q>=16, C>0, R=3 modulo 4, R>3q, c>8q^9, and F+alpha<q.
Choose its normalized strong pair f,I with I=i c^2. Put Maux=Delta I.
The standard auxiliary reconstruction uses

    V*=chi_Maux(R)/Maux, y*=psi_Maux(R),
    T_old=(V*+c+R f^2)/(c f^2).

The inherited reconstruction proves T_old a positive integer and
y*>V*>0. We need the stronger bound T_old>F+alpha, which follows
directly from growth. Since R>=7,

    V*>=Maux^(R-1)>=Maux^6,
    f^2=1+Delta I^2<Maux^2,  Maux>=c^2,
    T_old>V*/(c f^2)>Maux^4/c>=c^7>q>F+alpha.

Thus T=T_old-F-alpha is a strictly positive integer. This proves that
the coordinate translation loses no canonical refutation witness; it
does not claim a bijection on all old positive zeros.

The same growth proves T_old>C_f as well. Indeed I>=c^2 implies
I^3/c>=1, and Delta^4>Aparam, so

    T_old>Maux^4/c=Delta^4 I*(I^3/c)>Aparam I=C_f.

Form L,W only after choosing the strong and auxiliary pair. Then
L=k T_old>C_f and L>k. The canonical transport has t0=Bt/(q-1)>=q,
s<k and tau>ell. Thus

    r=W t0+tau-ell-k-s>qW-2k>2L,

because q>=16 and L>k. Set

    n=r-L-V*-C_f+f+y*=r-L-C_f+f+(y*-V*)>0.

The new Zbar equals M(tau+f+y*), so N8=0. The canonical adaptive
main carrier supplies positive gamma and A1=0, as in the inherited
weighted source. All eleven supplied variables are positive.

## 7. One equation, exact degree, and exact operation count

Both N8 and A1 are squares modulo four: the norm tail contains 64 and
4 divides U. Therefore

    N8+A1+N8*A1=0  iff  (1+N8)(1+A1)=1
                          iff  N8=A1=0.

The potential negative units would require a residual -2, impossible
modulo four. No sign condition on the residuals is assumed.

The degree audit uses a universal double-center identity rather than a
naive gate bound. For independent symbols z,a,b,c,e,f put

    x=z+b+c, B=b^2-e, C=c^2-f,
    Nc=(x^2-a-B-C)^2-4(aB+aC+BC),
    N=Nc^2-64aBCx^2.

Assign respective weights (8,16,11,22,18,26). Exact expansion has 30
terms in Nc and 229 terms in N. Their leading weighted forms are

    in63(Nc)=8bc^2z,
    in126(N)=64b^2c^4(z^2-a).

For the actual polynomial substitute

    z=Zbar-MV-M C_f, a=A, b=M C_f, c=MV,
    e=M^2(I^2-1), f=-M^2(V^2-1)/delta.

These substitutions are exact because C_f^2-Df=I^2-1 and
(MV)^2-Cnum/delta=-M^2(V^2-1)/delta. The apparent denominator only
occurs in this proof identity. Multiplying the inner norm center by
delta^2 and the outer norm by delta^4 gives precisely Ncenter and N8.
The exponent of f is at most four, so the cleared identity is polynomial.
The complete 229 coefficients and substitutions are in
`DOUBLE_CENTER_CERTIFICATE.json` and are regenerated and checked exactly.

Here delta has degree18. Thus Ncenter has degree99 and N8 has degree198.
The actual degrees of I,Df,Q,V,C_f,L,W,Zbar are

    5,14,18,18,7,2,3,22.

The centered z has degree8 and the main residual A1 degree13. Consequently
degree(P11)=211, as the following attained-degree certificate confirms.
Let q0=3 beta j, k0=eta+zeta, I0=i k0^2Y^2,
Df0=X^2Y^2 I0^2, Q0=X^4Y^4 I0^2, Cf0=XY I0,
L0=k0(T+F+alpha), ell0=X k0Y^2, R0=q0^3(q0-F), and
Bt0=(K0q0+X)(q0-F-alpha)-q0F. Then

    in198(N8)=64 Q0^4 q0^32 Df0^4 R0^4 Cf0^2
                    *L0 Bt0 (L0 Bt0-2ell0),
    in13(A1)=32 q0^2 k0 X^2Y^4(4q0^2Y gamma+R0).

The coefficient of

    j^48 i^18 eta^39 X^30 Y^67 T^2 F^4 alpha^2 gamma

in P11 is 2^13(3 beta)^48>0, independently of K0,MC,MF. The T^2 factor
selects the L0^2 Bt0^2 term and excludes the ell0 term. Minimum q0 degree
then selects F^4 from (q0-F)^4 and X^2 alpha^2 from Bt0^2.

The literal graph has 64 multiplications, 31 additions and 17 subtractions,
giving 112 operations. Its two-residual system has 109 operations.

## 8. Logical conclusion and limits

Composing the two zero-existence implications with the inherited ordinary
native/compiler and syntactic-refutation calibration proves, by ordinary
arguments formalizable in ZFC,

    ZFC proves: no strictly positive zero of P11 iff Con(ZFC).

No consistency assumption is used. This does not prove either side
separately, lower the existing nine-positive variable bound, establish a
global optimum, or replace the outstanding end-to-end formal calibration.
The exact audits certify the finite formulas, degree, costs, and payloads;
the unbounded proof is the argument above and the explicitly named sources.

