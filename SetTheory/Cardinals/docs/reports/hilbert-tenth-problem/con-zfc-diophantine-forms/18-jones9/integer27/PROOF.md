# Direct 27-integer Diophantine forms of Con(ZFC)

## Status, sources, and what is new

This is an ordinary mathematical reduction, formalizable in ZFC. It is not a
new Lean/Rocq certificate. It combines package 09's three-root amalgamation
with package 14's signed-domain theorem, at ProveIt commit
`f0ae4e0991ca44a7bb4e5671d42e33d775e48035`. The new part is the extension of
amalgamation to signed h,T,gamma,t, an odd signed i, and square w. The
exceptional cases t=0 and T=0 are excluded explicitly, rather than silently
using the positive-variable proof. The result has 27 unrestricted integer
unknowns, improving the 29 in package 14 under this particular metric.

The imported premises are the native-window/Pell compiler and K215 calibration,
and package 14's signed normalized-core theorem. Those premises are not proved
by the finite checks in this directory. Package 11's T4 coefficient tuple can
be used as a whole: its compiler has the same four-port interface and permits
arbitrarily large independent width and height powers of five. Its d=5^18 is
odd, so the square-w completeness argument in package 14 still applies. The
old package-06 whole tuple is a conservative fallback. Ports from distinct
tuples must never be mixed.

The new constructions are not claimed globally minimal and do not improve
the classical existential nine-variable theorem. Their particular advantage
is a fully displayed small circuit with degree and sign bounds audited here.

## 1. Formula before positive-port substitution

Seven coordinates are positive:

    J,F,alpha,z,s,eta,zeta > 0.

Six coordinates are unrestricted:

    h,r,T,u,gamma,t in Z.

Put i=2r+1 and w=u^2, and define substituted polynomial abbreviations

    q=beta J+1, X=wq, Y=sq^3, E=XY, k=eta+zeta,
    c=kY+eta, a=E+Y, H=4a+3, Delta=a^2+H,
    Dmain=X+ac+gamma H,
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J,
    Nmain=Dmain^2-Delta c^2,
    Nk=k-hE-R,
    Nt=(K+w)(q-F-alpha)+q-F-z(q-1),
    L0=E kY, A=1+L0(L0+k), I=ic^2,
    D=1+Delta I^2, Q=Delta(D-1), v=cT, z0=c+RD, d=Q-1.

Here beta,K,MC,MF are the exact fixed four coefficient ports. MF is the
shifted port, not the native mask. The letter D denotes the radicand of the
deleted strong root; Dmain is a different polynomial.

There are two weights:

    M_full=D+v^2,
    M_low=k I^2+T^2.

For either weight put

    W=Dv^2+z0^2,
    e=QW-1,
    Broot=2Qvz0,
    C=d(t^2+M^2 A)-e,
    U=C^2+D Broot^2-4d^2 t^2 M^2 A,
    Res=U^2-D(2C Broot)^2.

The single equation is

    Nmain Nk Nt (1+Res)-1=0.                         (P)

The alternative four-equation system is

    Nmain=Nk=Nt=1,       Res=0.                     (S)

Every symbol above is an abbreviation, not another quantified unknown.

## 2. Unit extraction and initial bounds

At a zero of (P), all four factors are units. Since Delta is 0 or 3 modulo
4, Nmain cannot be -1. Since Res=U^2 modulo 4, 1+Res cannot be -1 either.
Consequently

    Nmain=1, Res=0, Nk=epsilon, Nt=nu,
    epsilon,nu in {-1,1}, epsilon nu=1.             (1)

The system (S) is the special case epsilon=nu=1.

Initially X>=0, whereas Y,k,c,a,H,Delta are positive. If u=0 then X=E=0
and a=Y, so

    Nmain=H(2ac gamma+gamma^2 H-c^2).

This cannot be 1 because H=4Y+3>1. Thus u is nonzero, w>=1, and
X>=q>=16. The inherited weak-transport argument gives Cword=q-F-alpha>=0
and, using the exact mask bounds,

    q(q^2-1)<R<q^4-2, E>=q^4>R+2, a>R+2.           (2)

No deleted root is used here. If h<0, k=R+epsilon+hE<0, a contradiction;
hence h>=0. Also Y>=q^3>=4096 and 0<eta<k give c<k(Y+1).

## 3. A useful new consequence of the main norm: h is positive already

Let A0=a+2, so Delta=A0^2-1. Pell classification of the positive c and
absolute Dmain gives c=psi_A0(p), |Dmain|=chi_A0(p), p>=1. Here
psi_A0(1)=1, psi_A0(2)=2A0, psi_A0(3)=4A0^2-1.

Since c>1, p is not 1. If p=2 and Dmain>0, then

    Dmain-ac=H+4.

The defining congruence Dmain-ac=X modulo H would give X=4 modulo H.
But 16<=X<H, which is impossible. If p=2 and Dmain<0, direct expansion
gives 4(Dmain-ac)=-1 modulo H, hence 4X=-1 modulo H. This is impossible
because 0<4X+1<H. Therefore p>=3 and

    c>=4A0^2-1.

If k<=E, c<k(Y+1)<=E(Y+1)<=E(E+1)<4(E+2)^2-1<4A0^2-1,
again impossible. Thus k>E. In view of (2), h=0 would give
k=R+epsilon<E, so

    h>=1, k>R, k>E.                                (3)

This proof uses only the main norm and existing outer bounds. In particular
it does not invoke the first Pell norm before reconstructing its root.

## 4. Strict weight domination, for both weights

We prove

    A M^2>4(Dv^2+z0^2),
    d M^2 A>2Q(Dv^2+z0^2).                         (4)

The second follows from the first because Q>=2 and d=Q-1>=Q/2.

### Full weight

Using k>R and c<k(Y+1),

    c^2+R^2<k^2((Y+1)^2+1)<=5k^2Y^2,
    A>L0^2=k^2X^2Y^4>=256k^2Y^4>16(c^2+R^2).

For M=D+v^2, M^2>=4Dv^2, M^2>=D^2, and
z0^2=(c+RD)^2<=2D^2(c^2+R^2). Therefore

    4(Dv^2+z0^2)<=M^2[1+8(c^2+R^2)]<M^2 A.

### Lower weight

From A0<2E, c<2kY and L0=kEY we obtain

    A>A0^2 c^2/16,
    A>A0^4 Y^2/16>32 A0^4.                         (5)

The second inequality uses k>E, proved in section 3, and Y>=4096.
Because I^2=i^2c^4>c and Delta=A0^2-1,

    D<A0^2 I^2,
    z0=c+RD<2k A0^2 I^2.

For M=kI^2+T^2, M>=kI^2 and M^2>=4kI^2T^2. Since k>R>3q>=48,
the first inequality in (5) gives A M^2>8Dv^2 (also immediate if T=0).
The second gives A M^2>8z0^2. Adding those two strict inequalities and
dividing by two proves the first inequality of (4).

Consequently, for every integer t,

    C=d t^2+d M^2 A-(QW-1)>d t^2+QW+1>0.           (6)

All these inequalities were established before any root restoration.

## 5. The new exceptional-case exclusions

### Excluding t=0

At t=0 the resultant is exactly

    Res=(C^2-D Broot^2)^2.

But D Broot^2=4Q^2 Dv^2 z0^2<=Q^2W^2, while (6) gives C>QW+1.
Thus Res>0, contradicting (1). Hence t is nonzero.

### Excluding T=0

First note the uniform bound

    2<z0<Q-1.                                     (7)

Indeed z0=c+RD>2 and

    Q-z0=(Delta-R)D-Delta-c
         >=D-Delta-c
         =1+Delta(i^2c^4-1)-c>1.

Here Delta>R, |i|>=1 and c>=2. If T=0, then v=Broot=0 and Res=0
forces C^2=4d^2t^2M^2A. Since t,d,M are nonzero,

    tau=C/(2dtM)

is rational with tau^2=A in Z, so tau is an integer. Put y=t-M tau.
The defining equation for C gives d y^2=e=Qz0^2-1. Thus

    (Q-1)(y^2-z0^2)=z0^2-1>0.

Integrality implies |y|>=z0+1, so

    z0^2-1>=(Q-1)(2z0+1)>z0(2z0+1)>z0^2-1,

using (7), a contradiction. Therefore T, v and Broot are nonzero.

The proof has now established every denominator needed below, including the
ones absent from the original positive-variable argument.

## 6. Exact reconstruction and soundness

Define proof-only rational quantities

    f=-U/(2C Broot),
    tau=(C+Broot f)/(2dtM),
    y=t-M tau.

Res=0 gives f^2=D. The definition of U then gives
(C+Broot f)^2=4d^2t^2M^2 A, hence tau^2=A. A rational number whose
square is an integer is an integer (reduce its fraction to lowest terms).
Therefore f,tau,y are integers, and direct expansion gives

    d y^2=e-Broot f=Q(vf-z0)^2-1.

Since f^2=D, vf-z0=c(Tf-1)-Rf^2 is exactly the source auxiliary V.
We have reconstructed all three normalized equations

    tau^2-L0(L0+k)=1,
    f^2-Delta i^2c^4=1,
    QV^2-(Q-1)y^2=1,

without a sign assumption on their roots. Together with (1), these are
precisely a solution of the normalized source product in package 14's domain:
seven positive coordinates, i odd signed, w square, and f,h,T,tau,y,gamma
unrestricted. The imported signed-domain theorem therefore decodes a blank
halting K215 run. This invocation occurs only after reconstructing every
source equation; it is not used to justify reconstruction denominators.

## 7. Completeness and conversion to 27 unrestricted integers

The source canonical witness can be chosen with i positive odd and w a
positive square: take strong Pell index m=cR and use odd five-power tableau
dimensions, exactly as package 14 proves. This remains valid for T4 because
d=5^18 and the padded width/height are odd powers of five. Choose an integer
r with i=2r+1, and an integer u with u^2=w. For either weight put
t=M tau+y. All forward algebraic identities give Res=0, and the unchanged
outer factors are 1. Thus every blank halt yields a solution of (P) and (S).

For each of the seven positive coordinates x substitute three separate
unrestricted variables by

    x=P(a_x,b_x,c_x)=a_x^2+a_x+b_x^2+c_x^2+1.        (8)

This is always positive, and represents every positive integer: Legendre's
three-square theorem represents 4x-3 (positive and 1 modulo 4) as exactly
one odd and two even squares. Expanding those squares gives (8).
There are 7*3+6=27 unrestricted unknowns. All operations are polynomial
with integer coefficients. The finite coefficient recipe is independent
of whether K215 halts. Composition with K215's syntactic-refutation
calibration proves in ZFC that absence of integer solutions is equivalent
to Con(ZFC).

## 8. Exact operation and degree counts

Package 09's full/lower-weight products cost 84/85 operations. Each of
seven positivity substitutions costs 7, odd i costs 2, and square w costs
1. Hence the new products cost 136/137. Every binary +,-,* is charged,
including multiplication by fixed numerals. Fixed coefficient ports and
register reuse are free. The four-equation circuits omit six finalizer
gates and cost 130/131. The scripts check all gates and all ports are live.

| Weight | Unknowns | Equations | Exact degree | Ops | Multiplications |
|---|---:|---:|---:|---:|---:|
| Full | 27 Z | 1 | 1116 | 136 | 72 |
| Lower | 27 Z | 1 | 1004 | 137 | 73 |
| Full | 27 Z | 4 | 1064 maximum | 130 | 69 |
| Lower | 27 Z | 4 | 952 maximum | 131 | 70 |

For an exact degree proof, give weight 2 to the seven positive source
coordinates and w, and weight 1 to i,h,T,gamma,t. The relevant weights are

| Expression | Weighted degree |
|---|---:|
| q,X,Y,E,k,c,a,Delta,R | 2,4,8,12,2,10,12,24,8 |
| Nmain,Nk,Nt | 35,13,4 |
| A,I,D,Q,v,z0,e | 44,21,66,90,11,74,238 |
| M_full, M_low | 66,44 |
| C_full,U_full,Res_full | 266,532,1064 |
| C_low,U_low,Res_low | 238,476,952 |

For the lower weight, C has the unique leading term -e_top, U has the
unique leading term C_top^2, and Res has the unique leading term U_top^2;
the competing final norm term has degree 892. The product consequently
has degree 952+35+13+4=1004. The full weight has C dominated by dM^2A,
and the analogous product degree is 1064+35+13+4=1116. These leading
terms are nonzero. In particular Nmain's leader is
8 gamma a_top^2 c_top, Nk's is -h E_top, and Nt's is
w(q_top-F_top-alpha_top)-z_top q_top. The latter contains -z_top q_top
uniquely in z_top. No product of these nonzero forms vanishes.

The top homogeneous substitutions in (8), i=2r+1, and w=u^2 preserve
nonvanishing: set the second and third variables of each positivity block
to zero, leaving an injective monomial substitution into distinct square
variables, plus the nonzero scalar substitution i->2r. Therefore these
are exact degrees of the literal integer polynomials for every beta>0,
not just upper bounds at generic coefficient choices.

## 9. Reproduction and limits of the checks

Run `python3 build_integer27.py` (also works with `python3 -O`). It reads the
two exact vendored upstream circuits, emits the four new JSON DAGs, checks
96 signed assignments against a separately written formula for each weight,
checks 144 isolated signed root components, and records two modular line
degree diagnostics for each packet. There are also 6,786 finite evaluations
of the gap obstruction inequality. These corroborate algebra and counts;
the universal inequalities and semantic proof are sections 2-7 above.

The checks neither produce an accepting K215 run nor verify the inherited
universal compiler, the K215 calibration, or any ZFC proof object. The degree
diagnostics are supplementary; section 8 supplies the exact symbolic proof.

## Further questions

1. Can the signed root elimination be done with a degree below 1004 while
   retaining 27 unrestricted unknowns and a comparable circuit?
2. Can the initial main-norm bound p>=3 simplify other signed-domain proofs?
3. Can another indispensable positive port be replaced by a canonically
   surjective square/odd witness, without adding exceptional zero solutions?
4. Formalize the signed amalgamation and coefficient-interface transfer in
   Lean/Rocq before treating these arithmetic results as formal artifacts.
