# A smaller twelve-variable norm for Con(ZFC)

This is an ordinary algebraic and number-theoretic reduction, formalizable in
ZFC. It combines the rational-root recovery argument of package 20 with the
scalar-norm circuit of package 21. It assumes the same certified blank K215
compiler interface, using one whole coefficient tuple. It is not a new
proof-assistant theorem and does not prove the consistency of ZFC.

The reviewed repository pin is
`ae3007ca4467011e0e051c84acb4a1dd13971b0e`. Source packages are below
`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/`.

## 1. Polynomial definitions

Supply precisely twelve strictly positive integers

    J,F,alpha,z,h,i,T,s,w,eta,zeta,r.

The four fixed ports are beta=B-1, K0, MC and shifted MF. They must be
instantiated together using one proved blank compiler tuple. Put

    q=beta J+1, Cw=q-F-alpha, X=wq, Y=sq^3, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y, H=4a+3,
    Delta=a^2+H=(a+2)^2-1,
    ell=E kY, A=1+ell(ell+k), G=1+Delta c^2,
    b0=X+ac,
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J,
    Nk=k-hE-R,
    Nt=(K0+w)Cw+(q-F)-z(q-1),
    I=i c^2, D=1+Delta I^2, Q=(Delta I)^2, d=Q-1,
    v=cT, b=c+RD, P=Q D v^2, U=Q b^2,
    e=P+U-1, Baux=2Qvb.

The new weight and carrier are

    M=(kI+T)^2, L=1+HM, S=b0+Hr.

For a formal indeterminate x, put

    C(x)=d(x^2+M^2 A)-e,
    F(x)=[C(x)^2 + D Baux^2 - 4d^2 x^2 M^2 A]^2
         -4D Baux^2 C(x)^2.

Let F_H(z)=H^8 F(z/H), an integer polynomial, and define

    N=F_H(S-L sqrt(G)) F_H(S+L sqrt(G)).

This is a polynomial in the twelve supplied coordinates. The radicals are
only a convenient identity defining the norm; they introduce no quantified
unknown or nonpolynomial operation. Its explicit +,-,* circuit is supplied.

The equation is

    Nk Nt (1+N)-1=0.                              (P)

An equivalent system is Nk=1, Nt=1, N=0. For counting system operations the
last equation is emitted directly as equality of the final two norm terms.
Its size is 12 unknowns, 3 equations, degree 1072, 111 operations. The single
equation has exact degree 1081 and 116 operations. The sum of squares has
degree 2144 and 119 operations.

## 2. Inherited bootstrap, before root recovery

The authenticated blank compiler's weak transport/index bootstrap applies
when Nk=Nt=epsilon, epsilon in {-1,+1}, and gives

    q>=16, X>=16, Y>=4096,
    0<R<q^4-2, E>=q^4>R+2,
    k=R+epsilon+hE>E,
    kY<c<k(Y+1)<2kY.

In particular k>R and k>E>=16Y. Put A0=a+2; then A0<2E, since
E>=16Y and Y>=4096. These facts use neither the main/root equations nor any
positivity of a root being reconstructed.

The remaining proof is valid with exactly this bootstrap. At a system
solution it holds with epsilon=1. At a product solution the parity argument
in Section 7 gives N=0 and the same common epsilon before using any root.

## 3. A stronger inner bound

Let P0=Dv^2+b^2, so QP0=e+1, and let M0=kI^2+T^2.
The elementary estimates

    A>A0^2 c^2/16, A>64 A0^4,
    D<A0^2 I^2, b<2k A0^2 I^2

follow as follows. Since ell=EkY and A0c<4EkY, the first inequality follows
from A>ell^2. Since k>E and Y>=4096, ell>E^2Y and A>E^4Y^2>64 A0^4.
Finally c<I^2, R<k, and k A0^2>1 give the displayed bound on b.

Now M0^2>=4kI^2T^2 and M0^2>=k^2 I^4. Hence

    A M0^2 > (k/4) A0^2 c^2 I^2 T^2 >16 Dv^2,
    A M0^2 >64 A0^4 k^2 I^4 >16 b^2.

The first uses k>E>=16^4>64. Summing the two strict inequalities gives
A M0^2>8P0. Since d=Q-1>=Q/2, we obtain

    d A M0^2>4QP0.

Moreover M=(kI+T)^2>=kI^2+T^2=M0 for k>=1. Thus

    d A M^2>4QP0.                                (1)

This strengthens package 20's weight estimate, and removes its extra
doubling of M0. All terms here are positive.

## 4. Root bounds and the outer separation

The eight complex roots of F, with multiplicity, are the coherent branches

    x=M tau+y, tau^2=A, f^2=D,
    d y^2=e-Baux f=Q(vf-b)^2-1.                   (2)

This follows by factoring F first with f^2=D and then with tau^2=A.
No denominator or nonzero assumption is used in this factorization.

Every branch satisfies |y|<2(v sqrt(D)+b). Indeed

    |y|^2 <= [Q(v sqrt(D)+b)^2+1]/(Q-1)
             <4(v sqrt(D)+b)^2,

because Q>1, Q>=2, and v sqrt(D)+b>1. This bound includes imaginary
branches. A stronger bound from (1) is |y|<M sqrt(A):

    |y|^2 <= (2QP0+1)/d <4QP0/d <A M^2.

We next establish the gap needed for the unweighted carrier S=b0+Hr.
Since Delta>(a+1)^2 and c>kY,

    sqrt(G)>(a+1)c>(E+Y+1)kY.

Also k>2 and (ell+k/2)^2-A=k^2/4-1>0, so sqrt(A)<ell+k/2. Therefore

    sqrt(G)-sqrt(A)>k(Y^2+Y-1/2)>kY^2.            (3)

This sharper gap proof was suggested in the independent audit of the new
construction. It relies only on the elementary pre-recovery bounds.

Since D<A0^2 I^2, v=cT, A0<2E, c<2kY, E<k, and R<k,

    v sqrt(D)<4k^2 Y I T,
    b=c+RD<2kY+4k^3 I^2<5k^3 I^2.

The last step uses k>16Y, I>=1. Consequently every auxiliary branch obeys

    |y|<8k^2 Y I T+10k^3 I^2.                    (4)

But M=k^2 I^2+2kIT+T^2, so (3) gives

    M(sqrt(G)-sqrt(A))
      > k^3 Y^2 I^2+2k^2 Y^2 I T
      >10k^3 I^2+8k^2 Y I T,                     (5)

where Y>=4096 is much stronger than needed. Combining (4) and (5), every
root x of F satisfies

    |x|<=M sqrt(A)+|y|<M sqrt(G)<L sqrt(G)/H.     (6)

Suppose N=0. At least one of F_H(S-L sqrt(G)) and F_H(S+L sqrt(G))
vanishes. If G is not a square, write F_H(S-L sqrt(G))=E0+E1 sqrt(G)
with integer E0,E1. Its norm zero forces E0=E1=0, since otherwise G
would be a rational square, hence an integer square. Both factors would
then vanish. Their corresponding roots of F differ by 2L sqrt(G)/H,
contradicting (6) and the triangle inequality. Therefore G is an integer
square, and we obtain an integer u with u^2=G and rational

    x=(S-Lu)/H, F(x)=0.

This root u must be positive. If u<0, then S=L u+H x<0 by (6), whereas
S=b0+Hr>0. Thus u=+sqrt(G).

## 5. Recover the three inner integral roots

For real x, (1) and Baux sqrt(D)<=QP0 give

    C(x)>3QP0+1>Baux sqrt(D)>0.

Also F(0)=[C(0)^2-D Baux^2]^2>0, so the recovered rational x is nonzero.
Put

    V(x)=C(x)^2+D Baux^2-4d^2 x^2 M^2 A,
    f=-V(x)/(2C(x)Baux),
    tau=(C(x)+Baux f)/(2dxM), y=x-M tau.

These are rational. From F(x)=0 one obtains f^2=D, so f is an integer.
Then (C+Baux f)^2=4d^2 x^2 M^2 A gives tau^2=A, so tau is an integer.
The remaining rational y satisfies

    Q(vf-b)^2-(Q-1)y^2=1.                        (7)

The rational auxiliary Pell saturation lemma of packages 20/21 applies:
if m>=2 and V are integers and rational y satisfies
m^2 V^2-(m^2-1)y^2=1, then y is integral. Here m=Delta I and V=vf-b.
For completeness: writing m^2-1=d0 b^2 with squarefree d0 makes by
integral by valuations; classification of integer Pell units, together
with chi_j|chi_l only when l is an odd multiple of j, then yields b|by.
Thus y is integral and x=M tau+y is integral.

Since L=1+HM, reducing S=L u+Hx modulo H gives u=b0 mod H. Hence

    gamma=(u-b0)/H

is integral and the main Pell equation and congruence are restored.
The restored first Pell equation forces k=2 psi_(2XY^2+1)(n), n>=1.
Because k>E>=16^4>48, n is not 1 and k>=4(2XY^2+1)>X. Thus c>k>X.
Since u>0 and Delta>(a+1)^2, u>(a+1)c, and so
gamma H=u-ac-X>c-X>0. This is exactly package 20's direct positivity
argument; no unproved signed-gamma theorem is needed.

Taking absolute values of tau and y is harmless. If f<0, change the signs
of both f and T. The inherited signed-quotient normalized compiler theorem
then applies, forces epsilon=+1, and recovers a blank K215 halting tableau.
The ordinary signed strong theorem could alternatively be used after
i_ordinary=Delta i. This is the same inherited soundness boundary as
package 20; no new universal-machine or compiler claim is made.

Conversely take a canonical positive normalized compiler witness, with
u=b0+H gamma, tau>0, y>0, f>0. Define

    r=gamma+M(u+tau)+y.

This is a positive integer and gives S=L u+H(M tau+y). The corresponding
factor of N vanishes. Nk=Nt=1 then gives (P). This proves equivalence with
the inherited blank compiler, and hence with syntactic ZFC inconsistency.

## 6. Explicit scalar-norm evaluator

The following evaluator is the optimized identity from package 21, with
the inner weight M separated from the outer weight L. All symbols are
polynomial abbreviations:

    n=(HM)^2 A, V0=S^2+L^2 G, V1=2SL,
    C0=d(V0+n)-H^2 e, C1=d V1,
    Kf=4d^2 n, Kc0=Kf V0, Kc1=Kf V1,
    Z=4H^4 P U,
    Cs0=C0^2+G C1^2, Cs1=2C0 C1,
    W0=Cs0-Kc0-Z, W1=Cs1-Kc1,
    N0=W0^2+G W1^2-4Z Kc0,
    N1=2W0 W1-4Z Kc1,
    N=N0^2-G N1^2.

The identity underlying the optimization is

    (C^2+K-Z)^2-4C^2 K=(C^2-K-Z)^2-4KZ.

It avoids multiplication of two arbitrary quadratic coefficient pairs.

## 7. Product finalizer and parity

V1 is even, C1 is even, Cs1 is divisible by 4, and Kc1 is divisible by 8.
Thus W1 is divisible by 4 and N1 is divisible by 8. Therefore

    N=N0^2 mod 64.

If Nk Nt(1+N)=1, all three factors are integer units. Since 1+N cannot be
-1 modulo 4, it is +1, so N=0 and Nk=Nt=epsilon with epsilon in {-1,+1}.
This supplies the exact weak-sign situation used above. In particular
no conclusion about consistency is assumed in extracting the unit signs.

## 8. Exact degrees and arithmetic cost

All fixed ports have degree zero and each supplied variable degree one.
The relevant degrees for the unweighted square construction are

    c=5, a=H=6, Delta=12, ell=11, A=G=22, I=11,
    D=34, Q=d=46, b=38, P=92, U=e=122,
    M=24, L=HM=30, S=11, n=V0=82, V1=41,
    C0=134, C1=87, Kc0=256, Kc1=215, Z=238,
    W0=268, W1=221, N0=536, N1=489.

The unique top-degree contribution to C0 is -H^2 e. It propagates through
the unique top-degree square at each later stage. Thus

    N_top=(H_top^2 e_top)^8,

and deg N=1072 exactly; the competing G N1^2 has degree only 1000.
Writing q0=beta J and k0=eta+zeta explicitly gives

    N_top=2^32 i^48 k0^96 w^80 s^176 q0^656(q0-F)^16.

This is nonzero for every beta>0. The product has degree 1072+7+2=1081.
For example the coefficient of

    J^677 h z i^48 eta^96 w^81 s^177

is +2^32 beta^677, uniformly nonzero. The squared norm is the unique
highest-degree term in the sum of squares, of degree 2144.

The complete emitted ledger charges every binary +,-,* including literal
numeral multiplication. Sharing and comparisons are free, consistently
with the repository convention. No supplied variable or gate is dead.

| Form | Variables | Equations | Exact degree | Operations |
|---|---:|---:|---:|---:|
| System, direct final comparison | 12 positive | 3 | 1072 | 111 |
| Product equation | 12 positive | 1 | 1081 | 116 |
| Sum of squares | 12 positive | 1 | 2144 | 119 |

The system compares N0^2=G N1^2 directly, avoiding the final subtraction.
The same normalization reduces package 21's 112-operation system to 111,
so this is a tie in normalized system operation count, with smaller degree.
The 116-operation product ties package 21's arithmetic cost while lowering
degree from 1353 to 1081. Its degree is below package 20's 1145 and it uses
seven fewer operations than that package's product. These are comparisons
within the inspected explicit twelve-variable family, not optimality
claims and not improvements over the nine-variable Jones specialization.

## 9. Simpler-proof variants

One may instead use S=L b0+Hr, keeping M=(kI+T)^2 and L=1+HM.
This adds one multiplication. It avoids the gap estimates (3)-(5).
Indeed the inner bound gives |x|<2M sqrt(A). Also sqrt(G)>sqrt(A) and
b0>sqrt(A). For the latter,

    a^2 k^2Y^2-A
      =k^2[EY(2Y^2-1)+Y^4]-1>0,

and b0>akY. Thus

    (S+L sqrt(G))/H >L(b0+sqrt(G))/H>2M sqrt(A),

so that branch cannot be a root of F. If G were nonsquare, norm zero
would force both branches to vanish, a contradiction. The same argument
excludes the negative main root. The recovered main congruence remains
valid since L=1 mod H; completeness uses r=L gamma+M tau+y.

This variant has degree 1081 and 117 operations (112 for the system).
Using M0=kI^2+T^2 in this weighted-carrier variant adds one operation,
giving 118/113. The degrees are unchanged. Both are delivered as explicit
circuits for the reader who prefers the shorter outer proof.

## 10. Verification boundary

`build_hybrid12.py` emits all nine circuits. For each of the three variants,
it checks 24 exact signed assignments against an independent eight-component
conjugate-product evaluator, the finalizer and parity identities, all gate
dependencies, liveness, and two nonzero leading evaluations modulo primes.
These checks audit algebra and accounting. The unbounded proofs above
establish the number-theoretic reduction; the inherited compiler and K215
consistency calibration are explicitly dependencies. No accepting K215 run
or full astronomical solution is constructed, and no proof-assistant build
is claimed.
