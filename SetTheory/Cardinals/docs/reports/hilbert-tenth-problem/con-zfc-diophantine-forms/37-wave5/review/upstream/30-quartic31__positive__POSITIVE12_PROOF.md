# A smaller twelve-positive-variable synthesis

## Result and logical scope

The three-equation circuit `positive12_system.json` has twelve strictly positive
supplied variables, 107 charged binary arithmetic operations (66 multiplications,
41 additions/subtractions), and residual degrees 7, 2, 1072. Its single-equation
product `positive12_product.json` has 111 operations (68 multiplications,
43 additions/subtractions) and exact total degree 1081.

This combines package 20's main-root/inner-root merger with package 21's congruence
carrier and scalar norm factorization, and adds a smaller separating weight and
a trace/product quadratic-remainder evaluator. It is strictly smaller in both
operation count and degree than the wave-3 12-variable degree winner
(20: degree 1145, 123 operations) and operation winner (21: degree 1353,
116 operations). It also improves the previous local twelve-variable form
(degree 1257, 139 operations). It is not a variable-count improvement and is
not claimed globally optimal. Package 18's explicit nine-variable construction
remains a separate, extremely high-degree choice.

The four fixed coefficients are the complete materialized compact Wang943 tuple
from package 19: B=2^(5^10), beta=B-1, K0=K, MC=MC, MF=MF_source. The last is the
shifted mask, not MF_native. The local `COEFFICIENT_BINDING.json` supplies every
payload hash and a finite recipe/source; no coefficient is unspecified and no
individual port is mixed with another compiler. All other displayed registers
below are computed expressions, not quantified variables.

The inherited compiler and literal K215 calibration imply, by ordinary
mathematics formalizable in ZFC,

    ZFC proves: (no positive solution) iff Con(ZFC).

This is an equivalence, not a proof of consistency or a new end-to-end
proof-assistant formalization. The finite checker below tests only the arithmetic
identities, counts, leading degrees, payloads and synthetic radical witnesses,
not the inherited unbounded compiler/calibration theorem.

## 1. Definition

The twelve supplied positive integers are

    J,F,alpha,z,h,i,T,s,w,eta,zeta,t.

Retain the common interface:

    q=beta*J+1, Cw=q-F-alpha, X=wq, Y=sq^3, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y, H=4a+3,
    Delta=a^2+H=(a+2)^2-1,
    ell=E*kY, A=1+ell*(ell+k), G=1+Delta*c^2, b0=X+a*c,
    R=((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J,
    Nk=k-hE-R,
    Nt=(K0+w)*Cw+q-F-z*(q-1).

Define

    I=i*c^2, D=1+Delta*I^2, Q=Delta*(D-1)=(Delta*I)^2,
    d=Q-1, v=c*T, b=c+R*D,
    P=Q*D*v^2, U=Q*b^2, e=P+U-1, Baux=2*Q*v*b,
    M=k*(I^2+T^2), L=H*M+1, W=b0+H*t.

For a formal indeterminate x put

    C(x)=d*(x^2+M^2*A)-e,
    F(x)=[C(x)^2+D*Baux^2-4*d^2*x^2*M^2*A]^2
          -4*C(x)^2*D*Baux^2.

Write F_H(z)=H^8 F(z/H). The polynomial being enforced is

    N=F_H(W-L*sqrt(G))*F_H(W+L*sqrt(G)).

The radical notation is only a compact definition of an integer polynomial;
the following division-free scalar formula is its complete evaluator:

    n=(H*M)^2*A, dn=d*n,
    HP=H^2*P, HU=H^2*U, He=HP+HU-H^2=H^2*e,
    j=4*HP*HU=H^4*D*Baux^2,
    Trace=2*d*(W^2+L^2*G),
    Knorm=d^2*(W^2-L^2*G)^2,
    AA=2*(dn+He), constant=(dn-He)^2-j,
    at=Trace-AA, bt=constant-Knorm, coef=16*dn*j,
    vr=at*(at*Trace+2*bt)-coef,
    ur=bt^2-at^2*Knorm,
    N=ur^2+Trace*ur*vr+Knorm*vr^2.

The system and product are

    Nk=1, Nt=1, N=0;
    P12=Nk*Nt*(1+N)-1=0.

Each multiplication by 2,4,16 and every other binary operation is charged in
the emitted JSON. Scalar comparison is free in the system ledger.

## 2. Why the evaluator is exactly the intended norm

The identity

    (C^2+j-K)^2-4*j*C^2=(C^2-K-j)^2-4*K*j

holds in any commutative ring. With z=H*x it rewrites F_H(z) as

    [ (d*z^2)^2-AA*(d*z^2)+constant ]^2-coef*(d*z^2).

For z=W+/-L*sqrt(G), put x_+/-=d*z^2. Their sum and product are exactly
Trace and Knorm. Modulo x^2-Trace*x+Knorm, the expression x^2-AA*x+constant
is at*x+bt. Squaring and subtracting coef*x leaves ur+vr*x. Its norm is
ur^2+Trace*ur*vr+Knorm*vr^2, proving the formula uniformly, including square,
zero or coincident quadratic specializations. There is no black-box resultant,
nonzero-discriminant assumption or extra witness.

## 3. Product units and the bounds available before root recovery

Set x0=d*(W^2+L^2*G). Then Trace=2*x0 and

    Knorm=x0^2-4*d^2*W^2*L^2*G.

Consequently N is congruent to (ur+x0*vr)^2 modulo 4. Thus 1+N cannot be
-1. At a positive root of P12, each of its three integer factors is a unit,
so N=0 and Nk=Nt=epsilon for a common epsilon in {1,-1}.

The inherited weak transport/mask bootstrap, which permits both signs and the
boundary Cw=0, gives

    Cw>=0, q>=16, X>=q, Y>=q^3, E=XY,
    3q<R<q^4-2, k=R+epsilon+hE>E.

It follows without using any eliminated roots that

    kY<c<2kY, a+2<2E, D<(a+2)^2*I^2,
    c<I^2, R>1, Y^2>20R, kY>8E.

Every denominator used below is nonzero: H,M,d,Baux are positive; Q>1,
D>1 and A>1. The bounds come from the whole selected coefficient tuple's
common-interface theorem, not merely from residue tests of its four ports.

## 4. The smaller separating weight

Put Aparam=a+2. First,

    sqrt(G)>(a+1)c,
    sqrt(A)<ell+k.

Since c>kY and a=E+Y,

    sqrt(G)-sqrt(A)>k*(Y^2+Y-1)>kY^2.

Also sqrt(A)>ell=EkY>kY^2, because X>1 and E=XY.

The new choice M=k(I^2+T^2) bounds both kinds of auxiliary terms cheaply.
Using I^2+T^2>=2IT and kY>8E,

    2*v*sqrt(D)<8*k*E*Y*I*T < (1/2)*M*k*Y^2.

Further c<I^2, D<4E^2 I^2 and RE^2>1 imply

    b=c+RD<5RE^2 I^2.

Since k>E and Y^2>20R,

    2b<10RE^2 I^2 < (1/2)*M*k*Y^2.

Therefore

    2*(v*sqrt(D)+b)<M*k*Y^2
        <min(M*sqrt(A), M*(sqrt(G)-sqrt(A))).             (1)

This sharpens both separation roles at once. In particular, with
P0=Dv^2+b^2 and e=QP0-1,

    M^2*A>4*(v*sqrt(D)+b)^2>4P0,
    d*M^2*A>2Q*P0,

because d=Q-1>=Q/2. Consequently for every real x,

    C(x)>Q*P0+1>Baux*sqrt(D)>0.                          (2)

No recovered square root, rationality, sign or integer quotient is used in
these estimates. They are weaker in one numerical constant than package 20's
old d M^2 A>4QP0 bound, but (2) is precisely what reconstruction requires.

## 5. All complex roots and exclusion of spurious branches

The elementary factorization of F gives the complete root description

    x=M*tau+y,
    tau^2=A, f^2=D,
    d*y^2=e-Baux*f=Q*(v*f-b)^2-1.                        (3)

Indeed, factor F first using f^2=D and then using tau^2=A:

    [C(x)+Baux*f]^2=4*d^2*x^2*M^2*A,
    C(x)+Baux*f=2*d*x*M*tau.

Expanding the last equality gives (3), and conversely (3) gives F(x)=0.
Both factorizations are valid over the complex numbers without dividing.
The two f roots are real. For either of them and any complex y satisfying
(3), the absolute-value estimate gives

    |y|<2*(v*sqrt(D)+b).

For example d|y|^2=|Q(vf-b)^2-1|<Q(v sqrt(D)+b)^2 and Q/d<=2.
The strict inequality also covers a negative right side: its absolute value
is at most 1, while Q(v sqrt(D)+b)^2>1.

By (1), every complex root x of F obeys

    |x|<=M*sqrt(A)+|y|<M*sqrt(G).                       (4)

Moreover x=0 is not a root: (2) gives
F(0)=[C(0)^2-D*Baux^2]^2>0. This will justify the rational-recovery
formula's denominator rather than silently discarding a zero branch.

## 6. Recover the main root and its congruence

If N=0, choose bmain=+sqrt(G) or -sqrt(G) with
F_H(W-L*bmain)=0 and put x=(W-L*bmain)/H. Thus F(x)=0.

If G is not an integer square, its two roots are irrational quadratic
conjugates, so both F_H(W-L*sqrt(G)) and F_H(W+L*sqrt(G)) vanish.
Their associated x roots have distance 2L sqrt(G)/H. By (4) the distance
is strictly less than 2M sqrt(G), contradicting L=HM+1. Thus G is a square
and bmain is an integer; x is rational.

The chosen bmain cannot be negative. Indeed W=b0+Ht>0, but then

    W=L*bmain+H*x < -L*sqrt(G)+HM*sqrt(G)<0

by (4). Therefore bmain>0. No unsupported absolute-value replacement of
an affine main-root expression has occurred.

## 7. Recover the other roots and every denominator

For the rational real x just obtained, (2) and x!=0 justify

    Ux=C(x)^2+D*Baux^2-4*d^2*x^2*M^2*A,
    f=-Ux/(2*C(x)*Baux),
    tau=(C(x)+Baux*f)/(2*d*x*M),
    y=x-M*tau.

The equation F(x)=0 gives f^2=D. The squared identity in Section 5 gives
tau^2=A. These rational roots of integer squares are integers. Expansion
restores (3), so V=vf-b is an integer and

    Q*V^2-(Q-1)*y^2=1.

Here Q=S^2 with the integer S=Delta*I>=2. The rational auxiliary Pell
saturation lemma below makes y an integer. Hence x=M*tau+y is integral.
As W=b0+Ht=L*bmain+Hx and L=1+HM, reduction modulo H gives
bmain=b0 modulo H. Therefore gamma=(bmain-b0)/H is an integer.

In fact gamma>0 without a signed-main-root extension: sqrt(Delta)>a+1,
bmain>0 and bmain^2=1+Delta c^2 give bmain>(a+1)c. Also
c>k>E>X, so bmain-ac-X>c-X>0.

### Rational auxiliary Pell saturation

If S>=2 and V are integers and rational y satisfies
S^2 V^2-(S^2-1)y^2=1, write S^2-1=d0*b0^2 with squarefree d0>1.
The rational z=b0*y is integral because a reduced denominator squared
would divide squarefree d0. Both (S,b0) and (|SV|,|z|) are nontrivial
positive integer-coordinate Pell solutions for d0. Write them as indices
m,n in the powers of the fundamental integer-coordinate Pell unit.
For its coordinates chi_j,psi_j, the identities modulo chi_m give
chi_(j+2m)=-chi_j and chi_(2m-j)=-chi_j. Reduce n modulo 2m and reflect
into 0<=r<=m. Since 1<=chi_r<chi_m for r<m, divisibility chi_m|chi_n
forces n to be an odd multiple of m. The addition formulas then imply
psi_m|psi_n. Thus b0 divides |z|, and y is integral. This uses the ordinary
integer Pell group, not the possibly larger half-integral unit group.

## 8. Soundness and direct completeness

We have restored

    tau^2-ell*(ell+k)=1,
    (X+ac+gamma H)^2-Delta*c^2=1,
    f^2-Delta*i^2*c^4=1,
    Q*[c*(T*f-1)-R*f^2]^2-(Q-1)*y^2=1,
    Nk=Nt=epsilon.

The identity vf-b=c(Tf-1)-Rf^2 uses f^2=D. Gamma is positive; tau and y
can be replaced by their positive absolute values. If f<0, change f and T
simultaneously to their negatives, preserving Tf and every relevant equation.
The signed-quotient extension of the normalized blank interface allows this
signed T and common weak unit sign. It forces epsilon=+1 and recovers the
blank K215 computation, exactly as package 20's inherited package-09 theorem.
The mask/decoder does not depend on the harmless auxiliary sign choices.

Conversely start with any canonical positive normalized blank-compiler witness.
Keep all eleven retained coordinates and set

    t=gamma+M*bmain+M*tau+y>0.

Then W=L*bmain+H(M*tau+y), so its corresponding factor F_H(W-L*bmain)
vanishes. Hence N=0 and Nk=Nt=1. This proves completeness directly,
without changing i, choosing a new Pell index or imposing a new divisibility
restriction. It proves equivalence in existence, not a bijection of witnesses.

## 9. Exact degrees

Fixed coefficients have degree zero. The unchanged degrees are
c=5,a=H=6,Delta=12,R=4,ell=11,A=G=22,I=11,D=34,Q=d=46,
v=6,b=38,P=92,U=e=122. Our new degrees are

    M=23, L=29, W=11, n=80, dn=126,
    HP=104, HU=He=134, j=238,
    Trace=126, Knorm=252, AA=134, constant=268,
    at=134, bt=268, coef=364, vr=402, ur=536.

He has the nonzero highest form H_top^2 U_top. Because deg(He)>deg(dn),
constant and bt have top form He_top^2; because 536>520, ur has top
form He_top^4. In N the other two term degrees are at most 1064 and 1056,
strictly below deg(ur^2)=1072. Thus

    N_top=He_top^8=H_top^16*U_top^8

is nonzero, proving exact degree 1072 without a generic-specialization claim.
The nonzero Nk,Nt leading forms add 7+2, proving exact degree 1081 for P12.
All fixed positive beta slices have these degrees. The checker supplements
this proof with two independent finite-field univariate degree tests.

## 10. Provenance and verification boundary

`SOURCE_PINS.json` records the immutable repository pin
`ae3007ca4467011e0e051c84acb4a1dd13971b0e`, exact relevant blob IDs and local
SHA-256 hashes. The new proof/emitter/checker are locally authored; no received
program is executed, imported, installed or used to mutate the public repository.
The new-owned checker evaluates received circuit JSON only as inert arithmetic
records and verifies the new circuit against a separately implemented
multiquadratic conjugate product. Synthetic kernel witnesses do not claim to
encode an accepting ZFC-refutation computation.

