# Twelve positive unknowns by amalgamating the main Pell root

## Current complete coefficient instantiation

Every main JSON packet and its builder in this release selects the complete
`T4-4094-binary-copy-zero-padding-5pow11` tuple from
`../coefficients/COEFFICIENTS.json`, with tuple SHA-256
`726ac1d0ae1957f75f71966a65c8730403998a1f719e927f6894babea12cf938`.
The aliases are Bm1/beta -> beta, Kconstant/K0 -> K, MC -> MC, and
MF -> MF_source. MF_source is the shifted port MF_native + B - 1.
The whole-tuple transfer proof is `../coefficients/COEFFICIENT_PROOF.md`;
it preserves the native interface, rank congruence, parity, positive odd i,
and positive square w required by the signed and low-degree reductions.
Here B = 2^(5^11). References below to original06/blank67 and d = 5^67
describe the historical source proof, not the numerical instance selected
by this release. Its same completeness argument applies through the
proved transfer with odd d = 5^11 and odd five-power tableau area.
No individual coefficient is mixed with another compiler's tuple.
The vendored source evidence remains unchanged.

## Result and scope

This construction extends package 09 of ProveIt's wave-2 report, inspected at
`f0ae4e0991ca44a7bb4e5671d42e33d775e48035`. Keep its four symbolic coefficient
ports, including its shifted MF convention. The algebra is unchanged;
the complete numerical instance is replaced by the proved tuple above. In the notation below Bm1=B−1 is itself the fixed port.

The result is an explicitly emitted polynomial in **12 strictly positive
unknowns**, with exact degree **1145** and a **123-operation** straight-line
circuit (81 multiplications, 42 additions/subtractions). It represents the
same blank K215 halting condition as package 09. Consequently the inherited
formalizable reduction gives

    ZFC proves: (no positive solution of P12=0) iff Con(ZFC).

A three-equation system costs 119 operations, maximum degree 1136. Its
sum-of-squares polynomial costs 126 operations and has exact degree 2272.
All binary arithmetic operations, including multiplication by fixed
numerals, are counted. The abbreviations are polynomial expressions, not
additional unknowns. No claim of global minimality or kernel verification
is made.

The new substantive step is that the main Pell root, including its
congruence modulo H, can be combined with the three roots already combined
in package 09. A rational auxiliary Pell-root lemma closes the integrality
issue that a plain resultant calculation would otherwise leave open.

## 1. Explicit polynomial

The twelve supplied positive integers are

    J, F, alpha, z, h, i, T, s, w, eta, zeta, t.

Use the unchanged common interface

    q=Bm1 J+1, Cw=q−F−alpha, X=wq, Y=sq³, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y, H=4a+3, Delta=a²+H,
    R=((q−1)(q−F)+alpha)(q²−1)+(MC+q MF)J,
    Nk=k−hE−R,
    Nt=(Kconstant+w)Cw+q−F−z(q−1).

Define the inner root data

    Lfirst=E(kY), A=1+Lfirst(Lfirst+k), I=ic²,
    D=1+Delta I², Q=Delta(D−1)=(Delta I)², d=Q−1,
    v=cT, z0=c+RD, P=Dv²+z0², e=QP−1, Baux=2Qvz0,
    M0=kI²+T², M=2M0.

Define the outer weight and congruence carrier

    S=2M(Lfirst+k), L=HS+1,
    b0=X+ac, G=1+Delta c², W=Ht+Lb0.

The following finite expressions define the resultant without any
black-box resultant primitive. They are the even and odd parts in a
formal b with b²=G:

    Z0=W²+L²G, Z1=−2WL, n=H²M²A,
    C0=d(Z0+n)−H²e, C1=d Z1,
    q0=C0²+G C1², q1=2C0 C1,
    j=H⁴ D Baux², r=4d²n,
    U0=q0+j−r Z0, U1=q1−r Z1,
    Even=U0²+G U1²−4j q0,
    Odd=2U0 U1−4j q1,
    Res12=Even²−G Odd².

The requested single polynomial is

    P12=Nk Nt (1+Res12)−1.

The three-equation version is Nk=1, Nt=1, Res12=0. The alternative single
sum of squares is (Nk−1)²+(Nt−1)²+Res12².

## 2. Unit extraction and weak bounds

At a positive zero of P12 all three factors are integer units. For every
integer a, Delta=(a+2)²−1 is 0 or 3 modulo 4, so G=1+Delta c² is 0 or 1
modulo 4. A difference Even²−G Odd² is therefore never 2 modulo 4.
Consequently 1+Res12 cannot be −1, and

    Res12=0, Nk=Nt=epsilon, epsilon in {−1,+1}.

The same weak transport bootstrap used in package 09's product13 proof
applies before any root has been recovered. It gives

    Cw>=0, q>=16, 0<R<q⁴−2, E>=q⁴>R+2,
    X>=16, Y>=4096, R>3q, k=R+epsilon+hE>R.

In particular R,z0,v,Baux are positive, Q>=2, d>0, I>1, A>1.
The exceptional Cw=0 case is not discarded at this stage.

Here is the denominator bound for the chosen lower-degree weight, with
its proof recalled so this construction is not relying on an unstated
positivity assumption. Put Aparam=a+2. From the bounds above,

    k>E, c<2kY, Aparam<2E,
    Lfirst=kEY>Aparam c/4,
    Lfirst>E²Y>4 Aparam².

Hence

    A>Aparam² c²/16, A>16 Aparam⁴,
    D<Aparam² I², z0=c+RD<2k Aparam² I².

For the last inequality use R<k and c<I². Also

    M0²>=4k I² T², M0>=kI², k>R>3q>=48.

These imply separately A M0²>4Dv² and A M0²>4z0². Averaging gives
A M0²>2P; since d=Q−1>=Q/2,

    d A M0²>QP, and therefore d A M²>4QP.             (1)

No main-root equation, no sign of gamma, and no recovered auxiliary
integer is used in these inequalities.

## 3. The inner polynomial and its complete root description

For a scalar x define

    C(x)=d(x²+M²A)−e,
    U(x)=C(x)²+D Baux²−4d²x²M²A,
    F(x)=U(x)²−D(2C(x)Baux)².

For every real x, (1) and Baux sqrt(D)<=QP give

    C(x)>3QP+1>Baux sqrt(D)>0.                       (2)

Over the complex numbers the roots of F have the following elementary
description:

    x=M tau+y,
    tau²=A, f²=D,
    d y²=Q(vf−z0)²−1=e−Baux f.                      (3)

To verify this description without a primitive-element theorem, factor
F as U+2CBaux f over either choice f²=D. The resulting equation is

    (C+Baux f)²=4d²x²M²A.

Factoring once more with tau²=A gives
C+Baux f=2dxM tau, which is exactly the last equation of (3) after
putting y=x−M tau. Conversely these equations give F(x)=0. There are
no exclusions involving zero denominators in this factorization.

Every complex branch obeys a uniform bound. Even when y is imaginary,

    |y|² = |Q(vf−z0)²−1|/d
          <= (2QP+1)/d
          < 4QP/d
          < A M².

The inequality 2QP+1<4QP uses QP>1. Since
(Lfirst+k)²>A, it follows that

    |x| <= M sqrt(A)+|y| <2M sqrt(A)<S.              (4)

This bound is valid for every root of F, not only its real roots.

## 4. The outer norm recovers an integral main root

Let

    F_H(z)=H⁸ F(z/H).

Writing out F_H gives

    [ (d z²+H²(dM²A−e))²+H⁴D Baux²
       −4d² z²H²M²A ]²
    −4D H⁴Baux²[d z²+H²(dM²A−e)]².

The even/odd expressions in section 1 say exactly

    F_H(W−Lb)=Even+b Odd, when b²=G.

Thus Res12 is the product F_H(W−L sqrt(G)) F_H(W+L sqrt(G)).
At a zero at least one of these factors vanishes. Choose b=+sqrt(G)
or −sqrt(G) accordingly and put x=(W−Lb)/H; then F(x)=0.

Suppose G is not a square. The identity Even²=G Odd² then forces Even=Odd=0: otherwise
G=(Even/Odd)² would be a rational square and hence an integer square.
Thus the other factor is zero too. Both x=(W−Lb)/H and x'=(W+Lb)/H are roots of F, so (4) gives

    2L sqrt(G)/H=|x'−x|<=|x|+|x'|<2S.

But L=HS+1 and sqrt(G)>=1 give L sqrt(G)/H>S, a contradiction.
Therefore G is a square and b is an integer. Since W>0 and (4), the
negative choice b<0 would give W=Lb+Hx<−L sqrt(G)+HS<0. Thus b>0.
Now x is rational, but integrality of x is not yet assumed.

## 5. Rational recovery of all inner roots

The value x cannot be zero: F(0)=(C(0)²−D Baux²)²>0 by (2).
Both C and Baux are nonzero. Set

    f=−U(x)/(2C(x)Baux),
    tau=(C(x)+Baux f)/(2dxM),
    y=x−M tau.

These are rational numbers. The equation F(x)=0 gives f²=D, hence
f is an integer. The identity (C+Baux f)²=4d²x²M²A gives tau²=A,
hence tau is an integer. Expansion gives

    Q(vf−z0)²−(Q−1)y²=1.                            (5)

The remaining rational y is an integer by the lemma in section 6,
with the integer sqrt(Q)=Delta I and integer V=vf−z0. Therefore
x=M tau+y is an integer. Since W=Ht+Lb0 and W−Lb=Hx,

    H divides L(b−b0).

The exact identity L=HS+1 gives gcd(L,H)=1. Thus

    gamma=(b−b0)/H

is an integer, and the original main norm and congruence have been
restored. gamma is provisionally signed; this is deliberately not
silently treated as a positive witness.

## 6. Rational auxiliary Pell-root integrality

Lemma: If J0,V are integers with J0>=2, y is rational, and

    (J0 V)²−(J0²−1)y²=1,

then y is an integer.

Write J0²−1=d0 s0² with d0>1 squarefree and s0>0. The rational
z=s0 y satisfies d0 z²=(J0 V)²−1. If z has a reduced denominator m,
then m² divides the squarefree integer d0, so m=1. Thus z is integral.
The cases z=0 or V=0 are impossible. Choose the fundamental positive
solution u0+v0 sqrt(d0) of the integral Pell equation. Its powers give
all its positive integral solutions. For some m,n>=1,

    J0=x_m, s0=z_m, |J0 V|=x_n, |z|=z_n,
    x_r+z_r sqrt(d0)=(u0+v0 sqrt(d0))^r.

Modulo x_m, the multiplication formulas give

    x_{r+2m} == −x_r,  x_{2m−r} == −x_r   (mod x_m).

Indeed (u0+v0 sqrt(d0))^{2m} is −1 in the quadratic ring modulo x_m.
Reduce n modulo 2m, and then reflect to an index r in [0,m].
If r<m, then 1<=x_r<x_m, contradicting x_m|x_n. Hence
n is an odd multiple of m. The elementary identity
z_m|z_{lm} for every positive integer l now gives s0|z_n, so y=z/s0
is integral. This argument uses the integer Pell group, not the larger
ring of integers with possible half-integral coordinates.

An independent proof is in dependencies/RATIONAL_AUXILIARY_PELL_LEMMA.md.

## 7. Soundness and completeness of the compiler interface

At this point the recovered integers satisfy

    b=X+ac+gamma H, b²−Delta c²=1,
    tau²−Lfirst(Lfirst+k)=1,
    f²−Delta i²c⁴=1,
    Q[c(Tf−1)−Rf²]²−(Q−1)y²=1,
    Nk=Nt=epsilon.

The identity vf−z0=c(Tf−1)−Rf² uses f²=D. Roots tau,y are nonzero;
f is nonzero. The signs of f,tau,y,gamma have not been assumed.

We discharge gamma's provisional sign directly, without invoking any
signed-gamma extension. The restored first norm gives
k=2 psi_(2XY²+1)(n), n>=1, by the inherited first-Pell classification.
Since k>R>48, n cannot be 1; hence k>=4(2XY²+1)>X and c>k>X.
Since b>0 and Delta>(a+1)², the main norm gives b>(a+1)c. Therefore

    gamma H=b−ac−X>c−X>0.

Thus gamma is in fact positive. Replace tau,y by their positive absolute
values. If f<0, change f,T simultaneously to −f,−T. This gives exactly
the signed-quotient interface already proved sound in package 09,
ROOT_AMALGAMATION_PROOF.md, section 2: f is positive, T may be signed,
and all other retained source ports, including gamma, are positive.
That proof forces epsilon=1 and recovers the blank tableau.

A verbatim copy of the inherited package-09 root and signed-quotient
proof is supplied as dependencies/09_ROOT_AMALGAMATION_PROOF.md. Its two
underlying signed-quotient proof notes are also copied verbatim in
dependencies/, with pinned fetch provenance. This
argument does not require the ordinary strong rank theorem, a signed-gamma
extension, an odd-i restriction, or a square-w substitution.

Conversely, take a positive normalized package-09 solution with main root
b=b0+gamma H and roots f,tau,y. Define the positive integer

    t=L gamma+M tau+y.

Then W=Lb+H(M tau+y), so the factor F_H(W−Lb) vanishes. Hence Res12=0,
and Nk=Nt=1 gives P12=0. This proves the exact existential equivalence.

## 8. Exact degree certificate

Every supplied unknown has degree 1; fixed coefficient ports have degree
0. The unchanged base degrees are

    c=5, a=6, H=6, Delta=12, R=4, Lfirst=11,
    A=22, I=11, Q=46, D=34, v=6, z0=38, e=122.

The new degrees are

    M=23, S=34, L=40, b0=11, G=22, W=51.

There is an important cancellation: b0²−G is not degree 22, but

    b0²−G=X²+2Xac−Hc²−1,

of exact degree 16, with leading form −H_top c_top². Therefore

    Kpair=W²−L²G
         =L²(b0²−G)+2HtLb0+H²t²

has exact degree 96 and leading form −L_top² H_top c_top².

Write the cleared inner polynomial as

    F_H(z)=a8 z⁸+a6 z⁶+a4 z⁴+a2 z²+a0.

Direct inspection gives a8=d⁴ and

    degree(a_j)<=536−44j, j in {0,2,4,6,8}.

For example H²(dM²A−e) has degree 134, the quadratic-in-z² inner
bracket has coefficient degrees 92,180,268, and the final subtraction
has lower degree. The five bounds are respectively 184,272,360,448,536.

Put z_±=W±L sqrt(G). Their product Kpair has degree 96. For i>=j,
the two cross terms in the norm combine to

    a_i a_j Kpair^j (z_+^(i−j)+z_-^(i−j)).

The symmetric power has degree at most 51(i−j). Consequently each
combined term has degree at most

    1072+7 max(i,j)+min(i,j).

The unique maximum occurs at i=j=8, giving 1136. Its leading form is

    d_top⁸ (−L_top² H_top c_top²)⁸,

which is nonzero for every valid coefficient slice. Thus Res12 has
exact degree 1136, not merely the uncancelled pair-arithmetic bound.
Nk and Nt have exact degrees 7 and 2, so P12 has exact degree 1145.
The resultant square is uniquely highest in the sum of squares, whose
exact degree is 2272.

## 9. Reproducibility and verification boundary

Run `python build_root12.py`. It emits the complete binary-operation
circuits, rejects dead gates or unused ports, checks 100 signed integer
assignments against an independent quadratic-ring implementation,
checks 18 isolated nested-root/congruence fixtures, and verifies the
claimed degrees on two modular univariate specializations. The receipt
is ROOT12_CHECKS.json.

The finite tests supplement, but do not replace, the uniform degree and
number-theoretic proofs. No accepting K215 run, enormous full witness,
or instantiated astronomical coefficient is evaluated. This is an
ordinary mathematical reduction using inherited compiler and logical
endpoint lemmas, not a new proof-assistant certificate.
