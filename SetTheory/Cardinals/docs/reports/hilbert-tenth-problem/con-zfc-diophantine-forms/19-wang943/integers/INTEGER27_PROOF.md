# Twenty-seven unrestricted integers by a weighted three-root norm

## Result and interface

`integer27_weighted_root136_degree1116.json` is a literal equation in 27 unrestricted integers, of exact degree1116 and136 operations (72 multiplications,64 additions/subtractions). It combines the84-operation weighted-root circuit of package09 with package14's seven-positive-port, odd-i, square-w signed theorem. The proof is ordinary mathematics formalizable in ZFC, conditional on the same authentic fixed compiler/calibration theorems; it is not a new proof-assistant certificate or minimum claim.

The coherent original package06 quartet is the baseline backend; alternate whole-tuple bindings are specified separately. MF always means the shifted source mask, not its native unshifted value.

Use the same q,X,Y,E,k,c,a,H,Delta,R,L,N1,Nk,Nt as in `INTEGER28_PROOF.md`. Retain positive J,F,alpha,z,s,eta,zeta. Let h,T,gamma,t,r,u be arbitrary integers, and put i=2r+1,w=u². Introduce only computed abbreviations

    A=1+L(L+k), D=1+Delta i²c⁴, Q=(Delta i c²)²,
    d=Q-1, v=cT, b=c+RD, e=Q(Dv²+b²)-1,
    B=2Qvb, M=D+v²,
    C=d(t²+M²A)-e,
    U=C²+D B²-4d²t²M²A,
    Res=U²-D(2CB)².

The equation is

    N1 Nk Nt (1+Res)-1=0.                                      (1)

The emitted evaluator shares products as in package09 and does not separately compute B. The displayed formula is a mathematically identical expansion.

## 1. Outer signs and bootstrap

At a zero, all four integer factors are units. N1 cannot equal -1 because Delta is0 or3 modulo4. Also Res is a square modulo4, so 1+Res cannot equal -1. Hence N1=1, Res=0 and Nk=Nt=epsilon for epsilon in {-1,1}.

The retained main norm immediately excludes w=0: then X=0,a=Y,Dmain=ac+gamma H and reduction modulo H yields1=0, impossible H=4Y+3>1. Thus X>=q>=16. Weak transport gives C_word=q-F-alpha>=0, followed by the source bounds

    3q+1<R<q⁴-2, E>=q⁴>R+2, a>R+2.

Since k=R+epsilon+hE>0, signed h must satisfy h>=0. Consequently k>=R-1, and

    R<=k+1<2k, c<k(Y+1), Y>=q³>=4096.

This does not assume h>0, k>R, or k>E. No deleted first root has yet been restored.

## 2. Stronger domination, valid for signed T and t

Let Sgeom=Dv²+b². Since L=kXY²,

    A>k²X²Y⁴.

Using R<2k, c<k(Y+1), and Y>=1 gives

    c²+R²<k²[(Y+1)²+4]<=8k²Y².

As X>=16 and Y>=4096, we have

    A>16(c²+R²)+1.                                            (2)

The stronger stated constant follows directly from k²X²Y⁴>=256k²Y⁴ and16(c²+R²)<128k²Y², leaving much more than one of slack.

D>1, Q>2 and d>=Q/2. Moreover

    M²=(D+v²)²>=4Dv²,
    M²>=D²,
    b²=(c+RD)²<=2D²(c²+R²).

Therefore

    4Sgeom <= M²[1+8(c²+R²)] < A M².

Multiplying by d>=Q/2 gives the crucial strengthened domination

    d A M² > 2Q Sgeom = 2(e+1).                               (3)

In particular C=d t²+dAM²-e>e+2>0. These estimates depend on T only through v² and hence hold for signed or zero T.

## 3. Exclude t=0 before division

At t=0, Res=(C²-D B²)². But

    |B|sqrt(D)=2Q|v|b sqrt(D)<=Q(Dv²+b²)=e+1,

whereas (3) gives C>e+2. Thus C²>D B², contradicting Res=0. Hence t!=0. This also covers B=0.

## 4. Exclude T=0 before the strong-root division

Suppose T=0. Then v=B=0 and Res=0 forces

    C²=4d²t²M²A.

Since d,t,M are nonzero, tau=C/(2dtM) is rational and tau²=A is an integer, so tau is an integer. Put y=t-M*tau. Expanding the displayed identity with the definition of C gives

    d y²=e=Qb²-1.

These are integer roots; no rational Pell saturation lemma is needed here.

The bootstrap implies 0<R<a<Delta,c>2. Since i is nonzero,

    Q-b=(Delta-R)D-Delta-c
       >=1+Delta(i²c⁴-1)-c>1.

Thus1<b<Q. The equation Qb²-(Q-1)y²=1 implies |y|>=b+1, then

    b²-1=(Q-1)(y²-b²)>=(Q-1)(2b+1)>b²-1,

a contradiction. Therefore T!=0 and B!=0, while C,d,t,M were already shown nonzero.

## 5. Restore all three roots

Set

    f=-U/(2CB),
    tau=(C+Bf)/(2dtM),
    y=t-M*tau.

The resultant gives f²=D, so f is a rational integer. Expanding U+2CBf=0 gives

    (C+Bf)²=4d²t²M²A,

hence tau²=A and tau is an integer. Then y is an integer and direct expansion yields

    d y²=e-Bf=Q(vf-b)²-1.

Also V=vf-b=c(Tf-1)-Rf² and f²-Delta i²c⁴=1. Therefore the normalized first, strong and auxiliary norms are exactly restored. The existing signed theorem of package14 applies to the seven positive ports, odd i,square w and arbitrary signs of the recovered f,tau,y and supplied h,T,gamma. It gives a correct blank tableau and the inherited consistency equivalence.

## 6. Completeness and count

Choose package14's canonical normalized witnesses with odd i and square w. Keep all retained coordinates and put t=M*tau+y. This gives C+Bf=2dtM*tau and U+2CBf=0, hence Res=0; all outer factors are one. No new tuning or positive-only inference is required.

Seven disjoint positivity surjections contribute21 coordinates, and the six free coordinates h,T,gamma,t,r,u give27 integers. The84-operation parent plus49 positivity gates and3 odd/square gates yields136=72M+64A. All gates and ports are live.

## 7. Exact degree

Use degree2 on the seven positive ports and w, and degree1 on i and the other signed coordinates. Then

    deg(A,Q,D,v,b,M)=(44,90,66,11,74,66),
    deg(e)=238, deg(dM²A)=266, deg(C)=266,
    deg(U)=532, deg(Res)=1064.

The leading terms are successively dM²A, C² and U²; every competing term is strictly smaller. The outer degrees are35,13,4, giving total1116.

Writing Q0=beta J and k0=eta+zeta, the weighted final top form is

    -8 h gamma i²⁴ k0⁵⁷ w⁴³ s¹⁰⁰ Q0³⁴³
       * [w(Q0-F-alpha)-zQ0].

After i=2r+1, w=u² and the seven positivity substitutions, the coefficient of

    J_a⁶⁸⁸ h gamma r²⁴ eta_a¹¹⁴ u⁸⁶ s_a²⁰⁰ z_a²

is +2²⁷ beta³⁴⁴, nonzero for beta>0. Its exponent sum is1116, proving exact degree uniformly.

## Verification

Fresh `build_integer27.py` and `verify_integer27.py` parse the pinned upstream circuit only as inert JSON. The checker verifies all-gate/all-port liveness,150 independent signed formula evaluations and two exact modular leading-coefficient extractions; `INTEGER27_CHECKS.json` records PASS. These finite checks supplement the complete sign/denominator proof above and the unbounded inherited compiler/calibration arguments.
