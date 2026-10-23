# Twenty-six unrestricted integers with an unscaled saturated auxiliary root

## Result and coefficient convention

`integer26_unscaled_four_root192_degree2465.json` is a literal polynomial in 26 unrestricted integers, of exact total degree 2465, evaluated using 192 binary operations (117 multiplications and 75 additions/subtractions). Its lack of integer zeros is equivalent to Con(ZFC), by ordinary mathematics formalizable in ZFC, with the inherited exact-machine calibration. This is not a new proof-assistant certificate or a claim of global minimality.

The primary instantiation selects the complete audited compact Wang943 coefficient quartet through `COEFFICIENT_BINDINGS.json`. The original package-06 quartet is a separate coherent alternative. `COEFFICIENT_TRANSFER.md` explains the signed-domain transfer; no individual coefficient ports are mixed. MF always denotes the shifted source mask.

The earlier degree-3185 scaled-auxiliary construction remains in `INTEGER26_PROOF.md` for provenance. This refinement removes its unnecessary scaling of the auxiliary root by d: the rational auxiliary Pell saturation lemma already proves the unscaled root integral before reconstructing gamma.

## 1. Definitions and literal polynomial

Retain positive J,F,alpha,z,s,eta,zeta. Let h,T,t,r,u be arbitrary integers, and put i=2r+1 and w=u². Define the computed polynomials

    q=beta J+1, C=q-F-alpha, X=wq, Y=sq³, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y, H=4a+3,
    Delta=a²+H, Dbase=X+ac,
    R=((q-1)(q-F)+alpha)(q²-1)+(MC+q MF)J,
    Nk=k-hE-R, Nt=(K0+w)C+q-F-z(q-1),
    L=E kY, A=1+L(L+k), G=1+Delta c²,
    I=i c², S=Delta I, Q=S², D=1+Delta I², d=Q-1,
    v=cT, b=c+RD, e=Q(Dv²+b²)-1, B=2Qvb,
    W=2*((S*i)*v²+b),
    P=HW, K=P+1, M=6W, u_weight=6P=HM,
    Z=Ht+K Dbase.

In the rank-four free algebra with formal tau²=A and g²=G, put

    F(tau,g)=[d*(Z-u_weight*tau-K*g)²-H²e]²-H⁴B²D.

Let Res be the product of F over the four formal signs of tau and g. The literal norm circuit computes this integer polynomial without divisions. The equation is

    Nk Nt (1+Res)-1=0.                                       (1)

The norm evaluator ends in Res=N00²-A*N10² with N10 even. Thus Res is a square modulo four. At a zero of (1), 1+Res cannot be -1, so Res=0 and Nk=Nt=epsilon in {-1,1}.

## 2. Sign-safe bound without assuming w or T nonzero

The seven positive ports imply q,Y,k,c,a,H,Delta positive, c>2, H>1 and Delta>1. Also

    q-F-z(q-1)=1-F-(z-1)(q-1)<=0.

If C<=-1 then Nt<=-K0<-1, impossible. Hence C>=0. The authentic coefficient bounds yield R>0, and consequently b>0, even before excluding w=0.

The odd i is nonzero. Therefore Q>2, d>0, D>1 and

    Q-D=Delta(Delta-1)i²c⁴-1>0.

For signed i,T one has S*i>=|S| and v²>=|v|. Hence

    W>=2(|Sv|+b)>0.                                         (2)

No absolute value occurs in the polynomial.

A zero of Res gives real roots tau,g with tau²=A, g²=G and F(tau,g)=0. Work in the totally real Galois field Q(tau,g), allowing degree one, two or four. Define

    y=(Z-HM*tau-K*g)/H.                                     (3)

If B!=0, let f=(e-dy²)/B. Then F=0 says f²=D and dy²=e-Bf. Every actual field conjugate f' is one of +/-sqrt(D), and, with V'=vf'-b,

    d(y')²=Q(V')²-1,
    |y'|<sqrt(Q/d)(|v|sqrt(D)+b)<2(|Sv|+b)<=W.

If B=0, positivity of Q,b,c gives v=0. The same factor equation gives dy²=Qb²-1 directly, so |y'|<2b<=W for every actual conjugate. This branch does not divide by B and does not need f.

Thus all actual conjugates of y have absolute value less than W. The linear relation is

    Z=HM*tau+K*g+H*y.                                       (4)

## 3. Rational auxiliary Pell saturation

We use the independently proved lemma:

    If S0>1 and V are integers and y is rational, then
    S0²V²-(S0²-1)y²=1 implies y is an integer.

The complete proof is in `../audit/RATIONAL_AUXILIARY_PELL_SATURATION.md`. It reduces S0²-1 to a squarefree Pell coefficient and uses the integral Pell divisibility implication x_m|x_n => n=m modulo 2m. No squarefreeness of Q-1 or generic field-degree assumption is made here.

Consequently, once tau and g are rational integers, (3) makes y rational. If B!=0, f is rational with integral square D and hence integral; saturation with V=vf-b proves y integral. If B=0, saturation applies directly with V=-b. In either case y is integral before gamma is reconstructed.

Now define gamma=(g-Dbase)/H. Equation (4) gives

    t=M*tau+K*gamma+y.

Thus K*gamma is integral. Since H*gamma is integral and gcd(K,H)=1, gamma is integral.

## 4. Exclude w=0 before using dominance

Suppose w=0. Then X=E=L=0 and A=1, so tau=+/-1 is already a rational integer. If a field automorphism changed the sign of g, subtracting its image of (4) would imply

    2K sqrt(G)<=2HW,

contrary to K=HW+1>HW and sqrt(G)>1. Hence g is rational and integral. Section 3 then proves y and gamma integral, including the B=0 branch.

But g=ac+gamma H at X=0 and g²-Delta c²=1. Reducing this equation modulo H gives 1=0 modulo H, impossible since H>1. Therefore w>=1 and X>=q>=16.

## 5. Galois separation at positive square scale

Since X>=16 and Y>=1,

    a+2=E+Y+2<2E, c=kY+eta<k(Y+1)<=2kY.

As Delta=(a+2)²-1 and c>1,

    sqrt(G)<(a+2)c<4L<4sqrt(A).

Also HW>4, so K<(5/4)HW. Therefore

    K sqrt(G)+HW<5HW sqrt(A)+HW<6HW sqrt(A)=HM sqrt(A).

An automorphism flipping tau would contradict this inequality after subtracting its image of (4). Thus every automorphism fixes tau, so tau is rational and integral. A subsequent g sign flip would force K sqrt(G)<=HW, again impossible. Hence g is rational and integral. Section 3 supplies integral y and gamma in either B branch.

This reasoning uses only actual automorphisms. It remains valid when either radicand or their product is a square and imposes no sign or nonzero restriction on t.

## 6. Exclude T=0, then restore the signed source

Now w>0, so the weak transport bounds give

    3q+1<R<q⁴-2, E>=q⁴>R+2, a>R+2.

Signed h cannot be negative because k=R+epsilon+hE>0. Thus h>=0 and k>=R-1. In particular 0<R<a<Delta. As c>2,

    Q-b=(Delta-R)D-Delta-c
       >=1+Delta(i²c⁴-1)-c>1.

Therefore 1<b<Q. If T=0, then B=0 and the already integral y satisfies Qb²-(Q-1)y²=1. It follows that

    (Q-1)(y²-b²)=b²-1>0,

so |y|>=b+1 and b²-1>=(Q-1)(2b+1)>b²-1, a contradiction. Hence T!=0 and B!=0. The rational integer f=(e-dy²)/B is now well defined.

We have recovered the integral relations

    tau²=1+L(L+k),
    g=X+ac+gamma H, g²-Delta c²=1,
    f²=1+Delta i²c⁴,
    V=vf-b=c(Tf-1)-Rf²,
    QV²-(Q-1)y²=1.

Together with Nk=Nt=epsilon, these are exactly package14's normalized source on its established signed domain: seven positive ports, odd i, square w, and otherwise signed f,h,T,tau,y,gamma. Its signed-domain theorem, with the whole-tuple coefficient transfer, yields the calibrated blank tableau. A positive-only source theorem is not used on these signed roots.

## 7. Completeness and variable count

From any accepting blank computation choose the canonical normalized witnesses supplied by package14 and the compiler transfer: odd i, square w, and seven positive retained ports. The strong Pell index is m=cR; odd five-power padding supplies the square scale. There is no new requirement i=Hj, no period change and no altered Pell index.

Set t=M*tau+K*gamma+y. Then (4) holds and the source auxiliary and strong equations give F(tau,g)=0. Thus Res=0 and (1) holds. This proves equivalence in existence.

Represent each retained positive port by its own Pos(a,b,c)=1+a²+b²+c(c+1), a surjection from three integers onto the positive integers. Retaining h,T,t,r,u gives 7*3+5=26 unrestricted integer variables. The139-operation positive-root parent acquires one sign-safe-bound multiplication, reusing the already computed v² register, 49 positivity gates and three odd/square substitution gates, for192 operations:117M+75A. All gates and ports are live.

## 8. Uniform exact degree 2465

Give the seven positive ports and w weight two, and i,h,T,t weight one. Then

    L=22, a=12, c=10, R=8, Delta=24, D=66, Q=d=90, b=74;
    W=74, P=K=u_weight=86, M=74, Z=108.

The signed-bound term (S*i)*v² has degree68, less than b's74. Both A and G have leading square L_top². The four leading linear forms Z-u_weight*tau-K*g are

    -6K_top L_top, +6K_top L_top, -4K_top L_top, +8K_top L_top.

The H²e term has degree262, below d times the linear square's degree306. The terminal H⁴B²D has degree464, below the preceding square's degree612. Therefore

    Res_top=1152⁴*d_top⁸*(K_top L_top)¹⁶,

nonzero of degree2448. Multiplying Nk and Nt of degrees13 and4 gives exact degree2465.

Writing Q0=beta J and k0=eta+zeta,

    d_top=i²k0⁴w⁴s⁸Q0²⁸,
    K_top=8i²k0⁴w³s⁷Q0²⁷(Q0-F),
    L_top=wk0s²Q0⁷.

After all substitutions, the coefficient of

    J_a¹⁵⁷⁸ h r⁴⁸ eta_a²²⁴ u¹⁹⁴ s_a⁴¹⁸ z_a²

is +2¹²⁴*3⁸*beta⁷⁸⁹. It is nonzero for the actual beta>0 and the exponent sum is2465. The certificate proves exact degree uniformly, not by sampling.

The independent evaluator checks the four-factor norm using free-algebra multiplication rather than the nested circuit, plus liveness and exact modular coefficient tests. Its finite diagnostics supplement, not replace, the unbounded Pell and compiler proofs.

