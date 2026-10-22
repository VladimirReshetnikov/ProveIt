# Twenty-six unrestricted integers by a four-root norm

## Statement

This note extends the new twelve-coordinate scaled-auxiliary-root norm to 26 unrestricted integer coordinates. It uses exactly seven positive original ports, odd i, square w, and otherwise signed inputs. The argument below first uses the original coherent package-06 quartet, with beta=Bm1, K0=Kconstant and shifted MF. The primary instantiated equation uses the separately audited complete compact Wang943 tuple selected by `COEFFICIENT_BINDINGS.json`; `COEFFICIENT_TRANSFER.md` explains the signed-domain transfer. Its ordinary proof is formalizable in ZFC and inherits the same blank-machine/refutation calibration; it is not a fresh proof-assistant certificate or a minimum claim.

## Definitions

Retain positive J,F,alpha,z,s,eta,zeta, and let h,i,T,w,t be supplied coordinates with i=2r+1 and w=u² for integers r,u. Thus i is nonzero, w>=0, and h,T,t are fully signed. Define

    q=beta J+1, C=q-F-alpha, X=wq, Y=sq³, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y, H=4a+3,
    Delta=a²+H, Dbase=X+ac,
    R=((q-1)(q-F)+alpha)(q²-1)+(MC+q MF)J,
    Nk=k-hE-R, Nt=(K0+w)C+q-F-z(q-1),
    L=E kY, A=1+L(L+k), G=1+Delta c²,
    I=i c², S=Delta I,
    Q=S², D=1+Delta I², d=Q-1,
    v=cT, b=c+RD, e=Q(Dv²+b²)-1, B=2Qvb,
    W=2d*((S*i)*(v*T)+b),
    P=H W, K=P+1, M=6W, u_weight=6P=HM,
    Z=Ht+K Dbase.

All names are computed polynomials, not additional unknowns. In the rank-four free algebra with formal r0²=A and sigma²=G, form

    F(r0,sigma)=[(Z-u_weight*r0-K*sigma)²-H²*d*e]²-H⁴*d²*B²*D.

Let Res be its norm, the product over all four formal sign choices of r0 and sigma. Sign invariance makes Res an integer polynomial; the literal norm arithmetic is emitted without division. The equation is

    Nk Nt (1+Res)-1=0.                                         (1)

In the explicit norm evaluator the last step is Res=N00²-A*N10² with N10 even. Thus Res is a square modulo four. At a zero of (1), 1+Res cannot be -1; consequently Res=0 and Nk=Nt=epsilon for epsilon in {-1,1}.

## 1. Bounds available even when w=0

Here q,Y,k,c,a,H,Delta are positive and c>2, H>1, Delta>1. Because F,z are positive,

    q-F-z(q-1)=1-F-(z-1)(q-1)<=0.

If C<=-1, Nt=(K0+w)C+q-F-z(q-1)<=-K0<-1, impossible. Hence C>=0. Authentic coefficient bounds then give R>0; hence b>0. These facts hold before excluding w=0.

The odd i is nonzero. Therefore Q>2, d>0 and D>1. Also D<Q, since

    Q-D=Delta(Delta-1)i²c⁴-1>0.

For signed i,T,

    S*i=Delta i²c²>=|S|,
    v*T=cT²>=|v|.

Thus the polynomial bound W is positive and

    W >= 2d(|S v|+b).                                         (2)

No absolute-value operation appears in the emitted circuit.

## 2. Algebraic roots and a bound on every actual conjugate

A zero of Res provides real square roots r0,sigma with r0²=A, sigma²=G and F(r0,sigma)=0. Work in the totally real Galois field Lfield=Q(r0,sigma), allowing degree one, two or four. Put

    rho=(Z-HM*r0-K*sigma)/H.

Then rho is real and lies in Lfield. If B!=0 define

    f=(d*e-rho²)/(d*B).

The equation F=0 says f²=D and rho²=d(e-Bf). Every field conjugate f' is one of +/-sqrt(D). With V'=v f'-b,

    rho'²=d[Q(V')²-1] < dQ(|v|sqrt(D)+b)².

Since sqrt(D)<|S| and sqrt(Q/d)<sqrt(2)<2, (2) gives |rho'|<W. This holds for every actual field conjugate of rho, without assuming independent formal sign changes generate all automorphisms.

If B=0 then v=0 because Q,b,c are positive. The specialized factor equation gives rho²=d*e=d(Qb²-1). Every actual conjugate consequently satisfies

    |rho'|=sqrt(d(Qb²-1))<2db<=W.

Thus in either case every actual field conjugate has absolute value strictly less than W. There is no division by B in the B=0 branch.

The defining linear relation is

    Z=HM*r0+K*sigma+H*rho.                                    (3)

## 3. First exclude the zero-square branch

Suppose w=0. Then X=E=L=0 and A=1, so r0=+/-1 is already a rational integer. If a field automorphism changed sigma's sign, subtracting its image of (3) would give

    2K sqrt(G) <= 2H W.

But K=HW+1>HW and sqrt(G)>1. This is impossible. Thus sigma is rational and integral, and then rho is rational.

If B!=0, f is rational and f²=D implies f is integral; rho²=d(e-Bf) is therefore integral. If B=0, rho²=d*e is already integral. In either case rho, being rational with integral square, is an integer.

Define gamma=(sigma-Dbase)/H. Equation (3) gives

    t=M*r0+K*gamma+rho.

Hence K*gamma is an integer. The denominator of gamma divides H, whereas gcd(K,H)=1 because K=HW+1. Thus gamma is an integer. Now sigma=ac+gamma H and sigma²-Delta c²=1. Reducing this main norm modulo H yields 1=0 modulo H, impossible since H>1. This excludes w=0 without applying the first-root dominance estimate outside its range.

Consequently w>=1 and X>=q>=16.

## 4. Galois separation at positive square scale

From X>=16 and Y>=1,

    a+2=E+Y+2<2E,
    c=kY+eta<k(Y+1)<=2kY.

Since Delta=(a+2)²-1 and c>1,

    sqrt(G)<(a+2)c<4E kY=4L<4sqrt(A).

Moreover HW>4, so K=HW+1<(5/4)HW. Therefore

    K sqrt(G)+H W < 5HW sqrt(A)+HW < 6HW sqrt(A)=HM sqrt(A).

If a field automorphism flipped r0, subtracting its image of (3), and bounding the possible sigma change and the two rho terms, would contradict precisely this strict inequality. Thus every automorphism fixes r0. Hence r0 is rational and integral.

Now the second separation argument of Section3 applies unchanged: a sigma flip would force K sqrt(G)<=HW, contradicting K>HW. Therefore sigma is rational and integral; rho is rational. Exactly as in Section3, either B!=0 gives integral f and rho, or B=0 directly gives integral rho. In either case gamma is integral.

This argument remains valid if either radicand or their product is a square. No irreducibility assumption or generic field-degree claim is used. There is also no positivity or nonzero assumption on t.

## 5. Exclude the zero auxiliary quotient

With w>0, the source weak-transport bounds give

    3q+1<R<q⁴-2, E>=q⁴>R+2, a>R+2.

Signed h cannot be negative because k=R+epsilon+hE>0. Thus h>=0 and k>=R-1. In particular 0<R<a<Delta and c>2.

Exactly as in the gap proof,

    Q-b=(Delta-R)D-Delta-c
       >=1+Delta(i²c⁴-1)-c>1.

Hence 1<b<Q.

Suppose T=0, equivalently B=0. Then y=rho/d is rational and

    Q b²-(Q-1)y²=1.

The rational auxiliary Pell saturation lemma in the independent audit applies with positive integer |S|>1 and integer V=b, so y is an integer. Because b>1,

    (Q-1)(y²-b²)=b²-1>0,

forcing |y|>=b+1 and b²-1>=(Q-1)(2b+1)>b²-1, a contradiction. Thus T!=0 and B!=0.

Now f=(d*e-rho²)/(d*B) is unambiguously a rational integer. Put y=rho/d. With integral V=vf-b,

    (Q-1)y²=Q V²-1.

The same rational auxiliary Pell saturation lemma proves y integral. The lemma states that for integer S0>1,V and rational y, S0²V²-(S0²-1)y²=1 implies y integral. Its complete independent proof uses fundamental integral Pell solutions and the implication x_m|x_n => n=m mod2m; it does not assume squarefreeness of Q-1 or a generic unit generator.

## 6. Restore the signed normalized source and prove completeness

We have integral tau=r0, Dmain=sigma, f,gamma,y. Their exact equations are

    tau²=1+L(L+k),
    Dmain=X+ac+gamma H, Dmain²-Delta c²=1,
    f²=1+Delta i²c⁴,
    V=vf-b=c(Tf-1)-Rf²,
    Q V²-(Q-1)y²=1.

Together with Nk=Nt=epsilon these give the normalized product on exactly package14's established signed domain: seven positive ports, nonzero odd i, square w, and unrestricted f,h,T,tau,y,gamma. Its soundness theorem recovers the correct signs and the calibrated blank tableau. No positive-only parent theorem is applied to signed reconstructed roots.

Conversely, choose package14's canonical normalized witnesses from an accepting computation. Its existing completeness proof supplies odd i and square w using the index m=cR and odd five-power padding; no new divisibility by H, modular period, or altered Pell index is required. Set rho=d*y and

    t=M*tau+K*gamma+rho.

The three canonical terms are positive, though t is allowed to be any integer. Equation (3), the source auxiliary norm and f²=D give F(tau,Dmain)=0. Hence Res=0 and (1) holds. This proves equivalence in existence.

## 7. Count and exact degree

Replace each of J,F,alpha,z,s,eta,zeta by its own Pos(a,b,c)=1+a²+b²+c(c+1), a surjection from three integers to the positive integers. Keep h,T,t and the odd/square parameters r,u unrestricted. The total is7*3+5=26 integers.

For the exact degree, give the seven positive ports and w weight two, and i,h,T,t weight one. The relevant weighted degrees are

    L=22, a=12, c=10, R=8, Delta=24, D=66, Q=d=90, b=74;
    W=164, P=K=u_weight=176, M=164, Z=198.

The extra signed-bound term (S*i)(v*T) has degree58, below b's74. It does not affect the leading form of W. The two radicands A,G have degree44 with the same leading square L_top², since (ac)_top=L_top.

In the four formal factors, the highest linear forms Z-u_weight*r0-K*sigma specialize to

    -6K_top L_top, +6K_top L_top, -4K_top L_top, +8K_top L_top.

The subtracted term H²*d*e is lower degree, as is the terminal H⁴*d²*B²*D term. Therefore

    Res_top = (6⁸ 4⁴ 8⁴)(K_top L_top)¹⁶,

which is nonzero. This proves Res has exact degree3168. Nk and Nt have degrees13 and4, respectively, so (1) has exact degree3185.

Writing Q0=beta J and k0=eta+zeta,

    K_top=8 i⁴ k0⁸ w⁷ s¹⁵ Q0⁵⁵(Q0-F),
    L_top=w k0 s² Q0⁷.

After the odd and square substitutions and positivity expansions, the coefficient of

    J_a²⁰²⁶ h r⁶⁴ eta_a²⁸⁸ u²⁵⁸ s_a⁵⁴⁶ z_a²

is +2¹⁴⁰*3⁸*beta¹⁰¹³, nonzero for beta>0. Its exponent sum is3185. This is a uniform symbolic certificate, not an inference from finite sampling.

The literal circuit and finite check receipt separately report the fully charged operation ledger. This note's unbounded arithmetic and inherited compiler/calibration proofs remain essential; finite evaluations alone do not establish the consistency equivalence.
