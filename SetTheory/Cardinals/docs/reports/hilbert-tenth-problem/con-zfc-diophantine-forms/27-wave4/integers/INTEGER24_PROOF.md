> Release binding: all new generated artifacts in this directory use the complete mixed-radix Wang943 tuple, B=2^(5^9), selected by COEFFICIENT_BINDING.json. Historical source tuples mentioned below document predecessors or valid alternatives, not the selected numerical instance. The sibling coefficients/COEFFICIENT_PROOF.md proves the full adapter and simultaneous canonical restrictions.

# Twenty-four unrestricted integers from signed-scale norm saturation

## Result and provenance

Combine the literal norm evaluator of `21-norm12` with the signed odd-scale theorem of `23-separating12`, both read at repository pin
`VladimirReshetnikov/ProveIt@ae3007ca4467011e0e051c84acb4a1dd13971b0e`, under
`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/`.
The result is a three-equation system in **24 unrestricted integer unknowns**, using 159 binary arithmetic gates and maximum residual degree 2416; its product finalizer uses 163 gates and has exact degree 2432, and its sum of squares uses 166 gates and has degree 4832.

This proof needs one whole authentic compiler coefficient tuple `(beta,K0,MC,MFsrc)` satisfying the source odd-scale and odd-multiplier completeness hypotheses. The package-23 T5263 tuple is an explicitly documented such instance; its MF port is the shifted source mask. The expressions do not introduce four additional existential unknowns. Do not mix individual constants from different compiler tuples. Any newer compiler replacement must separately preserve the native interface, five-power odd padding, and population identity `popcount(R)=3 log2(q)+2`.

This is an ordinary mathematical argument relative to the cited compiler and Pell proofs, not a new proof-assistant certificate. Its result is an equivalence with finite ZFC refutation and hence an equivalence of *lack* of integer solutions with Con(ZFC), not a proof of either consistency or inconsistency.

## 1. Variables and equations

Exactly six ports are positive:

    J, F, alpha, z, eta, zeta.

The remaining supplied ports are

    i=2i0+1, s=2s0+1, w=w0^2,
    h, T, r arbitrary integers.

For each positive port independently substitute

    Pos(x,y,t)=1+x^2+y^2+t(t+1).

This is always positive and onto the positive integers, by Legendre's three-square theorem applied to `4n-3`. Thus there are `6*3+6=24` integer unknowns. All subsequent symbols are polynomial abbreviations, not extra quantified unknowns:

    q=beta J+1; C=q-F-alpha;
    X=wq; Y=sq^3; E=XY;
    k=eta+zeta; c=kY+eta;
    a=E+Y; H=4a+3; Delta=a^2+H;
    ell=EkY; A=1+ell(ell+k); G=1+Delta c^2;
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MFsrc)J;
    Nk=k-hE-R; Nt=(K0+w)C+q-F-z(q-1);
    D=1+Delta i^2 c^4;
    Q=(Delta i c^2)^2=Delta(D-1); d=Q-1;
    v=cT; b=c+RD;
    e=Q(Dv^2+b^2)-1; Baux=2Qvb;
    Bnd=v^2+D+2b;
    L=1+H Bnd; S=X+ac+Hr.

In the free algebra with formal `u^2=G`, `tau^2=A`, define

    F(u,tau)=[d(S-Lu-HLtau)^2-H^2 e]^2-H^4 Baux^2 D,
    N=Norm_G,u(Norm_A,tau(F)).

Here `Norm_g(p0+p1*x)=p0^2-g*p1^2` after reduction modulo `x^2-g`. It is a finite polynomial computation, not an invocation of roots in the equation. The supplied JSON expands it as binary addition, subtraction and multiplication gates.

The comparison system is `Nk=1, Nt=1, N=0`. The product is

    P24=Nk Nt (1+N)-1.

The sum-of-squares option is `(Nk-1)^2+(Nt-1)^2+N^2`.

The same literal source evaluator works unchanged even when H and L are negative. This is the key refinement: no H-square replacement or additional positivity variable is needed.

## 2. Units and all pre-reconstruction bounds

The source norm circuit ends `N=N0^2-G N1^2`, where N1 is divisible by 8 as an integer polynomial. Hence N is a square modulo 4. At a zero of P24, the three factors are integer units; `1+N=-1` is impossible modulo 4. Therefore

    N=0; Nk=Nt=epsilon in {-1,1}.

For the comparison/SOS forms, epsilon=1 from the outset. This unit argument is independent of all signs and is used first.

The positive ports, w>=0, and K0>=2 give weak transport C>=0. Indeed if C<=-1, then

    Nt=(K0+w)C+1-F-(z-1)(q-1)<=-(K0+w)<=-2,

contradicting Nt=+/-1. The authentic coefficient/mask bounds therefore give

    q>=16; q(q^2-1)<R<q^4-2.

No first, main or auxiliary root has been restored. In particular no assumption that s>0, w>0 or h>=0 has been used.

Since s is odd, set Z=|Y|>=q^3. Then X>=0, |a|=(X+1)Z, and a and c have the same sign. Moreover

    |c|>k(Z-1)>1;
    |H|>=4Z-3>6;
    Delta=(a+2)^2-1>q^4>R;
    G=1+Delta c^2>4.

The lower bound on Delta in the negative case follows from
`Delta>=(q^3-1)(q^3-3)>q^4`; the positive case is larger. Since i is odd it is nonzero, and

    D>Delta+|c|; Q>1; d>0;
    b=c+RD>D-|c|>1;
    Q-b=(Delta-R)D-Delta-c>D-Delta-|c|>0.

The displayed strict inequality may be replaced by >= in its middle step if Delta-R=1; its final positivity is unchanged. Thus **1<b<Q** already, including X=0 and either sign of s.

We have ell=XkY^2>=0 and A>=1. A=1 is explicitly allowed before the zero-w boundary is excluded.

## 3. Sign-safe separation inequalities

A zero of N supplies coherent algebraic roots u,tau,f, with

    u^2=G, tau^2=A, f^2=D,
    d y^2=Q(vf-b)^2-1=e-Baux f,
    S=Lu+HLtau+Hy,

where `y=(S-Lu-HLtau)/H`. The product identity includes all signs and remains valid when radicands are squares, extensions coincide, or Baux=0. Work in a finite normal closure over Q.

Every conjugate y' satisfies, also when complex,

    |y'|^2 <= [Q(|v|sqrt(D)+b)^2-1]/(Q-1)
             <2(|v|sqrt(D)+b)^2.

Since `v^2+D>=2|v|sqrt(D)`, the positive integer Bnd satisfies

    |y'|<Bnd.

Put B=|H|Bnd. Then B>2. For H>0, L=1+B; for H<0, L=1-B. In either case

    |L|>B/2; L!=0.

As sqrt(G)>2 this yields the first strict separation:

    |L|sqrt(G)>B=|H|Bnd.                       (I)

This is the missing signed-H argument; one must not reuse the positive-L inequality literally.

After w=0 has been excluded in Section 4, X>=q>=16. Uniformly for either sign of Y,

    |a+2| <= (X+1)Z+2 < 2XZ,
    |c| < 2kZ,
    sqrt(G)<|a+2||c|<4XkZ^2=4ell<4sqrt(A).

The bound `sqrt(G)<|a+2||c|` follows because `G=(a+2)^2 c^2-(c^2-1)` and |c|>1. Since |H|>6 and A>=1,

    |H|sqrt(A)-sqrt(G)>2.

Together with |L|>B/2 this gives the second strict separation:

    |HL|sqrt(A)>|L|sqrt(G)+|H|Bnd.              (II)

## 4. Restore integrality on the X=0 boundary and exclude it

Suppose X=0. Then ell=0 and A=1, so tau=+/-1 is already a rational integer. If u were irrational, an automorphism would change u to -u while fixing tau and S; the linear relation would imply

    2|L|sqrt(G)<=2|H|Bnd,

contrary to (I). Hence u is rational and integral, and y is rational.

If Baux!=0, the relation `f=(e-dy^2)/Baux` makes f rational and integral, since its square D is an integer. Then `V=vf-b` is an integer and the equation

    Q V^2-(Q-1)y^2=1

makes y integral by the rational auxiliary-Pell saturation lemma (Section 6 below), because Q is the square of a nonzero integer and Q>1.

If Baux=0, the facts Q>0, b>1 and c!=0 force T=v=0. The equation directly becomes `Qb^2-(Q-1)y^2=1`; the same saturation lemma makes y integral without dividing by Baux or assuming f rational.

Now S=Lu+HLtau+Hy and L=1 mod H imply u=X+ac mod H. Therefore

    gamma=(u-X-ac)/H

is an integer. At X=0, the main norm gives

    1=u^2-Delta c^2
      =H(2ac gamma+H gamma^2-c^2),

impossible because |H|>1. Thus X>0 and w>0. This argument precedes (II), every rank argument, and any inference that s is positive.

## 5. Restore roots for X>0; exclude T=0

If tau were irrational, an automorphism flipping it in the linear relation would imply

    2|HL|sqrt(A)<=2|L|sqrt(G)+2|H|Bnd,

contrary to (II). Thus tau is rational and integral. A subsequent automorphism flipping irrational u contradicts (I), so u is integral. As in Section 4, y is rational, saturation makes it integral in both Baux branches, and gamma is integral by reduction modulo H.

If T=0, then v=Baux=0 and

    (Q-1)(y^2-b^2)=b^2-1>0.

Since y and b are integers, |y|>=b+1. But 1<b<Q implies Q-1>=b, so

    b^2-1 >= (Q-1)(2b+1) >= b(2b+1)>b^2-1,

a contradiction. Therefore T!=0 and Baux!=0. The reconstructed f is integral.

Consequently the recovered signed integer roots satisfy exactly

    tau^2=1+ell(ell+k),
    (X+ac+gamma H)^2-Delta c^2=1,
    f^2-Delta i^2 c^4=1,
    Q[c(Tf-1)-Rf^2]^2-(Q-1)y^2=1,
    Nk=Nt=epsilon.

## 6. Saturation lemma and signed-scale theorem being reused

The auxiliary saturation lemma is: if m>=2 and V are integers and y is rational, then
`m^2 V^2-(m^2-1)y^2=1` implies y is an integer. The full elementary Pell proof is in the vendored `21-norm12/proofs/NORM12_PROOF.md`, Section 3. Writing y=a/b in lowest terms, b^2 divides m^2-1; Pell classification for D0=(m^2-1)/b^2 and the divisibility implication `chi_j|chi_l => l is an odd multiple of j` force b|a and hence b=1. No generic claim that rational Pell points are integral is used.

At precisely this point, all hypotheses of `23-separating12/proofs/ODD_SCALE_27_PROOF.md`, Sections 1--4, hold: six positive ports J,F,alpha,z,eta,zeta; signed nonzero odd i and s; w>0 a square; arbitrary h,T,gamma,tau,f,y; the four normalized norms equal 1 and index/transport units have common sign. That source proves s<0 impossible by classifying the first/main Pell ranks, recovering p=R via signed auxiliary congruences, proving no wrap and then `|Y|>2^R`, and excluding both possible main-root signs modulo H. This is a proved source theorem being reused, not a new assumption about negative scales and not an application of its positive-only parent before signs have been recovered.

Thus s>0. The established signed normalized/ordinary compiler theorem now decodes a genuine accepting blank K215 computation and the calibrated finite syntactic ZFC refutation. It also recovers the positive index and transport signs. Neither h nor the reconstructed root signs require additional guards.

## 7. Completeness with all canonical restrictions simultaneously

The package-23 signed-scale theorem, Section 5, combines canonical odd normalized i and square w with the exact native-mask population formula

    popcount(R)=3 log2(q)+2.

The half-binomial valuation therefore gives `v2(Y)=3 log2(q)` and s odd. The package-14 canonical strong index m=cR gives odd i; independent five-power spatial and temporal padding makes the exponent of q odd, so w=2^R/q is a square. These are simultaneous restrictions on the same canonical accepting witness, not independent substitutions of incompatible tuples.

For that witness define

    r=gamma+Bnd u+L tau+y.

This integer gives S=Lu+HLtau+Hy identically. The source roots annihilate one norm factor. Nk=Nt=1, so all three finalizers have zeros. Choose independent Pos preimages of the six positive ports and set i0=(i-1)/2, s0=(s-1)/2, w0=sqrt(w). This constructs a zero in Z^24.

## 8. Metrics and exact degree

The six Pos substitutions cost 42 binary gates; the two odd maps cost four; the square map costs one, totaling 47. The original 112/116/119-gate source forms therefore become 159/163/166 gates. All gates and supplied ports are live.

Assign weight 2 to J,F,alpha,z,eta,zeta,w, and weight 1 to i,s,h,T,r. Then

    deg(q,X,Y,E,a,H,c,Delta)=(2,4,7,11,11,11,9,22),
    deg(A,G,D,Q,d,R,b,Bnd,L,S)=(40,40,60,82,82,8,68,68,79,20).

In the source pair evaluator, a0=H^2 L^2 A has degree220, whereas V0=S^2+L^2G has degree198 and V1=2SL degree99. Thus C0 has unique leading term d*a0, degree302; C1 has degree181. Kc0 degree582, while C0^2 has degree604, and Z has degree424. Consequently N0 has degree1208, N1 has degree1087 at most, and `G N1^2` degree2214 at most, strictly below N0^2 degree2416. The norm has the nonzero leading form

    N_top=d_top^8 H_top^16 L_top^16 A_top^8.

This has degree2416 for every authentic fixed beta>0. The index residual has degree12 with leader -h E_top; transport degree4 has leader `w(beta J-F-alpha)-z beta J`, nonzero. Hence product degree2432 and SOS degree4832, uniformly in the authentic coefficient tuple. Independent quadratic positive forms and odd linear forms preserve the displayed nonzero leaders.

The finite checks verify syntax, liveness, exact arithmetic agreement with the eight-dimensional conjugate product, substitution identities, parity, and leading forms. They supplement rather than replace the unbounded reverse proof and inherited compiler semantics.
