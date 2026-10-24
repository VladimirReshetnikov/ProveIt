# Eleven integers by selective coprime fusion

## Scope and outputs

The principal equations have eleven unrestricted integer coordinates and six fixed numeral ports. They combine (i) the previous centered-budget kernel, (ii) signed main-Pell folding before projection, and (iii) a new selective coprime fusion of the first-Pell and positivity radicands. The direct equation has degree728 and122 live binary arithmetic operations. Its auxiliary-centered sibling has degree688 and126 operations. A more aggressive all-radicand fusion gives degree1632 and114 operations, a different tradeoff.

These are ordinary mathematical zero-existence reductions, conditional only on the same explicitly retained native/compiler/refutation calibration as their sources. No global minimum, new formal kernel certificate, internal object-ZFC derivation, or proof of consistency is asserted. Exact polynomial and degree checks are separate from unbounded mathematical proofs.

## 1. Complete common definitions

Use independent integers j,C,z,h,r,v,w,T,c,n,s and the exact payloads beta,K0,MC,MF,cone_A,cone_B in coefficients/BINDING.json. In particular beta=2^1064921−1, MF is already shifted, cone_A=2^1113 and cone_B=2^666104. Define

 J=6j+1; q=beta*J+1; W=12w+4; X=qW; Y=(2v+1)q^3;
 E=XY; a=E+Y; H=4a+3; Delta=a^2+H=(a+2)^2−1;
 F=(K0+W)C−z(q−1);
 R=(q(q−F)−C)(q^2−1)+(MC+q*MF)J;
 k=R+1+hE; eta=c−Yk;
 Derr=(cone_A*F−q)^2+(cone_B*C−q)^2;
 Budget=k^2(q^2−Derr)−4q^2*eta^2;
 D=3Budget−4; L=XY^2*k; Dt=1+L(L+k);
 Dg=1+4D*Dt*s^2; P=Dt*Dg;
 I=2src^2; Df=1+Delta*I^2;
 Q=Delta^2*I^2; delta=Q−1;
 V=Df(c−R+4IT)−c; Cy=QV^2−1; Da=delta*Cy;
 K=X(3c−2X)+2; S=I*H^5;
 zc=HT+K; Ac=(zc^2+3H^2)(zc^3−19H^3).

All symbols here are polynomial abbreviations, not additional variables.
For the direct equation let Cshift=0; for the centered equation let Cshift=(2Q−1)V. Put

 Z=S(n+Cshift)−Ac;
 u=S^2*Df; b=4S^2*Da; e=16S^2*P;
 E8=[(Z^2−u−b−e)^2−4(ub+ue+be)]^2−64ube Z^2.

The equation is E8=0. This is an ordinary integer polynomial, displayed without any root or denominator. The identity

 E8=product over epsilon in {−1,1}^3 of
       (Z−epsilon1*sqrt(u)−epsilon2*sqrt(b)−epsilon3*sqrt(e))

is an algebraic identity, including zero/negative/dependent radicands. It can be proved in a free radical algebra, or by successive quadratic norms. The literal circuit and independent checker prove its full35-coefficient identity.

## 2. Bootstrap, positivity and selective fusion

The fixed tuple and affine restrictions give, unconditionally,
q even, q=2 mod3, |q|>=16, |X|>=64, |Y|>=4096 and |a|>=63*4096.
Thus H is odd/nonzero, Delta>1 and Delta=3 mod4. Dt>=1 because Dt=1+ell(ell+1)k^2, ell=XY^2. Df>=1.

The polynomial pi(x)=(x^2+3)(x^3−19) has no rational zero and has a root modulo every positive integer. The complete elementary proof, including p=2,3,19 and Hensel lifting/CRT, is retained in source/PRIME_TWELVE.md Section2. For the no-zero claim alone, x^2+3 has no real root and x^3−19 has no rational root.

If I=0, then S=0 and the polynomial is Ac^8. But Ac=H^5*pi(T+K/H) is nonzero because H!=0 and its argument is rational. Consequently I!=0 at every zero. Thus s,r,c are nonzero, |I|>=c^2 and Q>1. Moreover Df>|c|+1. Writing b0=c−R+4IT, either b0=0 and |V|=|c|>=1, or b0!=0 and |V|>=Df−|c|>1. Hence Cy>0, delta>0 and Da>0.

At a polynomial zero one of its three conjugate factors vanishes. If Dg<0, then P<0 and its term is the sole nonzero imaginary term, since Df and Da are positive and S!=0. This is impossible. Dg is odd, so Dg>0. If Budget<=1, then D<=−1 and Dg=1+4D*Dt*s^2<=−3. Therefore Budget>=2.

Exactly as in source/centered11-proof.md Section3, this implies k!=0,
Derr<q^2, |eta/k|<1/2, and the common strict sign of q,F,C,q−F−C. With m=|Y|, K0=|k| and C0=|c| it gives

 K0(m−1/2)<C0<K0(m+1/2), sign(c)=sign(kY).

No eta>0 assertion is needed yet.

Since I is even, Df=Da=1 mod4. Dt is odd, Dg=1 mod4, and P is odd. A vanishing factor, divided by S, says that a signed sum

 sqrt(Df)+2sqrt(Da)+4sqrt(P)

is rational. For positive odd integer radicands, write each root as an odd integer times the root of an odd squarefree integer. Within a nontrivial squareclass, the least power of2 among1,2,4 occurs uniquely and cannot cancel. Linear independence of distinct squarefree radicals therefore makes all three roots rational, hence integral.

The essential fusion identity is

 gcd(Dt,Dg)=gcd(Dt,1+4D*Dt*s^2)=1.

As positive coprime integers whose product P is a square, Dt and Dg are separately squares. We have therefore recovered integer roots f,tau,g,ytilde with

 f^2=Df; tau^2=Dt; g^2=Dg; ytilde^2=Da.

Set y=ytilde/delta in Q. It satisfies QV^2−(Q−1)y^2=1. The adjacent-coefficient Pell descent retained in source/centered11-proof.md Section4.2 proves y integral: in lowest terms its denominator b has b^2|Q−1; the standard norm-preserving descent decreases |V| while keeping that denominator; at |V|=1 it is1. All required hypotheses Q>1 and integer V were proved before this step.

The signed factor is now an integer identity, with last root ±tau*g. Hence S|Ac.

## 3. Scalar projection and recovery of the missing main root

Write Phi_H(z)=(z^2+3H^2)(z^3−19H^3). Since H^5|Ac=Phi_H(HT+K), monic valuation comparison proves H|K. Explicitly, if p^e exactly divides H and v_p(HT+K)=b<e, the leading term z^5 has valuation5b, strictly less than the other terms3H^2z^3, −19H^3z^2, −57H^5. Thus their sum cannot be divisible by p^(5e). This works for either sign of H.

Let Kquad=X(X+2ac)−1. The universal identity

 K=HXc−2Kquad

and oddness of H give H|Kquad.

The omitted main Pell norm is recovered BEFORE using this congruence for orientation. Put B0=|a+2|, C0=|c|, I0=|I|. We already have B0>=3, 0<C0<=I0 and f^2−(B0^2−1)I0^2=1. Write |f|=chi_B0(m0), I0=psi_B0(m0); then |f|>2I0. Put rho=(B0^2−1)I0. The auxiliary norm classifies rho|V|=chi_rho(nu), |y|=psi_rho(nu), and nu is odd because even-index chi_rho is ±1 modulo rho. The quotient-polynomial identity for odd nu and V=−c modulo f give

 psi_B0(nu)=±C0 modulo |f|.

Fold nu modulo2m0 and reflect to0<=p<=m0. Since psi_B0(p)+C0<=2I0<|f|, the congruence cannot wrap and gives C0=psi_B0(p), p>=1. This is the exact absolute folding argument in source/signed-quadratic-proof.md Section2. It does not require an odd multiplier I/c^2, a sign of a,c,I,V, or the missing main projection.

We now apply ONLY the pre-projection part of the centered signed-rank argument in source/centered11-proof.md Section5.2. Its hypotheses are precisely the common-sign packing bounds, the centered C0/K0 strip above, the recovered main classification, and the first, strong and auxiliary norms. The two auxiliary residues are still

 V=−c modulo f,  V=−R modulo c,

because V+R=Delta I^2(c−R)+4I Df T and c^2|I. The nonodd strong-rank step is proved there by Lucas composition: C0^2|I0 implies p|m0 and C0|m0. Thus no invalid odd normalization is used. The conclusions BEFORE main projection are

 p=R=2t+1, t>=24;
 |Y|>(|X|−3)^t/2−1.

The whole-product proof in source/signed-quadratic-proof.md Section5 depends only on that ratio bound, H|Kquad and c=sign(c)*psi_(a+2)(R), not on the old determinant guard. It gives

 |H|>2^(2R+2)|X|^2,
 H divides (sign(c)X−2^R)(2^R sign(c)X+1).

The absolute product is smaller than |H|, so it vanishes. The odd second factor is nonzero. Hence sign(c)X=2^R. The remaining centered orientation and uniform half-binomial argument, source/centered11-proof.md Sections5.2–5.3, gives X,c,k,Y>0 and0<eta/k<1/4. Section5.4 then explicitly regenerates fresh odd strong/auxiliary witnesses and an actual old signed Q41 zero. Its pinned ordinary native/compiler/calibration theorem supplies a finite syntactic ZFC refutation.

This ordering is important: no main root is assumed to extract the initial three radicals; folding supplies its classification; rank recovery precedes the scalar whole-product projection; old positivity and odd-kernel witnesses are restored only afterward.

## 4. Completeness and the fixed-witness quantifier order

Start with the same canonical outer witness supplied by a finite syntactic refutation in the retained source theorem. Its centered half-binomial values satisfy Derr<=q^2/2,0<eta/k<1/4, Budget>q^2 k^2/4>=64. Its Dt=tau^2 is a positive square. In addition Dt=1 mod3 unconditionally, because ell=XY^2 is0 or2 mod3. Therefore D*Dt=(3Budget−4)Dt is positive and2 mod3, hence nonsquare.

Ordinary Pell existence gives g0^2−D*Dt*u0^2=1 with positive g0,u0. Squaring the unit gives g=g0^2+D*Dt*u0^2 and s=g0*u0, so g^2=1+4D*Dt*s^2=Dg. Thus P=(tau*g)^2.

Now apply the FULL-RESIDUE interpolation theorem of source/centered11-proof.md Section6 with N=2s. It chooses ONE fixed positive strong pair I,f with8s c^2|I, and for this fixed pair every class modulo I contains an auxiliary T satisfying our unchanged V and norm. Set r=I/(2sc^2).

The canonical main projection implies H|Kquad, hence H|K; write kappa=K/H. Choose a root a modulo I of pi(x+kappa), and only then use interpolation to choose T=a modulo I and an integral y. It follows that

 Ac/S=pi(T+kappa)/I is an integer.

Finally set

 n=Ac/S+f+2delta*y+4tau*g−Cshift.

This integer makes one conjugate factor vanish. The order is outer data, guard Pell s/g, fixed strong I/f/r, intersective residue and T/y, then n. No varying of the strong pair after choosing a residue is hidden here.

Consequently E8 has an integer zero exactly when the retained source theorem has a finite syntactic ZFC refutation. Composing the stated ordinary calibration gives the desired ZFC-provable equivalence of universal nonvanishing and Con(ZFC), with the same explicit formalization boundary as the source.

## 5. Optional all-radicand fusion

Keep the common prefix through Dg, but replace I by

 I=2src^2*Dt*Dg*Dm*(a+2), Dm=1+Delta*c^2.

Recompute Df,Q,delta,V,Cy,Da,S with this I. Use the uncentered Z=Sn−Ac. Two equations are

 E2int=Z^2−S^2 Df*Dt*Dg*Da=0,
 E2rat=delta*Z^2−S^2 Df*Dt*Dg*Cy=0.

Both are literal integer polynomials. E2rat has no actual division. Their exact degrees are1892 and1632, respectively, at114 operations each. The rational-cleared form is the preferred lower-degree sibling.

The I=0 specialization is Ac^2 or−Ac^2, hence nonzero. For I!=0 the same |I|>=c^2, V and Da positivity proof applies. Either equation forces Dg>0. All four positive radicands Df,Dt,Dg,Da are pairwise coprime:

 - gcd(Dt,Dg)=1 as before.
 - I is divisible by Dt*Dg, so Df=Da=1 modulo each of Dt,Dg.
 - Modulo Df, Q=−Delta, delta=−(a+2)^2, V=−c and Cy=−Dm. Thus Da=(a+2)^2 Dm modulo Df. Since I is divisible by(a+2)Dm, Df is coprime to both factors, giving gcd(Df,Da)=1.

For E2int, (Z/S)^2=Df Dt Dg Da; its rational square root is integral, and coprimality makes each factor a square. For E2rat, (delta Z/S)^2=Df Dt Dg Da gives the SAME conclusion. Once Da is a square, adjacent-Pell descent makes y=sqrt(Cy/delta) integral. The integral case has Z/S=±f*tau*g*ytilde; the rational-cleared case has Z/S=±f*tau*g*y. In either case S|Ac. The rest of soundness is exactly Section3.

For completeness, Dm and a+2 are positive fixed outer quantities; Dt and Dg are fixed before selecting I. Use full-residue interpolation with N=2s Dt Dg Dm(a+2), then set r=I/[2s c^2 Dt Dg Dm(a+2)]. The same scalar-intersective residue construction works. Choose n=Ac/S+f*tau*g*ytilde in the integral case, or n=Ac/S+f*tau*g*y in the rational-cleared case.

## 6. Degree and cost

For the principal three-root pair, degS=34, degDf=20, degQ=32, degV=25, degDa=114, degDt=34, degDg=60, degP=94, and degAc=35 (the short K has degree4). The radicands u,b,e have degrees88,182,162.

Direct Z has degree35, so the three-root norm has degree728 and leading b0^4. For the centered equation put C0=S(2Q−1)V and s0=Sn−Ac. The exact cancellation is

 b−C0^2=S^2(−V^2−4Q+4).

Consequently omega=Z^2−b has degree at most126. Rewrite the same norm as

 [(omega−u−e)^2−4(ue+b(u+e))]^2−64ube Z^2.

The inner bracket has degree344 and leading−4b0 e0, while the last term has degree614. Thus the full degree688 leading form is16b0^2e0^2. The actual leading forms are nonzero, with an explicit nonzero coefficient using only powers of2,3,beta certified in check.py. This is a universal cancellation proof, not a numerical degree sample.

The all-fused degrees follow from degI=118, degDf=248, degQ=260, degV=367, degCy=994, degDa=1254, degS=148. The unique highest product term has degree1892 or1632. Exact leading monomials with nonzero authentic coefficients are checked separately.

Every binary addition, subtraction and multiplication (including squares and scalar products) is charged. Leaves and shared reuse are free. build.py emits only integer leaves, the eleven coordinate leaves, the six authentic fixed ports and binary arithmetic nodes. check.py authenticates coefficient bytes, checks every live mathematical register against an independently transcribed polynomial, proves the entire universal norm identity, verifies topology and variable closure, and checks exact degree leading forms. No repository file is changed by reproduction.
