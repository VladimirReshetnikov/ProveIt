# Eleven integers: main-radicand square-root saturation

## Result and boundary

This package gives a new two-root arithmetic reduction. The primary literal equation `free_main_saturated11_sharp.json` has eleven unrestricted integer variables, exact total degree 352, and 132 live binary arithmetic operations. Companions have degree/cost pairs 376/127 and 364/131. The weak-scale companions have 428/123, 412/127, and 396/128. All retain the same six authenticated source34 numeral payloads, including already shifted MF. No ten-variable endpoint, proof of consistency, global optimum, new encoded object-ZFC derivation, or end-to-end proof-assistant certificate is asserted.

The new ingredient is square-root saturation by the previously omitted main Pell radicand. It makes THREE radicands pairwise coprime without putting the entire main radicand into the strong ordinate. A quadratic norm then replaces the old octic. A sharp integral center cancels two full powers of the Pell base. The free-scale carrier and strengthened budget are credited to the concurrent fifteen-variable free-scale construction, retained at source/FREE_SCALE_PROOF.md. Here its weak quintic projector requires a strictly stronger fifth-power size argument, supplied below.

The old ordinary native/compiler/finite-refutation calibration is inherited only after recovering all its explicit arithmetic hypotheses. Its unbounded dependencies are retained in source/ and pinned in SOURCE_PINS.json. Finite audits certify identities, literal graphs, fixed numerals and degrees, not those unbounded theorems.

## 1. Complete equation

The unknowns j,C,z,h,r,v,w,T,c,n,s range over all integers. The fixed ports are beta,K0,MC,MF,cone_A,cone_B. In particular beta=2^1064921-1, cone_A=2^1113, and cone_B=2^666104. Every other name below is a polynomial abbreviation, not another unknown.

    J=6j+1, q=beta J+1, W=12w+4, X=qW, Y=v,
    E=XY, a=E+Y, A=a+2, H=4a+3, Delta=a^2+H=A^2-1,
    F=(K0+W)C-z(q-1),
    R=(q(q-F)-C)(q^2-1)+(MC+q MF)J,
    k=R+1+hE, eta=c-Yk,
    Derr=(cone_A F-q)^2+(cone_B C-q)^2,
    B0=k^2(q^2-Derr)-4q^2 eta^2,
    Budget=Y^2 B0-k^2 q^8,
    ell=XY^2, L=ell k, Dt=1+L(L+k),
    D=3Budget-4, Dg=1+4D Dt s^2,
    P=Dt Dg=Dt+(12Budget-16)(Dt s)^2,
    Dm=1+Delta c^2, Ub=rc^2, U=A Ub,
    Df=1+Delta U^2 Dm, Q=Delta^2 U^2 Dm, delta=Q-1,
    V=Df(c-R+4U Dm T)-c, Cy=QV^2-1, Da=delta Cy,
    K=X(3c-2X)+2,
    M=2q^3, Dc=HM, S=srH M^5,
    zc=Dc T+M K+H(Y-q^3),
    Ac=(zc^2+3Dc^2)(zc^3-19Dc^3),
    lambda=(2Delta+1)Ub Dm,
    Z=S(n+lambda V)-Ac.

The final equation is

    [delta Z^2+delta S^2 P-4S^2 Dm Df Cy]^2
       -4 delta^2 S^2 P Z^2 = 0.                       (1)

It contains no division, radical, variable exponent, or implicit witness. Direct and simply centered variants replace lambda V by 0 and 2A U Dm V respectively. These are integer polynomial translations of n, so preserve zero-existence with exact inverse maps.

For the weak-scale family replace Y=v by Y=qv, Budget by B0, M by 2q^2, and Y-q^3 in zc by v-q^2. All other definitions remain unchanged. Its projection proof is given separately below.

## 2. Unconditional bootstrap and the two-root identity

The authentic tuple gives q even, q=2 modulo 3, |q|>=beta-1>=16, X=0 modulo 8, X=2 modulo 3, and |X|>=4|q|. H is odd and nonzero. If Y=0 then a=0, A=2 and Delta=3. Otherwise |a|>=|X|-1>=63, so again Delta>1 and A is nonzero. Hence Dm>=1 and Df>=1. Since A and Delta=A^2-1 cannot both be odd, Delta A is even; therefore Q is divisible by 4, delta is odd and never zero, and Df=1 modulo 4. No parity of Y is assumed yet. Dt>=1 because Dt=1+ell(ell+1)k^2, and Dt is odd because 8 divides X. Dg and P are odd, hence nonzero.

The zero-free intersective polynomial pi(t)=(t^2+3)(t^3-19) has no rational root. Thus Ac=Dc^5 pi(zc/Dc) is nonzero. At S=0, (1) is delta^2 Ac^4, nonzero. Every zero therefore has r,s nonzero.

Da is strictly positive. If c=0, U=Q=0 and Da=1. If c!=0, |U|>=2c^2 and Df>|c|+1. With b=c-R+4U Dm T, either b=0 and |V|=|c|>=1, or |V|>=Df-|c|>1. Thus Q>1, Cy>0 and Da>0.

For delta!=0, (1) is delta^2 times the product of the four complex factors

    Z +/- 2S sqrt(Dm Df Cy/delta) +/- S sqrt(P).

The first radicand equals Dm Df Da/delta^2 and is strictly positive. If P were negative, its radical would be the only nonzero imaginary term, contradicting vanishing of a factor. Hence P>0, Dg>0. Since s!=0 and Dt>=1, Budget<=1 would give Dg<=-3. Thus Budget>=2.

For the free-scale equation, Budget>0 gives k!=0, Y!=0 and B0>0. Since B0<=k^2q^2,

    Y^2 B0>k^2q^8 implies |Y|>|q|^3.

The standard centered-budget inequalities now follow from B0>0: Derr<q^2, |c/k-Y|<1/2, and F,C,q-F-C have q's common nonzero sign. In particular c!=0. The authentic packing bounds give

    |q|(|q|^2-1)<R<|q|^4-2.

## 3. Two squareclasses and three coprime factors

Multiply a normalized vanishing factor by delta. It says that a signed sum of

    2 sqrt(Dm Df Da),       delta sqrt(P)

is rational. P is positive and odd, while delta is odd. In any common nontrivial squarefree class, the second root's integer coefficient is odd; the first coefficient is even (even if Dm itself has square factors of two). Thus the terms cannot cancel. If their squareclasses differ, independence of distinct squarefree radicals excludes cancellation as well. Therefore Dm Df Da and P are integer squares.

The THREE factors Dm,Df,Da are pairwise coprime. Modulo Dm, Df=1 and Q=0, so Da=1. Modulo Df,

    Q=-Delta, delta=-A^2, V=-c, Cy=-Dm, Da=A^2 Dm.

Since A divides U, Df=1 modulo A. Since also gcd(Dm,Df)=1, this proves gcd(Df,Da)=1. Positivity therefore makes each of Dm,Df,Da a square. Write

    d^2=Dm, f^2=Df, e^2=Da

with positive roots. Also gcd(Dt,Dg)=1, so Dt=tau^2 and Dg=g^2, with sqrt(P)=tau g.

Define only in the proof

    I=U d, T_old=dT.

These are integers and satisfy c^2|I. For c!=0, I!=0, Q=(Delta I)^2>1, and the exact strong and auxiliary formulas are

    f^2=1+Delta I^2,
    V=f^2(c-R+4I T_old)-c.

The rational y=e/delta solves QV^2-(Q-1)y^2=1 and is integral by the retained adjacent-Pell denominator descent. Briefly, for reduced denominator b, b^2 divides Q-1; the map V'=(2Q-1)V-2(Q-1)y, y'=(2Q-1)y-2QV preserves integrality of V and the denominator b, and after signs decreases |V| until |V|=1, where |y|=1. In the exceptional c=0 case, Q=0, delta=-1 and y=-1 is already integral.

Hence the factor equation has integral normalized roots 2dfy and tau g, giving S|Ac. This conclusion also holds in the c=0 branch, which is needed for the weak-scale variant's early CRT argument.

## 4. Free-scale carrier, parity, and signed rank recovery

From S|Ac we have M^5|Ac. If p^e exactly divides M and v_p(zc)=b<e, the term zc^5 has valuation 5b, strictly lower than the other three terms of

    Ac=zc^5+3Dc^2 zc^3-19Dc^3 zc^2-57Dc^5.

This contradicts p^(5e)|Ac. Thus M|zc, giving

    M | H(Y-q^3).

Its 2-primary part and oddness of H prove that Y is even. We do NOT infer gcd(H,q)=1 yet. Also H|Ac gives H|(M K)^5. Put Kq=X(X+2ac)-1. The identity

    K=HXc-2Kq

and oddness of H give

    H | (q^3 Kq)^5.                                    (2)

The retained signed rank proof now has its complete pre-projection hypotheses: |Y|>|q|^3, the centered strip and common signs, first and strong Pell norms, the main Pell root d, c^2|I, and residues V=-c modulo f and V=-R modulo c. The second follows from V+R=Delta I^2(c-R)+4I Df T_old. In particular |XY|>3R+1, so its first-index congruence is unchanged. It yields main index p=R, first index (R+1)/2, and

    R=2t+1, t>=36,
    c=sign(c) psi_A(R),
    |Y|>(|X|-3)^t/2-1,
    |H|>|X|(|X|-3)^t.

The source often states only t>=24. The stronger t>=36 used here follows immediately from R>|q|(|q|^2-1)>=4080. Its nonodd strong-rank lemma uses c^2|I, never an oddness assumption on I/c^2. No main projection has been used to obtain these conclusions.

## 5. Stronger fifth-power whole-product projection and late CRT

Let x=|X|, sigma=sign(c), and

    Pi=(sigma X-2^R)(2^R sigma X+1).

The signed Pell projector congruence is 2^R Kq=Pi modulo H. From (2), and odd H, we obtain H|q^15 Pi^5. Each factor of Pi has absolute value less than 2^(R+1)x. Therefore

    |q|^15 |Pi|^5 < 2^(20t-10) x^25,
    |H|>x^(t+1)/2^t.

Here |q|<=x/4 and R=2t+1 were used. The actual x>=4(beta-1)>=2^64 and t>=36 give

    64(t-24)-(21t-10)=43t-1526>=22>0.

Consequently |q|^15|Pi|^5<|H|. The divisible integer is zero. Since q!=0 and the odd second factor of Pi is nonzero, sigma X=2^R.

Now q divides X, so |q| is a power of two. H is odd, hence gcd(H,M)=1. The earlier divisibility M|H(Y-q^3) finally gives M|Y-q^3. Thus

    Y=(2v_old+1)q^3, v_old=(Y-q^3)/(2q^3) in Z.

Also the exact projector implies H|Kq and H|K. Since X=2 modulo 3 and R is odd, sigma=+1 and X=2^R. The inherited surviving first-index sign gives k>0 and then Y>0. Its uniform centered half-binomial theorem now applies with exactly the restored cubic scale and gives 0<eta/k<1/4. Fresh strong/auxiliary private witnesses restore an actual old signed Q41 zero as in source/centered11-proof.md Section5.4. The retained source34/native/compiler calibration supplies a finite syntactic ZFC refutation.

For clarity, the exact nonodd strong-rank result is source/centered11-proof.md Section5.2: writing |c|=psi_B(p), |I|=psi_B(m), c^2|I first gives p|m; composition then gives c|m/p, hence c|m and m>2p. This is the version applied to I=Ud and the exact restored V=f^2(c-R+4I T_old)-c. No odd-multiplier result is substituted here. After orientation, the literal restoration in its Section5.4 keeps the outer coordinates and constructs fresh I_star=psi_A(Rc), f_star=chi_A(Rc), rho_star=Delta I_star. Since A is even and R,c odd, I_star and rho_star are odd; composition gives c^2|I_star. Thus r_old=(rho_star/c^2-1)/2 is integral. With t=(R-1)/2 and the odd quotient polynomial Q_t(z^2)=chi_z(2t+1)/z, choose V_star=(-1)^(t+1)Q_t(rho_star^2) and y_star=psi_rho_star(R). The exact congruences V_star=-c modulo f_star^2 and V_star=-R modulo c give integral o_star=(V_star+c)/f_star and j_star=(V_star+R)/c. They restore the old rows V_star=f_star o_star-c=c j_star-R and k=1-V_star+c j_star+hE. The established positive eta and k-eta supply the old positivity witnesses, while 2^((R-1)/2) restores its square coordinate. These are fresh private witnesses, not a claim that incoming I/c^2 was odd. Only this actual old zero is passed to the retained native/compiler calibration.

For the weak-scale family, q divides Y from the start, hence H=3 modulo q and gcd(H,M)=1. Section4's valuation argument directly yields M|v-q^2 and H|K^5. Thus the original cubic scale is recovered before excluding c=0: B0>0 and |c/k-Y|<1/2 then exclude that branch. The retained fifth-power projection bound, without the q^15 factor, applies verbatim. No strengthened budget is needed in this variant.

## 6. Completeness with the strong pair fixed

Begin with the canonical native outer witness from a finite syntactic refutation. In the free-scale family set v equal to its canonical Y; in the weak family set v=q^2(2v_old+1). The front-end values Y,F,R,k,c,A,H,Delta remain unchanged. The canonical data have Dm=d^2, A even positive, c=psi_A(R)>0, R=3 modulo4, c=R modulo4, Dt=tau^2, and B0>q^2k^2/4. They also have Y>X=2^R>4q^3. Hence

    Budget=Y^2 B0-k^2q^8
           >k^2q^2(Y^2/4-q^6)>64.

For the weak family its Budget=B0 also exceeds64. Because X=2 modulo3, ell=XY^2 is0 or2 modulo3 and Dt=1 modulo3. Therefore (3Budget-4)Dt is positive and2 modulo3, a nonsquare. A positive Pell unit, squared once, gives s,g>0 with g^2=1+4D Dt s^2.

Now d,A,c,s are fixed. Choose ONE positive strong Pell pair I,f with

    4s A d c^2 | I, f^2-Delta I^2=1,

using the retained finite-period construction. Set r=I/(A d c^2) and U=I/d. Keep this strong pair fixed. Every prime dividing d s r divides I. The supported-modulus interpolation theorem retained in source/POWERED_SATURATION_PARENT.md Section5 therefore realizes every T_old residue modulo d s r for this same pair.

The canonical projector gives H|K; put kappa=K/H. Write v_old for the original cubic-scale coordinate. In either family,

    zc=HM(T+kappa+v_old),
    Ac=(HM)^5 pi(T+kappa+v_old),
    Ac/S=H^4 pi(T+kappa+v_old)/(sr).

Choose an intersective root a0 for pi(a0+kappa+v_old) modulo sr. Prescribe

    T_old=d a0 modulo d s r.

Supported interpolation supplies such T_old and an integral y. Define T=T_old/d, an integer with T=a0 modulo sr. Then the displayed Ac/S is integral, and 4I T_old=4U Dm T is precisely the new auxiliary coefficient. Finally choose

    n=Ac/S+2dfy+tau g-lambda V,

or use the corresponding direct/simple shift. One norm factor vanishes.

The order is outer data, guard s/g, one fixed strong I/f/r, intersective residue, interpolated T_old/y and T, then n. No strong pair is changed after selecting a residue. This proves completeness. Together with soundness and the explicitly retained ordinary calibration, universal nonvanishing over Z^11 is ZFC-provably equivalent to syntactic Con(ZFC).

## 7. Exact degree and costs

For the free-scale sharp equation the important degrees are

    a3, Delta6, k5, B0_14, Budget18, Dt18, P56,
    Dm8, Ub3, U6, Df26, Q32, V41, Cy114,
    M3, Dc6, S20, Ac35, lambda17, Z78.

For weak-scale they are respectively a4, Delta8, k5, Budget16, Dt22, P62, Dm10, Ub3, U7, Df32, Q40, V50, Cy140, M2, Dc6, S16, Ac35, lambda21, Z87.

Write W0=Sn-Ac. The exact sharp-center identity is

    lambda^2-4Dm Df = Dm^2 Ub^2-4Dm.

Consequently the inner bracket of (1) equals

    delta W0^2+2delta S lambda V W0+delta S^2 P
    +S^2{[delta(Dm^2 Ub^2-4Dm)-4Dm Df]V^2+4Dm Df}.

Its unique highest-degree term is S^2 Q Dm^2 Ub^2 V^2, of degree176 in the free family and198 in the weak family. Every other displayed contribution has lower degree. The final correction4delta^2 S^2 P Z^2 has degree316 or348, below352 or396. Thus the claimed exact degrees follow.

A completely explicit attained leading monomial for the free sharp equation is

    j^124 w^64 v^64 s^4 r^24 c^68 T^4

with coefficient 2^288 3^188 beta^124>0. Its exponents sum to352. The weak sharp monomial replaces j^124 by j^168 and has coefficient2^332 3^232 beta^168>0, total degree396. No generic-coefficient assumption is used.

For the simple center lambda=2A U Dm, the exact difference is 4U^2Dm^2-4Dm, giving degrees364/412. For the direct equation the unique leading term is (4S^2 Dm Df Cy)^2, giving376/428. The audit independently propagates attained leading monomials through every gate, using the proved cancellation cut only at the inner bracket.

Each binary addition, subtraction, or multiplication costs one; scalar products and squares are charged, while literal leaves and reuse are free. All eleven variables and all six actual numeral ports are live. The selected literal files have no uncounted abbreviations. Normal and optimized-Python audits test local free-ring bindings, complete four-conjugate identity, coprimality remainders, rescaling and center identities, topology, liveness, exact attained degree, and complete coefficient payload/recipe bindings.

The literal strengthened guard uses the exactly equal schedule Budget=(Yk)^2(q^2-Derr)-q^2[4(Y eta)^2+(k q^3)^2], and L=E(Yk). These identities share existing arithmetic and account for the final operation counts; they do not change the mathematical polynomial. The weak simple and sharp forms are dominated by the free direct form and are retained as audited comparisons, not frontier claims. The new nondominated pairs are428/123,376/127,364/131,352/132.
