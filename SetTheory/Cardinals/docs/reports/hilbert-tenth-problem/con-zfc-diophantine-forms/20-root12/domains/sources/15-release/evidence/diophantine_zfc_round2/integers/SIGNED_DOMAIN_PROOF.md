# Signed-domain refinement and unrestricted-integer lifts

## Scope and exact domain

Start with the six-equation Start-only system, or its 25-equation / 34-variable quadratic presentation in `diophantine_zfc_encoding/start_only_quartic34.json`. The four compiler coefficients retain their exact fixed recipes. The present result is an algebraic/Pell-domain refinement; it does not independently replace the machine, compiler, mask, or completeness proofs.

Only the following nine coordinates need be strictly positive:

    J, F, alpha, z, i, s, w, eta, zeta.

The coordinates f, h, T, tau, y, gamma, and every added register may range over all integers. The resulting system has a solution if and only if the original all-positive system has a solution. This is an equivalence of existential statements, not a coordinatewise absolute-value bijection: in particular, a negative auxiliary root may require fresh auxiliary witnesses to restore the original positive presentation.

The same domain refinement applies to the original product polynomial P67 and reduced-coefficient P68. In that case one first recovers the unit factors with index/transport signs epsilon,nu in {+1,-1}; the proof below includes those signs. For the quadratic system they are both +1 from the outset.

## 1. Derived geometry and elementary bounds

Use the usual polynomial abbreviations:

    q=(B-1)J+1, C=q-F-alpha, X=wq, Y=sq^3, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y, A=a+2, H=4a+3,
    Delta=A^2-1, D=X+ac+gamma H,
    G=q(q-F)-C,
    R=G(q^2-1)+(MC+q MFsrc)J,
    rho=Delta i c^2, V=c(Tf-1)-Rf^2.

Thus q>=16, X>=q, Y>=q^3, E>=q^4, k,c,a,Delta,rho are positive before using f,h,T,gamma. Moreover rho>1. On the 34-variable system its gate equations uniquely enforce these expressions; no sign restriction on a derived gate is needed.

For P67/P68, Delta>0 permits the usual proof-only cancellation of Delta. The consecutive-product negative-norm lemma, Delta=0 or3 modulo4, and rho^2 being a square force the first, main, strong and auxiliary norm factors all to +1. Only the index and transport factors can initially have signs epsilon,nu, with epsilon nu=1. This uses none of the signs now relaxed.

The transport equation or unit gives C>=0, since

    q-F-z(q-1)=1-F-(z-1)(q-1)<=0.

Consequently q-F=C+alpha>0. The authentic mask ranges 0<MC,MF_native<B-1 and MFsrc=MF_native+B-1 imply the inherited weak bounds

    q(q^2-1)<R<q^4-q^3+q^2-1<q^4-2,
    R-2>3q+1, E>R+2, a>R+2.

These are established before mask decoding, dyadic q, or a sign assertion for h or gamma. If the transport factor is already +1, then C>0 immediately. The preliminary C=0 boundary for the product formulation is retained until nu=+1 is recovered.

## 2. The index quotient h is automatically positive

The index equation is k=R+epsilon+hE. Since k>0 and E>R+2, h>-1, hence h>=0. Suppose h=0. Put u=XY^2. Then

    2<k=R+epsilon<q^4<=q^7<=u,
    tau^2=u(u+1)k^2+1.

There is no integer solution of this norm for 2<k<u. This follows from the standard first positive Pell coefficients 2 and 8u+4, but also has the following elementary consecutive-square proof. If k=2r with r>=2, then

    u(u+1)k^2+1=(uk+r)^2-(r^2-1),

which lies strictly between (uk+r-1)^2 and (uk+r)^2 because 0<r^2-1<2(uk+r)-1. If k=2r+1, it lies strictly between (uk+r)^2 and (uk+r+1)^2: the lower difference is uk+1-r^2>0 and the upper difference is uk+r^2+2r>0. These inequalities follow from k<u. Contradiction. Thus h>0.

## 3. Strong and auxiliary Pell classification without signs of f,T,V,y

The strong norm gives

    f^2=1+Delta i^2 c^4,
    |f|>c^2>2c,
    |f|=chi_A(m), psi_A(m)=i c^2

for m>0. Write c=psi_A(p) and |D|=chi_A(p), p>0; these hold regardless of D's sign. The first norm similarly gives |tau|=chi_(2XY^2+1)(n), k=2psi_(2XY^2+1)(n), n>0. The standard first/main growth comparison gives p>n. As 2n=R+epsilon modulo E and 0<R+epsilon<E, n>=(R-1)/2>=24. Hence c>2p. Since h>0 and E>R+2, k>2R and c>2R.

Strong divisibility gives p|m. Write m=pb. Dividing the square-root coefficient of (chi_A(p)+c sqrt(Delta))^b by c and reducing modulo c gives

    psi_A(pb)/c = b chi_A(p)^(b-1) modulo c.

Its left side is divisible by c and gcd(chi_A(p),c)=1, so c|b. Thus pc|m and m>2p. This is the direct normalized-strong rank argument, not the older relaxed-rank theorem.

The auxiliary norm is

    rho^2 V^2-(rho^2-1)y^2=1.

V=0 is impossible. Since V=-c modulo f and |f|>2c>4, V=+1 and V=-1 are impossible as well. Also y=0 would imply rho^2 V^2=1, impossible because rho>1. Put v=|V|>1 and sigma=sign(V). Ordinary Pell classification gives

    rho v=chi_rho(ell), |y|=psi_rho(ell), ell>0.

The index ell is odd because the even-index first coordinate is +1 or -1 modulo rho. Write ell=2u+1 and use the integer quotient polynomials

    chi_Z(2u+1)=Z Q_u(Z^2),
    Q_u(1-A^2)=(-1)^u psi_A(ell),
    Q_u(0)=(-1)^u ell.

Since rho^2=Delta(f^2-1)=1-A^2 modulo |f| and c|rho, while f^2=1 modulo c, the defining V expression gives

    Q_u(rho^2)=v,
    (-1)^u psi_A(ell)=-sigma c modulo |f|,
    (-1)^u ell=-sigma R modulo c.

Squaring the first congruence and applying the Pell doubling identity gives

    chi_A(2ell)=chi_A(2p) modulo chi_A(m).

The standard plus step-down lemma, with 0<2p<m, gives ell=+p or-p modulo m, therefore modulo c. The second congruence then gives R=+p or-p modulo c. Since 0<R,p<c/2, p=R. Crucially, both appearances of sigma disappear in the signed target conclusion. Neither T>0 nor V>0 nor a positive auxiliary quotient is used.

The ordinary no-wrap argument now gives 2n=R+epsilon. If epsilon=-1, Pell duplication forces c>k(Y+1), contrary to kY<c<k(Y+1). Thus epsilon=nu=+1, R is odd, and C>0. These steps are unchanged by the signs of f,T,gamma.

## 4. The main root and gamma are automatically positive

Put r=(R-1)/2>=24. The standard lower-ratio argument uses only the first/main Pell magnitudes and kY<c<k(Y+1); it gives

    Y>X^r/3, a>X^(r+1)/3, 2^R<a, X<a.

In fact a>X 2^R because (X/4)^r>6 for X>=16,r>=24. Let

    e_R=chi_A(R)-a psi_A(R).

The Pell projection recurrence gives e_R=2^R modulo H. Also

    (chi_A(R)-ac)(chi_A(R)+ac)=1+Hc^2=1 modulo H.

If D=-chi_A(R), the defining equation D=X+ac+gamma H gives chi_A(R)+ac=-X modulo H. Multiplying the two congruences forces X 2^R+1=0 modulo H. But

    0<X 2^R+1<a+1<H,

a contradiction. Hence D=chi_A(R)>0. The projection equation now gives X=2^R modulo H; since both are in (0,a), they are equal. Finally

    e_R=2c-psi_A(R-1)>c>X,
    gamma=(e_R-X)/H>0.

The inequality c>X follows already from R>=3, c=psi_A(R)>A>a>X. Thus gamma is positive on every mixed-domain solution.

## 5. Decoding, converse, and limits

After X=2^R, all power extraction, inverse population, field recovery, and native mask decoding use only J,F,alpha,z,s,w,eta,zeta and the recovered positive geometric quantities. They do not use a sign of f or T. In particular, no assumed R=3 modulo4 is needed for soundness. Decoding yields a genuine blank K215 computation. Conversely, the original completeness proof supplies all-positive witnesses from any such computation, and those are valid mixed-domain witnesses. Optional restoration of positive auxiliaries may be done after decoding; it is not needed to justify the domain extension.

Therefore the mixed-domain system and product polynomial have exactly the same existential truth value as the original positive construction. Together with the inherited compiler theorem, ZFC proves that their absence of solutions is equivalent to Con(ZFC). This is an ordinary proof intended to formalize in ZFC, not a claim of a new Lean/Rocq-checked Diophantine theorem.

## 6. Three signed coordinates represent every positive integer

Define Pos(x,y,z)=1+x^2+y^2+z(z+1). It is positive for all integers. For n>=1, 4n-3 is 1 modulo4 and cannot have Legendre's excluded shape 4^a(8b+7). By the three-square theorem it has exactly one odd root and two even roots. Write these 2z+1,2x,2y, respectively, and divide by4 to obtain n=Pos(x,y,z). The exact representation theorem is also formalized in the Archive of Formal Proofs: https://isa-afp.org/entries/Three_Squares.html .

Replacing each of the nine positive original coordinates by a separate Pos gives:

- Original 15-coordinate compact polynomial: 33 unrestricted integer variables.
- Original 34-coordinate quadratic system: 52 unrestricted variables and 25 residual equations of degree at most4; their squared sum is one polynomial of exact degree8.
- Retaining the 34 original coordinates and adding nine Pos relations: 61 unrestricted variables and 34 quadratic equations; their squared sum is one exact quartic.

The degree8 assertion follows from the J^2 term in the first residual after substitution; the quartic assertion follows from any positivity residual's squared quadratic leading part. Sums of squares of real homogeneous polynomials cannot identically cancel. These are exact explicit upper bounds, not minimality claims.

## 7. Transfer to ordinary strong coordinates and smaller eliminations

For `quadratic/ordinary_quartic33.json`, replace the normalized strong block by I=i c^2 and I^2=Delta(f^2-1), and put rho=I. No pointwise substitution i_normalized=i_ordinary/Delta is used. Section3 first proves the main/first size bounds without the strong block: n>=24, p>n, and standard Pell growth imply c>A Delta^2. The inherited ordinary-strong rank theorem therefore applies to i>0 and |f|. It yields

    |f|=chi_A(m), I=Delta psi_A(m), p|m, c|m, m>=c>2p.

Moreover f^2-1=I psi_A(m), so c^2 divides f^2-1. Thus rho^2=-Delta modulo |f|, c|rho, and V=-c modulo |f|, V=-R modulo c hold exactly as in Section3. Also |f|>2c follows from f^2=1+i^2 c^4/Delta and c>A Delta^2. The signed auxiliary rank proof and Section4 are unchanged. Completeness maps the original normalized witness to i_ordinary=Delta i_normalized. Therefore this ordinary33 system also needs positivity only at the same nine ports.

Its exact lifts have 60 unrestricted variables and33 quadratic equations (one quartic), or51 unrestricted variables and24 degree-at-most4 equations (one degree8 polynomial).

The same transfer applies to the ordinary six-factor product, not only its system. Before using any strong equation, Qordinary=Delta(f^2-1) is0 or1 modulo4 for every signed f because Delta is0 or3 modulo4. Its strong factor 1+I^2-Qordinary can therefore never be-1, and its auxiliary factor Qordinary(V^2-y^2)+y^2 is congruent to a square modulo4 and also cannot be-1. The product's integer-unit argument thus first forces both factors to+1, restoring Qordinary=I^2 and precisely the ordinary system used above. The remaining index and transport signs are recovered by Section3 as before.

The exact register eliminations in `quadratic/start_only_sextic25.json` and `quadratic/ordinary_octic20.json` are polynomial identities over all integers. Their sign-restricted arguments are needed only to preserve the all-positive presentation, not for the mixed-domain one: all eliminated registers are free. The first-root shear tau=t+E(c-eta) is an affine bijection of the unrestricted root coordinate t, regardless of its sign. Consequently the same nine positive-port condition applies after those eliminations as well. Explicit substitution and computed degree/variable counts are recorded in the accompanying JSON packets and verification receipt.

## 8. A 32-integer norm-eliminated form

The 14-coordinate construction in `pell/start_only14_polynomial75.json` eliminates f. It retains the same nine positive ports and allows h,T,tau,y,gamma to be arbitrary integers. Its norm reconstruction uses

    d=1+Delta i^2 c^4, Q=Delta(d-1), b=c+Rd, u=cT,
    A=Q(du^2+b^2-y^2)+y^2-1,
    Bcross=2Qub, Hnorm=A^2-d Bcross^2.

The product's unit argument forces Hnorm=0 even for signed T,y: Hnorm+1=A^2+1 modulo4 and cannot equal-1. The first/main and transport estimates are unchanged, giving Delta>R, c>2 and d>Delta+c. Hence

    b>1, Q-b=(Delta-R)d-Delta-c>0.

If T=0, then u=Bcross=0 and Hnorm=0 implies A=0, or

    Q b^2-(Q-1)y^2=1.

Because b>1 and Q>1, this equation forces y^2>b^2, hence |y|>=b+1. Then b^2-1=(Q-1)(y^2-b^2)>=(Q-1)(2b+1), which forces b>=2Q-1. This contradicts b<Q. Thus T is nonzero, Bcross is nonzero, and f=A/Bcross is rational with f^2=d. A rational square root of an integer is an integer, so signed f is restored. The rest of the signed-domain proof applies exactly. Completeness is inherited from the positive14 construction.

Nine separate Pos substitutions therefore give a literal polynomial in32 unrestricted integers, with138 binary operations and exact degree584. The larger degree is a genuine tradeoff for deleting one variable; it does not dominate the33-variable compact polynomial.

## 9. Signed root shears and a 33-integer degree159 polynomial

On unrestricted roots, both substitutions tau=L+t and y=V+e are affine bijections with integer polynomial inverses. They need no positive-gap proof. Therefore the ordinary strong polynomial with both shears, `pell/start_only_ordinary_sheared71.json`, inherits the same nine-positive-port theorem. Its nine Pos substitutions produce33 unrestricted variables,134 binary operations, and exact degree159.

The source weighted degrees, assigning weight2 to the nine positive ports and weight1 to every other witness, are24,35,39,13,4,44 for its six factors. Their sum is159. A nonzero degree159 leading monomial is

    J^46 h gamma i^2 eta^8 w^6 s^13 T f^3 e z,

with coefficient16 beta^46. Replacing each positive port by its disjoint Pos form preserves this monomial by selecting the square of its first new coordinate. Thus the exact degree holds at every authentic beta>0, not just at sampled compiler constants.

## 10. Uniform exact-degree certificates on the authentic coefficient slice

These degree claims do not rest on the dense diagnostic fixtures. Give the nine positive original ports weight2 and all signed original ports weight1; fixed coefficients have weight0. Write

    Q0=beta J, k0=eta+zeta,
    T2=w(Q0-F-alpha)-z Q0.

The relevant weighted leading forms of the three compact products are as follows. Their factors are ordinary nonzero polynomials in independent original coordinates whenever beta>0.

For P67, with factor weighted degrees44,35,116,13,4,92, the degree304 leading form is

    -8 Q0^91 h gamma i^4 k0^13 w^13 s^26 T^2 f^2 T2.

In particular the monomial

    J^92 h gamma i^4 eta^13 w^13 s^26 T^2 f^2 z

has coefficient8 beta^92 and weighted degree304.

For the root-eliminated P14, with factor weighted degrees44,35,13,4,488, the degree584 leading form is

    8 Q0^177 (Q0-F)^4 h gamma i^12 k0^27 w^21 s^48 T2.

The monomial

    J^182 h gamma i^12 eta^27 w^21 s^48 z

has coefficient-8 beta^182 and weighted degree584. Here the top term of the new norm is A^2: Qaux and d have degrees92 and68, b has degree76, A has degree244, and the subtracted cross term has strictly smaller degree. Thus no hidden norm cancellation changes this leader.

For the doubly sheared ordinary product, with factor weighted degrees24,35,39,13,4,44, the degree159 leading form is

    -16 Q0^45 h gamma i^2 k0^8 w^6 s^13 T f^3 e T2.

This gives the coefficient16 beta^46 asserted in Section9. The signed shear variables t and e have weight1. Consequently the degree24 first-factor leader is -L k0, not the full positive-degree leader L(2t-k0); retaining the old unweighted leading form without this weight adjustment would be incorrect.

The fixed ports K,MC,MF occur only below these leading weighted degrees. Since the actual compiler has beta=B-1>0, every displayed coefficient is nonzero after its actual fixed coefficients are substituted. Finally, the leading homogeneous part of Pos(a,b,c) is a^2+b^2+c^2. Substituting these disjoint blocks into a nonzero weighted leader is injective: specialize all b,c to0, obtaining the injective monomial map x to a_x^2 for positive ports and leaving signed ports unchanged. The displayed nonzero leaders therefore survive the integer-domain conversion, uniformly at the authentic fixed coefficient values. The independent checker supplies matching exact formal-cut upper bounds; dense specializations are only an additional lower-bound cross-check.

