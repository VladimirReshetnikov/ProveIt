# Two rational square conditions with a nonzero center

## Result and scope

The short-index construction below is a fixed polynomial in eleven unrestricted integers of exact degree810 with112 live binary arithmetic operations. Its weak-scale companion has degree654 with117 operations. A native-index cubic-scale comparison has degree906 with111 operations but is dominated by the separate degree882/110-operation product equation and is retained only for transparent comparison.

The new mechanism removes the A Dm saturation from the incoming three-factor coprime product and instead uses a denominator-cleared two-square identity. A nonzero-center argument, rather than fixed prime-separating weights, individually recovers both rational squares. The inherited signed source calibration is unchanged. These are ordinary arithmetic proofs, not new kernel-checked or object-ZFC derivations, and no global minimum or proof of consistency is claimed.

## 1. Full polynomial and its two scale choices

The variables are j,C,z,h,r,v,w,T,c,n,s, all unrestricted integers. The six fixed numeral ports beta,K0,MC,MF,cone_A,cone_B are exactly the full payloads in coefficients/. In particular beta=2^1064921-1, cone_A=2^1113, and cone_B=2^666104. The compiler coefficient MF is already shifted. No port is quantified.

Define

    J=6j+1, q=beta J+1, W=12w+4, X=qW,
    F=(K0+W)C-z(q-1),
    R=[q(q-F)-C](q^2-1)+(MC+q MF)J.

For the degree810 equation use

    Y=(2v+1)q^3, index_modulus=4q^4.

For the degree906 comparison use the same Y but index_modulus=XY. For the degree654 weak-scale equation use

    Y=qv, index_modulus=XY.

Continue, in all cases, with

    E=XY, a=E+Y, H=4a+3, Delta=a^2+H=(a+2)^2-1,
    k=R+1+h index_modulus, eta=c-Yk,
    Derr=(cone_A F-q)^2+(cone_B C-q)^2,
    Budget=k^2(q^2-Derr)-4q^2 eta^2, D=Budget-4,
    ell=XY^2, Dt=1+ell(ell+1)k^2,
    Dg=1+D Dt s^2, P=Dt Dg,
    U=rc^2, Df=1+Delta U^2 P,
    Q=Delta^2 U^2 P, delta=Q-1,
    b=c-R+4UPT, V=Df b-c, Cy=QV^2-1,
    K=X(3c-2X)+2.

For the cubic-scale equations set

    S=srH, zc=HT+K,
    Ac=(zc^2+3H^2)(zc^3-19H^3).

For the weak-scale equation set

    M=2q^2, Dc=HM,
    S=srH M^5,
    zc=Dc T+MK+H(v-q^2),
    Ac=(zc^2+3Dc^2)(zc^3-19Dc^3).

Finally define, for every variant,

    Z=S(n+V)-Ac, Aux=S^2 Cy, Guard=S^2 P Df,
    Inner=delta(Z^2-Guard)-Aux,
    Ftwo=Inner^2-4delta Aux Guard.                      (1)

Equation Ftwo=0 is the complete ordinary integer polynomial. The literal graph computes P=Dt+D(Dt s)^2, U=rc^2, UP=UP, strong=(Delta U)UP, Df=strong+1 and Q=Delta strong; all are exactly the displayed polynomials. Symbols are abbreviations, not new unknowns. There are no divisions, radicals, variable exponents or unresolved ports in the graph.

## 2. Unconditional facts and the new parity guard

The fixed tuple and affine definitions give q even, q=2 modulo3, |q|>=beta-1, X=0 modulo8, X=2 modulo3 and |X|>=4|q|. H is odd and nonzero. For cubic Y, |Y|>=|q|^3 and Delta>1. For weak Y, if v=0 then Delta=3; otherwise |a|=|(X+1)qv| is much larger than4, again giving Delta>1. No nonzero-Y assumption is made yet in the weak case.

Since ell is an integer, ell(ell+1)>=0 and Dt>=1. Since X is a multiple of8 and Y is even in both scales, ell is a multiple of32; in particular Dt=1 modulo4. The cone coefficients are divisible by16 and q is even, so

    Budget=-(qk)^2 modulo16,
    Budget=0 or12 modulo16,
    D=12 or8 modulo16.                                (2)

For explicit verification, Budget+(qk)^2 equals

    k^2[2q(cone_A F+cone_B C)-(cone_A F)^2-(cone_B C)^2]
        -4q^2 eta^2,

whose terms are all divisible by16. Thus D is a multiple of4, is nonzero and is never a square. Consequently

    Dg=1 modulo4, P=1 modulo4, P!=0.

Since Delta>1, Df=1+Delta U^2 P never vanishes, Q can never be1, and Cy=QV^2-1 never vanishes. In particular delta!=0. These claims do not presuppose P>0 or a Pell interpretation.

The scalar quintic pi(t)=(t^2+3)(t^3-19) has no rational root. With the nonzero denominator d=H or Dc, Ac=d^5 pi(zc/d) is therefore nonzero. If S=0, (1) is delta^2 Ac^4, nonzero. Every zero has S!=0 and hence s,r!=0. This does not yet prove c!=0.

## 3. The zero-center obstruction

At Z=0 the exact polynomial identity is

    Ftwo=S^4(Cy-delta P Df)^2.                          (3)

Suppose Ftwo=0 and Z=0. Then Cy=delta P Df. Since Q is divisible by P, Cy=-1 modulo P. The right side is divisible by P, so P divides1. The congruence P=1 modulo4 excludes P=-1; hence P=1. Now Dt is a positive integer and P=Dt Dg=1, so Dt=Dg=1. The equality Dg=1+D Dt s^2 then forces D=0, contradicting (2). Therefore

    Z!=0                                               (4)

at every integer zero. No sign, square-root extraction, auxiliary denominator descent, or scale restoration has been used in proving this.

## 4. Separate the two squares without a fixed weight

Put t=Z/S, a0=Cy/delta and b0=P Df, only as rational numbers in this proof. Dividing (1) by the nonzero rational square delta^2 S^4 gives

    (t^2-a0-b0)^2=4a0 b0.                             (5)

By (4), t!=0. Define rational numbers

    y0=(t^2+a0-b0)/(2t), p1=(t^2-a0+b0)/(2t).

A direct expansion of (5) gives

    y0^2=a0, p1^2=b0, y0+p1=t.                        (6)

Thus the two square conditions separate algebraically. No unjustified inference that an arbitrary sum of radicals is rational is used; the nonzero-center proof supplies the essential hypothesis. Since b0 is an integer, the rational number p1 is an integer. P Df is nonzero, hence strictly positive.

Also gcd(P,Df)=1, because Df=1 modulo P. Unique prime factorization therefore makes |P| and |Df| individually integer squares. P is odd and P=1 modulo4; it cannot be the negative of an odd square. Thus P>0. It follows that Df=1+Delta U^2 P>0. Choose positive integers p0,f with

    P=p0^2, Df=f^2.

Since gcd(Dt,Dg)=1, Dt>=1 and P>0, their product square splits as

    Dt=tau^2, Dg=g^2, p0=tau g

with positive integers tau,g. If Budget<=3, then D<=-1 and s!=0 give Dg<=1-Dt<=0, contrary to Dg>0. Therefore Budget>=4; (2) strengthens this to Budget>=12. It follows that k!=0, Derr<q^2 and

    |c/k-Y|<1/2, sign(c)=sign(kY) whenever cY!=0.        (7)

The disk inequality also gives the same nonzero common signs of q,F,C,q-F-C as the retained source proof.

## 5. Integer auxiliary root and carrier divisibility before scale restoration

Set I=U p0. Then I is an integer, c^2 divides I, and

    f^2=1+Delta I^2, Q=(Delta I)^2,
    V=f^2(c-R+4I T_old)-c, T_old=p0T.                  (8)

Equation (6) gives the rational auxiliary equation

    QV^2-(Q-1)y0^2=1.                                 (9)

If c=0, then U=I=Q=0 and (9) gives y0^2=1, so y0 is integral. If c!=0, then r!=0 and p0>0 imply I!=0, |I|>=c^2 and Q>1. Adjacent-coefficient Pell descent makes y0 integral. Namely, write y0=A/B in lowest terms. B^2 divides Q-1. The map

    V'=(2Q-1)V-2(Q-1)y0,
    y'=(2Q-1)y0-2QV

preserves (9), keeps V' integral and preserves the least common denominator B by its integral unimodular matrix. After reflecting signs, V>1 and y0>0 imply V<y0<QV/(Q-1), hence -V<V'<V; the norm excludes V'=0. Descent reaches |V|=|y0|=1 and therefore B=1.

In both c cases, (6) now gives t=y0+p1 in Z. As Z=S(n+V)-Ac,

    S divides Ac.                                     (10)

This is proved before assuming the cubic scale, c!=0, or Q>1 in the weak-scale case. It is the critical ordering point for that variant.

For cubic Y, reducing (10) modulo H gives H|K^5. Inequality (7) and |Y|>=|q|^3 exclude c=0.

For weak Y, H=3 modulo q and H is odd. Since q=2 modulo3,

    gcd(H,2q^2)=1.

Write M=2q^2 and Dc=HM. Since M^5 divides S, (10) implies M^5|Ac. If p^e exactly divides M and v_p(zc)=b<e, expansion

    Ac=zc^5+3Dc^2 zc^3-19Dc^3 zc^2-57Dc^5

shows that the first term has strictly smaller valuation5b than each other term. This contradicts p^(5e)|Ac. Thus M|zc. Reduction modulo M and gcd(H,M)=1 give

    M | v-q^2, v=q^2(2v_old+1),
    Y=(2v_old+1)q^3.                                  (11)

The old nonzero cubic scale is restored. Inequality (7) now excludes c=0. The other component H|Ac gives H|(MK)^5, hence H|K^5 by coprimality. No unsound inference H|K from H|K^5 is made.

## 6. Signed rank and native-source restoration

After Section5, every variant has exactly the required signed kernel data:

- the actual cubic scale, Delta=(a+2)^2-1>1 and nonzero c,I;
- c^2|I, f^2-Delta I^2=1, and |I|>=c^2;
- the auxiliary Pell equation (9) with y0 integral;
- V=-c modulo f and V=-R modulo c, by (8);
- the first Pell square Dt=tau^2;
- common nonzero signs of q,F,C,q-F-C, the strict centered strip (7), and the unchanged packing bounds |q|(|q|^2-1)<R<|q|^4-2;
- the powered main projection H|K^5.

For the XY index modulus, the signed strong-index proof in inherited/centered11-proof.md Section5.2 and the absolute folding in inherited/signed-quadratic-proof.md Section2 apply. The proof explicitly allows arbitrary nonzero I/c^2; no odd multiplier is assumed. For 4q^4, the smaller-index proof in PROOF.md Section5 applies: 4q^4>3R+1 and 4q^4|2XY^2 restore the same first-index congruence, and after orientation the ordinary h_old=(k-R-1)/(XY) is regenerated.

These arguments first give R=2t0+1, t0>=24, and

    |H|>x(x-3)^t0, x=|X|>=2^64,
    c=sign(c) psi_(a+2)(R).

For completeness, the actual projection step uses the identity

    2Kquad=HcX-K, Kquad=X(X+2ac)-1.

Since H is odd, H|K^5 implies H|Kquad^5. The retained signed Pell congruence gives H|Pi^5 for

    Pi=(sign(c)X-2^R)(2^R sign(c)X+1).

The bounds |Pi|^5<2^(20t0+20)x^10 and |H|>x^(t0+1)/2^t0 imply |Pi|^5<|H|, since 64(t0-9)-(21t0+20)=43t0-596>=436. Thus Pi=0 and sign(c)X=2^R. The unchanged late orientation and uniform half-binomial proof restore X,c,k,Y>0, 0<eta/k<1/4, the exact main projector and all original native source rows after fresh private witnesses are regenerated.

This proves the soundness reduction to a finite syntactic ZFC refutation under the same named ordinary source34/compiler calibration. Its copies, provenance and notices are retained in inherited/. No new end-to-end formal verification is asserted.

## 7. Completeness with no cyclic witness selection

Start with a finite syntactic refutation and its canonical outer data. These fix q,X,Y,c,R,k,Dt=tau^2, Budget>=64 and the exact main projector H|K. For the short modulus choose h=(k-R-1)/(4q^4); its integrality follows from the first Pell recurrence as in PROOF.md Section5. For the weak variant set v=q^2(2v_old+1), leaving the canonical numerical Y and all outer registers unchanged.

D=Budget-4 is positive and nonsquare by (2). Since Dt=tau^2 is a nonzero square, D Dt is positive nonsquare. Ordinary Pell existence supplies positive s,g with g^2=1+D Dt s^2. Fix these and put p0=tau g.

Choose one strong Pell pair I,f with

    4s p0 c^2 | I, f^2-Delta I^2=1.

The retained supported-modulus interpolation theorem permits this pair and keeps it fixed thereafter. Set r=I/(p0 c^2), so U=rc^2=I/p0. Every prime factor of p0sr divides I. No strong pair is changed after a residue is selected.

For cubic scale put kappa=K/H. Choose a0 modulo sr with pi(a0+kappa)=0 modulo sr. For weak scale use pi(a0+kappa+v_old)=0 modulo sr. Intersectivity of pi is the retained quintic theorem. Supported-modulus interpolation for this fixed I,f supplies T_old in the residue

    T_old=p0 a0 modulo p0sr

with its integral auxiliary Pell ordinate y. Consequently T=T_old/p0 is an integer and T=a0 modulo sr. Formula (8) then is exactly the new auxiliary definition because I T_old=UPT.

In the cubic case Ac=H^5 pi(T+kappa), giving Ac/S integral. In the weak case zc=HM(T+kappa+v_old) and Ac=(HM)^5 pi(T+kappa+v_old), again giving Ac/S integral. Now set

    n=Ac/S+y+p0f-V.

This is an integer, Z/S=y+p0f, Cy=delta y^2 and P Df=(p0f)^2. Substitution makes (1) zero. All witness choices are in the order outer data, guard s/g, one fixed I/f/r, intersective residue, T_old and T/y, then n. The guard never depends on the subsequently chosen strong pair.

Both existence directions hold. Composing the retained ordinary calibration, ZFC proves that universal nonvanishing of each displayed fixed polynomial over Z^11 is equivalent to Con(ZFC).

## 8. Exact degree and actual nonzero coefficients

Let q0=6beta j, X0=12q0w and write Y0=2v q0^3 for cubic scale or Y0=q0v for weak scale. Let a0=X0Y0. The highest k part is h a0 for the native cubic index, 4h q0^4-q0^3F0 for the short index, and h a0-q0^3F0 for weak scale, where F0=12wC-q0z. The ties in the latter two forms are retained.

The common leading factors are

    P0=-4q0^2 X0^4 Y0^10 k0^6 s^2,
    U0=rc^2, Df0=a0^2 U0^2 P0, Q0=a0^4 U0^2 P0,
    V0=4a0^2 U0^3 P0^2 T, Cy0=Q0 V0^2.

The degree tables are

    variant       P  Df   Q   V  Cy  S  Ac
    native       94 112 124 210 544  8  35
    short        82 100 112 186 484  8  35
    weak         62  76  84 142 368 16  35.

Put Wc=Sn-Ac, so Z=Wc+SV and degWc=35. The complete centering identity is

    Inner=delta Wc^2+2delta S V Wc
                +S^2(1-V^2-delta P Df).                (12)

In each variant the unique highest term is -S^2 V^2. Its degrees are436,388,316. The squared Inner therefore has degree872,776,632, respectively. The correction -4delta S^4 Cy P Df has degree906,810,654, respectively, strictly higher. Thus it gives the entire nonzero highest homogeneous form.

For the two cubic variants that form is

    -2^30 q0^16 X0^50 Y0^98 k0^48 s^20 r^16 c^24 T^2.

The native attained coefficient is

    [j^552 w^98 v^146 h^48 s^20 r^16 c^24 T^2] Ftwo
        =-2^924 3^650 beta^552.

The short attained coefficient is

    [j^552 w^50 v^98 h^48 s^20 r^16 c^24 T^2] Ftwo
        =-2^876 3^602 beta^552.

For weak scale S0=128sr a0 q0^10 and the entire top form is

    -2^50 q0^56 X0^50 Y0^98 k0^48 s^20 r^16 c^24 T^2.

Its maximal-h coefficient is

    [j^300 w^98 v^146 h^48 s^20 r^16 c^24 T^2] Ftwo
        =-2^546 3^398 beta^300.

Each monomial exponent sum is the claimed degree, and each coefficient is nonzero at the authentic fixed beta. Maximal h makes the choice unique even where k0 has two summands. These are exact actual-DAG leading-coefficient proofs, not numerical tests or generic-coefficient assumptions.

## 9. Arithmetic checks and limitations

The generators and checkers are owned adaptations of the attributed lowops DAG tools. The checkers never import their producer. They validate topology, full liveness, all eleven variables, complete six-port bindings and actual decompressed bytes, complete local polynomial cuts, the two-root and center identities, exact leading coefficients at every node with (12) at its cancellation gate, and modified-formula negative controls. Both normal and optimized Python checks pass.

The degree906 comparison is explicitly not a Pareto improvement. Degree810/112 operations and degree654/117 operations are new tradeoff points against the inspected round15 schedules. This does not assert global minimality, historical priority for Pell or norm identities, or a new formal calibration endpoint.
