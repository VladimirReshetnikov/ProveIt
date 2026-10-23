# Independent review of the two shorter norm weights

Status: both weight changes are mathematically sound under their explicitly inherited pre-recovery bounds. The positive degree calculation below is an independent leading-form derivation. Final circuit fidelity/counts should be checked against the generated artifacts. No new end-to-end kernel result is claimed.

## 1. Twelve positive unknowns: halve the outer carrier

Source: [24-integer24/sections/positive.tex](https://github.com/VladimirReshetnikov/ProveIt/blob/8c6eec9d19ef80538c8e61ff6e0180040583446a/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/24-integer24/sections/positive.tex), especially “Separation bounds before recovering roots” and “Rationality, integrality, and the compiler interface.”

Keep the source M1069 or M1073 and all its preceding definitions, but replace N=1+2HM by L=1+HM and W=Ht+L b0. The old proof's symmetric outer separation does not apply verbatim. A stronger one-sided argument is available because t and b0 are positive.

The source proves uniformly for every complex auxiliary conjugate y that |y|<M sqrt(A), and also G>A>0. Independently,

    b0=ac+X=ell+E eta+Yc+X>ell+k>sqrt(A).

Here Y>=1 and c=kY+eta>k give Yc>k; and (ell+k)^2−A=ell*k+k^2−1>0 since k>=2.

Every root x of the inner rational polynomial has the form x=M tau+y, tau^2=A, hence |x|<2M sqrt(A). A vanished outer factor supplies x=(W−L g)/H for g^2=G. The negative g branch would give

    x_plus=(W+L sqrt(G))/H
          =t+(M+1/H)(b0+sqrt(G))
          >2M sqrt(A),

which is impossible. If sqrt(G) were irrational, a rational-field automorphism changing its sign would turn the valid root x_minus into this same forbidden root x_plus of the inner rational polynomial. Therefore g is the positive integer square root of G.

Now x is rational. A sign-flipping automorphism for irrational tau would require a difference of magnitude 2M sqrt(A) between two y conjugates, impossible by their strict uniform bounds. Thus tau and then y are rational. The source's B1>0 recovers f rational, hence integral; rational Pell saturation makes y integral. Finally H gamma and L gamma are integers and gcd(H,L)=1, so gamma is integral. All subsequent signed-root compiler recovery is inherited unchanged. Completeness takes a canonical positive witness and t=y+M tau+L gamma>0.

This argument is noncircular: no square, integrality, or main-root sign is assumed before the outer branch is excluded. Negative or complex auxiliary roots are covered by the source's uniform modulus bound.

### Independent exact-degree derivation for M1069

Use the source's homogeneous scaling and abbreviate

    B = R0 E0^2 i^2 c0^4                       (degree 38),
    D1 = R0 E0 Y0 i^2 c0^4                    (degree 36),
    D2 = R0 E0 (s q0^2) i^2 c0^4              (degree 35).

The source already proves M sqrt(A)−b has leader D2. The positive main-quotient branch gamma=(sqrt(G)−b0)/H has order −1 and L gamma has order 32. Its eight coherent factors therefore have four degree-35 cancellation factors with leaders ±D2 and four degree-38 factors with leaders ±2B.

For the negative branch gamma=−(sqrt(G)+b0)/H, the new halved carrier gives L gamma the leading value −2B. Six of its eight factors have leaders 2B,2B,4B, each twice. For the remaining two factors,

    t−y−M sqrt(A)−L gamma
      = (b−y) + (M sqrt(A)−b)
        + M(b0+sqrt(G)−2sqrt(A)) + (b0+sqrt(G))/H+t.

The first term has degree at most 23, the second has degree 35, and the final two have degree at most 5 and 1. The key expression b0+sqrt(G)−2sqrt(A) has leader 2Y0c0 of degree 9: both b0 and sqrt(G) agree with ac through that order, while sqrt(A) agrees with ell. Thus the two exceptional factors have degree 36 and leader 2D1.

Multiplying all sixteen coherent factors, including the source prefactor d^8 H^16, gives

    Omega_top = 2^14 d0^8 H0^16 B^10 D1^2 D2^4,
    deg Omega = 8*46+16*6+10*38+2*36+4*35 = 1056.

All displayed factors are nonzero as polynomials for every authentic beta>0. Multiplying by the nonzero degree-7 index and degree-2 transport leaders gives exact product degree 1065. This is a uniform leading-form argument, not only a modular degree sample.

## 2. Twenty-four unrestricted integers: remove the surplus iI term

Sources:

- [27-wave4/integers/INTEGER24_RATIO_WEIGHT_PROOF.md](https://github.com/VladimirReshetnikov/ProveIt/blob/8c6eec9d19ef80538c8e61ff6e0180040583446a/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/27-wave4/integers/INTEGER24_RATIO_WEIGHT_PROOF.md).
- [27-wave4/integers/INTEGER24_PROOF.md](https://github.com/VladimirReshetnikov/ProveIt/blob/8c6eec9d19ef80538c8e61ff6e0180040583446a/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/27-wave4/integers/INTEGER24_PROOF.md), especially Sections 2–7.

The old ratio weight is W_old=2*((iI)*(1+5Rac)+v^2). Replace it by

    W_new=2*(5Rac*iI+v^2), I=i c^2.

The signed pre-recovery bounds give q>=16, R>q(q^2−1), |a|>=q^3, |c|>1, a and c of the same sign, and odd i nonzero. Hence iI=i^2 c^2>0 and

    (Rac−1)iI>2.

The source's strict all-conjugate estimate is

    |y'|/sqrt(G)<iI+v^2+2+4Rac*iI
                 <v^2+5Rac*iI=W_new/2.

The second inequality is exactly the displayed pre-recovery bound. It is valid for T=0, X=0, and either sign of s,i,H. W_new remains positive with B=|H|W_new>8.

With L=1+HW_new and the first-root coefficient 2HW_new, the source's subsequent inequalities are unchanged:

    |L|sqrt(G)>|H| |y'|,
    |L|sqrt(G)+|H| |y'|<(117/64)B sqrt(A)<2B sqrt(A)

(the second is used only after X=0 has been excluded). The exact same saturation, zero-Baux, zero-X, zero-T, and negative-s arguments therefore apply in the same order. Completeness introduces no new restriction.

The deleted iI term has strictly lower degree. Consequently the source's nonzero tied-leading certificate

    norm_top=(99*899)^4 d0^8 H0^16 b0^16

(where this b0 means the source's leading homogeneous part of b, not the positive-family abbreviation ac+X) remains unchanged. The norm/system degree is 1920 and product degree 1936. Symbol names should be disambiguated in a combined report.

## 3. Scalar trace/product evaluator identity

The shared cheaper evaluator can be audited independently of either weight. For x=S−L u, u^2=G, a=m^2 A and Z=H^4 Baux^2 D, write

    C=d(x^2+a)−H^2e, K=4d^2 a x^2.

Eliminating tau from [d(x−m tau)^2−H^2e]^2−Z yields

    (C^2−K−Z)^2−4KZ.

Put theta=−2SL u, theta^2=Theta=4S^2 L^2 G, r0=S^2+L^2 G, C=C0+d theta and K=Kc+kf theta. Then

    x0=C0^2+d^2 Theta−Kc−Z,
    x1=2C0d−kf,
    n0=x0^2+Theta x1^2−4ZKc,
    n1=2x0x1−4Zkf.

The remaining norm is exactly n0^2−Theta n1^2. These are polynomial identities, valid for all signs and all degenerate radicands. They justify the scalar evaluator provided the builder implements these exact definitions. Operation counts are properties of that literal implementation, not of this algebra alone.

## 4. Additional positive refinement: shift w and reach degree 1061

The positive worker subsequently proposes old_w=w_new+q, with w_new>0, and replaces the source majorant's sq^2 term by sq. This further step passes independent review.

[Source 30's complete coefficient transfer](https://github.com/VladimirReshetnikov/ProveIt/blob/8c6eec9d19ef80538c8e61ff6e0180040583446a/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/30-quartic31/integers/COEFFICIENT_TRANSFER.md) supplies canonical q=2^t, old_w=2^(R−t), and R>3q+1. Since q>=16, t<q and R>2t, so old_w>q. Therefore w_new=old_w−q is positive on every such canonical witness. Soundness simply maps w_new to the positive old_w=w_new+q. This is a completeness-preserving restriction, not an assumption about all source witnesses.

The tighter ratio bound is

    Y/X = s q^2/(w_new+q) < s q.

Source 24's proof uses the substituted majorant term only to bound Y/X in its displayed identity for (a+2)^2 rho. Hence the same proof establishes |y|<M sqrt(A) for

    C3=E+2(X+Y)+sq,
    M=I(2T+R C3 i c).

For exact degree, the source cancellation identity becomes

    C3 ell−Delta c
      =(2EX+Esq−Y^2−4E−4Y−3)c−E C3 eta.

The two potentially tied top-degree terms together have degree 13. The first can be simplified using X=(w_new+q)q and E=XY:

    2EX+Esq−Y^2=Y(2X^2+s w_new q^2).

The other term −E C3 eta has the same degree and MUST be retained. Their complete leading bracket is

    T3=(2E0X0+E0sq0−Y0^2)c0−E0^2 eta
      =X0^2Y0^2(eta+2 zeta)+(eta+zeta)s^3 q0^8 w_new.

This is a nonzero positive-coefficient polynomial for every beta>0. Thus M sqrt(A)−b now has degree 34, with nonzero leader

    D3=R0 i^2 c0^3 T3.

An earlier informal audit omitted the tied −E0^2 eta term; the full expression above corrects that omission. The resulting degree is unchanged.

The halved-carrier large-branch cancellation remains degree 36 with leader 2D1. The full norm leader is therefore

    Omega_top=2^14 d0^8 H0^16 B^10 D1^2 D3^4,
    deg Omega=8*46+16*6+10*38+2*36+4*34=1052.

The index and transport leaders still have degrees 7 and 2 and are nonzero after the linear shift. The exact product degree is 1061. This argument is independent of finite-field ray tests; those tests remain useful implementation diagnostics.
