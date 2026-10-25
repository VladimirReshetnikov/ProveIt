# Single-product saturation with an amplified scale carrier

## Result and precise boundary

Four literal ordinary integer polynomials give new degree/live-operation tradeoffs at eleven unrestricted integer variables:

- `weak_product11_none.json`: exact degree 648, 115 binary operations.
- `weak_product11_simple.json`: exact degree 640, 118 operations.
- `free_product11_none.json`: exact degree 580, 119 operations.
- `free_product11_simple.json`: exact degree 574, 122 operations.

The degree648/115-gate equation is a new nondominated point in the reviewed combined frontier and strictly improves the newly recovered degree654/117-gate endpoint in both metrics. The other three equations are audited comparison constructions: recovered degree488/118-gate and degree464/119-gate equations dominate them. In particular the prior degree352/132-gate and degree840/110-gate endpoints remain relevant. No ten-variable result, global optimum, consistency proof, new encoded object-ZFC derivation, or end-to-end proof-assistant certificate is claimed.

The new construction combines the source's one-product square-root saturation with the weak/free amplified scale carrier, and applies a quadratic center directly to the single-product equation. The soundness proof below explicitly handles the weak-scale Y=0 branch: carrier integrality is recovered before the main-root folding theorem, whose large-base hypotheses would not yet hold in that branch.

The ordinary native/compiler/refutation theorem is inherited only after restoring a literal old signed source zero. Finite audits certify all gates, identities, coefficients and attained degrees, not the unbounded inherited arithmetic or compiler theorems.

## 1. Full equations and fixed numerals

All eleven unknowns j,C,z,h,r,v,w,T,c,n,s range over Z. The six fixed integer coefficients beta,K0,MC,MF,cone_A,cone_B are precisely the complete payloads in `coefficients/BINDING.json`, including the already shifted MF. In particular beta=2^1064921-1, cone_A=2^1113 and cone_B=2^666104. Their finite reconstruction recipe is retained. All other names in this proof are polynomial abbreviations, not variables.

Common definitions are

    J=6j+1, q=beta J+1, W=12w+4, X=qW,
    E=XY, a=E+Y, A=a+2, H=4a+3, Delta=a^2+H=A^2-1,
    F=(K0+W)C-z(q-1),
    R=(q(q-F)-C)(q^2-1)+(MC+q MF)J,
    k=R+1+hE, eta=c-Yk,
    Derr=(cone_A F-q)^2+(cone_B C-q)^2,
    B0=k^2(q^2-Derr)-4q^2 eta^2,
    ell=XY^2, L=ell k, Dt=1+L(L+k),
    D=3Budget-4, Dg=1+4D Dt s^2,
    P=Dt Dg=Dt+(12Budget-16)(Dt s)^2,
    Dm=1+Delta c^2, BP=Dm P,
    Ub=rc^2, U=A Ub, Df=1+Delta U^2 BP,
    Q=Delta^2 U^2 BP, delta=Q-1,
    V=Df(c-R+4U BP T)-c, Cy=QV^2-1, Da=delta Cy,
    K=X(3c-2X)+2, Dc=HM,
    zc=Dc T+M K+H(v-qscale),
    Ac=(zc^2+3Dc^2)(zc^3-19Dc^3), S=srH M^5.

Choose one of two scales:

    weak: Y=qv, qscale=q^2, M=2q^2, Budget=B0;
    free: Y=v, qscale=q^3, M=2q^3, Budget=Y^2 B0-k^2q^8.

For the direct equation put lambda=0; for the centered equation put lambda=A U BP. Define

    Z=S(n+lambda V)-Ac.

The final polynomial, for either scale and either center, is

    Fnew = delta Z^2 - S^2 BP Df Cy.                    (1)

It is one ordinary integer polynomial with no radicals, divisions, variable powers or unstated witnesses. The centered/direct zero sets are related by the integral bijection n_direct=n_center+lambda V with every other input unchanged. It therefore suffices to prove the direct case, while retaining the center in the displayed final witness.

The literal builder shares Yk, uses L=E(Yk), and evaluates the free Budget as

    (Yk)^2(q^2-Derr)-q^2[4(Y eta)^2+(kq^3)^2].

Every abbreviation in (1) has a fully expanded division-free DAG in the named JSON file. Binary scalar products and squares count as operations; numeral leaves and register reuse do not.

## 2. Unconditional facts and the square-product bootstrap

The authentic affine front gives q even, q=2 modulo3, |q|>=beta-1>=16, 8|X, X=2 modulo3 and |X|>=4|q|. In either scale H is odd and nonzero. If Y=0, then A=2 and Delta=3. If Y!=0, |a|=|(X+1)Y|>=|X|-1>=63, so A!=0 and Delta>1 as well. Thus Dm>=1 on every integer assignment.

Since ell(ell+1)>=0, Dt=1+ell(ell+1)k^2>=1. Also Dt, Dg and P are odd, so BP is nonzero. Df cannot vanish: it is1 if U=0, and otherwise |Delta U^2 BP|>=Delta>1. Similarly Q is0 or has absolute value greater than1, so delta!=0 and Cy!=0. Hence Da!=0.

The polynomial pi(t)=(t^2+3)(t^3-19) has no rational zero, since its quadratic factor is strictly positive over R and19 is not a rational cube. Therefore Ac=Dc^5 pi(zc/Dc)!=0. At S=0, equation(1) is delta Ac^2!=0. Every zero thus has r,s nonzero.

The nonzero integers BP,Df,Da are pairwise coprime. Df=1 modulo BP, and Q=0 modulo BP makes Da=1 modulo BP. Modulo Df,

    Q=-Delta, delta=-A^2, V=-c, Cy=-Dm, Da=A^2 Dm.

Since A|U and Dm|BP, Df=1 modulo both A and Dm. Thus gcd(Df,Da)=1 also. These claims do not assume any signs or parity of Y.

Multiply(1) by delta and divide by the nonzero rational square S^2:

    (delta Z/S)^2=BP Df Da.                            (2)

A rational number with integral square is integral. Pairwise coprimality makes the absolute values of all three factors squares. Moreover Delta A^2 is divisible by4 for every integer A. Thus Df=1 modulo4, whereas a negative square is0 or3 modulo4. Consequently Df>0.

If c!=0 then U!=0, and BP<0 would force Df<0, impossible. If c=0 then U=0, Dm=Df=Da=1, and (2) itself gives BP>0. Thus BP>0 in every case. Since Dm>0, P>0. Equation(2) now also gives Da>0. Write

    p0^2=BP, f^2=Df, e^2=Da

with positive integer roots. In particular Dg>0. If Budget<=1, then D<=-1 and s!=0, Dt>=1 give Dg<=-3, a contradiction. Thus Budget>=2.

The weak case immediately has B0>0. In the free case Budget>0 gives Y!=0,k!=0,B0>0 and, since B0<=k^2q^2,

    Y^2 B0>k^2q^8 implies |Y|>|q|^3.                  (3)

For both cases the usual centered-budget inequalities give k!=0, Derr<q^2, |c/k-Y|<1/2, and the common strict sign of q,F,C,q-F-C. The authentic packing bound is

    |q|(|q|^2-1)<R<|q|^4-2.                           (4)

We have not yet invoked main-root folding or first-Pell classification.

## 3. Carrier integrality before folding

If c=0, equation(1) directly reads Z^2=S^2 BP, so Z/S is an integer. If c!=0, define the proof-only integers

    I=U p0, T_old=p0 T.

They obey I!=0, c^2|I,

    f^2=1+Delta I^2, Q=(Delta I)^2>1,
    V=f^2(c-R+4I T_old)-c.

The rational y=e/delta satisfies

    QV^2-(Q-1)y^2=1.

The adjacent-Pell denominator-descent lemma retained in `source/centered11-proof.md` Section4.2 implies y is integral. This lemma depends on Q being an integer square greater than1, not on |A|>=3. In its proof a reduced denominator b satisfies b^2|(Q-1), and the norm-preserving step

    V'=(2Q-1)V-2(Q-1)y,
    y'=(2Q-1)y-2QV

preserves integrality of V and the reduced denominator b. After adjusting signs it strictly reduces |V| until |V|=1, where |y|=1, forcing b=1. Substituting Cy=delta y^2 into(1) and canceling delta gives

    Z^2=S^2 p0^2 f^2 y^2.

Thus Z/S is integral in this branch too. Since n+lambda V is integral, every zero satisfies

    S|Ac.                                              (5)

This argument avoids the erroneous use of large-base folding while weak Y might still be zero.

From(5), M^5|Ac. If p^e exactly divides M and v_p(zc)=b<e, the leading term zc^5 in

    Ac=zc^5+3Dc^2 zc^3-19Dc^3 zc^2-57Dc^5

has valuation5b, strictly less than each other term, including for p=3 or19. This contradicts p^(5e)|Ac. Hence M|zc and

    M|H(v-qscale).                                    (6)

Also H|Ac and zc=MK moduloH imply H|(MK)^5.

For the weak scale, H=3 moduloq, q is not divisible by3, and H is odd. Hence gcd(H,M)=1, and(6) gives

    v=(2v_old+1)q^2, Y=(2v_old+1)q^3                  (7)

for an integer v_old. It also gives H|K^5. In particular |Y|>=|q|^3 and Y even.

For the free scale we do not cancel H yet. Its oddness and the2-primary part of(6) give Y=v even. Equation(3) supplies the needed magnitude. Here H|(MK)^5 gives only

    H|q^15 K^5.                                       (8)

In both cases |Y|>=|q|^3>=1; the centered strip now excludes c=0. Therefore A has absolute value at least3, and the strong/auxiliary norms above have all required folding hypotheses.

## 4. Recover the missing main and first roots without circularity

Put B=|A|>=3, C0=|c| and I0=|I|>=c^2>=C0. Classify the strong Pell solution as f=chi_B(m), I0=psi_B(m), so f>2I0. With rho=Delta I, the auxiliary norm gives |rho||V|=chi_|rho|(nu) with nu odd. Its odd quotient-polynomial identity together with V=-c modulof implies

    psi_B(nu)=+/- C0 modulof.

Fold nu modulo2m and reflect to0<=p<=m. Since psi_B(p)+C0<=2I0<f, this congruence cannot wrap and gives psi_B(p)=C0, p>=1. This is exactly the early absolute-folding lemma in `source/signed-quadratic-proof.md` Section2. It uses no first root. Thus

    Dm=1+Delta c^2=d^2

for an integer d>0. As p0^2=Dm P, the rational square root p0/d of the integer P is integral, so P is a square. Because gcd(Dt,Dg)=1 and both are positive, each is a square:

    Dt=tau^2, Dg=g^2.

The original first/strong/auxiliary norm system is now fully restored. This order is essential: product-square extraction, carrier integrality, scale magnitude/parity, main-root folding, then first-root splitting.

## 5. Signed ranks, amplified projection, and source restoration

The exact auxiliary residues are V=-c modulof and V=-R moduloc. The latter follows from

    V+R=Delta I^2(c-R)+4I Df T_old.

Together with c^2|I, k=R+1+hXY, the centered strip, parity Y even, magnitude |Y|>=|q|^3 and(4), these are precisely the pre-projection hypotheses of `source/centered11-proof.md` Section5.2 and `source/signed-quadratic-proof.md` Sections4-5. In particular |XY|>3R+1. Their first-index congruence, nonodd strong-rank theorem, and auxiliary step-down give

    main index p=R, first index (R+1)/2,
    R=2t+1, t>=36, c=sign(c) psi_A(R),
    |Y|>(|X|-3)^t/2-1, |H|>|X|(|X|-3)^t.              (9)

For the nonodd strong-rank step the stated theorem uses c^2|I: composition first gives p|m, then c|m/p, hence c|m and m>2p. It does not require I/c^2 odd. The strengthened t>=36 follows already from(4) and |q|>=16, since R>4080. No main projection or restored exact free-scale congruence is used to prove(9).

Let x=|X|, sigma=sign(c), Kq=X(X+2ac)-1 and

    Pi=(sigma X-2^R)(2^R sigma X+1).

The identities K=HXc-2Kq and 2^R Kq=Pi moduloH turn the weak projection into H|Pi^5 and the free projection(8) into H|q^15 Pi^5. In either case it suffices to bound the latter integer, because H|Pi^5 also implies H|q^15 Pi^5. Both factors of Pi have absolute value less than2^(R+1)x. Using |q|<=x/4 and R=2t+1 gives

    |q|^15 |Pi|^5 < 2^(20t-10)x^25.

On the other hand(9) gives |H|>x^(t+1)/2^t. The actual coefficient satisfies x>=4(beta-1)>=2^64, and t>=36, so

    64(t-24)-(21t-10)=43t-1526>=22>0.

Therefore |q|^15|Pi|^5<|H|. The divisible integer is zero. Since q!=0 and the odd factor2^R sigma X+1 is nonzero, sigma X=2^R. Moreover X=2 modulo3 and R odd give sigma=+1 and X=2^R. The projector congruence now also gives H|Kq and H|K.

In the free case q|X=2^R makes |q| a power of two; as H is odd, gcd(H,M)=1. Only now can(6) be canceled to give

    Y=(2v_old+1)q^3, v_old=(Y-q^3)/(2q^3) in Z.        (10)

The inherited surviving first-index sign gives k>0, hence c>0 and Y>0. The uniform centered half-binomial theorem of `source/centered11-proof.md` Section5.3 applies to these exact outer coordinates and gives0<eta/k<1/4. It is not an uncontrolled large-Y limit.

Finally restore an actual old signed Q41 zero using the fresh private witnesses of that source's Section5.4, rather than assuming the incoming strong multiplier is odd. Explicitly take

    I_star=psi_A(Rc), f_star=chi_A(Rc), rho_star=Delta I_star.

A is even and R,c are odd, so I_star and rho_star are odd; composition gives c^2|I_star. Hence r_old=(rho_star/c^2-1)/2 is integral. With t=(R-1)/2 and Q_t(z^2)=chi_z(2t+1)/z, set

    V_star=(-1)^(t+1)Q_t(rho_star^2), y_star=psi_rho_star(R).

The exact congruences V_star=-c modulo f_star^2 and V_star=-R moduloc make o_old=(V_star+c)/f_star and j_old=(V_star+R)/c integral. They restore V_star=f_star o_old-c=c j_old-R and k=1-V_star+c j_old+hXY. The positive eta,k-eta provide the old positivity rows, and2^((R-1)/2) restores its square coordinate. Use v_old from(7) or(10). All outer coordinates are unchanged. Only this literal old zero is passed to the retained ordinary native/compiler/finite-refutation calibration. This proves soundness.

## 6. Completeness with the guard and strong pair fixed

Start with the canonical native outer witness supplied by a finite syntactic ZFC refutation. It has A even positive, Dm=d^2, Dt=tau^2, R=3 modulo4, c=psi_A(R)>0, c=R modulo4, and

    Y=(2v_old+1)q^3, B0>q^2k^2/4, Y>X=2^R>4q^3.

Set the new v=Y/q in the weak scale and v=Y in the free scale. Then every front-end value is unchanged. The weak Budget is B0>64. The free Budget obeys

    Budget>k^2q^2(Y^2/4-q^6)>64.

Because X=2 modulo3, ell=XY^2 is0 or2 modulo3, so Dt=1 modulo3. Hence (3Budget-4)Dt is positive and2 modulo3, and therefore nonsquare. A positive Pell unit squared once gives s,g>0 with

    g^2=1+4(3Budget-4)Dt s^2.

Fix this guard pair. Then P=(tau g)^2 and p0=d tau g are fixed positive integers.

Choose one positive strong Pell pair I,f with

    4s A p0 c^2|I, f^2-Delta I^2=1,

using the retained finite matrix-period construction. Define r=I/(A p0 c^2), U=I/p0. Keep this one strong pair fixed. Every prime of p0 s r divides I, so the supported-modulus interpolation theorem of `source/POWERED_SATURATION_PARENT.md` Section5 realizes every T_old class modulo p0 s r for this same pair. Its hypothesis4s c^2|I holds, and the chosen extra divisibility does not change the theorem.

The canonical projector gives H|K; put kappa=K/H. In either scale the carrier becomes

    zc=HM(T+kappa+v_old),
    Ac=(HM)^5 pi(T+kappa+v_old),
    Ac/S=H^4 pi(T+kappa+v_old)/(sr).

The inherited intersectivity theorem for pi(x)=(x^2+3)(x^3-19) supplies a residue a0 modulo sr with pi(a0+kappa+v_old)=0 modulo sr. Prescribe

    T_old=p0 a0 modulo p0 s r.

Supported interpolation supplies this integer T_old and an integral auxiliary y. Then T=T_old/p0 is integral and T=a0 modulo sr. Thus Ac/S is integral, and4I T_old=4U BP T exactly. Finally set

    n=Ac/S+p0 f y-lambda V.

One square root of(1) vanishes, so this gives a new integer zero. The order is canonical outer data, fixed guard s/g, fixed p0, one fixed strong pair I/f/r, intersective residue, interpolated T_old/y and T, then n. No previously selected strong pair or guard is changed to fit a later residue. This proves completeness.

Combining soundness and completeness with the specified inherited ordinary calibration, universal nonvanishing of each displayed polynomial over Z^11 is ZFC-provably equivalent to syntactic Con(ZFC).

## 7. Exact degrees, leading monomials, and finite replay

Free-scale degrees are

    a3, Delta6, k5, Budget18, Dt18, P56, Dm8, BP64,
    U6, Df82, Q88, V153, Cy394, S20, Ac35.

Weak-scale degrees are

    a4, Delta8, k5, Budget16, Dt22, P62, Dm10, BP72,
    U7, Df94, Q102, V174, Cy450, S16, Ac35.

For direct equations S^2 BP Df Cy uniquely dominates delta Z^2, giving580 and648. For the centered equations lambda=A U BP, the exact identity

    lambda^2-BP Df=U^2 BP^2-BP

cancels the apparent highest terms. With W0=Sn-Ac, the exact output is

    delta W0^2+2delta S lambda V W0
       +S^2{[delta(U^2 BP^2-BP)-BP Df]V^2+BP Df}.

Its unique highest-degree term is S^2 Q U^2 BP^2 V^2, giving574 and640. The syntactic DAG bounds remain580 and648 respectively; exact degree is certified by this identity, not guessed from a numerical sample.

The following actual nonzero coefficients certify attainment. Unlisted variable exponents are zero:

    free direct: j^318 w^64 v^92 s^16 r^12 c^34 z^42 T^2,
                 coefficient +2^478 3^389 beta^318;
    free center: j^316 w^62 v^90 s^16 r^12 c^34 z^42 T^2,
                 coefficient -2^472 3^385 beta^316;
    weak direct: j^372 w^64 v^106 s^16 r^12 c^34 z^42 T^2,
                 coefficient +2^546 3^443 beta^372;
    weak center: j^368 w^62 v^104 s^16 r^12 c^34 z^42 T^2,
                 coefficient -2^538 3^437 beta^368.

The Python standard-library checker does not import or invoke the builder. It checks the free-ring identity of every live named register, coverage of every arithmetic gate, topology and liveness, operation counts, pairwise-coprimality remainders, exact rescaling, the strengthened guard identity, the exact center cancellation cut and its unique maximal weighted term, and attained leading monomials at all gates. It authenticates every retained source and coefficient byte, reconstructs all six actual fixed ports, and rejects separate arithmetic-gate mutations at every gate, plus coefficient, variable, literal and degree mutations. Python -O runs the same checks because no removable assertions implement acceptance conditions.

## 8. Named proof dependency ledger

All following are copied locally and authenticated by `SOURCE_PINS.json`:

- `source/PRODUCT_SATURATION_PROOF.md`, Sections2-4 and6: three coprime factors, sign recovery, early absolute folding and fixed-strong-pair saturation completeness. This construction changes its order to establish carrier integrality before folding.
- `source/FREE_MAIN_SATURATION_PROOF.md`, Sections4-6: amplified free carrier, parity before exact scale, the strengthened fifth-power bound and fixed-strong interpolation.
- `source/CRT_CARRIER_PROOF.md`, Sections2-5: weak carrier valuation and CRT scale reconstruction.
- `source/centered11-proof.md`, Sections4.2 and5.2-5.4: adjacent-Pell denominator descent, nonodd strong rank, uniform centered interval and literal signed-source restoration.
- `source/signed-quadratic-proof.md`, Section2 and Sections4-5: early absolute folding, signed ranks and signed ratio bounds.
- `source/POWERED_SATURATION_PARENT.md`, Section5: arbitrary supported-modulus interpolation with one fixed strong pair.
- `source/PRIME_TWELVE.md` and `source/provenance/interpolation12/INTERPOLATION12.md`: the zero-free intersective quintic and underlying finite-period/auxiliary interpolation construction.
- `source/provenance/centered18/PROOF.md`, Section6: canonical centered source family and budget margin.
- The retained `source/provenance/rootfusion/`, `source/provenance/centered17/` and associated nested sources: the named ordinary signed/native/compiler/refutation calibration and its exact numeral binding. Their stated formalization boundary is retained unchanged.

This ledger identifies rather than replaces those unbounded dependencies. The archive's proof claim is ordinary arithmetic composed with the retained calibration, not a new machine-checked theorem of ZFC.
