# One product, eleven integers: 924/109 and 840/110

## Result and source boundary

The two literal integer polynomials have eleven unrestricted integer variables and the same six actual source34 numeral payloads as the independently reviewed degree352 family. Their exact degree/live-operation pairs are924/109 and840/110, strictly improving the incoming966/111 and882/112 endpoints in BOTH metrics. The new operation is square-root saturation by the product of the omitted main radicand and the existing guard product. Main-root folding is deliberately performed before extracting the first-Pell root; the proof below verifies that this is not circular.

All unbounded ordinary dependencies, coefficient recipes and notices are retained locally and hashed. The native/compiler/refutation calibration is inherited only after an actual old signed source zero is restored. This is not a proof of consistency, a global optimum, a new proof-assistant endpoint, or an encoded object-ZFC derivation.

## 1. Complete polynomial

The eleven variables j,C,z,h,r,v,w,T,c,n,s range over Z. Fix exactly beta,K0,MC,MF,cone_A,cone_B, including shifted MF and beta=2^1064921-1, cone_A=2^1113, cone_B=2^666104. Define only polynomial abbreviations:

    J=6j+1, q=beta J+1, W=12w+4,
    X=qW, Y=(2v+1)q^3, E=XY,
    a=E+Y, A=a+2, H=4a+3, Delta=a^2+H=A^2-1,
    F=(K0+W)C-z(q-1),
    R=(q(q-F)-C)(q^2-1)+(MC+q MF)J,
    M_index=E                     (native924/109),
    M_index=4q^4                  (short840/110),
    k=R+1+h M_index, eta=c-Yk,
    Derr=(cone_A F-q)^2+(cone_B C-q)^2,
    Budget=k^2(q^2-Derr)-4q^2 eta^2,
    ell=XY^2, L=ell k, Dt=1+L(L+k),
    D=3Budget-4, Dg=1+4D Dt s^2,
    P=Dt Dg=Dt+(12Budget-16)(Dt s)^2,
    Dm=1+Delta c^2, BP=Dm P,
    U=A r c^2,
    Df=1+Delta U^2 BP, Q=Delta^2 U^2 BP, delta=Q-1,
    V=Df(c-R+4U BP T)-c,
    Cy=QV^2-1, Da=delta Cy,
    K=X(3c-2X)+2, S=srH, zc=HT+K,
    Ac=(zc^2+3H^2)(zc^3-19H^3), Z=Sn-Ac.

The final polynomial is

    delta Z^2 - S^2 BP Df Cy = 0.                      (1)

There are no roots, denominators, variable exponents, implicit witnesses, or uninstantiated coefficients. P is evaluated with the displayed fused identity, L=E(Yk) shares Yk from eta, and the short modulus shares the existing4q^2 register in its product(4q^2)q^2.

## 2. Nonzero facts before extracting signs

The authentic affine front unconditionally gives q even, q=2 modulo3, |q|>=beta-1>=16, X=0 modulo8, X=2 modulo3, |X|>=4|q|, and |Y|>=|q|^3. Thus A is nonzero even with |A|>=3, H is odd/nonzero, Delta>1, and Dm>=1. Also Dt>=1 and Dt is odd; Dg and P are odd, hence nonzero. Consequently BP is nonzero.

Df cannot be zero: if U=0 it is1, while otherwise |Delta U^2 BP|>=Delta>1. Similarly delta cannot vanish, since Q is either0 or has absolute value at least Delta^2>1. Nor can Cy vanish: QV^2=1 would force Q=1. Hence Da is nonzero.

The quintic pi(t)=(t^2+3)(t^3-19) has no rational zero. Since Ac=H^5 pi(T+K/H), Ac is nonzero. At S=0 equation(1) reduces to delta Ac^2, also nonzero. Thus every zero has s,r nonzero. We do not yet exclude c=0, assert P>0, or invoke a Pell classification.

## 3. Coprime product and the sign bootstrap

The three nonzero integers BP,Df,Da are pairwise coprime, with signs still unrestricted. Df=1 modulo BP. Since Q=0 modulo BP, Da=1 modulo BP. Modulo Df,

    Q=-Delta, delta=-A^2, V=-c, Cy=-Dm,
    Da=A^2 Dm.

Because A|U and Dm|BP, Df is1 modulo both A and Dm. Hence gcd(Df,Da)=1 as well.

Multiply(1) by delta and divide by the nonzero rational square S^2:

    (delta Z/S)^2 = BP Df Da.                         (2)

A rational number whose square is an integer is integral. Thus the right side is a nonzero integer square. Pairwise coprimality makes the absolute value of each factor an integer square.

For every integer A, Delta A^2=(A^2-1)A^2 is divisible by4. Thus Df=1 modulo4, even if BP is negative. A negative square cannot be1 modulo4, so Df>0. If c!=0, then U!=0 and BP<0 would imply Df=1+Delta U^2 BP<0, impossible. Hence BP>0 in this case. If c=0, then U=0, Dm=Df=1 and Da=1; equation(2) itself gives BP=P>0. Therefore BP>0 unconditionally at a zero. Since Dm>0, P>0; then(2) makes Da>0 as well. There are positive integers

    p0^2=BP, f^2=Df, e^2=Da.                          (3)

Now Dg=P/Dt>0. As s!=0, Budget<=1 would give Dg<=-3. Hence Budget>=2. The centered budget yields k!=0, Derr<q^2, common strict signs of q,F,C,q-F-C, and |c/k-Y|<1/2. Because |Y|>=1, this excludes c=0 (equivalently, at c=0 the displayed Budget is nonpositive).

## 4. Recover the main square BEFORE splitting P

Define in the proof

    I=U p0, T_old=p0 T.

These are integers with I!=0, c^2|I and |I|>=c^2>=|c|. The exact recovered identities are

    f^2=1+Delta I^2,
    Q=(Delta I)^2>1,
    V=f^2(c-R+4I T_old)-c.

The rational y=e/delta satisfies QV^2-(Q-1)y^2=1. The adjacent-Pell denominator descent retained in source/centered11-proof.md Section4.2 makes y integral. Its norm-preserving map decreases |V| after signs while preserving the reduced denominator, until |V|=|y|=1.

We now use ONLY the early absolute folding theorem in source/signed-quadratic-proof.md Section2, not the later rank theorem requiring the first Pell root. For completeness, its precise argument is as follows. Put B=|A|>=3, C0=|c|, I0=|I|. Classify f=chi_B(m), I0=psi_B(m); then f>2I0. Put rho=Delta I. The auxiliary norm gives |rho| |V|=chi_|rho|(nu) with nu odd. The odd quotient-polynomial identity and V=-c modulo f imply

    psi_B(nu)=+/- C0 modulo f.

Fold nu modulo2m and reflect to0<=p<=m. Since psi_B(p)+C0<=2I0<f, this congruence cannot wrap and yields psi_B(p)=C0, p>=1. Therefore

    Dm=1+Delta c^2=d^2

for an integer d>0. This proof needs the strong and auxiliary norms and the bound C0<=I0, all already established; it does NOT use Dt being square, k's first index, the main projector, or orientation.

Only now does p0^2=Dm P imply P=(p0/d)^2. A rational square root of an integer is integral, so P is an integer square. Since gcd(Dt,Dg)=1 and both are positive, Dt=tau^2 and Dg=g^2 separately. The full original first/strong/auxiliary norm system has now been restored without circularity.

Canceling nonzero delta in(1) after Cy=delta y^2 gives Z^2=S^2p0^2f^2y^2. Thus Z/S is integral and S|Ac. In particular H|K^5.

## 5. Signed ranks, short index, and source restoration

The retained pre-projection signed rank theorem now has all its hypotheses. The actual residues are V=-c modulo f and V=-R modulo c, since

    V+R=Delta I^2(c-R)+4I Df T_old.

Its nonodd strong-rank proof (source/centered11-proof.md Section5.2) uses c^2|I to give c|m, not an unsupported oddness assumption.

For the native modulus, k=R+1+hXY is unchanged. For the short modulus M=4q^4, the authentic packing bound0<R<|q|^4-2 gives M>3R+1, while4|W and Y=(2v+1)q^3 give M|2XY^2. Thus the first-Pell recurrence yields epsilon 2n=R+1 modulo M. The same strip and growth argument gives main index p>n; strong/auxiliary step-down gives p=R. The negative congruence branch would give n>R and is impossible. No-wrap then gives2n=R+1. This is exactly the smaller-index argument retained in source/INCOMING_LOWOPS_PROOF.md Section5; it does not assume M=XY. The canonical positive first-Pell recurrence conversely has M|k-R-1. After orientation, reducing it modulo XY restores the literal old integer h_old=(k-R-1)/(XY).

Write R=2t+1, t>=24 and x=|X|>=4(beta-1)>=2^64. The retained sign-uniform ratio bound gives |H|>x(x-3)^t>x^(t+1)/2^t. Let Kq=X(X+2ac)-1 and sigma=sign(c). From K=HXc-2Kq and H odd, H|Kq^5. The Pell projector congruence gives

    H | [(sigma X-2^R)(2^R sigma X+1)]^5.

The product's fifth power has absolute value less than2^(20t+20)x^10<|H|, because64(t-9)-(21t+20)=43t-596>=436. Thus sigma X=2^R. The retained orientation and uniform half-binomial interval restore X,c,k,Y>0 and0<eta/k<1/4.

To avoid any silent oddness change, the source's Section5.4 regenerates I_star=psi_A(Rc), f_star=chi_A(Rc) and rho_star=Delta I_star. Since A even and R,c odd, rho_star is an odd multiple of c^2. The new r_old=(rho_star/c^2-1)/2 is integral. Its quotient-polynomial auxiliary V_star and y_star satisfy V_star=-c modulo f_star^2 and V_star=-R modulo c, giving the exact old o and j coordinates; eta,k-eta supply old positivity rows and2^((R-1)/2) its square coordinate. Together with h_old when needed, this is an actual old signed Q41 zero. Only then is the retained native/compiler/finite-refutation theorem invoked.

## 6. Completeness with the guard fixed before the strong pair

Start with the canonical native outer tuple. It already supplies Dm=d^2, Dt=tau^2, A even positive, R=3 modulo4, c=psi_A(R)>0 and c=R modulo4, with Budget>64. Use the appropriate native or short modulus to define h as in Section5.

Because Dt=1 modulo3, D Dt=(3Budget-4)Dt is positive and2 modulo3, a nonsquare. A positive Pell unit squared once gives s,g>0 with g^2=1+4D Dt s^2. Fix this guard pair. Then P=(tau g)^2 is fixed, and

    p0=d tau g

is a fixed positive integer satisfying p0^2=Dm P.

Choose ONE strong pair I,f such that

    4s A p0 c^2 | I, f^2-Delta I^2=1,

and set r=I/(A p0 c^2), U=I/p0. This is the retained finite-period construction. Keep I,f,r fixed. Every prime of p0 s r divides I. Supported-modulus interpolation (source/POWERED_SATURATION_PARENT.md Section5) therefore realizes every T_old class modulo p0 s r for this same strong pair.

The canonical projector gives H|K; write kappa=K/H. Select an intersective root a0 of pi(T+kappa) modulo sr and prescribe

    T_old=p0 a0 modulo p0 s r.

Interpolation supplies this T_old and an integral auxiliary y. Set T=T_old/p0, so T is integral, T=a0 modulo sr, and

    Ac/S=H^4 pi(T+kappa)/(sr) in Z.

The exact auxiliary equality is unchanged because4I T_old=4U BP T. Finally choose n=Ac/S+p0 f y. Equation(1) vanishes.

The order is canonical outer data, guard s/g, fixed p0, one strong I/f/r, intersective residue, auxiliary T_old/y and T, then n. No guard is reselected after the strong pair, and no strong pair is changed after selecting a residue. This proves completeness and the claimed ordinary equivalence of universal nonvanishing to syntactic Con(ZFC) through the same explicit calibration.

## 7. Exact degree and audit

Native register degrees are

    a6, k7, P94, Dm14, BP108, U9,
    Df138, Q150, V256, Cy662, S8, Ac35, Z35.

Short-index degrees replace k,P,BP,Df,Q,V,Cy by5,82,96,126,138,232,602. The term S^2 BP Df Cy uniquely dominates delta Z^2, yielding exact degrees924 and840.

Let q0=6beta j, X0=12q0 w, Y0=2v q0^3, a0=X0Y0. Write k0=h a0 in the native case and k0=4h q0^4-q0^3F0 in the short case, with F0=12wC-q0z. The complete top form is

    2^36 3^7 q0^14 X0^64 Y0^106 k0^42 s^16 r^12 c^34 T^2.

Its native attained coefficient is2^960 3^677 beta^564 at

    j^564 w^106 v^148 h^42 s^16 r^12 c^34 T^2,

and its short coefficient, selecting h^42, is2^918 3^635 beta^564 at

    j^564 w^64 v^106 h^42 s^16 r^12 c^34 T^2.

Their exponents sum to924 and840. These are exact authentic coefficients, not generic or sampled claims. Local standard-library audits and separate independent review verify every live gate, fixed-payload reconstruction, coprimality and rescaling identities, sign prerequisites, and exact attained degree; finite checks do not replace unbounded proof dependencies.
