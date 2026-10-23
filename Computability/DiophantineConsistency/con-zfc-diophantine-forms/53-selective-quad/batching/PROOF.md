# Eleven positive unknowns by denominator-reduced index absorption

## Result and scope

There are exactly eleven supplied positive integer variables:

    J,F,alpha,z,i,T,s,w,eta,zeta,t.

The full carrier gives one equation of exact total degree 958 in 117 binary arithmetic operations. Its two-equation system has residual degrees 2 and 956, in 113 operations, or 112 after the inherited positive transport shift. The short carrier gives degree 962 in 115 operations, and a shifted system of degrees 2 and 960 in 110 operations. Every addition, subtraction, and multiplication is charged, including scalar multiplication. Powers in the scalar evaluator are expanded into multiplication gates. Fixed coefficients and references to existing registers are free.

These results improve the pinned source38 eleven-positive frontiers 1154/123 and 1140/129 in both degree and arithmetic-operation count. The full equation is 16.98% lower degree than 1154. They do not dominate the twelve-positive degree-901 frontier and make no global optimality claim.

The proof combines source38's short-index reconstruction with source44's multiplier-one norm. Two additional arguments are necessary: the outer-root gap is weighted by d rather than compared with 1, and only Y, not E, is needed as the absorbed denominator. This is not merely a circuit rewrite.

The logical endpoint is, in ordinary mathematics formalizable in ZFC,

    no positive solution of the displayed equation iff Con(ZFC).

This is not a proof of Con(ZFC), a finite search, or a new end-to-end proof-assistant formalization. The calibrated blank-K215/compiler equivalence remains the explicit inherited dependency. No Sun representation theorem is used by this eleven-positive construction.

## 1. Fixed data and explicit equations

The four fixed ports beta,K0,MC,MF must be one whole authentic normalized blank-K215 tuple, with MF already the shifted high mask. The concrete delivered choice is the same materialized Wang943 121-by-8801 tuple used by source44, beta=2^1064921-1. The four compressed binaries and raw/compressed SHA256 hashes are in coefficients/ and COEFFICIENT_BINDING.json. The actual whole-tuple adapter is reproduced in upstream/COEFFICIENT_PROOF.md, Sections 1-5; upstream/SIGNED10_PROOF.md Section 2 identifies this tuple but is not itself that adapter proof. The arithmetic argument is uniform in any complete tuple satisfying the inherited interface; arbitrary numerical test ports do not define the calibrated equation.

Define the following integer polynomials in the eleven supplied variables:

    q=beta J+1, s0=s+3q, X=wq, Y=s0 q^3, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y,
    H=4a+3, Delta=a^2+H=(a+2)^2-1,
    ell=EkY, A=1+ell(ell+k), G=1+Delta c^2, b0=X+ac,
    Cw=q-F-alpha,
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J,
    Nt=(K0+w)Cw+q-F-z(q-1),
    I=ic^2, D=1+Delta I^2, Q=Delta(D-1)=(Delta I)^2,
    d=Q-1, v=cT, b=c+RD,
    e=Q(Dv^2+b^2)-1, Baux=2Qvb,
    K=IT+1, L0=1+HK,
    delta=(a+2)c-ell                      [full carrier],
    delta=ac-ell                          [short carrier],
    S=HY, L=Y L0,
    W=Y[b0+H(t+b+delta)]+H(k-R-1).

The temporary K is not the fixed compiler coefficient K0. No abbreviation adds a quantified variable. Define

    N = product over g^2=G, tau^2=A, f^2=D of
        [d(W-Lg-S tau)^2-S^2 e+S^2 Baux f].          (1)

Each of g,tau,f takes two formal signs. The product is invariant under each formal sign change and is an integer polynomial, including at degenerate radicands. We do not assume independent Galois automorphisms of its formal radicals. The single equation and system are

    Nt(1+N)-1=0;                                   (2)
    Nt=1, N=0.                                    (3)

A completely division-free evaluator for N is

    dn=d S^2 A, HQ=S^2 Q,
    HP=HQ Dv^2, HU=HQ b^2, He=HP+HU-S^2, j=4HP HU,
    Trace=2d(W^2+L^2G), Knorm=[d(W^2-L^2G)]^2,
    AA=2(dn+He), constant=(dn-He)^2-j,
    at=Trace-AA, bt=constant-Knorm, coef=16dn j,
    vbar=coef-at(at Trace+2bt), ur=bt^2-at^2 Knorm,
    left=ur(Trace vbar-ur), right=Knorm vbar^2,
    N=right-left.

The JSON circuits are the exact gate-level definitions. In a system the last comparison is left=right, saving the final subtraction. Eliminating tau and f first gives (x^2-AA x+constant)^2-coef x in x=d z^2. The two values x corresponding to z=W+/-L sqrt(G) have sum Trace and product Knorm; reduction modulo their quadratic gives ur-vbar x and the displayed final norm. Thus the evaluator identity is universal.

## 2. Unit extraction and bounds before any square-root recovery

Let x0=d(W^2+L^2G). Then Trace=2x0 and

    Knorm=x0^2-4d^2 W^2 L^2G,
    N=(ur-x0 vbar)^2 modulo 4.

At a root of (2), both Nt and 1+N are integer units. N=-2 is impossible modulo 4, so N=0 and Nt=1. Conversely (3) implies (2).

The inherited authentic transport interface at Nt=1 yields

    q>=16, Cw>0, q-F>0, 3q<R<q^4-2.

In particular Cw>0 does not require a Pell root: if Cw<=0 then, since K0+w>0,

    Nt<=q-F-z(q-1)=1-F-(z-1)(q-1)<=0.

The positive coordinate shift now gives

    X>=q>=16, Y=(s+3q)q^3>3q^4>3R,
    E=XY>R+1, k>=2, kY<c<2kY, c>96,
    I>=c^2, a+2<2E.

We do not assume k>E or c>EY. Those stronger inequalities are unavailable before index reconstruction.

Put g=sqrt(G), f=sqrt(D), tau=sqrt(A), all positive real. Direct comparison gives

    1<A<Delta c^2<=Delta I=sqrt(Q),
    g>tau, g<(a+2)c<2Ec, f<(a+2)I<2EI.

For A<Delta c^2, use c>kY and
Delta c^2>(E+Y)^2 k^2Y^2, whose difference from A is greater than
k^2[EY(2Y^2-1)+Y^4]-1>0.

## 3. The weighted root-gap lemma

The identity

    (Ig)^2-(cf)^2=I^2-c^2

implies Ig>cf. Since I>=c^2 and c>=2,

    Ig-cf=(I^2-c^2)/(Ig+cf)>I/(8Ec).                (4)

Indeed I^2-c^2>=3I^2/4 and Ig+cf<2Ig<4EIc; the weaker displayed constant suffices. Also

    b+cf<6E^3 I^2, d>(1/2)E^4 I^2.

The first follows from b=c+R D<5R E^2 I^2<5E^3 I^2 and cf<2E I^2; the second follows from Delta>E^2. Combining with (4),

    d(Ig-cf)>E^3 I^3/(16c)
              >=E^3 I^2 c/16
              >6E^3 I^2>b+cf,                    (5)

because c>96. This replaces the earlier, stronger and inapplicable Ig-cf>1 condition.

The roots of the inner norm have coherent form

    x=tau'+y, (tau')^2=A, (f')^2=D,
    d y^2=Q(vf'-b)^2-1=e-Baux f'.                (6)

This is an algebraic factorization, without division by x or any root. For either sign of f' and every complex y, write Z=b+vf>1. Then

    |y|^2<=[QZ^2+1]/d<[Z(1+1/d)]^2.

For the second inequality the numerator of the difference is QZ^2-d>0. Since T>=1,

    Z/d<=[T(b+cf)]/d<T(Ig-cf)

by (5). Consequently

    |y|<b+ITg, |x|<b+(IT+1)g=b+Kg.               (7)

## 4. Recovering integral radicals and the weak index congruence

At N=0 some main sign gives x=(W-Lg')/S satisfying the inner norm. For g'=-g,

    x=b+t+delta+(k-R-1)/Y+b0/H+(K+1/H)g>b+Kg.

Here t+(k-R-1)/Y>0 follows from Y>3R, while delta>0 and b0>0. This contradicts (7). If G were nonsquare, quadratic conjugation of the rational-coefficient inner polynomial would force the forbidden main sign as well. Thus g is a positive integer and x=(W-Lg)/S is rational.

Define C(x)=d(x^2+A)-e. The inner polynomial is

    F(x)=[C(x)^2+D Baux^2-4d^2x^2 A]^2
          -4C(x)^2 D Baux^2.

If C(x)=0 and F(x)=0, substitution of x^2=e/d-A yields the integer identity

    d^2 A^2-d e A+Q^2v^2b^2D=0.

Modulo Q this says Q divides A(A-1), impossible because 1<A<sqrt(Q). Likewise F(0)=0 would give Q|(A-1)^2, also impossible. Therefore x and C(x) are nonzero. With

    Ux=C(x)^2+D Baux^2-4d^2x^2 A,
    f'=-Ux/(2C(x)Baux),
    tau'=(C(x)+Baux f')/(2dx), y=x-tau',

F(x)=0 gives (f')^2=D, (tau')^2=A and (6). These rational square roots of integers are integral.

The inherited rational Pell saturation lemma says that m^2 V^2-(m^2-1)y^2=1, for integers m>=2,V and rational y, forces y integral. One proof writes y=u/v reduced, obtains v^2|(m^2-1), and compares the integer-coordinate Pell solutions (m,v) and (m|V|,|u|) for discriminant (m^2-1)/v^2. Divisibility of their abscissas forces the latter fundamental-unit index to be an odd multiple of the former index: reduce modulo twice the former index, reflect, and use strict growth. Ordinate divisibility then gives v|u, hence v=1. The discriminant is positive and nonsquare; zero-coordinate exceptions are excluded by the original equation.

Apply this with m=Delta I and V=vf'-b. Then y and x are integers. Reducing W=Lg+Sx modulo Y yields only

    Y divides H(k-R-1).                           (8)

This is intentionally weaker than the old E-divisibility and is all that is needed.

## 5. Identifying the main Pell index before using (8)

Let A0=a+2 and let chi,psi be its standard Pell sequences, whose fundamental integer-coordinate unit is (A0,1). There are positive indices p,m with

    g=chi(p), c=psi(p), |f'|=chi(m), I=psi(m).

Since I=ic^2, strong divisibility gives p|m. Write m=pj. Composition gives
psi(m)=c psi_g(j). Modulo c, g^2=1 and psi_g(j)=j g^(j-1), so c|j. Thus

    m>=pc>2p, c|m.

Also p>=2, and psi(p)>=(2A0-1)^(p-1)>2p, so p<c/2. Since c>2Y>6R, R<c/2 too.

The recovered auxiliary equation is

    QV^2-(Q-1)y^2=1,
    V=c(Tf'-1)-R(f')^2,
    Q=(Delta I)^2=Delta((f')^2-1).

Writing S0=Delta I, Pell classification shows S0|V|=chi_S0(j0) with positive odd j0=2r+1. The odd-index polynomial Q_r satisfies

    chi_S0(2r+1)=S0 Q_r(S0^2),
    Q_r(1-A0^2)=(-1)^r psi_A0(2r+1),
    Q_r(0)=(-1)^r(2r+1).

Modulo |f'|, Q=1-A0^2 and V=-c, whence psi_A0(j0)=+/-c. Squaring and using Pell doubling yields chi_A0(2j0)=chi_A0(2p) modulo chi_A0(m). Signed index reduction gives j0=+/-p modulo m: reduce 2j0 modulo 2m, reflect into [0,m], and use strict growth with 0<2p<m. The negative signed representative cannot coincide with chi_A0(2p), since 2chi_A0(m-1)<chi_A0(m). Hence j0=+/-p modulo c.

On the other hand Q is divisible by c^4, (f')^2=1 modulo c, and V=-R modulo c, so Q_r(0) gives j0=+/-R modulo c. Thus R=+/-p modulo c. Both p and R are strictly between 0 and c/2, forcing p=R. This is source38's signed-index reconstruction; it uses neither the deleted quotient nor a main congruence modulo H.

## 6. Why denominator Y suffices

The recovered square A gives

    (tau')^2-k^2 EY(EY+1)=1.

The fundamental positive integer-coordinate solution for discriminant EY(EY+1) is (2EY+1,2): ordinate 1 is excluded by consecutive squares and ordinate 2 is attained. Put P0=2EY+1. Then for some n>=1,

    |tau'|=chi_P0(n), k=2psi_P0(n).

Since P0>A0 and c>k, monotonicity of Pell sequences gives n<p=R. Also P0=1 modulo E, hence

    k=2n modulo E, and therefore modulo Y.         (9)

Now gcd(Y,H)=gcd(Y,3)<=3. By (8), with mu=Y/gcd(Y,H),

    2n=R+1 modulo mu, mu>=Y/3>R.

Since 1<=n<=R-1, |2n-R-1|<R<mu, and so

    2n=R+1.

Equation (9) now gives full E|(k-R-1), not merely Y-divisibility. Define

    h=(k-R-1)/E>0.

Positivity holds because R>3q>=48 implies n>=25 and k=2psi_P0(n)>2n. Dividing the carrier identity by Y gives

    b0+H(t+b+delta+hX)=L0 g+H(tau'+y).

Since L0=1 modulo H, g=b0 modulo H. Thus gamma=(g-b0)/H is integral. It is positive: n>=2 gives k>=4P0>X and c>X, while g>(a+1)c, so g-b0>c-X>0.

We have reconstructed the authentic normalized compiler equations with h,gamma positive, tau',f',y integral, Nt=1 and k-hE-R=1. Replacing tau',y by absolute values is harmless; if needed replace f',T simultaneously by -f',-T. The inherited signed-quotient interface extracts a blank K215 halt, hence a finite ZFC refutation. This states the inherited boundary rather than asserting a new formalization of it.

## 7. Completeness and both positive coordinate changes

Take a canonical normalized compiler witness of a blank K215 halt. Its established properties include X=2^R, Y>2^R and R>3q. Since q>=16 and 2^(3q)>3q^4, the old positive s-coordinate obeys s_old=Y/q^3>3q. Hence s=s_old-3q is positive and preserves all original quantities.

Use positive canonical g,tau,f,y,gamma,h. Since V=vf-b is a nonzero integer, the auxiliary equation gives y>=|vf-b|>=b-vf. Both carrier corrections satisfy 0<delta<g: ell/c>E/2>2 gives (a+2)c-ell<ac<g. Define

    t=gamma+Kg+tau+y-b-delta-hX.

This is integral and

    t>gamma+ITg+tau+y-b-hX
      >=gamma+tau+T(Ig-cf)-hX>0.

The final strict inequality uses Ig>cf and tau>ell=EkY>k/Y>hX, where hX=(k-R-1)/Y. Its defining identity makes W=Lg+S(tau+y), so (1) vanishes, with Nt=1. Thus the new equation and system are complete.

For the shifted system use

    (K0+w)Cw=F+z(q-1)

instead of Nt=1. It is the substitution z_old=z+1. Every new solution gives an old one. Conversely canonical witnesses have Cw>0, w=2^R/q>q>F, and the original transport equation then forces z_old>=2. Thus z stays positive. The shift saves one gate and changes no degrees.

## 8. Exact degree and leading form

Let N12 denote source44's multiplier-one twelve-positive norm, with old s-coordinate s_old and carrier t_old. In the localization at Y, our formal norm satisfies the exact identity

    N=Y^16 N12(s_old=s+3q,
                t_old=t+(k-R-1)/Y).              (10)

Each of eight factors is scaled by Y^2. As N12 has degree at most 16 in t_old, all denominators clear. The rational shift has total degree 0 (R has degree 4 and Y degree 4), below t's degree 1. It cannot change any highest factor leader in the established Laurent factor certificate. The affine substitution s_old=s+3q has invertible highest-linear part s+3beta J, so it preserves nonvanishing of the highest form.

For clarity, write

    q0=beta J, s00=s+3q0, k0=eta+zeta,
    X0=wq0, Y0=s00 q0^3, E0=X0Y0, c0=k0Y0,
    I0=ic0^2, H0=4E0, ell0=E0c0,
    d0=E0^4 I0^2,
    B=R0 E0^2 I0^2, R0=q0^3(q0-F), V=I0 T ell0.

The inherited full norm's exact degree is 892, with nonzero leading form

    -2^14 H0^16 d0^8 B^8 V^4 ell0^2 k0 Y0^2
           [2t+k0-iT c0/E0].

The short norm has exact degree 896, with leading form

     2^16 H0^16 d0^8 B^8 V^4 ell0^2 k0 Y0^2 c0.

These are polynomial after cancellation of the displayed denominator. The full form is nonzero for every authentic beta>0 because its t coefficient is nonzero. Multiplication by Y0^16 contributes 64 degrees. Hence the new norm degrees are 956 and 960. The transport leading form is

    Nt_2=w(q0-F-alpha)-zq0,

nonzero for every beta>0. Thus the product degrees are exactly 958 and 962, not merely generic upper bounds. The scalar circuit's coarse syntactic degree is larger because it does not track norm cancellations.

The full inherited factor-degree certificate consists of four factors of degree 119 and four of degrees 107,107,105,97. The short version replaces 97 by 101. The substitution in (10) leaves every factor leader unchanged, since its rational carrier perturbation has degree 0 rather than 1. More explicitly, put r=(k-R-1)/Y and let Z12=W12-L0 g-H tau in an unscaled source44 factor. Replacing t by t+r changes that factor by 2d Z12 H r+dH^2 r^2. Since deg(Z12)<=44, deg(d)=46 and deg(H)=6, these two Laurent terms have degrees at most 96 and 58, both strictly below the smallest original factor degree 97. This supplies a direct factor-level check rather than an assumption that substitution preserves a canceled highest form.

## 9. Finite verification and sources

Run build_eleven.py and check_eleven.py, then repeat the checker under python -O. The builder verifies all four actual payload hashes and audits every supplied input, fixed port and gate for liveness. The checker independently multiplies all eight formal conjugate factors at 24 signed exact-integer and 60 modular assignments per carrier, verifies the mod4 guard, checks three complete finite-field polynomial rays per carrier both with illustrative and actual fixed ports, verifies the analytic highest forms, and checks the transport shift. It also stresses 288 pre-index parameter choices, including k=2 with arbitrarily large X, precisely where the old bound Ig-cf>1 is unavailable. These finite checks support identities and transcription; the unbounded proof is the argument above plus the stated inherited interfaces.

The repository baseline is main commit 124c07c0b77a9e20e84676514d8b1ff78536ea3f, fetched through the GitHub connector. Relevant source directories under Computability/DiophantineConsistency/con-zfc-diophantine-forms are:

- 38-batching11/eleven/ELEVEN_POSITIVE_PROOF.md: initial quotient absorption, signed-index reconstruction and shift s_old=s+3q.
- 44-b4-sparse/positive/PROOF.md: multiplier-one merger, rational-root exceptional-case exclusion, outer norm, completeness and exact degree-892/896 factor certificate.
- 31-sun10/coefficients/COEFFICIENT_PROOF.md: the actual complete 121-by-8801 Wang943 tuple adapter, including its unbounded rank controller and positive/signed completeness promises. It is copied as upstream/COEFFICIENT_PROOF.md.
- 31-sun10/signed10/SIGNED10_PROOF.md: Section 2 identifies the same whole tuple and port conventions; its Sun integer finalization is not used here.
- 37-wave5/positive/upstream/30-POSITIVE12_PROOF.md and 26-ratio12__proofs__RATIO12_PROOF.md: explicit normalized compiler reconstruction and the signed-quotient boundary, copied as upstream/NORMALIZED_COMPILER_PROOF.md and upstream/RATIO12_PROOF.md. Their older coefficient tuple is provenance, not the selected tuple; the copied source31 adapter supplies the replacement.

DEPENDENCIES.md distinguishes the locally checked reduction from the inherited marked-Wang/compiler and blank-K215 calibration theorems. The independent all-presentation package audit in ../elimination/audit_package.py also verifies the twelve pinned source blobs, original binding and coefficient-adapter hashes, all live gate ledgers, and 72 complete polynomial rays over finite fields. Both audit programs pass under ordinary Python and Python -O.

The mathematical notes and code are AI-assisted. No independent human review or kernel-checked consistency theorem is claimed.
