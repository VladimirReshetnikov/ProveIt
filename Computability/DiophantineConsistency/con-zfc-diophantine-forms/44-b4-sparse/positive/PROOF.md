# Removing the inner separator: twelve positive unknowns, degree 901

## Result and comparison

The new full-carrier polynomial has twelve strictly positive unknowns, exact degree 901 and 112 charged binary arithmetic operations. Its three-equation system has maximum degree 892 and 107 operations, or 106 after the inherited positive transport-coordinate shift. The shorter carrier gives degree 905 in 110 operations, and a degree-896 system in 105 or 104 operations. Every binary addition, subtraction and multiplication is charged, including multiplication by a numeral; comparisons in a system are free. These counts include all expressions, with sharing, and every gate and supplied port is live.

Compared with the pinned twelve-positive degree-1022/124-operation construction, degree 901 removes 121 degrees (11.84%) and 12 operations. Compared with its degree-1013/120-operation system, the new shifted system removes 121 degrees and 14 operations. This is a structural improvement, not just evaluator rewriting: the inner radical-separating multiplier disappears completely. The new outer weight exploits a previously unused relation between the two Pell radicands.

The reduction is ordinary mathematics formalizable in ZFC. It proves that each displayed presentation has no solution in the stated positive domain if and only if Con(ZFC), through the inherited normalized blank-K215 compiler. It does not prove consistency, claim global minimality, give eleven unknowns, or provide a new kernel-checked end-to-end certificate.

## 1. Fixed instance and common interface

Use the entire materialized source31 121-by-8801, 943-tile coefficient tuple, with beta=2^1064921-1, K0=K, MC=MC and MF=MF_source, the shifted mask. All four ports must come from that tuple. COEFFICIENT_BINDING.json records the four binary and gzip hashes, source adapter proof and explicit relative-path basis. The byte payloads are shared with the sibling sun/sources/data directory in the full release; they are not duplicated. The original source30 compact tuple is historical provenance only, not the selected fixed instance. The proof below is uniform in any complete authentic normalized tuple satisfying the stated common interface; source31's complete coefficient adapter instantiates it here. These are fixed integers, not extra existential parameters. The emitter verifies all four payload hashes and never imports or executes received programs. Finite test values are not a replacement coefficient selection.

The supplied positive variables are

    J,F,alpha,z,h,i,T,s,w,eta,zeta,t.

Define the unchanged polynomials

    q=beta J+1, Cw=q-F-alpha, X=wq, Y=sq^3, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y, H=4a+3,
    Delta=a^2+H=(a+2)^2-1,
    ell=EkY, A=1+ell(ell+k), G=1+Delta c^2, b0=X+ac,
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J,
    Nk=k-hE-R, Nt=(K0+w)Cw+q-F-z(q-1),
    I=ic^2, D=1+Delta I^2, Q=Delta(D-1)=(Delta I)^2,
    d=Q-1, v=cT, b=c+RD,
    e=Q(Dv^2+b^2)-1, Baux=2Qvb.

Only the merger and carrier change. Put

    K=IT+1, L=1+HK, W=b0+H(t+b+delta),
    delta=(a+2)c-ell              (full carrier),
    delta=ac-ell                 (short carrier).

Every name in these displays other than the twelve supplied variables and four fixed ports is a polynomial abbreviation. In particular K is a new computed outer weight and is not the fixed compiler coefficient K0.

For a formal x define

    C(x)=d(x^2+A)-e,
    F(x)=[C(x)^2+D Baux^2-4d^2 x^2 A]^2-4C(x)^2 D Baux^2.

The norm is the integer polynomial

    N=H^16 F((W-L sqrt(G))/H) F((W+L sqrt(G))/H).

Equivalently it is the product of eight factors

    d(W-L g-H tau)^2-H^2 e+H^2 Baux f,
    g=+/-sqrt(G), tau=+/-sqrt(A), f=+/-sqrt(D).

Signs are formal conjugate-product notation, not a claim of independent Galois automorphisms. The root symbols add no quantified variables. The three presentations are

    P=Nk Nt(1+N)-1=0;
    Nk=1, Nt=1, N=0;
    S=(Nk-1)^2+(Nt-1)^2+N^2=0.

## 2. Division-free scalar evaluator and unit guard

The emitted circuit uses the same trace/remainder identity as source30 and the Horner norm evaluation of source37. With the inner multiplier equal to one, put

    dn=d H^2 A, HQ=H^2 Q, HP=HQ Dv^2, HU=HQ b^2,
    He=HP+HU-H^2, j=4HP HU,
    Trace=2d(W^2+L^2G), Knorm=[d(W^2-L^2G)]^2,
    AA=2(dn+He), constant=(dn-He)^2-j,
    at=Trace-AA, bt=constant-Knorm, coef=16dn j,
    vbar=coef-at(at Trace+2bt), ur=bt^2-at^2 Knorm,
    term1=ur(Trace vbar-ur), term2=Knorm vbar^2,
    N=term2-term1.

To verify, eliminate tau and f first. The resulting expression in x=d z^2 is (x^2-AA x+constant)^2-coef x. For z=W+/-L sqrt(G), those two x values have sum Trace and product Knorm. Reduction modulo x^2-Trace x+Knorm gives ur-vbar x, whose norm is exactly term2-term1. This is an identity over an integer polynomial ring and includes zero, square or coincident radicands.

Writing x0=d(W^2+L^2G) gives Trace=2x0 and Knorm=x0^2-4d^2W^2L^2G. Therefore

    N = (ur-x0 vbar)^2 modulo 4.

At a product root, the three integer factors Nk,Nt,1+N are units. Since N cannot be -2 modulo 4, necessarily N=0 and Nk=Nt=epsilon for a common epsilon in {1,-1}. A system root gives epsilon=1 immediately.

## 3. Bounds available before recovery

The unchanged authentic weak compiler interface, valid for both unit signs and the boundary Cw=0, supplies

    q>=16, X>=q, Y>=q^3, E=XY>=q^4,
    3q<R<q^4-2<E, k=R+epsilon+hE>E,
    kY<c<2kY, a+2<2E.

Thus E>=65536, Y>=4096, c>EY and I>=c^2. In particular c>=2, I>c, and all H,Q,d,v,b,Baux are positive. All uses of these inequalities precede any recovered square root; the coefficient-interface theorem is not replaced by finite residue checks.

Let g=sqrt(G), f=sqrt(D), tau=sqrt(A) denote the positive real roots for estimates. We have g<(a+2)c<2Ec and f<(a+2)I<2EI, because c,I>1. Also

    Delta c^2>A>1.

Indeed Delta c^2>(E+Y)^2 k^2Y^2, while A=1+E^2k^2Y^2+Ek^2Y. Their difference is greater than k^2[EY(2Y^2-1)+Y^4]-1>0. Consequently g>tau and

    1<A<Delta I=sqrt(Q).                       (3.1)

The following two estimates replace all inner-separation requirements:

    b+cf<d,                                   (3.2)
    Ig-cf>1.                                  (3.3)

For (3.2), since c<I^2 and D<4E^2I^2,

    b<5RE^2I^2<5E^3I^2,  cf<2EcI<2EI^2,
    d=Delta^2I^2-1>(1/2)E^4I^2>6E^3I^2>b+cf.

All inequalities use only E>=65536 and the preceding bounds.
For (3.3), the exact identity

    (Ig)^2-(cf)^2=I^2-c^2

first gives Ig>cf. Since I>=c^2 and c>=2,

    Ig-cf=(I^2-c^2)/(Ig+cf)
          >I^2/(4Ig)>I/(8Ec)=ic/(8E)>Y/8>1.

## 4. Recover the main radical without an inner separator

The roots of F have the coherent description

    x=tau'+y, (tau')^2=A, (f')^2=D,
    d y^2=Q(vf'-b)^2-1=e-Baux f'.             (4.1)

This follows by the two elementary quadratic factorizations and does not divide by x, C(x), or any root.

For either f' and even a complex y put Z=b+vf>1. Then

    d|y|^2<=Q Z^2+1,
    [Z(1+1/d)]^2-(QZ^2+1)/d=(QZ^2-d)/d^2>0.

Thus |y|<Z+Z/d. Since T>=1, (3.2) yields Z=b+Tcf<=T(b+cf)<Td. Equation (3.3) yields T(Ig-cf)>T. Hence

    |y|<b+vf+T<b+ITg,
    |x|<=tau+|y|<b+(IT+1)g=b+Kg.              (4.2)

At N=0 choose g'=+/-g with F((W-Lg')/H)=0. A negative choice would instead give

    x=(W+Lg)/H=b+t+delta+b0/H+(K+1/H)g>b+Kg,

contradicting (4.2); both carrier corrections are positive since ac-ell=kY^2+a eta>0. If G were nonsquare, the actual quadratic conjugation of Q(sqrt(G)) would carry the vanishing rational-coefficient expression at one sign to the other sign, which has just been excluded. Thus g is a positive integer, and x=(W-Lg)/H is rational.

This argument does not assume all auxiliary roots are real. It uses actual quadratic conjugation only for G, not independent automorphisms of every formal root.

## 5. Modular obstructions recover the inner roots

The conventional argument forced C(x)>0 by a large multiplier. The following integer-modulus obstruction proves the only needed conclusion, C(x)!=0, without any multiplier.

Suppose C(x)=0 at a root of F. Then D Baux^2=4d^2x^2 A. Substituting x^2=e/d-A and Baux=2Qvb yields the integer identity

    d^2 A^2-d e A+Q^2v^2b^2D=0.

Modulo Q, both d and e are -1; therefore Q divides A(A-1). But (3.1) gives 0<A(A-1)<Q, a contradiction. Separately, F(0)=0 would yield

    (dA-e)^2=D Baux^2,

hence Q divides (A-1)^2, also impossible by (3.1). Thus x and C(x) are nonzero at every root of F.

For the rational x already recovered, define

    Ux=C(x)^2+D Baux^2-4d^2x^2 A,
    f'=-Ux/(2C(x)Baux),
    tau'=(C(x)+Baux f')/(2dx), y=x-tau'.

The equation F(x)=0 gives (f')^2=D. Substitution gives (tau')^2=A and (4.1). Thus the rational f',tau' are integers, being rational square roots of integers. All denominators have now been justified rather than silently excluding an exceptional branch.

The rational y is also an integer. Use the following inherited Pell saturation lemma: if m>=2 and V are integers, and m^2V^2-(m^2-1)y^2=1 with y rational, then y is integral. A proof is included in the next section. Apply it with m=Delta I and V=vf'-b. Therefore x is integral. Reducing W=Lg+Hx modulo H gives g=b0 modulo H, so gamma=(g-b0)/H is an integer. Moreover g>(a+1)c and c>X, hence gamma>0.

## 6. Rational Pell saturation and compiler reconstruction

For completeness, write y=p/q reduced, q>0. The equation forces q^2 to divide m^2-1. Put D0=(m^2-1)/q^2; it is a positive nonsquare integer. The integer-coordinate Pell solutions (m,q) and (m|V|,|p|) are powers of the fundamental positive integer-coordinate unit, with indices j,l. Their abscissas chi_j,chi_l satisfy chi_j|chi_l. Pell addition gives chi_(n+2j)=-chi_n modulo chi_j and chi_(2j-n)=-chi_n modulo chi_j. Reducing and reflecting l to 0<=r<=j, strict growth 0<chi_r<chi_j for r<j forces l to be an odd multiple of j. The ordinate addition formulas then give q|p, so reducedness gives q=1. This uses the integer-coordinate Pell group, not half-integral units.

We have recovered

    (tau')^2-ell(ell+k)=1,
    (X+ac+Hgamma)^2-Delta c^2=1,
    (f')^2-Delta i^2c^4=1,
    Q[c(Tf'-1)-R(f')^2]^2-(Q-1)y^2=1,
    Nk=Nt=epsilon.

The auxiliary identity is vf'-b=c(Tf'-1)-R(f')^2. Take positive absolute values of tau',y. If f'<0, simultaneously replace f',T by -f',-T. The inherited normalized signed-quotient interface permits that signed T, forces epsilon=1 and extracts an accepting blank K215 computation. Gamma was already proved positive, so no new signed-main-root theorem is assumed. The existing K215 syntactic-refutation calibration supplies the logical endpoint ZFC-inconsistency.

## 7. Constructive completeness and the positive coordinate

Conversely take a canonical positive normalized compiler witness, including g,tau,f,y,gamma>0. The integer V=vf-b cannot be zero in QV^2-dy^2=1. Thus

    y^2=V^2+(V^2-1)/d>=V^2, so y>=|vf-b|>=b-vf.

Both corrections obey delta<g. Indeed ell/c> E/2>2, so (a+2)c-ell<ac<g; the short correction is smaller. Define the new integer

    t=gamma+Kg+tau+y-b-delta.

It is positive, because

    t>gamma+ITg+tau+y-b>=gamma+tau+ITg-vf>0.

The last strict inequality follows from Ig>cf. Its defining identity gives W=Lg+H(tau+y), so a coherent factor of N vanishes. Also Nk=Nt=1. This construction neither enlarges a Pell index nor imposes a new divisibility restriction on a compiler coordinate.

The shifted system uses (K0+w)Cw=F+z(q-1), corresponding to z_old=z+1. Soundness follows by substitution. Authentic solutions have Cw>0 and X=wq=2^R with R>3q, hence w>q>F and (K0+w)Cw-F>0. Thus z_old>=2 and the shifted z remains positive. This inherited shift saves one arithmetic operation. It is applied only after compiler reconstruction, not as a premature weak bound.

Combining soundness and completeness and negating proves, in ZFC, that absence of positive solutions is equivalent to Con(ZFC).

## 8. Exact degrees and nonzero leading forms

All supplied variables have weight one and the four fixed ports weight zero. Write a subscript 0 for highest homogeneous parts, and use formal Laurent expansions solely for degree calculation. Put

    q0=beta J, k0=eta+zeta, X0=wq0, Y0=sq0^3,
    E0=X0Y0, c0=k0Y0, I0=ic0^2, H0=4E0, ell0=E0c0,
    d0=E0^4 I0^2, B=R0 E0^2 I0^2, R0=q0^3(q0-F),
    V=I0 T ell0.

Their degrees are respectively H:6, ell:11, d:46, B:38 and V:23. The positive-leading roots have g0=tau0=ell0 and f0=E0 I0. The exact identity used in (3.3) gives the degree-one leading form

    ITg-vf = Ti c0/(2E0) + terms of smaller degree.

For a factor with signs (sg,sa,sf), write

    Z=W-Hb-H sa tau-L sg g.

The factor is

    2dHbZ+dZ^2-H^2b^2-H^2QDv^2+H^2+sf 2H^2Qb vf.

The degree-119 terms cancel exactly when sf=sg. The four noncanceling factors have leading forms -sg 4H0^2 d0 B V and degree119. For the matched signs, the potentially degree104 part dZ^2-H^2QDv^2 has degree at most94: its leading square cancellation follows from

    d I^2 G-Q D c^2=Q(I^2-c^2)-I^2G.

The other large terms have degree at most88, except the displayed linear terms. For the full carrier the four matched factors, ordered (sg,sa)=(+,+),(-,-),(-,+),(+,-), have exact degrees and leading forms

    107: -4H0^2 B d0 ell0,
    107:  4H0^2 B d0 ell0,
    105:  4H0^2 B d0 k0 Y0^2,
     97:  H0^2 B d0 [2t+k0-iT c0/E0].

For the last line it is essential to retain the supplied t, whose Ht term ties the degree-one radical correction. The last bracket is a nonzero rational homogeneous expression; the prefactors cancel its denominator. It is nonzero for every authentic fixed beta>0 because t occurs independently with nonzero coefficient.

Consequently the exact full norm leading form is

    -2^14 H0^16 d0^8 B^8 V^4 ell0^2 k0 Y0^2
        [2t+k0-iT c0/E0],                      degree892.

For the short carrier, the last matched factor instead has degree101 and leading form -4H0^2 B d0 c0. The exact norm leading form is

    2^16 H0^16 d0^8 B^8 V^4 ell0^2 k0 Y0^2 c0, degree896.

Every omitted matched-branch term is lower: the short radical error is degree5, while the full special error is degree1; the branch b0-g has degree5, and b0+g degree11, still below the relevant linear term except Ht in the explicitly retained special case. These bounds also follow by substituting the displayed exact square identity and keeping the cross terms of Z.

The nonzero leading parts of Nk,Nt are -hE0 and w(q0-F-alpha)-zq0, with degrees7 and2. Thus product degrees are901 and905 uniformly for every fixed valid tuple, not just at generic numerical ports. The sum-of-squares degree doubles the norm degree.

## 9. Reproduction, provenance and scope

Run python build_positive.py, then python check_positive.py. The emitter requires only the standard library. The independent checker uses NumPy for complete univariate polynomial multiplication over three prime fields, not numerical interpolation. It verifies the analytic leading coefficients and exact degrees, independently multiplies the eight formal radical factors for 24 signed exact-integer and 60 modular assignments per carrier, includes zeros and degeneracies, checks the mod 4 guard and 24 transport-coordinate shifts per carrier. All checks remain active under python -O. Finite diagnostics corroborate arithmetic identities and transcription; they do not replace the proofs above or verify the inherited unbounded compiler.

SOURCE_PINS.json records immutable repository commits, blob IDs and local SHA256 values. The current review pin is 22e75dd6b87b1b199bb08c778d7cf075ae5aae08. The historical source30 Wang943 recipes are preserved only for provenance at their original immutable pin ae3007ca4467011e0e051c84acb4a1dd13971b0e. The selected whole tuple is source31, as recorded in COEFFICIENT_BINDING.json. Main inherited dependencies are source30's complete positive compiler interface and Pell saturation, source34's positive carrier corrections, and source37's sharper auxiliary-root bound, scalar evaluator and transport shift. The new contributions are the mod-Q exceptional-root exclusion with inner multiplier one, the relation (Ig)^2-(cf)^2=I^2-c^2 used for outer recovery, and the combined degree-901 carrier.
