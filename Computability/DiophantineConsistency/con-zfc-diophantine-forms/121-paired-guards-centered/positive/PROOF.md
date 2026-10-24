# Auxiliary-powered coprime Pell fusion

## Result and precise scope

There are three explicit integer polynomials, each in the same ten strictly positive variables J,F,alpha,i,T,x,Y,n,eta,zeta. Their literal binary circuits have respectively 94,96,97 operations and exact degrees 262,258,254. Every coefficient is fixed by the complete original compact44 tuple in coefficients/. A zero exists exactly when a finite syntactic refutation exists under the retained source61/native/controller calibration. Thus, at that calibration, absence of positive zeros expresses Con(ZFC).

This is an ordinary unbounded arithmetic proof relative to that fully retained calibration, not a new machine-checked Lean endpoint or a claim that ZFC is consistent. No global minimum is claimed. The changes are deliberately distinguished from new upstream results: coprime product fusion and upper/sharp centering already occur in the Saturated Pell arrival; the auxiliary index bound already occurs in Structural Compression. The new result combines those mechanisms on the fused direct chart and contracts the redundant q^4 gate. It improves the arrival's 98/258 and 99/254 by two operations each, and supplies the uncentered 94/262 tradeoff.

## 1. Complete formulas

Let beta,K0,MC,MF be exactly the ports in coefficients/BINDING.json. They obey beta odd, beta>=31, K0>0 and 0<MC<beta<MF<2beta. Define

    q=beta*J+1, X=q+x, mu=q^2+1, A=mu*Y*(X+1)+1,
    Delta=A^2-1, H=4A-5, k=eta+zeta, c=kY+eta,
    v0=X*mu^2*Y^2, D=v0*(v0+1)*k^2+1, E=i*c^2,
    G=(q-1)*(q-F)+alpha,
    R=G*(q^2-1)+(MC+q*MF)*J, e=k-R-1,
    C=q-F-alpha, B=(q*K0+X)*C-q*F,
    Fs=1+Delta*D*E^2, Q=Delta^2*D*E^2, delta=Q-1,
    b=c*(T+alpha)-R, V=Fs*b-c, Dnum=Q*V^2-1,
    P=q^4*(q-1), M=P*mu^2*H, Kpos=X*(3c-2X)+2.

Choose the fixed center S=0, S=(A+1)DE, or S=ADE for the uncentered, upper, or sharp circuit, respectively. S is not an extra variable. Put

    Z=P*mu^2*[H*(n+V+S-bB)+Kpos]
        +H*[mu^2*(q(q-1)Y-q^3B-(q-1)X)-P*e],
    s=delta*Z^2, u=delta*M^2*D*Fs, v=M^2*Dnum,
    N=(s-v-u)^2-4uv.

The requested equation is N=0. All abbreviations are integer polynomials. The complete live circuits are uncentered.json, upper.json, sharp.json. The exact rational-center identity is

    Z/M=n+V+S+Kpos/H+Y/q^3-WB/[q(q-1)]-X/q^4-e/mu^2,
    W=1+q(q-1)b.                                           (1)

Fractions and roots appear only in the proof, not the circuit.

## 2. Root extraction and the exact inherited interface

Before any input is known to be a zero, D>1, E>=c^2, Fs>c+2, Q>1 and delta>0. For integer b, either b=0 and V=-c, or |V|>=Fs-c>1. Hence a=D*Fs and d_y=Dnum/delta are positive. They are unequal: delta*a=Dnum is impossible modulo D, since Q=0 modulo D makes Dnum=-1 modulo D.

The identity

    (z^2-a-d_y)^2-4*a*d_y
      = product_{epsilon,nu=+/-1}(z-epsilon*sqrt(a)-nu*sqrt(d_y))

therefore shows that a zero gives a nonzero rational signed sum of the roots. Squaring and solving linearly gives both roots rational. The integer a is a square and gcd(D,Fs)=1 because Fs=1 modulo D. Thus

    D=tau^2, Fs=f^2, tau,f positive integers,
    I=tau*E, f^2-Delta*I^2=1, Q=(Delta*I)^2, c^2 divides I.

The adjacent-Pell rational-to-integral descent gives y=sqrt(d_y) an integer. For completeness, if y=a/m in lowest terms and Qv^2-(Q-1)y^2=1, then m^2 divides Q-1. For v>1 the transformation

    v'=(2Q-1)v-2(Q-1)y, y'=(2Q-1)y-2Qv

preserves the norm, keeps v' integral and the reduced denominator m of y', and has 0<|v'|<v. The inequalities v<y<Qv/(Q-1) prove the decrease; v'=0 is impossible. Descent reaches v=1,y=1, so m=1. Start with v=|V|. We obtain

    Z/M=epsilon*tau*f+nu*y.                               (2)

The retained all-index folding lemma now applies, because A>=3, c<=I, c^2|I and V=-c modulo f. It gives c=psi_A(p) for an odd p>=1. The first norm gives k=2*psi_(2v0+1)(n0). The case n0=1 forces eta=zeta=1 and c=2Y+1, strictly between psi_A(1)=1 and psi_A(2)=2A. Therefore n0>=2 and k>=8v0+4. Since c>=3, p=1 is excluded, and

    c>=psi_A(3)=4Delta+3,
    c>kY>=k>=8v0+4,
    R<c*alpha/4,
    b>c*(T+3alpha/4)>c, V>1, Kpos>0.                     (3)

The mask bound R<c*alpha/4 is exactly the retained pre-transport estimate, not a consequence of C>0. None of (2)-(3) assumes B>=0, a main-index equality, q even, or divisibility of e by mu^2. The source of these universal folding and mask interfaces, including their proofs, is retained in source/PRIOR96_PROOF.md and its named source/*.md and SOURCE61.tex dependencies.

## 3. A large auxiliary index replaces the transport majorant

Write S0=Delta*I, so Q=S0^2. The equation S0^2V^2-(S0^2-1)y^2=1 and V>0 give S0*V=chi_S0(nu0) for a positive Pell index nu0. Even indices have chi_S0(nu0)=+/-1 modulo S0, so nu0 is odd. By (3),

    V=Fs*b-c>(Fs-1)c=Delta*I^2*c>4Q.

The indices 1 and 3 have V=1 and V=4Q-3 respectively. Therefore nu0>=5 and

    V>=16Q^2-20Q+5>8Q^2,
    b=(V+c)/Fs>8Q,                                      (4)

where Fs=1+Delta*I^2<Q and Q>=3.

Put h_y=y-V>0. Because Q-1>2Fs,

    h_y=(V^2-1)/[(Q-1)(y+V)]<V/[2(Q-1)]<b/4.            (5)

Also b-e=c(T+alpha)-k+1>0, so e<b; since mu^2>4,

    e/mu^2<b/4.                                         (6)

This is an upper bound, even when e is negative. It uses no divisibility. Finally, f<A*I, hence

    tau*f<A*D*E<Q,
    X/q^4<X<D<Q,
    tau*f+X/q^4<2Q<b/4.                                 (7)

Here Delta^2*E>A is immediate from A>=3,E>=1, and D>v0>X.

If B<=-1, then WB/[q(q-1)]<-b because W=1+q(q-1)b. Solve (1)-(2) for n. The chosen S is nonnegative on the positive domain, while Kpos/H and Y/q^3 are positive. Using (5)-(7) gives

    n< b/4+b/4+b/4-b=-b/4<0,

a contradiction. Thus B>=0 before any main-index or denominator claim.

## 4. Soundness by a whole-polynomial positive transfer

Let N_old be precisely the 96-operation fused polynomial in source/prior96_equation.json. It uses L_old=HDE+b and center S_old=0. The universal identity

    n_old=n+S+HDE*B                                      (8)

makes its entire carrier exactly equal to the new carrier: the change in n cancels the change from L_old*B to bB and inserts S. All kernel registers, M and both norm radicands agree. Consequently

    N_new(J,F,alpha,i,T,x,Y,n,eta,zeta)
      =N_old(J,F,alpha,i,T,x,Y,n+S+HDE*B,eta,zeta)

as integer polynomials, with no solution or positivity premise. At a new positive zero, Section 3 has proved B>=0. Therefore n_old>0, and every old coordinate is positive. The complete retained old soundness theorem applies and yields a finite refutation.

This transfer preserves its rigorous chronology: B>=0 gives C>0 and the mask range; strong-rank and signed-index lemmas give p=R; only then parity gives q even, denominator coprimality gives mu^2|e, first-index comparison gives n0=(R+1)/2, and the ratio plus whole-product projection gives X=2^R. The remaining fractions give q|X, q^3|Y and the native transport condition. Reconstruction uses a fresh unscaled A_source=Y(X+1)+2. No mixed coefficient tuple, premature cancellation modulo H, or identification of scaled and unscaled strong witnesses occurs.

## 5. Completeness with positive witnesses, including t=0

A finite refutation supplies canonical source data from the retained construction: X=2^R>q, R=3 modulo4, R>3q, q^3|Y, q^4|X, and the positive first/main data. Set x=X-q, c=psi_A(R), k=2psi_(2v0+1)((R+1)/2), tau=chi_(2v0+1)((R+1)/2), eta=c-kY and zeta=k-eta. The zero-offset ratio theorem makes eta,zeta positive, D=tau^2, and rho=(k-R-1)/mu^2>=0. The native source transport supplies t=B/[q(q-1)]>=0.

Choose a positive power m of the determinant-one Pell recurrence matrix that is the identity modulo tau*c^2. Finite order in the finite invertible matrix group proves that such m exists. Its strong ordinate I=psi_A(m) is divisible by tau*c^2. Set i=I/(tau*c^2)>0 and f=chi_A(m), so E=I/tau and the literal Fs=f^2, Q=(Delta I)^2.

Use the retained auxiliary-completeness lemma with its explicit witness

    S0=Delta*I, V_*=chi_S0(R)/S0, y=psi_S0(R),
    T_*=(V_*+c+R*f^2)/(c*f^2), T=T_*-alpha.

The lemma proves T_* integral. With r=(R-1)/2>=2, the elementary Pell growth bound gives V_*>=(3Q)^r>=9Q^2, and therefore T_*>9S0>alpha. Thus T>0 and the literal V equals V_*.

Put h_y=y-V_*. Since V_*>1 and y<2V_*,

    h_y=(V_*^2-1)/[(Q-1)(y+V_*)]>V_*/(4Q)>=9Q/4.         (9)

The universal projection gives an integer kappa=Kpos/H with 0<kappa<c<I. Also sY=Y/q^3<Y<c<I and uX=X/q^4>0 are integers. For either centered choice,

    S-tau*f<2DE<2I^2,

since (A-1)I<f<AI and E>1. For S=0 the same upper bound is automatic. Define

    n=W*t+rho+tau*f-S+h_y-kappa-sY+uX.                   (10)

This is an integer. Its total negative loss is less than 2I^2+2I<4I^2, whereas (9) exceeds 4I^2 because Q=Delta^2 I^2 and Delta>=3. Thus n>0 even when t=0. Substitution in (1) gives Z/M=tau*f+y, and a norm factor vanishes. This proves completeness without asserting a positive inverse of (8) on arbitrary old zeros.

## 6. Exact degrees with nonzero highest forms

Set q0=beta*J, X0=q0+x, k0=eta+zeta. The exact leading forms are

    [N_uncentered]_262 = -2^10 q0^126 X0^30 Y^62 i^10 k0^32 (q0-F)^2,
    [N_upper]_258 = 2^11 q0^124 X0^29 Y^61 i^10 k0^32 (q0-F)^2,
    [N_sharp]_254 = 2^10 q0^122 X0^28 Y^60 i^10 k0^32 (q0-F)^2.   (11)

They are nonzero at the fixed coherent ports, since beta>0. For example the coefficients of J^126 x^30 Y^62 i^10 eta^32 F^2, J^124 x^29 Y^61 i^10 eta^32 F^2, and J^122 x^28 Y^60 i^10 eta^32 F^2 are respectively -2^10 beta^126, 2^11 beta^124, and 2^10 beta^122. Their exponent sums are exactly 262,258,254.

Here is an exact global degree proof, rather than only a syntactic bound or numerical ray. Scale all ten variables by t and work over their rational function field in formal Laurent series at t=infinity. The relevant degrees are A4,E5,D16,Fs34,Q42,V38,M13 and g=sqrt(D Fs)25. The rational remainder

    r=n-bB+Kpos/H+Y/q^3-B/[q(q-1)]-X/q^4-e/mu^2

has degree at most6. Choose formal roots g near ADE and y near V. The exact identities

    (ADE-g)(ADE+g)=D^2E^2-D,
    (y-V)(y+V)=(V^2-1)/(Q-1)

give degrees ADE-g=17 and y-V=-4. Therefore S-g has degree21 with leading DE for upper centering and degree17 with leading DE/(2A) for sharp centering; these both dominate r. The exact norm factorization is

    N=delta^2 M^4 product_{epsilon,nu=+/-1}(Z/M+epsilon*y+nu*g).

For S=0, two factors have degree38 and leading2V; the other two have degree25 and opposite leading g. Total degree is 2*42+4*13+2*38+2*25=262. For upper/sharp, the two leading38 factors remain, one remaining factor has degree25 and leading2g, and the last has degree21 or17. Totals are258 and254.

To verify the coefficients set a0=q0^2 X0Y, e0=i*k0^2Y^2, d0=q0^8X0^2Y^4k0^2 and r0=q0^3(q0-F). Then the leading forms of delta,M,V,g are a0^4d0e0^2, 4q0^9a0, -a0^2d0e0^2r0, a0d0e0. Multiplication of the four factors gives (11). Formal square roots exist by the binomial series with square leading forms; no analytic limit or positivity assumption is used in this degree proof.

## 7. Literal operations and replay

Relative to the frozen prior96 graph, remove exactly HI=HDE and L=HI+b, and change LB=L*B to LB=b*B. This gives94 operations. For the upper center insert Cg=(A+1)DE and nVCg=nV+Cg:96. For the sharp center also insert Afull=(A-1)+1:97. All remaining rows, including the optimized P=q^3*q(q-1), are unchanged. Every gate and input is live.

Run python -B build.py --check and python -B check.py, then the same with -O. check.py uses no disabled assertions. It audits every row, all coefficient hashes and bit lengths, complete signed old/new carrier and norm translations, the universal free-polynomial translation identity, the universal four-factor and centered identities, exact integer univariate ray expansions, actual-payload modular leading forms, independent closed-form carrier evaluations and concrete Pell-period examples. These checks detect transcription errors and supplement, not replace, the unbounded arguments above.

## 8. The ordinary chart and its shorter three companions

The same construction also has a multiplicative-base chart with positive variables J,F,alpha,i,T,w,Y,n,eta,zeta. Set X=qw (so X>=q>=32), B_t=(K0+w)C-F and P=q^3(q-1). Keep A,D,E,Fs,Q,V,Kpos and all other kernel definitions. Its carrier is

    Z=P*mu^2*[H*(n+V+S-bB_t)+Kpos]
       +H*[mu^2*((q-1)Y-q^3B_t)-P*e],
    M=P*mu^2*H, W=1+(q-1)b,
    Z/M=n+V+S+Kpos/H+Y/q^3-WB_t/(q-1)-e/mu^2.           (12)

The norm is unchanged. All root-extraction, folding and auxiliary-index arguments in Sections2-3 hold for X>=q. If B_t<=-1, its transport term is less than -b. There is no +X/q^4 error, so the same stronger contradiction proves B_t>=0 and C>0.

For clarity, the ensuing inherited interfaces on this chart are: 3q<R<q^4-2; p=R from normalized rank and signed-index recovery; q even from mask parity; gcd(mu^2,q^3(q-1)H)=1 and thus mu^2|e; n0=(R+1)/2 from first-index comparison; Y>X^r/3 and X^(r+1)<H from the exact ratio theorem, where R=2r+1. The integral center gives H|q^3(q-1)Kpos. Since H is odd and Kpos=HXc-2Kquad, universal projection gives

    H | q^3(q-1)(X-2^R)(2^R X+1).

The full right-hand product has absolute value smaller than H by the retained height argument. Therefore X=2^R. This is a whole-product bound, not cancellation of a possibly nonunit factor modulo H. Now q|X already holds from X=qw, so q is a power of two. The residual fraction in (12) gives q^3|Y and (q-1)|B_t because gcd(q^3,q-1)=1 and W=1 modulo q-1. Fixed-minus parity gives R=3 modulo4 and the same ratio rounding gives the source half-binomial. Fresh unscaled source reconstruction proves soundness. This is the complete post-transport interface proved for this chart in retained source/SATURATION_SEMANTICS.tex and the original ZERO/SHORT/WEIGHTED proof files; it is uniform in the complete coherent original tuple used here.

Completeness keeps the same canonical first, main, strong-period and explicit auxiliary witnesses from Section5, uses w=X/q>0 and t=B_t/(q-1)>=0, and omits uX from (10):

    n=W*t+rho+tau*f-S+h_y-kappa-sY.

Exactly the estimate (9) proves n>0, including t=0, and the center becomes tau*f+y. Hence all three ordinary polynomials have exactly the same refutation equivalence.

Their gate counts and exact degrees are89/288,91/283,92/278. Relative to a direct graph, replacing its five-gate B by the three-gate B_t saves two; deleting qbJ saves one; and deleting the low-X product and its subtraction saves two. No operations on fixed ports are silently omitted. The choices X=qw versus X=q+x are different coordinate charts, not a pointwise polynomial substitution claimed to preserve total degree.

Their highest homogeneous forms, with q0=beta J and k0=eta+zeta, are

    [N_ord,uncentered]_288=-2^10 q0^152 w^30 Y^62 i^10 k0^32(q0-F)^2,
    [N_ord,upper]_283=2^11 q0^149 w^29 Y^61 i^10 k0^32(q0-F)^2,
    [N_ord,sharp]_278=2^10 q0^146 w^28 Y^60 i^10 k0^32(q0-F)^2.

They are nonzero for the actual ports. The same exact Laurent factorization proves them: the degrees are A5,E5,D18,Fs38,delta48,V42,M13,g28; y-V has degree-6; upper/sharp defects have degrees23/18, both above the remainder bound6. The totals are 96+52+84+56=288, 96+52+84+28+23=283 and96+52+84+28+18=278. For the coefficient multiplication use a0=q0^3wY, d0=q0^10w^2Y^4k0^2 and m0=4q0^8a0 in Section6.

The ordinary graphs do NOT take their coefficients from the incoming BFS-calibrated JSON. They are built from this packet's own complete original compact44 graphs, preserve the binding byte-for-byte, and apply only the uniform ordinary-chart theorem. No original K0 is identified with the different BFS K0.
