# Independent ordinary audit: coprime first/strong Pell fusion

## Outcome and scope

The new 98-operation, ten-strictly-positive-variable construction is mathematically sound and complete relative to the same pinned source/native/refutation calibration as its accepted direct-zero-offset parent. The exact total degree is 266, not the syntactic bound 288. The argument below, not the finite controls, establishes the new unbounded arithmetic reduction. No new Lean theorem or encoded internal-ZFC proof object is certified here. No global minimality claim is made.

The reviewed equation is `positive/equation.json`, based on repository commit `84e16e43092614bae262ca59651cb9d77e31a255`. Its equation SHA256 is recorded in CHECK.json. The source theorem is inherited, not independently re-proved in this focused transformation audit. Its complete coherent coefficient tuple must remain intact.

Notation: D is the first radicand; E=i*c^2 is the polynomial register called I; f is the positive root of Fstrong; tau is the positive root of D. The reconstructed strong Pell ordinate is Iactual=tau*E, which is not a polynomial register. This distinction is essential.

## 1. No degenerate or nonintegral branch survives

At positive inputs q>=32, X>q, k>=2, c>=3, E>=c^2 and Vfirst=X*mu^2*Y^2. Hence D=Vfirst(Vfirst+1)k^2+1>X>1. Delta=A^2-1>1, Q=Delta^2*D*E^2>1 and M=q^4(q-1)mu^2H>0. Also Fstrong=1+Delta*D*E^2>c. Since V=Fstrong*b-c, an integer V cannot vanish: that would force Fstrong to divide c with 0<c<Fstrong. Therefore QV^2-1>0 and both normalized radicands

    a=D*Fstrong, d=(QV^2-1)/(Q-1)

are strictly positive. This handles b=0 and both signs of b simultaneously, before any root or center is declared rational.

After division by the nonzero factor (Q-1)^2*M^4, the scalar equation is

    (z^2-a-d)^2=4ad, z=Z/M rational.

The zero-center branch would imply a=d. Multiplication by Q-1 would then give (Q-1)D*Fstrong=QV^2-1. Reduction modulo D gives 0=-1, impossible because D>1. Thus z is nonzero. The quartic factors over the real numbers as the product of z-eps*sqrt(a)-nu*sqrt(d), so some signed sum is rational and nonzero. Squaring this relation gives each signed radical as a rational linear expression in z,a,d. Both radicals are rational.

A rational square root of a positive integer is integral. Moreover gcd(D,Fstrong)=1 because Fstrong=1 modulo D. Prime valuations in the integer square D*Fstrong are even, and coprimality forces each factor separately to be a square. Thus D=tau^2 and Fstrong=f^2 with positive integers tau,f. Consequently

    Iactual=tau*E, f^2-Delta*Iactual^2=1,
    Q=(Delta*Iactual)^2, c^2 divides Iactual, Iactual>=c.

The rational y=sqrt(d) is also integral, by the retained adjacent-coefficient descent. For completeness, write y=u/m reduced. The norm QV^2-(Q-1)y^2=1 gives m^2|(Q-1). With |V|>1 the transformation

    V'=(2Q-1)|V|-2(Q-1)y,
    y'=(2Q-1)y-2Q|V|

preserves the norm, makes V' an integer with 0<|V'|<|V|, and preserves the reduced denominator m of y'. Taking absolute values and descending to |V|=1 forces m=1. The cases V=0 and y=0 are impossible. Thus no denominator assumption is being imported before it is proved.

The center is now an integer of the form eps*tau*f+nu*y. Unlike the old three-root norm, no pair/triple radical cancellation or residue analysis modulo mu is needed.

## 2. Folding, positivity, transport and index order

All universal strong/auxiliary folding hypotheses hold for Iactual: c<=Iactual, f^2-Delta*Iactual^2=1, Q=(Delta*Iactual)^2, and V=-c modulo f. The odd auxiliary index folds to an odd p, so c=psi_A(p) with positive odd p. The first equation gives k=2psi_(2Vfirst+1)(n0) and tau=chi_(2Vfirst+1)(n0). If n0=1, then k=2 forces eta=zeta=1, and c=2Y+1 lies strictly between psi_A(1) and psi_A(2). Thus n0>=2 and

    c>8X*mu^2*Y^2.

This is unchanged from the parent and yields c>2X, Kpos>0, the mask bound R<c*alpha/4, b>0, V>0 and |e/mu^2|<b/2. The auxiliary norm gives

    y-V=(V^2-1)/[(Q-1)(y+V)]<V/[2(Q-1)]<b/2,

using Fstrong<Q-1 and V<Fstrong*b.

The changed transport multiplier is exactly the needed one. Since f<A*Iactual,

    tau*f<A*D*E.

Also D>X and E>=1, so X/q^4<D*E. Therefore

    tau*f+X/q^4<(A+1)D*E<H*D*E.

The final inequality uses A>2 and H=4A-5. Merely stating A>X and DE>=1 would not justify the preceding comparison; the explicit D>X observation repairs that wording without changing the construction.

If B<=-1, W=1+q(q-1)L and L=HDE+b>0 give WB/[q(q-1)]<-L. Solving the center for n and using the two b/2 bounds gives n<HDE+b-L=0, a contradiction. Thus B>=0, then C>0, then the old mask argument yields 3q<R<q^4-2. No q-evenness or denominator cancellation was used.

The normalized rank and signed auxiliary-index lemmas now apply: c^2|Iactual, c>2R, c>2p, V=-c modulo f and V=-R modulo c. They imply p=R. Since p is odd, R is odd. If q were odd, beta odd would make J even, and both summands of R would be even. Hence q is even. Only now is gcd(mu^2,q^4(q-1)H)=1 licensed.

## 3. Projection and source reconstruction are unaffected

The center is integral, so the single-modulus separation yields mu^2|e. The first-index proof uses only the unchanged first norm, c=psi_A(R), 2Vfirst+1>A and the bound R<q^4<mu^2. Indeed n0<R and the first norm gives 2n0 congruent R+1 modulo mu^2. The absolute value of 2n0-(R+1) is strictly smaller than mu^2, forcing equality. This avoids any unnecessary assumption that this difference is initially nonnegative.

With R=2r+1, r>=48, the unchanged zero-offset ratio yields Y>X^r/3 and X^(r+1)<H. Integrality of the center and e/mu^2 gives H|q^4(q-1)Kpos. The identity Kpos=HXc-2Kquad and odd H allow cancellation of 2 only. The universal projection then gives

    H divides q^4(q-1)(X-2^R)(2^R X+1).

The entire product has absolute value below H by the inherited X>=q>=32, r>=48 height estimate. Thus X=2^R. This uses the complete product, not an invalid cancellation of q or q-1 through H. It makes Kpos/H integral.

Next the remaining center fraction has numerator

    q(q-1)Y-q^3WB-(q-1)X

and denominator q^4(q-1). Reduction modulo q gives q|X only at this stage. Hence q=2^kappa. Since R>3q and 4kappa<=q, q^4|X. Writing B=q*Bt and removing X/q^4, coprimality of q^3 and q-1 gives q^3|Y and q-1|Bt, because W=1 modulo q-1. Thus t=Bt/(q-1)>=0 is integral.

The unchanged fixed-minus auxiliary parity and ratio rounding apply to these same A,c,R,X,Y,Iactual,f,V,y. Their conditions are exactly those already proved, so R=3 modulo 4 and Y is the source half-binomial. Fresh unscaled source reconstruction proceeds at A_source=Y(X+1)+2, not at the current scaled A. The new fusion does not identify these parameters or reuse a strong witness from the wrong parameter family.

## 4. Fresh completeness and the full period

Starting with the pinned canonical source data, choose the same new zero-offset c,k,tau as the parent; the ratio interval gives positive eta,zeta and rho=(k-R-1)/mu^2>=1. To enforce the new divisor, set h=tau*c^2 and take a positive period m of the invertible determinant-one matrix

    U=[[2A,-1],[1,0]] modulo h.

The finite matrix group guarantees U^m=Id. In the standard recurrence formula, the lower-left entry of U^m is psi_A(m). Therefore h divides psi_A(m). Put Iactual=psi_A(m) and i=Iactual/(tau*c^2). These are positive integers, and D=tau^2 makes the polynomial Fstrong equal chi_A(m)^2. Taking a period modulo tau and a separate c^2 divisibility statement would not suffice when they share factors; the construction correctly uses the full product modulus tau*c^2.

The retained auxiliary-completeness lemma permits any strong solution with c|Iactual, not merely the former canonical index Rc. It gives a positive auxiliary pair and Tstar=(V+c+Rf^2)/(cf^2). Its growth estimate remains valid for the larger arbitrary strong ordinate and implies Tstar>alpha. Thus T=Tstar-alpha is positive.

The projection gives 0<kpos=Kpos/H<Xc<f, while tau>Y>=Y/q^3. Here tau,f>2, so tau*f>tau+f and in particular tau*f>Y/q^3+kpos. With uaux=y-V>0 and uX=X/q^4>0, define

    n=W*t+rho+tau*f+uaux-Y/q^3-kpos+uX.

It is an integer and strictly positive even for t=0. The new center becomes tau*f+y exactly. Therefore the scalar quartic vanishes. This is a fresh canonical completeness construction, not an unsupported pointwise mapping of the old i coordinate.

## 5. Exact degree and literal certification

The independently derived leading degrees are D16, E5, Delta8, Fstrong34, Q42, V38, L25, W27, M13. Although Z has degree 51, the exact subtraction Z0=Z-MV leaves degree 40. The identity

    omega=(Q-1)Z0^2+2(Q-1)MVZ0-M^2(V^2-1)

has term-degree bounds 122,133,102. The middle term uniquely supplies degree 133. The other norm inputs have degrees u118 and v144, so (omega-u)^2-4uv has unique top omega^2 of degree 266.

Writing q0=beta*J, X0=q0+x, k0=eta+zeta and

    B0=(q0*K0+X0)(q0-F-alpha)-q0*F,

the complete highest part is

    omega0=2^7*q0^63*X0^15*i^5*Y^31*k0^16*B0*(q0-F).

The highest-x component of omega0^2 has x exponent 32. Selecting alpha^2 F^2 eta^32 gives the coefficient 2^14*beta^126 at

    J^126*x^32*i^10*Y^62*eta^32*alpha^2*F^2.

It is nonzero for the actual fixed beta>0, and its exponents sum to 266. Thus the degree claim is exact for the bound tuple, not just generic symbolic coefficients.

The independent audit.py imports neither the producer nor its checker. It checks 98 live operations (59 multiplications, 21 additions, 18 subtractions), all ten witnesses, the pinned parent and repository, and all four compressed/raw coefficient hashes. It compares the literal circuit with a separately written direct evaluator at 160 signed/positive controls, proves the universal normalization and centered identities symbolically, and checks the leading-form product and degree-attaining coefficient. These controls supplement, rather than replace, the preceding unbounded argument.

## Portable replay addendum

The replay script now derives its root from its own location and reads only the bundled positive component. No Git clone, Git executable, network access, or original workspace is needed. The original audit script and receipts are preserved under provenance. SOURCE_PINS.json records all 14 bundled source files, their SHA256 values, their original Git blob identities and paths at the pinned commit, and the original review hashes. The replay script pins that manifest itself and verifies every source and provenance hash. All former assertions are explicit checks that remain active under python -O. Normal and optimized replay produce identical substantive receipts. This packaging repair changes no equation, mathematical claim, or proof.
