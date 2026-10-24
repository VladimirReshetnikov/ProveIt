# One-sided residue control: ten positive unknowns, degree 912, 126 operations

## Result and source boundary

This packet supplies one fixed ordinary polynomial in ten strictly positive integer unknowns. Its exact total degree is 912 and its literal division-free circuit uses 126 live binary additions, subtractions, and multiplications. It improves the inspected four-root residue predecessor's 1152 / 131 in both measures, without changing its ten-variable domain or coefficient tuple.

The reduction is new relative to the inspected predecessor: translate the auxiliary coordinate, center the strong and auxiliary radicals, and bound the main-carrier residue only from above rather than in absolute value. A degree-two weight then replaces the predecessor's degree-38 majorant. The algebra does not establish global optimality or historical priority.

The complete compact44 coefficient tuple beta,K0,MC,MF is retained, with beta=2^590069-1 and MF already shifted. All four actual payloads and hashes are in coefficients/. They are fixed numerals, not witnesses. The calibration to finite ZFC refutations is inherited from the normalized compact44 source, with its native/compiler and K215 dependencies. The full ten-positive predecessor proof is retained as upstream/TEN_POSITIVE_PROOF.md; its normalized source and calibration references are retained in upstream/interfaces/. This is an ordinary proof formalizable in ZFC, not a newly supplied end-to-end Lean/Rocq or sealed object-language ZFC derivation.

## 1. Complete polynomial

The only quantified unknowns are

    j,F,alpha,i,T,X,s,n,eta,zeta > 0.

All the following are polynomial abbreviations:

    J=3j+1, q=beta*J+1, h=F+alpha, C=q-h,
    Y=q^3*s, E=X*Y, k=eta+zeta, c=k*Y+eta,
    a=E+Y, Aparam=a+2, H=4a+3, Delta=a^2+H=Aparam^2-1,
    ell=E*k*Y,
    R=((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J,
    Bt=(q*K0+X)*C-q*F,
    I=i*c^2, Df=1+Delta*I^2, Q=Delta^2*I^2, delta=Q-1,
    Told=T+h, Cf=Aparam*I,
    V=Df*(c*Told-R)-c,
    Dt=ell*(ell+k)+1, Dd=1+Delta*c^2,
    L=k*Told, W=1+(q-1)*L,
    v=k-R-1, U=q^5, S=q^4, b0=X+a*c, M=(q-1)*U,
    center=ell+k+n+L+s+V+Cf,
    Z=M*(H*center+b0)-H*U*W*Bt+H*(q-1)*(S*X-v),
    A=M^2*H^2*Dt, B=M^2*H^2*Df,
    D=M^2*Dd, Cnum=M^2*H^2*(Q*V^2-1).

Use this division-free four-root kernel:

    sigma=A+B+D,
    pairs=A*B+(A+B)*D,
    prod=A*B*D,
    aa=delta*(Z^2-sigma)+Cnum,
    tt=delta*Cnum*Z^2,
    kk=aa^2+4*(tt-delta^2*pairs),
    rr=16*delta^3*prod,
    bb=aa*kk-rr,
    ee=kk^2+16*tt*aa^2-4*rr*(delta*Z^2+Cnum),
    P10=ee^2-64*tt*bb^2.

The equation is P10=0. The literal graph is generated/p10_positive.json. Its circuit has 75 multiplications, 34 additions and 17 subtractions. Fixed numerals and reuse are free; squares and scalar products are charged.

For proof only, put Dy=(QV^2-1)/(Q-1). The kernel identity is

    P10=delta^8 * product_epsilon (Z-e1*M*H*sqrt(Dt)
       -e2*M*H*sqrt(Df)-e3*M*H*sqrt(Dy)-e4*M*sqrt(Dd)),

where each sign independently ranges over +/-1. The sixteen-factor product is a polynomial in the four squared roots, with degree at most eight in Dy, so denominator clearing is exact. The independent checker verifies the entire 495-term identity, not merely sampled evaluations. Both M*H and delta are positive on the declared domain.

## 2. Rational and integer root recovery

The predecessor's unconditional signed-subset separation applies with Told in place of T. For completeness, write positive roots t=sqrt(Dt), f=sqrt(Df), y=sqrt(Dy), d=sqrt(Dd). Positivity alone gives

    q>=16, Y>=q^3, c>=2Y+1, a>=2Y, I>=c^2,
    ell<t<ell+k<(a+1)c,
    f>(a+1)c^2, 0<d/H<c, t>2c+1.

Put b=c*Told-R. If b=0, V=-c and c<y<c+1; the four roots are superincreasing in order d/H,y,t,f. If b is a nonzero integer, |V|>=Df-c, whence y>f+t+d/H; the order d/H,t,f,y is superincreasing. The middle inequalities follow from f-t>(a+1)c(c-1) and f^2-c>2f. Thus no nonempty signed subset of t,f,y,d/H sums to zero.

In a multiquadratic field, roots from distinct rational square classes are linearly independent over Q. Projecting a rational signed sum onto any nontrivial square-class character would give a zero signed subset. Therefore a rational signed sum here makes every root rational. At P10=0 we obtain signed roots tau_*, f_*, y_*, d_* satisfying

    ell+k+n+L+s+V+Cf-W*Bt/(q-1)+b0/H+(S*X-v)/U
       =tau_*+f_*+y_*+d_*/H.

The first, strong, and main roots are integral because their squares are integers. The fourth is integral by adjacent-coefficient Pell descent applied to

    Q*V^2-(Q-1)*y_*^2=1.

That descent requires only integer Q>1 and integer V. In lowest terms y_*=b/m gives m^2 | Q-1. The norm-preserving map

    V'=(2Q-1)V-2(Q-1)y_*, y'=(2Q-1)y_*-2QV

has integral first coordinate, preserves the reduced denominator m, and, after taking positive signs, satisfies 0<|V'|<|V| whenever |V|>1. It reaches |V|=1, where |y_*|=1. All signs and possible rational denominators have thus been accounted for before positivity of C or native rank recovery is used.

## 3. Growth and a small one-sided residue bound

Integer first and main roots classify as

    |tau_*|=chi_(2XY^2+1)(m), k=2*psi_(2XY^2+1)(m),
    |d_*|=chi_(a+2)(p), c=psi_(a+2)(p).

Here chi and psi are the standard Pell sequences. Since c>1, p>=2. If m=1, k=2 and eta=zeta=1, so c=2Y+1<2(a+2), contradicting p>=2. Consequently m>=2 and

    k>8XY^2, c>8XY^3>=8q^9.

These conclusions precede C>0. The authentic mask inequalities 0<MC<beta and 0<MF<2beta give the unconditional bound

    |R|<Rhat=q^3(q+h).

Since h>=2 and c>8q^9, c*h>Rhat. Therefore

    0<c*Told-R<c*(T+2h), V>1.

Let y=|y_*|. From delta-(Delta-1)*Df=Delta*(I^2-1)>0 we obtain

    0<y-V<V/delta<c*(T+2h)/(Delta-1).

Since c<k(Y+1), a>=2Y, and Delta-1>4(Y+1), this implies

    y-V<k*(T+2h)/4<k*(T+h)/2=L/2.             (1)

Also f=|f_*|<Cf because Cf^2-Df=I^2-1>0.

Define rational proof coordinates

    r=tau_*-ell-k-s+W*Bt/(q-1),
    gamma=(d_*-b0)/H-(S*X-v)/U.

For either main-root sign, d_*<=d<(a+2)c, so

    gamma<2c/H+k/q^5+|R|/q^5
          <k/2+k/q^5+1/q+h/q^2
          <3k/4+h/4<k+h/2<=k*(T+h)/2=L/2.   (2)

Here 2c/H<k/2 follows from c<k(Y+1) and H>=8Y+3. For the next bound, q>=16 gives k/q^5<k/4, 1/q<h/8, and h/q^2<h/8. The last non-strict inequality is equivalent to k*T+k*h-2k-h>=0; it follows from T>=1 and (k-1)(h-1)>=1. No lower bound on gamma is asserted or needed.

The root equality reads

    r+gamma+f_*+y_*=n+L+V+Cf.

Using (1), (2), and f<Cf gives r>n>0 for every sign choice. The defining equation for r now gives

    W*Bt/(q-1)=ell+k+s+r-tau_*>0.

Thus Bt>0 and C>0. Only now do we use the native bounds 3q<R<q^4-2. This is the required noncircular positivity bootstrap.

## 4. Exact residue recovery and reconstruction

The remaining proof is the predecessor's Sections 4--7, with Told replacing T. It depends only on: the four integral roots; positive rational r; Y=q^3*s; the displayed merged root equality; C>0; and the same residues of V. All these have just been established. The centers L,V,Cf are integers and therefore do not alter the residue argument. Details are repeated to make the application explicit.

The normalized strong equation and I=i*c^2 imply a strong Pell index divisible by c and greater than 2p. With c>2R and c>2p, the signed auxiliary-index lemma applied to V=-c mod f and V=-R mod c gives p=R. Hence the first Pell index m satisfies 1<=m<R. Since r+gamma is integral, clearing its rational denominators yields U | H(q-1)(S*X-v). But q=2 mod 3 and H=3 mod q, so gcd(H,q)=1 and

    q^5 | q^4*X-v.

The first Pell recurrence gives k=2m mod 4XY^2. Thus q^4 | 2m-R-1; its absolute value is less than q^4, so R=2m-1. Now v=k-2m is a positive multiple of 4XY^2 and hence of q^5. Therefore q|X, (S*X-v)/U is integral, and

    (q-1)*(d_*-b0)/H is integral.              (3)

No coprimality of H with q-1 is asserted.

Put r0=(R-1)/2 and T0=2^R. Pell growth and c/k<Y+1 give

    Y>X^r0/2-1>q*2^R=q*T0.

The last inequality follows from q>=16, X>=q, and r0>=24. Modulo H, the main Pell polynomials satisfy

    chi_(a+2)(R)-a*c=T0,
    T0*(chi_(a+2)(R)+a*c)=1.

If d_* is negative, (3) makes (q-1)(1+T0*X)/H a positive integer smaller than one, impossible. Hence d_*>0. Then (3) makes (q-1)(T0-X)/H an integer of absolute value smaller than one, forcing X=T0. Consequently H|(d_*-b0), gamma is integral, r is integral, and (q-1)|Bt.

Restore the normalized source using

    w=X/q>0, h_source=v/(XY)>0,
    gamma_old=(d_*-a*c-X)/H>0,
    f_old=|f_*|, tau_old=|tau_*|, y_old=|y_*|,
    T_source=f_old*Told,
    z_new=((K0+w)*C-F)/(q-1)>0, z=z_new+1.

Positivity of gamma_old follows from d_*>(a+1)c and c>X. Every coordinate is an integer; the main, first, strong and auxiliary norms, the index congruence, and native transport equation hold exactly. This is a positive solution of the inherited calibrated normalized source.

## 5. Canonical completeness and freshness of choices

Start from a finite ZFC refutation and its canonical normalized compact44 source. Its outer coordinates are chosen first: q,Y,X,k,c,R,F,alpha, with X=2^R, R=3 mod 4, 3q<R<q^4-2, c>8q^9, and h=F+alpha<q. Choose the normalized strong pair f,I=i*c^2 next. The canonical auxiliary construction, with Maux=Delta*I, uses

    V*=chi_Maux(R)/Maux, y*=psi_Maux(R),
    Told=(V*+c+R*f^2)/(c*f^2).

This is a positive integer, and V*,y* satisfy the required norm. Since R>=7,

    V*>=Maux^(R-1)>=Maux^6,
    f^2<Maux^2, Maux>=c^2,
    Told>Maux^4/c>=c^7>q>h.

Also Told>Maux^4/c>Aparam*I=Cf, because Delta^4>Aparam and I^3/c>=1. Thus T=Told-h is strictly positive, and L=k*Told>Cf and L>k. Only now form L,W.

The canonical first index is m=(R+1)/2; v=k-2m is a positive multiple of 4XY^2. The rational gamma above is actually an integer and

    gamma=gamma_old-X/q+v/q^5>0,

since v/q^5>=4XY^2/q^5=4X*q*s^2>X/q. Define

    r=W*t0+tau-ell-k-s, where t0=Bt/(q-1)>=q.

The canonical bounds ell<tau<ell+k and s<k give r>qW-2k>2L. Finally set

    n=r+gamma+f+y*-L-V*-Cf.

This is an integer, and n>r-L-Cf>r-2L>0. The root identity holds with all four positive roots, so P10=0. There is no fresh congruence imposed on Y, no assumed freedom of a fixed auxiliary quotient, and no circular choice involving n or L. The order is outer source, strong pair, auxiliary pair, L and W, then r and n.

## 6. Exact degree, including cancellations

Naive gate propagation gives degree 1120, which is not the actual degree. Here is an exact leading-form proof. Scale every quantified variable by a formal parameter lambda and work in the Laurent-series field over the rational-function field of the original variables and fixed ports. All four squared-root leading coefficients are squares, so choose each formal root with its indicated positive leading center. This is a purely formal degree argument; it imposes no extra arithmetic restriction on inputs.

Write Kscale=M*H. Relevant degrees are

    q:1, Y:4, a:5, c:5, I:11, Cf:16, V:38,
    ell:10, M:6, Kscale:11, delta:42.

The exact identities imply the following leading-center errors:

    Kscale*sqrt(Dt)=Kscale*ell+O(lambda^12),
    Kscale*sqrt(Df)=Kscale*Cf - Kscale*I^2/(2Cf)
                     + terms of degree strictly below 17,
    Kscale*sqrt(Dy)=Kscale*V+O(lambda^7),
    M*sqrt(Dd)=M*b0+O(lambda^11).

For the strong root, the exact defect is Cf^2-Df=I^2-1 of degree 22. For the auxiliary root, Dy-V^2=(V^2-1)/delta has degree 34. For the main root, Dd-b0^2 has degree 15. These identities justify the displayed orders by the formal binomial expansion. Moreover

    Z=Kscale*(ell+Cf+V)+M*b0+O(lambda^15).

Consequently, among the sixteen linear factors, eight with the opposite auxiliary sign have degree 49, four with auxiliary sign aligned and strong sign opposite have degree 27, two with those signs aligned and first sign opposite have degree 21, and the remaining two have degree 17, irrespective of the main-root sign. In the last two factors the term Kscale*I^2/(2Cf), of degree 17, dominates both the degree-16 main center and the degree-15 remainder. There are no zero leading factors. The product therefore has degree

    8*49+4*27+2*21+2*17=576.

Multiplying by delta^8 adds 336, giving exact degree 912. Its leading form is

    4096*Q0^8*Kscale0^16*V0^8*Cf0^2*ell0^2*I0^4.

With q0=3*beta*j and k0=eta+zeta, direct simplification gives

    lead_912(P10)=2^44*q0^558*i^38*k0^86*X^68*s^154*(T+F+alpha)^8.

In particular,

    [j^558 i^38 eta^86 X^68 s^154 T^8] P10
       =2^44*(3*beta)^558>0.

The checker verifies the leading-form simplification exactly in a sparse integer polynomial ring. Independent finite-field univariate specializations verify the actual graph's degree and leading coefficient without using the formal branch calculation. Neither kind of calculation replaces the unbounded existence proof.

## 7. Conclusion and verification boundary

Sections 2--4 prove soundness, and Section 5 proves completeness. Compose these with the retained ordinary native/compiler/refutation calibration. ZFC therefore proves

    P10 has no strictly positive integer zero iff Con(ZFC).

No assumption of Con(ZFC) is used, and neither side is separately established. The explicit new contribution is a ten-positive polynomial of degree 912 in 126 operations, rather than a nine-variable result. A nonnegative ten-variable version is obtained by replacing each supplied variable x by x0+1; degree stays 912 and the delivered straightforward circuit uses ten more additions.
