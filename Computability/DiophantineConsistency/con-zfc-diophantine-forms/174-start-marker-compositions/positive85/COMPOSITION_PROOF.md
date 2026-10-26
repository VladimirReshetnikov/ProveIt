# Combining the inverse Lucas correction with a trace-linear auxiliary coordinate

Prepared 25 October 2026. This is a new composition relative to the explicitly
inspected ProveIt commit fb1bed5eb7196cf35abfaa746c18c6ee7eae6cfb. The bounded
comparison covers packages 163--165; no global minimality or literature
priority is claimed.

## The precise new result

The literal graph equations/inverse_lucas_trace85_degree232.json has ten
strictly positive integer variables, 85 live binary arithmetic operations
(51 multiplications, 18 additions, 16 subtractions), and exact total degree
232. It combines package 163's trace-linear auxiliary coordinate with
package 164's inverse Lucas correction. Package 163 costs 87 operations at
degree 232; package 164 costs 85 at degree 304. Their entire four-port
coefficient bindings, including every raw-byte hash, are identical.

The proof is an ordinary mathematical composition, formalizable in ZFC,
at the inherited native/refutation calibration boundary. It is not a newly
kernel-checked Lean/Rocq derivation and does not assert consistency or the
absence of a zero independently.

## 1. Literal equation

The independent positive integers are J,F,alpha,i,T,w,s,n,eta,zeta.
The entire four-tuple beta,K0,MC,MF is the tuple of package 164, not a
selection of ports from different encodings. Set

    h=beta J, q=h+1, C=q-F-alpha,
    X=qw, Y=qs, k=eta+zeta, c=kY+eta,
    A=Y(X+1)+1, Delta=A^2-1, H=4A-5,
    v=XY^2, ell=vk=(XY)(kY), E=1+ell(ell+k),
    R=[h(q-F)+alpha](q^2-1)+(MC+q MF)J,
    B=(K0+w)C-F, U=ic^2,
    a=Delta U^2E, F0=1+a, G=EF0,
    f=a+F0, Q=4Delta aF0,
    b=cT-R, V=fb-c, L=bV,
    K=X(3c-2X)+2,
    e6=6(k-R-1)-ell(k^2-4), D6=6q^6,
    M=hD6H,
    Z=hD6[H(n-LB)+K]-H[D6B+h(e6-6q^4s)].

The final polynomial is

    P = Q(Z^2-M^2GV^2)+(M^2G-Z^2).

The graph does not separately compute v; ell=(XY)(kY) shares two live
registers. All expressions above are polynomial abbreviations. There
are no additional quantified registers, variable exponents or division
operations. Quotients below are proof notation only.

## 2. Root extraction is unaffected by the correction

Write e*=e6/6, rho=e*/q^6, sigma=s/q^2, t=B/h, kappa=K/H,
z=Z/M and W=1+hL. The rational identity is

    z=n+kappa+sigma-Wt-rho.

Sections 3--4 of inherited/trace_PROOF.md apply verbatim: none of their
arguments uses the forward or inverse cubic correction. In particular
positive inputs give M>0, f>2c and Q>c^2. At a zero, valuation arguments
and rational adjacent-Pell descent give

    E=tau^2, F0=f0^2, G=g^2, z=epsilon*g*y,
    QV^2-(Q-1)y^2=1, epsilon in {1,-1},
    f^2-Delta I^2=1, I=2Ug, Q=(Delta I)^2, c^2|I.

The trace identity f-1=2Delta i^2 c^4 E is literal. Signed folding gives
c=psi_A(p), p odd positive. The first Pell norm gives
k=2psi_(1+2v)(m), m>=2, and c>8XY^3>=8q^4, c>X, K>0.

The main index-three and auxiliary index-three exclusions in package 163
are still valid. The latter uses exactly

    f(b-4Delta f)=c-(4Delta+3), or
    f(b+4Delta f)=c+(4Delta+3).

Both right sides are positive and smaller than f; both are impossible.
Thus its signed estimates hold:

    b!=0, sign(V)=sign(b), |V|>|b|,
    L>0, gy<L/2, |b|/q^6<L/2.

These are established before any assertion about B,C,R or the sign of V.

## 3. The inverse correction simplifies the sign argument

For every positive assignment k>=2 and vk(k^2-4)/6>=0, regardless of R.
Therefore

    e* <= k-R-1 < b,

the last inequality following from cT-k+1>0. In particular
rho<|b|/q^6. If B<=-1, then Wt<-L and

    n=epsilon gy-kappa-sigma+Wt+rho
      < L/2-L+|b|/q^6 <0,

a contradiction. Thus B>=0 and then C>0. The authenticated mask estimate
3q<R<q^4-2 is now licensed, so c>2R and b,V>0.

The explicit congruences required by package 163's rank recovery are

    V=-c (mod f), f=1 (mod c), V=-R (mod c).

Its normalized-rank and signed auxiliary-index theorems consequently give
p=R. This invokes the trace proof, not the invalid substitution of an
arbitrary Pell root into a trace formula.

## 4. Index authentication and denominator order are retained

Everything in Sections 3--4 of inherited/inverse_PROOF.md now applies
without change: the carrier identity and correction agree literally,
and all preceding hypotheses have been established in the correct order.
For clarity, let

    k=2m+8v C_m+32v^2 Z_m,
    C_m=binom(m+1,3), A_m=C_m+4vZ_m,
    d=2m-R-1, S_m=k^2+2mk+4m^2-4.

The exact identity is

    3(e*-d)=4v^2[24Z_m-A_m S_m].

Since v=q^3ws^2, every prime dividing q gives q^4|(e*-d).
The integral carrier first gives q^6|(e*-q^4s), hence q^4|e*.
The first Pell-base monotonicity gives m<R, so |d|<R<q^4 and d=0.

One must not infer q^6|e* yet: the factor 3 can obstruct it. Instead,
the integral carrier gives H|6hK. The retained uniform ratio bound and
whole-product projection force X=2^R. As q|X, q is a power of two.
Only then is division by 3 harmless, proving q^6|e*, q^2|s and h|B.
The complete outer endpoint is therefore

    X=2^R, q^3|Y, (K0+w)C-F=t(q-1), t>=0 integral.

The fixed-minus parity, half-binomial rounding and native reconstruction
are exactly the inherited interfaces. With all four actual coefficient
ports this extracts a finite syntactic ZFC refutation.

This establishes soundness for every new positive zero; it does not rely
on a finite search or on an inverse map that may fail to be integral.

## 5. Constructive completeness and a full-polynomial map

Start with any positive zero of the package 164 polynomial; the inherited
completeness theorem provides one from any finite ZFC refutation.
Its auxiliary coordinate is V_old=f^2(c T_old-R)-c. Define the polynomial

    d0=2Delta i^2 c^3 E, so f=1+c d0,
    T_new=f T_old-d0 R,
    n_new=n_old+(f-1)L_old B, L_old=(c T_old-R)V_old.

Keep every other independent coordinate. Then

    b_new=f b_old, V_new=V_old, L_new=f L_old,
    n_new-L_new B=n_old-L_old B.

Every other carrier term and finalizer register is unchanged. Consequently

    P_new(J,F,alpha,i,T_new,w,s,n_new,eta,zeta)
      = P_old(J,F,alpha,i,T_old,w,s,n_old,eta,zeta)

as an identity of polynomials over the fixed ports. At any old positive
zero the inherited proof gives 0<R<c/2, B>=0, b_old,V_old>0.
Hence T_new>f-(f-1)/2>0 and n_new>=n_old>0.
Thus this polynomial map sends every old positive zero to a new positive
zero. It does not assert an integral inverse for every new zero.

Combining this with soundness gives existential equivalence to a finite
ZFC refutation, and negating gives the required Con(ZFC) equivalence.

## 6. Exact cost and degree

Only two rows of package 164's 85-row graph change:

    Fsqr = 1+fouraF0       becomes trace_f = DpI2+Df,
    DfcTR = Fsqr*cTR       becomes DfcTR = trace_f*cTR.

The same fields are changed in package 163, while package 164's inverse
cubic replaces its forward cubic and removes two multiplication rows.
The full coefficient tuple and all independent coordinates are retained.
Every row remains live.

Set q0=beta J, k0=eta+zeta, and
B0=k0 s T-q0^2(q0-F). The complete highest homogeneous component is

    [P]_232 =
      -9*2^10 q0^100 w^26 s^58 i^10 k0^32 B0^2.

The leading part is identical to package 163's 87/232 graph: the inverse
cubic has degree nine and cannot affect the degree-57 carrier leader.
The dominant final term is -Q M^2 G V^2. Its degree is
80+22+50+80=232; QZ^2 has degree 194. The displayed leader has coefficient
-9*2^10 beta^100 at
J^100 w^26 s^60 i^10 eta^34 T^2, which is nonzero at the actual beta>0.

## 7. A further optional consequence, not needed by the main artifact

The inverse correction also removes the precise difficulty left open in
package 163's final question about L=b^2. Its low auxiliary-index bound
gives |b|>8f^3-1/2, g<f/2 and |V|<(3/2)f|b|, so gy<b^2/2.
The sign proof in Section 3 then works for L=b^2 because it uses only
e*<b, not the adverse forward cubic. Completeness can be constructed
directly using package 164's bound g>kappa+sigma+|rho| and any canonical
positive auxiliary pair with the trace-linear T. This yields another
85-operation degree-232 polynomial after changing L=cTR*cTR.
It has the same headline cost, degree and variable count, so it is not
promoted as an additional Pareto improvement here.

## Sources and scope

- ProveIt package 163, compact/PROOF.md, Sections 3--7.
- ProveIt package 164, positive/PROOF.md, Sections 2--5.
- The exact commit and Git blob IDs are in SOURCE_PINS.json.
- Both inherited graph specifications and proof files are retained locally.

The verifier checks exact finite graph, degree and polynomial identities.
It does not replace the unbounded Pell arguments, native calibration or
syntactic-refutation equivalence. No global simplest-equation claim is made.

