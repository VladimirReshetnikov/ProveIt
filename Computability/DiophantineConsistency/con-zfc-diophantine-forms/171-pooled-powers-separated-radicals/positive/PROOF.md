# Inverse-Lucas correction composed with the explicit Pell trace

## Result, exact scope, and comparison

`equation_bV.json` is a literal integer polynomial in ten independently
strictly positive variables, with **85 live binary integer-leaf operations and exact degree
232**. The matched incoming Trace_Radical circuit has 87 operations at the same degree232. Every square and fixed scalar multiplication is charged. The inherited indexed BFS943/radix67 four-number tuple remains coherent; its largest port has592,884 bits. A separate full one-anchor7309 specialization is supplied only with its own explicit calibration, not mixed port-by-port.

The comparison snapshot is ProveIt892d73e1ab4bc5fd34ecca1967b06dc47ca95494, and the matched source is docs/incoming/ConZFC_Trace_Radical_2026-10-25.zip. Its compact subtree is retained byte-for-byte in inherited_trace/. The inverse correction and projection-before-denominator proof are credited to the preserved round20 package; the unsquared trace theorem is credited to inherited_trace/PROOF.md. The present contribution composes those changes, gives the exact resulting circuit and verifies the composition.

At the retained ordinary native/refutation calibration, this polynomial has a positive zero iff there is a finite syntactic ZFC refutation. Thus ZFC proves its absence of positive zeros equivalent to Con(ZFC). This is not a consistency proof, a claimed zero, a global minimum, a literature-priority claim or a newly compiled end-to-end proof-assistant object. The coefficient box alone is not the refutation calibration.

## 1. Complete equation

Inputs are J,F,alpha,i,T,w,s,n,eta,zeta > 0. The four fixed ports are
beta,K0,MC,MF from the whole supplied tuple. They satisfy beta odd>=31,
K0>0 and 0<MC<beta<MF<2beta. All following definitions are polynomial
abbreviations, not extra unknowns:

    h=beta J, q=h+1, C=q-F-alpha,
    X=qw, Y=qs, k=eta+zeta, c=kY+eta,
    A=Y(X+1)+1, Delta=A²-1, H=4A-5,
    v=XY², ell=vk=(XY)(kY), E=1+ell(ell+k),
    R=[h(q-F)+alpha](q²-1)+(MC+q MF)J,
    B=(K0+w)C-F,
    U=ic², a=Delta U²E, F0=1+a, G=EF0,
    f=a+F0=1+2a, Q=4Delta aF0,
    b=cT-R, V=f b-c, K=X(3c-2X)+2,
    e6=6(k-R-1)-ell(k²-4), D6=6q⁶,
    M=hD6H,
    Z=hD6[H(n-LB)+K]-H[D6B+h(e6-6q⁴s)],
    P=Q(Z²-M²GV²)+(M²G-Z²).

Use L=bV. The circuit does
not compute v separately; it uses the already-live ell. For proof only set

    e*=e6/6=k-R-1-vk(k²-4)/6,
    rho=e*/q⁶, sigma=s/q², t=B/h, W=1+hL,
    kappa=K/H, z=Z/M.

Before asserting any divisibility, the exact rational identity is

    z=n+kappa+sigma-Wt-rho.                         (1)

There are no division gates, variable exponents, recurrence or binomial
operators, or hidden quantified variables in the actual polynomial.

## 2. Root extraction and signed bootstrap

The root extraction and signed trace-linear folding proof in inherited_trace/PROOF.md §§3–4 applies unchanged, since only the carrier correction changed. Every positive input has q>=32, X,Y>=q, k>=2, c>k, A>4, U>=c², f>2c and Q>c². V is nonzero, and identically

    f²=1+4aF0, Q=4Delta²U²G, gcd(E,F0)=1.

At a zero, prime valuations in (Q-1)z²=G(QV²-1) force G=g², E=tau² and F0=f0², with positive integral g=tau f0. The retained rational adjacent-Pell descent makes y=|z|/g integral, so z=epsilon gy and

    QV²-(Q-1)y²=1.

The polynomial trace and I=2Ug satisfy f²-Delta I²=1, Q=(Delta I)² and c²|I. Moreover f-1=2Delta i²c⁴E, so f=1 modulo c. The signed all-index folding theorem, using V=-c modulo f and no sign of R, gives c=psi_A(p), with p positive odd. The first norm gives k=2psi_(1+2v)(m), m>=1. Index m=1 is impossible; hence m>=2, k>=8v+4 and c>8XY³>=8q⁴. In particular c>X and K>0.

The inherited third-index exclusion uses q|X,Y, q>=32 and no correction. It rules out p=3 by the exact remainder

    eta=4Y²(Xu+1)+8Y(X+1)+3-4Y, u=X+2-2Y;

otherwise 2Y-X would be1 or2. Thus c>c3=4Delta+3. The case b=0 would give0<y²-c²=(c²-1)/(Q-1)<1, impossible. Hence b,V have the same nonzero sign. The exact trace-linear auxiliary-index-three equations are

    f(b-4Delta f)=c-c3, or f(b+4Delta f)=c+c3.

Their right sides lie strictly between0 and2c<f, so neither is possible. The auxiliary index is at least5. With Q>f², this gives

    |V|>8Q², |b|>(8Q²-c)/f>8f³-1/2>4g.

Also a>3g and y<(3/2)|V|. Consequently

    L=bV>0, gy<3L/8<L/2, |b|/q⁶<L/2.            (2)

Now k>=2 makes vk(k²-4)/6 nonnegative, independently of the sign of R.
Thus e*<=k-R-1<b, since b-(k-R-1)=cT-k+1>0. Consequently
rho<|b|/q⁶. If B<=-1 then Wt<-L; with positive n,kappa,sigma,
equations (1)--(2) would give

    n=epsilon gy-kappa-sigma+Wt+rho
      <L/2-L+|b|/q⁶<0.

This contradiction proves B>=0, then C>0. It handles every negative R
and R=0 uniformly, unlike the forward rank correction. Only now apply
the inherited mask bound 3q<R<q⁴-2. Since c>2R, b,V>0. The retained
normalized-rank and signed auxiliary-index theorems now give p=R: their residues are V=-c modulo f and V=-R modulo c, the latter following from the literal identity f=1 modulo c.
Thus R is positive odd, and mask parity gives q even and J odd.

## 3. Inverse-Lucas index authentication at every prime

The inherited finite polynomial expansion of the Lucas recurrence gives

    k=2psi_(1+2v)(m)=2m+8v C_m+32v² Z_m,            (3)
    C_m=binom(m+1,3), Z_m a nonnegative integer.

This is an unbounded recurrence identity, not an inference from tested m.
Since k is even, k(k²-4)/6 is integral: writing k=2u gives
4u(u-1)(u+1)/3, and one of three consecutive integers is divisible by 3.
Thus e* is integral at every zero.

Since Z=Mz with integral z and D6=6q⁶ divides M, reduce the literal numerator Z modulo D6. Its first term and the D6B term vanish, giving
6q⁶|hH(e6-6q⁴s). We have already proved e6=6e* with e* integral. Cancelling the common integer factor 6 from this divisibility (not in a residue ring) now gives
q⁶|hH(e*-q⁴s). Since h=q-1 and H=-1 mod q, gcd(q,hH)=1. Therefore

    q⁶ | e*-q⁴s, and q⁴ | e*.                     (4)

Put t0=2m, d=2m-R-1, A_m=C_m+4vZ_m, and
S_m=k²+kt0+t0²-4. The cubic difference identity and (3) give exactly

    3(e*-d)=4v²[24Z_m-A_m S_m].                    (5)

Indeed t0(t0²-4)=48C_m and k-t0=8vA_m. Since v=q³ws²,
q⁶ divides the right side. For each prime l|q with a_l=ord_l(q)>=1,

    ord_l(e*-d)>=6a_l-ord_l(3)>=4a_l.

Thus q⁴|(e*-d) and (4) implies q⁴|d. The first base 1+2XY² exceeds
A: their difference is Y(2XY-X-1)>0. If m>=R, monotonicity in base
and index would give k/2>=psi_A(R)=c, contrary to c>k. Hence 1<=m<R,
and |d|<R<q⁴. We conclude

    d=0, m=(R+1)/2.                               (6)

Do NOT conclude q⁶|e* at this point. In general (5) loses one factor
of 3. For q=3,v=27,m=2,R=3, e*=-47,911,824 is 243 modulo 729.
This is a modular diagnostic, not a putative zero of P. Even q does
not by itself repair the problem; q may have an odd prime factor.

## 4. Projection before full-denominator recovery

Integral z=Z/M gives H|Z. Reducing its literal numerator modulo H gives
H|6hq⁶K. Since gcd(q,H)=1, this yields

    H | 6hK.                                      (7)

No integrality of rho or sigma is used here, and no factor of 3 is canceled.
Write R=2r+1. Then r>=48. The retained uniform ratio theorem, now with
the authenticated pair of indices (6), gives

    Y>X^r/3, and X^(r+1)<3Y(X+1)<H.                (8)

The universal projection can be seen directly: modulo odd H, the scaled
recurrence gives 3*2^(R-1)psi_A(R)=4^R-1, because 4A=5 modulo H.
Multiplying K by 2^(R-1) therefore gives minus
(X-2^R)(2^R X+1) modulo H. All powers of 2 are units modulo H, so (7)
implies H|6h(X-2^R)(2^R X+1), without canceling arbitrary product factors.

For completeness put u0=2^R=2*4^r. Since 6<q³ and q³h<X⁴,

    6h |(X-u0)(u0X+1)|
      < X⁴(X+u0)(u0X+1)
      <=4*4^r X⁶+8*16^r X⁵ < X^(r+1)<H.           (9)

The penultimate inequality follows by dividing by X^(r+1): both terms
decrease as X>=32 and r>=48 increase, and at (32,48) their sum is
2^(-117)+2^(-25)<1. Thus the divisible whole product is zero. Its other
factors are positive, so X=2^R. Universal projection then gives H|K,
and kappa is a positive integer.

Since q|X and q>=32, q=2^a for an integer a>=5. Equation (5) with d=0
now gives q⁶|e*, since 3 is coprime to q. Thus rho is integral.
From (1), sigma-WB/h is integral. Multiplication by q²h and reduction
modulo q² gives q²|s. Then sigma is integral and h|WB. As W=1 mod h,
h|B, proving

    q³|Y, and t=B/h is a nonnegative integer.      (10)

The source data now exactly match the retained fixed-minus parity,
half-binomial rounding, and fresh native reconstruction interfaces.
The source base is Y(X+1)+2, not the present A. With the whole indexed
four-port tuple, that reconstruction yields a finite syntactic ZFC refutation.

## 5. Constructive strictly positive completeness

Conversely a finite refutation supplies the retained canonical outer data
q=2^a, X=2^R=qw, R>3q, R=3 mod4, q³|Y, C>0 and integral t=B/h>=0,
together with the native half-binomial interval. Set s=Y/q>0. Form

    c=psi_A(R), k=2psi_(1+2XY²)((R+1)/2),
    tau=chi_(1+2XY²)((R+1)/2),
    eta=c-kY, zeta=k-eta.

The retained exact ratio theorem gives 0<eta<k, so both new coordinates
are strictly positive. Equation (5) gives integral rho=e*/q⁶ because
q is a power of 2. Projection gives positive integral kappa, and
sigma=Y/q³ is integral. Unlike the forward correction, rho need not be
nonnegative; this is why the old lower bound for n is not simply copied.

Use a positive period of the Pell matrix at A modulo c²tau. Its determinant
is 1, so such a finite period exists. Its seed pair (f0,I0) has c²tau|I0.
Set i=I0/(c²tau)>0. Then a=Delta I0²=f0²-1, F0=f0² and G=g²,
where g=tau f0. The doubled pair f=2f0²-1, I=2f0I0 has the exact required definitions. The inherited trace-linear completeness theorem (inherited_trace/PROOF.md §7) starts with positive V,y satisfying the stronger congruence V=f²(cT_old-R)-c and sets

    T=(V+c+Rf)/(cf)=fT_old-((f-1)/c)R.

This is integral because c|(f-1), and strictly positive because its first displayed numerator and denominator are positive. It gives V=f(cT-R)-c exactly. This is an existence construction, not an unjustified inverse shift on arbitrary inputs.

Here is a direct bound handling the negative rho. Since psi_P(m)>=m,
k>=R+1. Also v k²>6. Therefore

    |rho| <= [k-R-1+vk(k²-4)/6]/q⁶
           < [k+vk³/6]/q⁶ < vk³/3.

For every i>=1 the identity for G gives

    g>sqrt(Delta)c²E>c²v²k²>vk³,

because E>v²k² and c>k. Thus |rho|<g/3. Moreover
sqrt(Delta)>A-1=Y(X+1)>X and cE>4 imply g>4Xc.
The canonical projection gives kappa<Xc, while sigma<=Y<Xc.
Consequently kappa+sigma<g/2, and

    g>kappa+sigma+|rho|.                            (11)

For the positive weight define

    n=gy+(1+hL)t+rho-kappa-sigma.                   (12)

All summands are integral; y>=1, t>=0 and (11) make n>0. Its carrier
is z=gy, so P=0. Thus every independent input has been constructed
strictly positively. Every permitted period seed works; no additional
cofinal enlargement is required. No refutation or zero is asserted to exist.

## 6. Literal cost, exact degree and verification

The incoming trace87_degree232 computes v=(XY)Y and ell=vk, followed by the four-gate rank cubic. The new graph deletes v, uses ell=(XY)(kY), and replaces the rank cubic by three gates k², k²-4, ell(k²-4). This saves two multiplications:85 live binary operations,51 multiplications,18 additions and16 subtractions. Integer leaves only; no rational-leaf count is silently compared.

Put q0=beta J, k0=eta+zeta and B0=k0 s T-q0²(q0-F). The complete leading homogeneous part is

    [P]_232=-9*2^10 q0^100 w^26 s^58 i^10 k0^32 B0².

It is nonzero at every actual beta>0. The exact degrees of a,f,Q,G,b,V,M,Z are36,36,80,50,4,40,11,57. The dominant term is -QM²GV² of degree232; QZ² has degree194. The inverse correction has degree9 and does not affect this highest component. These are polynomial identities, not numerical ray tests.

The independent standard-library verifier uses exact sparse-polynomial cuts covering every live row, reconstructs the entire leading form, checks the whole coefficient tuple and source pins, and rejects both alternative operations at every gate. Finite Lucas recurrence controls include the third-primary denominator obstruction. Such finite controls are diagnostics, not replacements for the unbounded proofs above. Both normal and optimized Python receipts must agree; build.py --check reproduces the exact graph.
