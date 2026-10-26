# Inverse-Lucas correction with projection before denominator recovery

## Result, exact scope, and comparison

`equation_bV.json` is a literal integer polynomial in ten independently
strictly positive variables, with **85 live binary operations and exact degree
304**. The unchanged-degree incoming Lucas correction costs 87 operations.
The 84-operation, degree-410 square-weight circuit is a dominated control,
not a new frontier claim. Squares and fixed scalar multiplications count.
The whole calibrated indexed BFS943/radix67 four-number tuple is retained;
its largest port has 592,884 bits. The coefficient payloads and an executable
finite reconstruction from the printed recipe are supplied.

At the explicitly retained ordinary native/refutation calibration, each
polynomial has a positive zero iff there is a finite syntactic ZFC refutation.
Thus ZFC proves its absence of positive zeros equivalent to Con(ZFC).
This is not a consistency proof, a claimed zero, a global minimum, a
literature-priority claim, or a newly compiled end-to-end proof-assistant object.

The comparison snapshot is ProveIt 7a8da414376a80b90ecf799f37ceb26fb9ac674e,
including the Lucas Corrections and Cofinal Witnesses incoming archives.
The second-order Lucas expansion and q-linear Y scale are inherited from
`inherited_lucas/PROOF.md`; the projection-before-denominator order is
inherited from the separately retained `inherited_projection.md`. The new
step is the **inverse** correction, evaluated at k rather than R+1. It
reuses ell=vk, saves two gates, removes the negative-rank sign casework,
and requires a new third-primary denominator repair and signed positive lift.

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
    Fs=1+4aF0, Q=Delta(Fs-1),
    b=cT-R, V=Fs b-c, K=X(3c-2X)+2,
    e6=6(k-R-1)-ell(k²-4), D6=6q⁶,
    M=hD6H,
    Z=hD6[H(n-LB)+K]-H[D6B+h(e6-6q⁴s)],
    P=Q(Z²-M²GV²)+(M²G-Z²).

Use L=bV for the principal and L=V² for the control. The circuit does
not compute v separately; it uses the already-live ell. For proof only set

    e*=e6/6=k-R-1-vk(k²-4)/6,
    rho=e*/q⁶, sigma=s/q², t=B/h, W=1+hL,
    kappa=K/H, z=Z/M.

Before asserting any divisibility, the exact rational identity is

    z=n+kappa+sigma-Wt-rho.                         (1)

There are no division gates, variable exponents, recurrence or binomial
operators, or hidden quantified variables in the actual polynomial.

## 2. Root extraction and signed bootstrap

The retained proof in `inherited_lucas/PROOF.md`, sections 2--3, applies
without alteration because only e6 changed. Its hypotheses hold at every
positive input: q>=32, X,Y>=q, k>=2, c>k, A>4, U>=c², Fs>2c and Q>c².
V is nonzero. The identities

    Fs=(1+2a)², Q=4Delta²U²G, gcd(E,1+a)=1

and prime valuations in (Q-1)z²=G(QV²-1) give
G=g², E=tau², F0=f0² with g=tau f0>0 integral. Rational adjacent-Pell
descent gives y=|z|/g integral, so z=epsilon gy, epsilon in {+1,-1}, and

    QV²-(Q-1)y²=1.

With f=1+2a and I=2Ug, one has f²-Delta I²=1, Q=(Delta I)² and
c²|I. Signed all-index folding gives c=psi_A(p) for positive odd p.
The first norm gives k=2psi_(1+2v)(m), m>=1. The case m=1 is impossible;
hence m>=2, k>=8v+4 and c>8XY³>=8q⁴. In particular c>X and K>0.
Here psi_A(0)=0, psi_A(1)=1 and psi_A(j+2)=2A psi_A(j+1)-psi_A(j).

The inherited third-index exclusions use q|X,Y and q>=32, not the old
correction. They prove, for either transport weight,

    b != 0, sign(V)=sign(b), |V|>|b|,
    L>0, gy<L/2, |b|/q⁶<L/2.                       (2)

For clarity the nontrivial bV bound is obtained by excluding p=3 with
the exact remainder eta=4Y²(Xu+1)+8Y(X+1)+3-4Y, u=X+2-2Y; this would
force 2Y-X in {1,2}. The auxiliary Pell index 3 would give either
Fs(b-4Delta)=c-(4Delta+3) or Fs(b+4Delta)=c+(4Delta+3), both impossible
since the right sides lie strictly between 0 and Fs. The auxiliary index
is therefore at least 5, giving |b|>4g and gy<3L/8. Both signs are covered.

Now k>=2 makes vk(k²-4)/6 nonnegative, independently of the sign of R.
Thus e*<=k-R-1<b, since b-(k-R-1)=cT-k+1>0. Consequently
rho<|b|/q⁶. If B<=-1 then Wt<-L; with positive n,kappa,sigma,
equations (1)--(2) would give

    n=epsilon gy-kappa-sigma+Wt+rho
      <L/2-L+|b|/q⁶<0.

This contradiction proves B>=0, then C>0. It handles every negative R
and R=0 uniformly, unlike the forward rank correction. Only now apply
the inherited mask bound 3q<R<q⁴-2. Since c>2R, b,V>0. The retained
normalized-rank and signed auxiliary-index theorems now give p=R.
Thus R is positive odd, and mask parity gives q even and J odd.

## 3. Inverse-Lucas index authentication at every prime

The inherited finite polynomial expansion of the Lucas recurrence gives

    k=2psi_(1+2v)(m)=2m+8v C_m+32v² Z_m,            (3)
    C_m=binom(m+1,3), Z_m a nonnegative integer.

This is an unbounded recurrence identity, not an inference from tested m.
Since k is even, k(k²-4)/6 is integral: writing k=2u gives
4u(u-1)(u+1)/3, and one of three consecutive integers is divisible by 3.
Thus e* is integral at every zero.

Clearing (1) through hH, using integral z, gives
6q⁶|hH(e6-6q⁴s). Cancelling the ordinary factor 6 now gives
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
where g=tau f0. The doubled pair f=2f0²-1, I=2f0I0 has the exact
required definitions. The retained auxiliary-completeness theorem supplies
positive V,y and the positive integer T=(V+c+Rf²)/(cf²). This is the actual
unshifted input, not a proposed inverse shift on arbitrary tuples.

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

For either positive weight define

    n=gy+(1+hL)t+rho-kappa-sigma.                   (12)

All summands are integral; y>=1, t>=0 and (11) make n>0. Its carrier
is z=gy, so P=0. Thus every independent input has been constructed
strictly positively. Every permitted period seed works; no additional
cofinal enlargement is required. No refutation or zero is asserted to exist.

## 6. Literal costs, exact degrees, and finite verification

The incoming correction computed v=(XY)Y, ell=vk and the four-gate
rank cubic. We delete the v gate, use ell=(XY)(kY), and replace the
four-gate rank cubic by three gates k², k²-4, ell(k²-4). Net saving:
two multiplications. There are no dead gates or unused inputs/ports.

Let q0=beta J, k0=eta+zeta, C0=q0-F-alpha and
B0=k0 s T-q0²(q0-F). The complete highest homogeneous forms remain

    [P_bV]_304=-9*2^12 q0^128 w^34 s^78 i^14 k0^44 B0²,
    [P_V²]_410=9*2^16 q0^166 w^46 s^104 i^20 k0^60 B0^4 C0².

Their exact expansions have 274 and 3750 monomials. The displayed
coefficients at maximal T power are nonzero because beta>0. The full
leading components, not numerical rays, prove the exact global degrees.
The inverse cubic has degree 9, below the leading carrier terms.

The independent verifier imports no producer, checks all live rows through
37 free-polynomial cuts per graph, reconstructs the complete leading forms,
authenticates all coefficient bytes, checks exact general identities, and
rejects both alternative operations at every gate plus a missing-correction
mutation (171 and 169 rejected mutations). Separate finite recurrence
controls include the third-primary obstruction; they are diagnostics,
not substitutes for the unbounded proofs above. Normal and optimized
Python receipts must agree. `build.py --check` reproduces both literal DAGs.

