# Put the scale in the Pell bases, not in the quotient

## Result and scope

The two supplied literal polynomials use exactly ten independently strictly
positive integer unknowns. Their complete arithmetic circuits have:

| Equation | Binary operations | Exact total degree |
|---|---:|---:|
| `equation_83_degree312.json` | 83 | 312 |
| `equation_89_degree278.json` | 89 | 278 |

They retain the whole four-number directly indexed BFS943 radix67 coefficient
tuple of the incoming Lucas Corrections construction, inspected in ProveIt
commit `7a8da414376a80b90ecf799f37ceb26fb9ac674e`. The coefficients are fixed
integers, supplied in full; they are not extra quantified coordinates.

The ordinary proof below, composed with the retained universal Pell and
native/refutation calibration, proves in ZFC that either polynomial has a
strictly positive zero exactly when ZFC has a finite syntactic refutation.
Equivalently, ZFC proves that no such zero exists iff Con(ZFC). No proof of
consistency, global simplicity optimum, historical priority, or new
proof-assistant certificate is asserted.

The change is structural. The incoming small-Y constructions put a factor q
into Y, thereby putting it into c=kY+eta and then into U=i*c^2. Here Y is the
independent positive input s. A separate Pell scale lambda=q preserves the
needed q-adic divisibility in the two Pell bases, without increasing c's
degree. Projection is performed before restoring the full denominator.

The 83/312 equation improves both cost and degree over the prior 84/328
point, and the 89/278 equation improves the prior 89/288 and 92/278 points
in those two metrics. Other points, including 80/338, 87/304 and the older
lower-degree forms, remain separate tradeoffs. These comparisons do not
rank coefficient storage or different domains as though they were equal.

## 1. Complete definitions

The independent variables are

    J,F,alpha,i,T,w,s,n,eta,zeta > 0.

The fixed ports beta,K0,MC,MF satisfy the inherited box

    beta odd >=31, K0>0, 0<MC<beta<MF<2beta.

Choose one of two charts:

    plain:     Wbase=qw, X=q*Wbase=q^2*w, D=q^7;
    corrected: Wbase=w,  X=q*Wbase=q*w,   D=6*q^7.

In both charts set

    h=beta*J, q=h+1, C=q-F-alpha, Y=s, lambda=q,
    k=eta+zeta, c=kY+eta,
    A=lambda*Y*(X+1)+1, Delta=A^2-1, H=4A-5,
    v=X*lambda^2*Y^2, E=1+v(v+1)k^2,
    R=[h(q-F)+alpha]*(q^2-1)+(MC+q*MF)J,
    B=(K0+Wbase)C-F,
    U=ic^2, a=Delta*U^2*E, F0=1+a, G=E*F0,
    Fs=1+4aF0, Q=Delta*(Fs-1),
    b=c(T+alpha)-R, V=Fs*b-c,
    K=X(3c-2X)+2, L=bV.

For the plain chart put

    e=k-R-1, eclear=e-q^4*s.

For the corrected chart put

    e6=6(k-R-1)-v(R+1)(R-1)(R+3),
    eclear=e6-6q^4*s.

Finally set

    M=hDH,
    Z=hD[H(n-LB)+K]-H[DB+h*eclear],
    P=Q[Z^2-M^2*G*V^2]+[M^2*G-Z^2].                 (1)

The requested single equation is P=0. These are polynomial abbreviations.
No factorial, variable exponent, binomial coefficient, division, or hidden
predicate occurs in either literal circuit. For proof notation only put

    sigma=Y/q^3, t=B/h, W=1+hL, kappa=K/H, z=Z/M.

In the plain chart rho=e/q^7. In the corrected chart let ebar=e6/6
and rho=ebar/q^7; ebar is only rational notation until its integrality
is proved. Both circuits satisfy identically

    P=(Q-1)Z^2-M^2G(QV^2-1),
    z=n+kappa+sigma-Wt-rho.                          (2)

All denominators are nonzero on the stated positive domain.

## 2. Initial root extraction and the reason for retaining T+alpha

Positive inputs give q>=32, X>=q, Y>=1, c>=3, A>=3, Delta>0,
U>=c^2, E>1, Fs>2c and Q>1. Thus V is nonzero for every integral b:
V=Fs*b-c, with 0<c<Fs. At a zero of P,

    (Q-1)z^2=G(QV^2-1).                             (3)

The identities

    Fs=(1+2a)^2, Q=4*Delta^2*U^2*G, gcd(E,F0)=1

show that each prime dividing G divides neither Q-1 nor QV^2-1.
Prime valuations in (3) force G to be a positive integer square g^2.
Its coprime positive factors are separately squares:

    E=tau^2, F0=f0^2, g=tau*f0.

The rational adjacent-Pell descent retained in the parent proves that
y=|z|/g is an integer. In detail, for y=r/m reduced, m^2 divides Q-1;
the norm-preserving map

    v'=(2Q-1)v-2(Q-1)y, y'=(2Q-1)y-2Qv

has integral nonzero v' and |v'|<v for v=|V|>1, and preserves the
reduced denominator of y. Reflection and descent reach v=y=1, forcing
m=1. Consequently

    QV^2-(Q-1)y^2=1, z=epsilon*g*y, epsilon in {+1,-1}.

Put f=1+2a and I=2Ug. Then

    f^2=Fs, f^2-Delta*I^2=1, c^2|I, Q=(Delta*I)^2.    (4)

The retained all-index folding theorem is uniform for every integer A>=3.
It permits a signed V and applies to (4), c<=I, and V=-c mod f.
It gives c=psi_A(p) for an odd positive integer p. Since c>=3, p>=3.
In particular

    c>=psi_A(3)=4A^2-1=4Delta+3>4q^4.               (5)

The last inequality follows already from A=qY(X+1)+1>q^2,
including the case Y=1. Thus c>X and K>0.

Unlike the incoming q-linear-Y chart, q need not divide Y here. Its
third-index exclusion cannot simply be reused. The retained positive
shift T+alpha supplies an alternative. The elementary mask upper bound,
valid before any sign assumption on C, is

    R<q^4+(alpha+2)q^2.

Therefore, using T,alpha>=1 and (5),

    b-c=c(T+alpha-1)-R
       >alpha(c-q^2)-q^4-2q^2
       >=c-q^4-3q^2>0.                             (6)

So b>c and V>0 before transport, even if R is negative. This is why
the extra addition T+alpha is kept in the new circuits.

Let S=Delta*I, Q=S^2. Pell classification gives SV=chi_S(j),
y=psi_S(j), with j odd: even traces are +/-1 mod S. By (5),(6),

    V=f^2b-c>c(f^2-1)>4Delta(f^2-1)=4Q.

Thus j=1 and j=3 are excluded. Hence j>=5 and

    V>=16Q^2-20Q+5>8Q^2,
    b=(V+c)/f^2>4Delta^2(f^2-1)=4Delta^3 I^2>4g.

The middle strict inequality uses f^2>2. Also y<3V/2. Consequently

    L=bV>0, gy<3L/8<L/2, b/q^7<L/2.                (7)

These bounds are valid with the free positive quotient Y=s; no hidden
assumption Y>=q or q|Y has been made.

## 3. Positive transport, including the cubic correction

The identity b-(k-R-1)=c(T+alpha)-k+1>0 follows from c>k.
Thus in the plain chart rho<b/q^7. If B<=-1, then Wt<-L.
Equation (2), with positive n,kappa,sigma, and (7) would give n<0.
Therefore B>=0 for the plain chart.

In the corrected chart put C_R=(R+1)(R-1)(R+3). Then

    rho < b/q^7-v*C_R/(6q^7).

When C_R>=0, the same contradiction applies. The only remaining integer
ranks are R<=-4 and R=0. Write Pmask=(MC+qMF)J>0. Identically

    R=(hC+q*alpha)(q^2-1)+Pmask.                   (8)

If R=-r<=-4, (8) implies C<0 and |C|>r/q^3. Here Wbase=w,
so B=-(K0+w)|C|-F<=-1-w|C|, and Wt<-(1+w|C|)L. Since
v=wq^3s^2, the adverse correction satisfies

    delta0=v(r-1)(r+1)(r-3)/(6q^7)
          <w*s^2*r^3/(6q^4).

Now b>r and V>(Fs-1)b, so L>(Fs-1)r^2. Since Fs-1>s^2,
one has w|C|L>delta0. Inserting this strict margin in (2) and using
(7) again yields n<0. If R=0, then C<0, |C|>=1 and the adverse
term is v/(2q^7)=w*s^2/(2q^4); b>c and L>Fs-1>s^2 give the
same contradiction. These are all sign cases of the cubic correction.

Thus both charts force B>=0. Since F>0 and K0+Wbase>0, C>0 follows.
Only now use the calibrated outer mask bound

    3q<R<q^4-2.                                    (9)

By (5), c>2R. The normalized strong-rank and signed auxiliary-index
lemmas apply with c^2|I, c>2p, V=-c mod f and V=-R mod c; the
extra c*alpha in b changes neither congruence. They give p=R.
In particular R is odd, and the retained mask parity gives q even and J
odd. This argument has not yet identified the first Pell index or assumed
rho or sigma integral.

## 4. Authenticate the first index before projection

The first square E=tau^2 gives

    k=2 psi_(1+2v)(n0), n0>=1.

The index n0=1 would give k=2 and c=2Y+1 strictly between 1 and 2A,
which is impossible. The first base is larger than A because

    (1+2v)-A=qY(2XqY-X-1)>0.

If n0>=R, monotonicity in base and index would give k/2>=psi_A(R)=c,
contrary to c>k. Hence 1<=n0<R.

For the plain chart, integrality of z and (2) gives

    q^7 | hH(e-q^4s).

Since H=4qY(X+1)-1=-1 mod q and h=q-1, gcd(q,hH)=1. Thus
q^4|e. The universal base-one recurrence gives

    k=2n0 mod 4v.

Here v=q^4*w*s^2, so q^4 divides 2n0-R-1. Its absolute value is
less than R<q^4; therefore 2n0=R+1. Returning to the full recurrence,
4v|e. This does not yet imply q^7|e; that deduction is deliberately
postponed until after projection.

For the corrected chart, put r0=(R+1)/2. The finite Lucas identity is

    2 psi_(1+2v)(m)=2m+8v*binom(m+1,3)+32v^2 Z_m,  (10)

where Z_m is a nonnegative integer. It follows from
psi_(1+2v)(m)=sum_(j=0)^(m-1)(4v)^j binom(m+j,2j+1).
Binomial symbols are used only in this proof. Since
C_R=48 binom(r0+1,3), ebar is now an integer and

    ebar=k-2r0-8v*binom(r0+1,3).

Clearing (2), then cancelling the literal factor 6, gives

    q^7 | hH(ebar-q^4s), hence q^4|ebar.           (11)

No inverse of 6 modulo q is used. Let d=2n0-R-1. Since q^3|v,
(10),(11) first give q^3|d. The exact polynomial identity

    6(ebar-d)=v*d[(2n0)^2+(2n0)(R+1)+(R+1)^2-4]
                 +192v^2 Z_(n0)

then gives q^6|6(ebar-d). For any prime ell|q, with
a_ell=v_ell(q)>=1, this implies

    v_ell(ebar-d)>=6a_ell-v_ell(6)>=6a_ell-1>=4a_ell.

Thus q^4|ebar-d, including at primes 2 and 3. With (11) and
|d|<R<q^4, this forces d=0. Consequently both charts have

    n0=(R+1)/2.                                    (12)

In the corrected chart, (10) now says ebar=32v^2 Z_(r0)>=0.
It does not yet justify the entire q^7 denominator.

## 5. Exponential projection before the full denominator

The literal numerator satisfies Z=hDK mod H. Since Z/M is integral
and H|M, H|hDK. Because H=-1 mod q, cancel only q^7 to obtain

    H|hK in the plain chart; H|6hK in the corrected chart.  (13)

There is no need to cancel 3 through H. This matters for the second
chart; gcd(6,H) is not silently assumed to be one.

Write R=2r+1. By (9), r>=48. The retained ratio theorem is uniform
in every lambda>=1, with A=lambda*Y*(X+1)+1 and P0=1+2Xlambda^2Y^2.
At lambda=q it gives

    xi < psi_A(2r+1)/psi_P0(r+1)
       < xi*(1+1/[Y(X+1)])^(2r),
    xi=(X+1)^(2r)/X^r.

Together with Y<c/k<Y+1, it yields Y>X^r/3, hence

    X^(r+1)<3Y(X+1)<H.                              (14)

The universal Pell projection identity, H odd, and (13) give
H|d0*h*(X-2^R)*(2^R X+1), with d0=1 or 6. The entire product,
not its individual factors, has absolute value below H. Indeed d0<q^3,
X>=q>=32, and the retained explicit estimate is

    q^3 h |(X-2^R)(2^R X+1)|
       <4*4^r X^6+8*16^r X^5<X^(r+1).

After division by X^(r+1), the last two bounds decrease in X and r;
at (32,48) their sum is 2^(-117)+2^(-25)<1. Thus

    X=2^R, and kappa=K/H is a positive integer.       (15)

The last integrality follows from the universal projection at X=2^R,
not from cancellation of d0*h in (13).

Since q|X and q>=32, q=2^m with m>=5. The elementary inequality
2^m>=2m and (9) imply R>6m. Thus q^6|X and q^8|v=Xq^2Y^2.
In the plain chart, 4v|e now gives q^7|e. In the corrected chart,
ebar=32v^2 Z_(r0) gives q^7|ebar. In both cases rho is a
nonnegative integer.

Now all of z,n,kappa,rho are integers. Equation (2) implies

    Y/q^3-WB/h is an integer.

Multiplication by q^3h and reduction modulo q^3 give q^3|Y;
reduction modulo h gives h|B, since gcd(q,h)=1 and W=1 mod h.
Therefore

    q^3|Y, t=B/h is a nonnegative integer.            (16)

The missing q divisibility is proved for every zero; it was not imposed
on the independent variable Y=s at the beginning.

## 6. Native restoration and positive completeness

Equations (9),(12),(15),(16) provide the inherited native outer data
J,F,alpha,Wbase,Y with X=qWbase=2^R. The fixed-minus parity and exact
half-binomial rounding theorems apply using the lambda-uniform ratio bound.
They give R=3 mod4 and the same native half-binomial Y. Construct fresh
source witnesses at A_source=Y(X+1)+2; do not identify that source base
with the present A=qY(X+1)+1. The retained whole-tuple native/refutation
calibration then yields a finite syntactic ZFC refutation.

Conversely such a refutation supplies canonical outer data with q^3|Y,
X=2^R, R>3q, R=3 mod4, and t=B/h>=0. Put s=Y. In the
plain chart choose w=X/q^2; in the corrected chart choose w=X/q.
These are positive integers since q^6|X, and Wbase=X/q remains the
actual native port in either chart.

Use fresh scaled bases A=qY(X+1)+1, P0=1+2Xq^2Y^2 and define

    c=psi_A(R), k=2psi_P0((R+1)/2), tau=chi_P0((R+1)/2),
    eta=c-kY, zeta=k-eta.

The uniform ratio and the inherited half-binomial identity give
0<eta<k, so eta,zeta are positive. The recurrence and q^6|X give
the required nonnegative integral rho in either chart, and projection
gives 0<kappa<Xc.

A positive multiple of a Pell matrix period modulo c^2*tau supplies
a seed pair (f0,I0) with c^2*tau|I0. Put i=I0/(c^2*tau)>0.
Then F0=f0^2, G=(tau*f0)^2, and doubling gives exactly (4).
The retained positive auxiliary reconstruction at this A supplies
V,y and T_*=(V+c+Rf^2)/(cf^2)>0. Its standard third-index exclusion,
now with R>=97, gives b>4g and hence T_*>4g/c>q>alpha;
here alpha<q from C>0 and g/c>(A-1)c>q. Thus T=T_*-alpha
is a positive integer, and the literal shifted b is recovered.

Finally set

    n=gy+(1+hL)t+rho-kappa-Y/q^3.

This is integral. Since f0>(A-1)I0>2Xc, whereas kappa<Xc and
Y/q^3<=Y<Xc, one has g=tau*f0>kappa+Y/q^3. Hence n>0.
Its carrier is z=gy, so (1) vanishes. Every independent coordinate
has been constructed positively. No positive-domain inverse shear or
inherited witness at a different Pell base has been presumed.

## 7. Literal arithmetic, full leading forms and checks

The parent q1 chart has 80 operations. The plain construction adds one
product to recover q^7, one to compute q*kY for the first norm after the
change c=k*s+eta, and the positive shift T+alpha: 83 operations.
The Lucas parent already computes v for its correction, so the corrected
construction adds only q^7 and T+alpha to its 87 operations: 89.

Let q0=beta*J and k0=eta+zeta. In both new charts c(T+alpha) has
degree three, while R has degree four. The whole leading part of b is
therefore -q0^3(q0-F); it contains no T. This change must be kept in
the degree audit. The complete leading homogeneous forms are

    [P_plain]_312 = -2^10 q0^140 w^34 s^78 i^14 k0^44(q0-F)^2,
    [P_corrected]_278 = -9*2^12 q0^106 w^34 s^78 i^14 k0^44(q0-F)^2.

Each has 135 collected terms. Selecting eta^44 and F^2 yields
nonzero coefficients -2^10 beta^140 and -9*2^12 beta^106. Both
claimed degrees are thus attained at the actual positive fixed beta.

The dominant term in each case is -Q M^2 G V^2. The two complete
degree lists (Q,M,G,V,Z) are respectively (82,13,52,76,96) and
(72,12,46,68,86); all competing finalizer terms have lower degree.

`verify.py` independently checks 28 exact free-polynomial cut identities
per equation, covering every actual gate; all live inputs and ports;
the complete leading forms; operation counts; all fixed coefficient hashes;
and twenty deliberate actual gate corruptions. It imports no producer.
`build.py --check` reconstructs the changed data from the frozen parent JSON.
Normal and optimized Python produce identical mathematical receipts.
These finite checks authenticate the explicit polynomials. The unbounded
Pell, congruence, sign and completeness arguments are the proofs above.

## 8. Dependencies and attribution

`upstream_lucas/` retains the incoming Lucas Corrections compact component,
including its literal coefficients, coefficient reconstruction, ordinary
source proofs, licenses and notices. The universal ratio proof is
`upstream_lucas/parent/proof_sources/uniform_ratio.md`; its Section 1
explicitly covers every real lambda>=1 and every Y>=1. Uniform folding,
strong rank, signed index and positive auxiliary reconstruction are in
`upstream_lucas/parent/proof_sources/universal_pell.tex`; the signed
all-index folding proof is in `upstream_lucas/parent/PROOF.md`.
`parent_cofinal_proof.md` supplies the projection-before-full-denominator
method. Both parent circuits are retained as data.

The new contribution is the free quotient Y=s with scale lambda=q, its
complete positive converse, and the two checked literal polynomials.
The existing Lucas correction and inherited native encoding are credited,
not presented as new results. The work was prepared with AI assistance.
