# Lower Y normalization by projecting before the full denominator

## Result, exact boundary, and priority

Four literal polynomials in ten independently strictly positive integer unknowns
are supplied. The useful new local operation/degree points are **79/382** and
**80/338**. The 78/516 and 79/456 square-weight controls are dominated by the
79/382 point or by the incoming 76/464 point, and are retained to audit the family.
Every equation uses the entire indexed BFS943 radix67 coefficient tuple, including
all four complete integer payloads. No numerical-port box alone licenses decoding.
The largest fixed port has 592,884 bits. Expanded coefficients may be larger.

At the stated retained ordinary Pell/native/refutation calibration boundary, each
polynomial has a positive zero if and only if the inherited syntactic calculus
has a finite ZFC refutation. Thus ZFC proves that absence of a positive zero is
equivalent to Con(ZFC). This is not a consistency proof, a claim that a zero
exists, a newly emitted proof-assistant or object-ZFC derivation, or global
optimality. Finite algebra checks do not replace the unbounded argument.

Newest inspected snapshot: ProveIt 3ecd6a6cf53d47519228328567f45fb7ee9781d9.
The incoming Centered Residues package already gives 75/626, 76/464, 77/460;
its sharing of XY and kY is explicitly inherited here. The incoming Coprime
Products package already proves Y=q²s,D=q⁵ at 80/382. Composing that denominator
with Centered's arithmetic sharing gives our 79/382 point, not a new denominator
theorem. Our substantive new chart is Y=qs, X=q²w, D=q⁶, with projection BEFORE
full-denominator recovery. The earlier rejected Y=qs,X=qw,D=q⁶ chart is not
reasserted: its first recurrence had only the visible q³ divisor. That defect is
repaired by the extra q in X, and its native transport coefficient is repaired
simultaneously by using Wbase=qw, rather than the new input w.
The sign-free removal of the auxiliary T+alpha shift, both signed third-index
exclusions, and fresh canonical positive T are inherited from
provenance/unshift.md and unshift_general.md; they are not new claims here.

## 1. Complete polynomial family

The independent inputs are J,F,alpha,i,T,w,s,n,eta,zeta > 0. The four fixed ports
are beta,K0,MC,MF, with the inherited beta odd>=31, K0>0 and
0<MC<beta<MF<2beta. Choose one of the following complete charts:

    q2: Wbase=w,  X=qw,    Y=q²s, D=q⁵, sigma=s/q;
    q1: Wbase=qw, X=q²w,   Y=qs,  D=q⁶, sigma=s/q².

In both charts X=q Wbase; sigma=Y/q³ is proof notation, not a division gate.
Define polynomial abbreviations

    h=beta J, q=h+1, C=q-F-alpha,
    k=eta+zeta, c=kY+eta, A=Y(X+1)+1,
    Delta=A²-1, H=4A-5, v=XY²,
    ell=(XY)(kY), E=1+ell(ell+k)=1+v(v+1)k²,
    R=[h(q-F)+alpha](q²-1)+(MC+q MF)J,
    e=k-R-1, B=(K0+Wbase)C-F,
    U=ic², a=Delta U²E, F0=1+a, G=EF0,
    Fsq=1+4aF0, Q=Delta(Fsq-1),
    b=cT-R, V=Fsq b-c, K=X(3c-2X)+2.

Choose L=V² or L=bV, and put

    M=hDH,
    Z=hD[H(n-LB)+K]-H[DB+h(e-sq⁴)],
    P=Q(Z²-M²GV²)+(M²G-Z²).                           (1)

The DAGs have only binary +,-,* gates, including every scalar multiplication
and square. All other symbols are polynomial abbreviations, not new unknowns.
For proof only let z=Z/M, kappa=K/H, rho=e/D, t=B/h and W=1+hL. Since
D sigma=sq⁴ in BOTH charts, the exact rational carrier identity is

    z=n+kappa+sigma-Wt-rho.                            (2)

No quotient in (2) is initially presumed integral.

## 2. Root extraction and both signed main branches

Every positive input gives q>=32, X,Y>=q, q|X,Y, k>=2, c>k,
A>4, Delta>=3, U>=c² and E>1. In particular a>c, Fsq>2c, Q>c².
For integral b, V is nonzero: if b=0, V=-c; otherwise |V|>=Fsq-c>1.
Thus QV²-1>0 and M>0. Identically

    Fsq=(1+2a)², Q=4Delta²U²G, gcd(E,F0)=1.             (3)

At P=0, (Q-1)z²=G(QV²-1). For every prime dividing G the other two
factors are -1 modulo that prime; rational-square valuations therefore force
G=g² with g>0 integral. Coprimality in (3) gives E=tau², F0=f0² and
g=tau f0. The rational y=|z|/g satisfies

    QV²-(Q-1)y²=1.                                    (4)

The rational adjacent-Pell descent retained in provenance/centered/PROOF.md,
section 3, proves y integral. For completeness, if y=r/m is reduced, then
m²|(Q-1); the norm-preserving map

    v'=(2Q-1)v-2(Q-1)y, y'=(2Q-1)y-2Qv

has integral nonzero v', |v'|<v for v=|V|>1, and preserves the reduced
denominator of y. Sign reflection and descent reach v=1,y=1. Hence m=1.
In particular z=epsilon gy is integral, epsilon in {+1,-1}.

The positive integers f=1+2a and I=2Ug satisfy

    f²=Fsq, f²-Delta I²=1, c²|I, Q=(Delta I)².           (5)

The retained signed all-index folding theorem (with its explicit proof in
provenance/centered/PROOF.md, section 3) applies to (4),(5), c<=I and
V=-c mod f, without presupposing V>0. It gives c=psi_A(p), p odd positive.
The first norm gives k=2psi_(2v+1)(n0), n0>=1. At n0=1, k=2 and
c=2Y+1 lies strictly between psi_A(1)=1 and psi_A(2)=2A, impossible. Thus

    n0>=2, k>=8XY²+4, c>8XY³>=8q⁵, c>X, K>0.          (6)

This uses neither positivity of B,C,R nor a transport sign.

## 3. Sign-free unshifted transport

If b=0, (4) gives y²=c²+(c²-1)/(Q-1), strictly between consecutive
integers. Hence b!=0, sign(V)=sign(b), and |V|>|b|. The inherited elementary
bounds can be checked directly from a=Delta U²E and g²=E(1+a):

    a²-g²=E[Delta U²E(Delta U²-1)-1]>0,
    Fsq-c>3a>3g, y<(3/2)|V|.

They imply gy<V²/2. For L=bV the two signed third-index branches must also be
excluded. Suppose p=3, so c=4A²-1. If n0>=3 then kY>32X²Y⁵, while
A<2XY gives c<16X²Y², impossible. Thus n0=2, k=8XY²+4. Writing
u=X+2-2Y gives the exact remainder

    eta=4Y²(Xu+1)+8Y(X+1)+3-4Y.                        (7)

For u<=-1 this is negative, since Y(X-1)>2(X+1) for X,Y>=32.
For u>=2, subtracting k leaves at least 4Y²+8Y(X+1)-4Y-1>0.
Since 0<eta<k, u must be 0 or 1, giving 2Y-X in {1,2}, contrary to
q|X,Y and q>=32. Therefore p>=5 and c>c3:=4Delta+3.

Set S=Delta I, Q=S². Classification of (4) gives
|V|=chi_S(j)/S for odd j. Even traces are +/-1 mod S and cannot be divisible
by S. Index one gives |V|=1. At index three, |V|=4Q-3; the two signs give

    Fsq(b-4Delta)=c-c3, or Fsq(b+4Delta)=c+c3.

Neither is possible because 0<c-c3<c+c3<2c<Fsq. Hence j>=5,
|V|>=16Q²-20Q+5>8Q², and, because Q>Fsq>2c,

    |b|>(8Q²-c)/Fsq>8Fsq-1/2>4Fsq>4g.

Thus L=bV>0 and gy<3L/8<L/2. These are sign-free estimates.

For either weight, e<b because b-e=cT-k+1>0, and rho<|b|/D.
If B<=-1, then Wt<-L, while kappa,sigma,n>0. Identity (2) gives

    n=epsilon gy-kappa-sigma+Wt+rho
      <L/2-L+|b|/D<0,

because D>2 and either L=V² with |V|>|b|, or L=bV with |V|>1.
Contradiction. Consequently B>=0 and C>0, since K0+Wbase>0 and F>0.
Only now invoke the mask bound 3q<R<q⁴-2. By (6), c>2R, so b,V>0.
The retained normalized rank and signed auxiliary-index interfaces have their
same c²|I,c>2R,c>2p and fixed-minus residues; they give p=R. Mask parity then
gives q even and J odd. No bound with uncontrolled alpha was used early.

## 4. First-index authentication with only the visible modulus

Integral z and (2) imply

    D | hH(e-sq⁴).

Because H=4Y(X+1)-1=-1 mod q and h=q-1, gcd(q,hH)=1. The denominator
is q⁵ or q⁶, so D|(e-sq⁴); in particular q⁴|e. The first recurrence is

    k=2n0 mod 4XY².                                   (8)

In chart q2, XY²=q⁵ws²; in chart q1, XY²=q⁴ws². Thus q⁴ divides the
modulus in BOTH charts, and q⁴|(2n0-R-1). Also P0=2XY²+1>A, because
P0-A=Y(2XY-X-1)>0. If n0>=R, monotonicity in base and index gives
k/2>=psi_A(R)=c, contrary to c>k. Therefore 1<=n0<R, and

    |2n0-R-1|<R<q⁴.

It follows that 2n0=R+1. Returning to the full congruence gives

    4XY² | e.                                        (9)

For q2, this already gives D=q⁵|e. For q1, it DOES NOT yet give q⁶|e;
we explicitly defer that conclusion. This is where the rejected older
Y=qs,X=qw chart would fail even to establish the first index, because its
visible recurrence modulus was only q³.

## 5. Projection before full-denominator recovery

The literal numerator, reduced modulo H, gives Z=hDK mod H. Since z=Z/M
is integral and H|M, H|hDK. Also gcd(H,D)=1 because D is a power of q
and H=-1 mod q. Therefore

    H | hK,                                          (10)

WITHOUT assuming rho integral. This exact reordering is the new step.

Put R=2r+1, r>=48. The retained uniform ratio lemma at scale one now applies
to the authenticated pair of indices R and (R+1)/2. It gives

    xi < psi_A(2r+1)/psi_(2XY²+1)(r+1)
       < xi(1+1/[Y(X+1)])^(2r),
    xi=(X+1)^(2r)/X^r.

Together with Y<c/k<Y+1 it gives Y>X^r/3 and
X^(r+1)<3Y(X+1)<H. The universal projection identity, H odd, and (10)
give H|h(X-2^R)(2^R X+1). In particular H divides the same expression
multiplied by q³. The retained whole-product bound uses only X>=q>=32
and r>=48 and bounds the absolute value of this WHOLE product by
X^(r+1)<H. It must be zero; its other factors are positive. Hence

    X=2^R, and kappa=K/H is a positive integer.         (11)

Here is an explicit height calculation, so that this application does not
rest on an unstated estimate. Set t0=2^R=2*4^r. Since q³h<X⁴ and X,t0>=1,

    q³h |(X-t0)(t0X+1)|
      < X⁴(X+t0)(t0X+1)
      <= 4*4^r X⁶+8*16^r X⁵ < X^(r+1).

For the last inequality, divide by X^(r+1): the two terms decrease as X
or r increases on X>=32,r>=48; at (32,48) their sum is 2^(-117)+2^(-25)<1.
No arbitrary factor of a composite modulus has been canceled.

Since q|X=2^R and q>=32, q=2^m for an integer m>=5. The elementary
inequality 2^m>=2m for m>=2 follows by induction. Thus

    R>3q=3*2^m>=6m, and consequently q⁶ | X.            (12)

Now (9) implies q⁶|e in chart q1. Thus rho=e/D is integral in both charts.
The denominator is recovered from a proved property of zeros, not a false
claim that q⁶ divides 4XY² at every positive assignment.

Identity (2) and integral z,kappa,rho now show sigma-WB/h integral. Write
sigma=s/q^j, with j=1 in q2 and j=2 in q1. Multiplication by q^j h and
reduction modulo q^j gives q^j|s, because gcd(q,h)=1. Reduction modulo h
gives h|B, because W=1 mod h and gcd(q,h)=1. Therefore

    q³ | Y, and t=B/h is a nonnegative integer.        (13)

## 6. Exact source endpoint and the fixed tuple

We have produced positive outer data J,F,alpha,Wbase,Y, with
C=q-F-alpha>0, X=q Wbase=2^R, q³|Y, and

    (K0+Wbase)C-F=t(q-1), t>=0.

The retained fixed-minus parity theorem gives R=3 mod 4; the exact ratio and
half-binomial rounding theorem gives the native half-binomial Y. These are
precisely the outer data used by the retained source reconstruction. Its base
is A_source=Y(X+1)+2, not our A=Y(X+1)+1. Use fresh source witnesses at that
base; the whole indexed BFS943 calibration then yields a finite syntactic ZFC
refutation. Equivalently, putting z_source=t+1>0 gives the literal native
transport equation

    (K0+Wbase)C+(q-F)-z_source(q-1)=1.

All four ports are the actual finite tuple copied and reconstructed here.
The scalar inequalities above are sufficient for early arithmetic, but are
not asserted to replace the calibrated native decoder. This component does
not claim a radix47 or radix55 specialization.

## 7. Constructive strictly positive completeness

Conversely a finite refutation supplies the retained canonical native outer data
q=2^m, X=2^R=q W_native, R>3q, R=3 mod4, q³|Y and
B=(K0+W_native)C-F with t=B/h>=0 integral, together with the half-binomial Y.
By (12), q⁶|X. In chart q2 choose w=W_native=X/q and s=Y/q².
In chart q1 choose w=X/q² and s=Y/q. These are strictly positive integers;
Wbase is exactly W_native in either case. In particular the coefficient of C
in the transport equation is unchanged. We do not falsely retain the old w
as the new independent input in chart q1.

Form A,P0 at scale one and set

    c=psi_A(R), k=2psi_P0((R+1)/2), tau=chi_P0((R+1)/2),
    eta=c-kY, zeta=k-eta.

The retained exact ratio/rounding theorem gives 0<eta<k, so both inputs are
positive. Congruence (9), q⁶|X, and the relevant D give rho>=0 integral.
Universal projection gives positive integral kappa<Xc.

Choose a positive multiple of a Pell matrix period at A modulo c²tau, with
seed pair (f0,I0), c²tau|I0. Take i=I0/(c²tau)>0. Then
a=Delta I0²=f0²-1, F0=f0² and G=(tau f0)². The doubled strong pair is
exactly f=2f0²-1, I=2f0 I0. The retained auxiliary-completeness theorem
supplies positive V,y and the positive integer

    T=(V+c+Rf²)/(cf²).

This is the actual unshifted input T; no subtraction of alpha is made.
The literal b,V definitions and (4) hold. Both transport weights are positive.
Set

    n=gy+(1+hL)t+rho-kappa-sigma.                      (14)

Here sigma=Y/q³ is a positive integer because canonical q³|Y. Moreover
sigma<Y<Xc, kappa<Xc, I0>=c², and
f0>(A-1)I0=Y(X+1)I0>2Xc. Hence g=tau f0>kappa+sigma.
Since y>=1,t>=0,rho>=0, (14) is a strictly positive integer. Its carrier is
z=gy, so (1) vanishes. Every independent coordinate has been constructed
positively. This is not an unproved inverse shear on arbitrary positive tuples.

## 8. Literal costs and complete global leading forms

The DAGs inherit Centered's identities A-1=XY+Y and ell=(XY)(kY).
From its q⁴ charts, delete q³, change Y, add D=q⁴q (q2) or D=q⁴q² (q1),
and add shift=sq⁴ and eclear=e-shift. This is net +2 operations for q2.
For q1 also split X into Wbase=qw and X=qWbase, adding one operation and
using Wbase in B. Thus the q2 circuits have 78/516 and 79/382; the q1
circuits have 79/456 and 80/338. All inputs, ports and gates are live.

Let q0=beta J, k0=eta+zeta and C0=q0-F-alpha. For q2 the whole top forms are

    [P_V²]_516 = 2^14 q0^272 w^46 s^108 i^20 k0^64 T^4 C0²,
    [P_bV]_382 = -2^10 q0^206 w^34 s^80 i^14 k0^46 T².

For q1 there is an important degree tie: deg(cT)=deg(R)=4. One must not
drop the R leading form. Define the homogeneous degree-three polynomial

    B0=k0 s T-q0²(q0-F).

Then the COMPLETE top forms are

    [P_V²]_456 = 2^14 q0^212 w^46 s^104 i^20 k0^60 B0^4 C0²,
    [P_bV]_338 = -2^10 q0^162 w^34 s^78 i^14 k0^44 B0².

Their exact sparse expansions have respectively 390,47,3750,274 monomials.
The selected coefficients at the maximal T powers are respectively
2^14 beta^272,-2^10 beta^206,2^14 beta^212,-2^10 beta^162, all nonzero
for the actual beta>0. Thus the asserted degrees are global exact degrees,
not ray samples or formal upper bounds. For q1, deg(Q,G,V,b,M,B) is
(90,56,84,4,12,3); deg Z is 183 or103. For q2 it is
(102,64,97,5,11,2); deg Z is207 or115. The unique top summand is QZ²
for V² and -QM²GV² for bV.

The independent finite checker does not import the producer. It covers every
literal row with 28 exact free-polynomial cuts, proves whole leading forms,
checks liveness, tuple hashes and complete coefficient reconstruction, and
rejects ten actual algebraic corruptions per equation. Normal and optimized
Python receipts agree byte for byte. It tests no alleged witness to a ZFC
refutation and does not infer universal arithmetic theorems from finitely many
zeros. Source pins identify the copied ordinary dependencies, including the
universal Pell lemmas, uniform ratio bound, and fixed indexed calibration.
