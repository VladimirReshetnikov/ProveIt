# Linear trace, free quotient, and inverse-Lucas composition

## Result and exact boundary

Three literal ordinary integer polynomials in **ten strictly positive integer
unknowns** have (degree, live binary-operation) pairs **(240,82), (232,85),
(214,87)**. A square and a multiplication by a fixed numeral each count as one
binary operation. The complete coherent directly indexed BFS943/radix67 tuple
(beta,K0,MC,MF) is retained, including every compressed numerical byte and its
finite reconstruction recipe; beta=2^590069−1. These are NOT equations over ten
unrestricted integers, and this tuple is not the six-port signed11 tuple.

The contributions compose and credit three incoming constructions: Strict
Horizons supplies Y=s with lambda=q and projection before denominator recovery;
Trace Radical supplies the explicit trace in place of its square; Unsquared
Factors/Linear Selectors supplies the inverse correction evaluated at k. A new
absolute transport bound below shows that their composition needs neither
q|Y before projection nor the extra positive shift T+alpha. The degree232/85
companion saves two gates against incoming trace232/87. The degree214/87 form
saves eighteen degrees against that same latest incoming point. The degree240/82
form is a separate lower-cost tradeoff. No global optimum is asserted.

The ordinary argument below, composed with the explicitly retained
native/refutation theorem, proves in ZFC that each equation has a positive zero
iff there is a finite syntactic ZFC refutation. Its negation is therefore
equivalent in ZFC to syntactic Con(ZFC). This does not prove either consistency
or unsolvability, and no new end-to-end proof-assistant/object-ZFC certificate
is claimed. Finite circuit checks do not replace the unbounded Pell and native
calibration theorems. All source proof texts used at the stated boundary are
retained; the source notes explicitly identify that boundary rather than
claiming an independently rebuilt transitive Lean development.

## 1. Complete equations

The independent inputs are J,F,alpha,i,T,w,s,n,eta,zeta>0. Put h=beta J,
q=h+1, C=q−F−alpha, k=eta+zeta. Choose one of these three charts:

| mode | Wbase | X | Y | lambda | D | correction eclear |
|---|---|---|---|---|---|---|
| free_plain | qw | q²w | s | q | q⁷ | k−R−1−q⁴s |
| scaled_inverse | w | qw | qs | 1 | 6q⁶ | 6(k−R−1−q⁴s)−vk(k²−4) |
| free_inverse | w | qw | s | q | 6q⁷ | 6(k−R−1−q⁴s)−vk(k²−4) |

In all cases define the following ordinary polynomial abbreviations:

    c=kY+eta, A=lambda Y(X+1)+1, Delta=A²−1, H=4A−5,
    v=X lambda²Y², E=1+v(v+1)k²,
    R=[h(q−F)+alpha](q²−1)+(MC+q MF)J,
    B=(K0+Wbase)C−F,
    U=ic², a=Delta U²E, F0=1+a, G=E F0,
    f=1+2a, Q=4Delta aF0,
    b=cT−R, V=fb−c, K=X(3c−2X)+2, L=bV,
    M=hDH,
    Z=hD[H(n−LB)+K]−H[DB+h eclear],
    P=Q(Z²−M²GV²)+(M²G−Z²).

The equation is P=0. Registers are abbreviations, not extra quantified inputs.
All exponents here are fixed small natural numbers, implemented by binary
multiplications. No quotient, recurrence, radical, factorial, binomial,
variable-exponent, or oracle gate occurs in the JSON polynomial.

For proof notation only write t=B/h, kappa=K/H, z=Z/M, W=1+hL. In
free_plain let e=k−R−1, rho=e/q⁷ and sigma=Y/q³. In the inverse charts let

    e*=k−R−1−vk(k²−4)/6,
    rho=e*/q^d, d=6 (scaled_inverse) or 7 (free_inverse),
    sigma=Y/q³.

Until integrality is proved these are rational numbers. Direct identities give

    P=(Q−1)Z²−M²G(QV²−1),
    z=n+kappa+sigma−Wt−rho.                       (1)

The carrier denominator is nonzero at every positive input.

## 2. Root extraction and a uniform signed transport bound

At every positive input q>=32, X>=q, Y>=1, k>=2, c>=3, A>4,
Delta>1, U>=c² and E>1. In the free charts lambda=q; in the scaled chart
Y=qs. Thus in every chart A>q². The identities

    f²=1+4aF0, Q=Delta(f²−1)=4Delta²U²G, gcd(E,F0)=1       (2)

are unchanged. Also f>2c and Q>c². Consequently V is nonzero for integral b.
At a zero, the first identity in (1) and prime valuations imply G=g² for a
positive integer g: every prime dividing G divides neither Q−1 nor QV²−1,
so its valuation in the rational square z² is even. Coprimality gives
E=tau² and F0=f0² with positive tau,f0 and g=tau f0.

The retained adjacent-coefficient descent proves y=|z|/g integral. Explicitly,
if y=r/m is reduced, m²|(Q−1). For u=|V|>1 the norm-preserving map

    u'=(2Q−1)u−2(Q−1)y, y'=(2Q−1)y−2Qu

has nonzero integral first coordinate with |u'|<u, and preserves the reduced
denominator m of its second coordinate. After sign reflection descent reaches
u=y=1, whence m=1. Thus z=epsilon gy with epsilon in {−1,1}, and

    QV²−(Q−1)y²=1.

Set I=2Ug. Then f²−Delta I²=1, Q=(Delta I)², c²|I, and c<=I.
The retained signed all-index folding theorem applies to V=−c modulo f
and yields c=psi_A(p) for a positive odd index p. Since c>=3, p>=3;
therefore

    c>=c3:=4A²−1=4Delta+3>4q⁴, c>X, K>0.          (3)

No sign of R,B,C,b or V and no q-divisibility of Y was assumed.

Here is the new transport bound, which replaces both the old third-main-index
exclusion and the positive shift T+alpha. If b=0, the auxiliary norm would give

    0<y²−c²=(c²−1)/(Q−1)<1,

impossible. Thus b is nonzero, sign(V)=sign(b), and |V|>1. Write
S=Delta I, Q=S². Pell classification of (SV,y) gives an odd auxiliary
index j: even traces are units modulo S, whereas SV is divisible by S.
Index one would give |V|=1; hence j>=3, and

    |V|>=4Q−3.

Furthermore a²/g²=Delta U² a/(1+a)>Delta U²/2>9, so f>6g.
Because c>=c3 and f>2c, the exact inequality

    |b| >= (|V|−c)/f
         >= 4Delta f−(c+c3)/f
          > 4Delta f−1 >4g                         (4)

holds for BOTH signs of V. In particular the possible j=3 case is harmless;
it is not falsely excluded. Also y<(3/2)|V|. Therefore

    L=bV=|b||V|>0, gy<3L/8<L/2,
    |b|/q^d<L/2 (d=6 or7).                         (5)

This argument works when Y=1 and before q³|Y is known. Its only index lower
bound is p>=3, not the q|Y-based p>=5 bound of an earlier chart.

## 3. Positive transport and the true main index

For the plain chart e=k−R−1<b, since b−e=cT−k+1>0. For the inverse
charts k>=2 makes vk(k²−4)/6 nonnegative, so e*<=e<b. Thus in every
chart rho<|b|/q^d. If B<=−1 then Wt<−L. The second identity in (1),
positive n,kappa,sigma and (5) would imply

    n=epsilon gy−kappa−sigma+Wt+rho
      <L/2−L+|b|/q^d<0,

a contradiction. Hence B>=0 and, because F>0,K0+Wbase>0, C>0.
This covers every integer R uniformly, including all negative ranks and zero.

Only now apply the authenticated whole-tuple mask bound 3q<R<q⁴−2.
By (3), c>2R, so b,V>0. The normalized strong-rank lemma, with c²|I,
and the signed auxiliary-index theorem apply to

    V=−c mod f, V=−R mod c.

The latter residue follows from f−1=2Delta i²c⁴E. Together with c>2p
and c>2R these give p=R. Thus R is positive odd; the retained mask parity
argument gives q even and J odd. None of this assumes rho or sigma integral.

## 4. The first index and all prime divisors

E=tau² gives k=2psi_(1+2v)(m), m>=1. The case m=1 would give k=2,
eta=zeta=1 and c=2Y+1 strictly between psi_A(1)=1 and psi_A(2)=2A.
It is impossible. The first base 1+2v exceeds A, since
lambda Y(2Xlambda Y−X−1)>0. Monotonicity and c>k therefore imply m<R.

In free_plain v=q⁴ws². Integral z and (1), with gcd(q,hH)=1, give
q⁷|(e−q⁴s), hence q⁴|e. The recurrence k=2m mod4v then gives
q⁴|(2m−R−1). Its absolute value is less than R<q⁴, so 2m=R+1.

In either inverse chart v=q³ws². The retained finite Lucas identity is

    k=2m+8v C_m+32v² Z_m,
    C_m=binom(m+1,3), Z_m a nonnegative integer.     (6)

It follows from the full finite binomial formula for psi_(1+2v); it is not
inferred from a finite list of m. Since k is even, k(k²−4)/6 is integral
(write k=2u and use the divisibility of u(u−1)(u+1) by3). Thus e* is integral.
Clearing (1) through hH, canceling the literal factor6 rather than inverting6
modulo q, gives q^d|hH(e*−q⁴s). Since H=−1 modq, this yields q⁴|e*.

Put t0=2m, d0=2m−R−1, A_m=C_m+4vZ_m and
S_m=k²+kt0+t0²−4. The exact cubic-difference identity is

    3(e*−d0)=4v²[24Z_m−A_m S_m].                  (7)

For any prime l|q with a_l=ord_l(q)>=1, it implies
ord_l(e*−d0)>=6a_l−ord_l(3)>=4a_l, including l=3.
Thus q⁴|d0, and |d0|<R<q⁴ gives d0=0. All three charts therefore have

    m=(R+1)/2.                                    (8)

Neither q⁶|e* nor q⁷|e* has been assumed at this stage; the third-primary
obstruction is real in general and is repaired only after projection.

## 5. Projection first, then the entire denominator

The literal numerator gives H|hDK because z is integral. Cancel only the
q-part, using gcd(q,H)=1: H|hK in free_plain and H|6hK in inverse
charts. Retain the factor6 through projection; do not cancel it through H.

Write R=2r+1. Then r>=48. The retained lambda-uniform ratio theorem applied
to the now authenticated indices (8), the base A=lambda Y(X+1)+1 and
1+2Xlambda²Y², and the strip Y<c/k<Y+1, gives

    Y>X^r/3, X^(r+1)<3Y(X+1)<H.

Modulo odd H, the universal scaled recurrence gives
3*2^(R−1)psi_A(R)=4^R−1; hence the retained projection gives
H|d1 h(X−2^R)(2^R X+1), where d1=1 or6. The whole product has absolute
value below H. Indeed d1<q³ and X>=q>=32 give the explicit bound

    d1 h |(X−2^R)(2^R X+1)|
      <4*4^r X⁶+8*16^r X⁵<X^(r+1)<H.

After division by X^(r+1), both terms decrease for X>=32,r>=48; their
sum at (32,48) is 2^(−117)+2^(−25)<1. Thus X=2^R, and the universal
projector itself proves kappa=K/H a positive integer. This does not cancel
an unproved factor of d1 h from a divisibility statement.

Since q|X, q=2^a for an integer a>=5. R>3q>=6a gives q⁶|X.
In free charts v=Xq²Y² is therefore divisible by q⁸. In free_plain,
4v|e yields q⁷|e. In free_inverse, (7) with d0=0 and q a power of two
yields q⁷|e*. In scaled_inverse v=X Y² and Y=qs already, so q⁸|v as
well, and (7) yields q⁶|e*. Thus rho is integral in every chart.

Now z,n,kappa,rho are integers, so sigma−WB/h is integral. Multiplying
by q³h and reducing modulo q³ gives q³|Y; reducing modulo h gives
h|B, because gcd(q,h)=1 and W=1 modh. Therefore t=B/h>=0 is integral.
These are precisely the retained native outer conditions. The fixed-minus
parity and half-binomial rounding theorems, uniform in lambda, reconstruct
fresh source witnesses at A_source=Y(X+1)+2; they do not identify that base
with the present A. The whole supplied indexed numerical tuple then gives
a finite syntactic ZFC refutation via the named native/refutation theorem.

## 6. Constructive completeness, including inverse rho<0

Conversely a finite refutation supplies the retained canonical outer data
q=2^a, X=2^R, R>3q, R=3 mod4, q³|Y, C>0 and integral t=B/h>=0.
For free_plain choose w=X/q²; otherwise w=X/q. Set s=Y in free charts
and s=Y/q in scaled_inverse. These are positive integers. Construct fresh
bases and first-Pell values

    A=lambda Y(X+1)+1, v=Xlambda²Y²,
    c=psi_A(R), k=2psi_(1+2v)((R+1)/2),
    tau=chi_(1+2v)((R+1)/2), eta=c−kY, zeta=k−eta.

The retained uniform exact ratio/half-binomial theorem gives 0<eta<k,
so both independent strip coordinates are positive. The same recurrence
identities and power-of-two divisibility above give integral rho, and
projection gives 0<kappa<Xc. Sigma=Y/q³ is positive integral.

Choose a positive Pell matrix period at A modulo c²tau, obtaining a seed
(f0,I0) with c²tau|I0. Set i=I0/(c²tau)>0, so a=f0²−1, G=(tau f0)²
and the doubled strong pair is f=1+2a, I=2f0I0. Keep this seed fixed.
The retained positive auxiliary reconstruction supplies a positive pair
(Vstar,y) with Vstar=f²(cTold−R)−c and the auxiliary norm. Define

    Tnew=(Vstar+c+Rf)/(cf).

This is an integer: Vstar+c is divisible by f², Vstar=−R modc, f=1 modc,
and gcd(c,f)=1. It is strictly positive because Vstar,c,R,f>0. It gives
Vstar=f(cTnew−R)−c exactly. No inverse shear of arbitrary positive tuples
is assumed, and no shift T+alpha needs to be recovered.

The inverse rho need not be nonnegative. Since k>=R+1 and vk²>6,

    |rho|<vk³/3.

For every chosen i>=1,

    g>sqrt(Delta)c²E>c²v²k²>vk³,
    g>4Xc.

The second bound uses sqrt(Delta)>A−1>X and cE>4. Since
kappa<Xc and sigma<=Y<Xc, one has kappa+sigma<g/2 and |rho|<g/3.
For the plain chart rho>=0 and the same g bound suffices. In every case set

    n=gy+(1+hL)t+rho−kappa−sigma.

This is a strictly positive integer. Its carrier satisfies z=gy, hence the
literal polynomial vanishes. All ten independent coordinates have been
constructed in their actual strictly positive domain, at one coherent tuple.

## 7. Exact degrees and complete highest forms

Put q0=beta J, k0=eta+zeta, and B0=k0 sT−q0²(q0−F). The complete highest
homogeneous components in the ten independent coordinates are

    [P_free_plain]_240
      =−2^8 q0^112 w^26 s^58 i^10 k0^32(q0−F)^2,
    [P_scaled_inverse]_232
      =−9*2^10 q0^100 w^26 s^58 i^10 k0^32 B0²,
    [P_free_inverse]_214
      =−9*2^10 q0^86 w^26 s^58 i^10 k0^32(q0−F)^2.

They have respectively 99,202,99 collected monomials. In the free charts
b's leading component is −q0³(q0−F), not a term involving T. In the scaled
chart the full degree tie is b0=q0 B0 and must not be dropped. Selecting
eta^32 F² gives nonzero coefficients −2^8 beta^112 and −9*2^10 beta^86
in the two free charts. Selecting eta^34 T² in the scaled chart gives
−9*2^10 beta^100. Since the authentic beta is positive, these are attained
actual degrees, not generic-port bounds or ray tests.

In mode order free_plain,scaled_inverse,free_inverse, the exact degrees
(Q,M,G,V,Z) are respectively (82,13,52,40,60), (80,11,50,40,57),
and (72,12,46,36,54). The unique dominant final term is −Q M² G V².
The producer and independent checker count every live gate, and the checker
records the complete top form of every register, not only the output.

## 8. Verification, dependencies, and limitations

`build.py --check` reconstructs all three literal graphs byte identically from
frozen JSON parents without executing them. `verify.py` imports no producer;
it verifies free-ring identities covering every gate, topology/liveness,
all full leading forms, the inverse cubic identity and trace substitution,
coefficient payloads and optional deep finite numeral reconstruction. Its
operator mutation mode rejects both alternative operations at all254 gates:
508 corruptions. Normal and Python−O deep receipts agree.

The selected inherited closure is `inherited/strict/`, with its compact
native/universal proof texts, source graphs, complete numerical payloads,
recipe and licenses; `inherited/TRACE_PROOF.md` and `TRACE_REVIEW.md` retain
the incoming trace argument; `inherited/INVERSE_PROOF.md`, `INVERSE_REVIEW.md` and inverse_bV.json
retain the inverse correction. `CLOSURE_MAP.md` resolves relocated historical
paths. The source theorems are explicitly credited and not relabeled as new.
No early inference from q³|HY to q³|Y is used anywhere. No result here changes
the separate signed11 fixed-frame degree298 lower bound.
