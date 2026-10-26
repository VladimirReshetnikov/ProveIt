# Constant dilation and third-order inverse Lucas interpolation

## Status and exact result

The literal circuit `constant_dilation11.json` uses eleven strictly
positive integer inputs, 104 live binary integer-leaf operations, and has
exact total degree 174. Every fixed coefficient belongs to the same complete
BFS943/radix67 tuple as the retained source-172 ten-positive equations.
The new reduction below is an ordinary proof that received an independent
mathematical audit within the AI-assisted workflow. Its logical endpoint inherits the explicitly
identified native/compiler/refutation calibration. It does not decide
consistency, claim global optimality, or provide a new end-to-end kernel object.

The relevant catalogued comparison is source 115's eleven-positive
degree-211, 107-operation equation. It has the same four fixed-port bit
lengths but a different whole-tuple K0 value, so this is a comparison of
domain and size metrics, not a same-polynomial contraction. The new formula
reduces both these metrics. The source-172 ten-positive degree-214,
87-operation equation uses the same whole tuple as this construction and retains
one fewer variable and fewer operations; it is a separate tradeoff.

## 1. Entire equation

All eleven coordinates

    J,F,alpha,i,T,w,Y,n,eta,zeta,kappa

are strictly positive integers. The literal JSON calls Y `s`.
Take the complete retained fixed integers beta,K0,MC,MF. Write lambda=210,
and put

    h=beta J, q=h+1, C=q-F-alpha, X=qw, k=eta+zeta,
    c=kY+eta, A=lambda Y(X+1)+1, Delta=A^2-1, H=4A-5,
    v0=XY^2, v=lambda^2 v0, ell=vk, E=1+ell(ell+k),
    R=[h(q-F)+alpha](q^2-1)+(MC+q MF)J,
    B=(K0+w)C-F, U=ic^2, a=Delta U^2 E, F0=1+a,
    G=EF0, f=1+2a, Q=4Delta aF0,
    b=cT-R, V=fb-c, L=bV, K=X(3c-2X)+2.

The integer-coefficient inverse polynomial is

    T3(k,x)=k -7350 x k(k^2-4)
              +5402250 x^2 k(k^2-4)(27k^2+8)
              -5672362500 x^3 k(k^2-4)(675k^4-324k^2+160).

Set

    e*=T3(k,v0)-R-1, D=q^7, M=hD,
    Z=M[n+kappa-LB]-DB-h[e*-q^4Y],
    P0=Q(Z^2-M^2GV^2)+(M^2G-Z^2), N=K-kappa H,
    P=(P0+1)(3N+1)-1.

The equation is P=0. These are all polynomial abbreviations, not additional
unknowns. The circuit contains no quotient, recurrence, factorial, radical,
or variable exponent. The displayed small powers are implemented by the
literal binary operations in the JSON.

The unit product is essential: because P0,N are integers, P=0 implies
P0+1 and 3N+1 are units. The second is 1 modulo 3, so cannot be -1.
Consequently P=0 if and only if P0=N=0. Unlike the rejected ten-variable
fixed-dilation attempt, the projector quotient is independently integral;
no assumption gcd(q,H)=1 is made.

## 2. A third-order inverse valid at every index

For any integer base b>=2 let chi_b,psi_b be the standard Pell sequences,
with psi_b(0)=0, psi_b(1)=1 and

    psi_b(m+2)=2b psi_b(m+1)-psi_b(m).

For m>=1 the exact polynomial identity is

    2 psi_(1+2v)(m)
      =2 sum_(j=0)^(m-1) binom(m+j,2j+1) (4v)^j.

It follows directly by the recurrence and Pascal identities. Define

    C1(k)=-k(k^2-4)/6,
    C2(k)=k(k^2-4)(27k^2+8)/360,
    C3(k)=-k(k^2-4)(675k^4-324k^2+160)/15120.

The first four terms of the formal inverse of this recurrence are
k+C1(k)v+C2(k)v^2+C3(k)v^3. Equivalently, direct substitution of

    K_m(x)=2m +8lambda^2 binom(m+1,3)x
         +32lambda^4 binom(m+2,5)x^2
         +128lambda^6 binom(m+3,7)x^3  (mod x^4)

gives the polynomial identity

    T3(K_m(x),x)=2m (mod x^4).                         (1)

This is an identity in Q[m,x], not a finite test over m. All coefficients
in T3 are integers because lambda^2/6=7350,
lambda^4/360=5402250 and lambda^6/15120=5672362500.
For each integer m, the full recurrence polynomial K_m belongs to Z[x].
Its first four coefficients agree with the displayed expansion. Hence (1)
actually asserts divisibility in Z[x] at every integer m:

    T3(2 psi_(1+2lambda^2 x)(m),x)-2m is in x^4 Z[x].    (2)

There is no prime-three cancellation or implicit inverse of 15120 modulo q.
The fixed dilation clears the coefficient denominators before any modular
argument. The supplied checker verifies the three zero coefficient
identities as exact rational polynomials in m.

The sign bound required by transport also holds before any index is known:

    k>=2, x>=1  implies  T3(k,x)<=k.                   (3)

To see this, write v=lambda^2 x>=1 and t=k^2>=4. The correction subtracted
from k is k(k^2-4) times

    v/6 - v^2(27t+8)/360
        +v^3(675t^2-324t+160)/15120.

The last two terms have nonnegative sum, since

    (675t^2-324t+160)-42(27t+8)
      =675t^2-1458t-176
      =675(t-4)^2+3942(t-4)+4792 >0.

Thus the bracket is positive, proving (3), including k=2.

## 3. Roots, signed transport and main rank

Unconditionally q>=32, X>=q, Y>=1, k>=2, c>=3, A>q and
Delta>1. The identities

    f^2=1+4aF0, Q=Delta(f^2-1)=4Delta^2 U^2 G,
    gcd(E,F0)=1

hold. Also f>2c and Q>c^2. At P0=0 write z=Z/M, a rational number:

    (Q-1)z^2=G(QV^2-1).                             (4)

Every prime dividing G divides neither Q-1 nor QV^2-1. Valuations in (4)
therefore make G a square. Coprimality gives E=tau^2, F0=f0^2 and
G=g^2, with positive integral roots and g=tau f0. The retained
adjacent-coefficient descent applied to

    QV^2-(Q-1)(|z|/g)^2=1

shows y=|z|/g is an integer. Thus z=epsilon gy is integral and
QV^2-(Q-1)y^2=1. For clarity, the descent writes a rational y in lowest
terms, observes that its denominator squared divides Q-1, and applies
(V,y)->((2Q-1)V-2(Q-1)y,(2Q-1)y-2QV), with sign reflections. The integral
first coordinate strictly decreases in absolute value and the denominator
of y is preserved, until |V|=|y|=1.

Set I=2Ug. The strong equations give f^2-Delta I^2=1, Q=(Delta I)^2
and c^2|I. The retained signed all-index folding lemma, from V=-c modulo f,
gives c=psi_A(p) for a positive odd p. Since c>=3, p>=3. The first norm
E=tau^2 gives k=2psi_P(m), P=1+2v and m>=1. If m=1 then k=2,
eta=zeta=1 and c=2Y+1 lies strictly between psi_A(1)=1 and psi_A(2)=2A,
impossible. Hence m>=2. The inequality

    P-A=lambda Y(2Xlambda Y-X-1)>0

and c>k imply m<p.

The changed free chart needs a fresh bound, because it does not have A>q^2.
Nevertheless

    c>2q^4                                                   (5)

already holds. If p>=5, then c>=psi_A(5)=16A^4-12A^2+1>4A^4>4q^4.
If p=3 then m=2. Thus k=8lambda^2XY^2+4 and c=4A^2-1, and

    c/k > (X+1)^2/(2X+1) > (X+1)/2.

Because c/k<Y+1 and X,Y are integers, 2Y>=X. Therefore
c>lambda^2 X^4-1>2q^4. This proves (5) in every case, without a sign of R.

The uniform transport estimate from source172 works with this new bound.
If b=0, the auxiliary equation gives
0<y^2-c^2=(c^2-1)/(Q-1)<1, impossible. Thus b is nonzero and V has its
sign. With the already integral S=Delta I, classifying the auxiliary Pell
trace/ordinate pair (S|V|,y) gives an odd index;
index one is impossible because |V|>1. Hence |V|>=4Q-3. Since
c3=4Delta+3=psi_A(3)<=c and f>2c,

    |b| >= (4Q-3-c)/f
         =4Delta f-(c+c3)/f >4Delta f-1>4g.

The last inequality uses f>6g, which follows from
a^2/g^2=Delta U^2 a/(1+a)>Delta U^2/2>9.
Also y<3|V|/2. Consequently L=bV>0, gy<3L/8 and |b|/q^7<L/2.

Set t=B/h, sigma=Y/q^3, rho=e*/q^7 and W=1+hL for proof only. The exact
carrier identity is

    z=n+kappa+sigma-Wt-rho.                          (6)

By (3), e*<=k-R-1<b. If B<=-1, then Wt<-L, and (6) yields
n< L/2-L+|b|/q^7<0, a contradiction. Therefore B>=0 and C>0.
The retained coherent-mask estimate now gives 3q<R<q^4-2. By (5), c>2R,
so b,V>0. The normalized strong-rank and signed auxiliary-index lemmas apply
with c^2|I, c>2p, c>2R, V=-c modulo f and V=-R modulo c. The latter
uses f=1 modulo c. They give p=R, hence R odd; the retained mask-parity
lemma gives q even and J odd.

## 4. First rank, projection and denominator recovery

Integral z=Z/M implies q^7|h(e*-q^4Y). As gcd(h,q)=1, q^7 divides
e*-q^4Y, and in particular q^4|e*. Since q|v0, identity (2) gives

    q^4 | e*-(2m-R-1).

We already know 1<=m<R and 3q<R<q^4. Thus |2m-R-1|<R<q^4, and

    2m=R+1.                                            (7)

No coprimality between q and H was invoked. That is the reason for the
eleventh coordinate kappa and the independent unit factor N.

Write R=2r+1, so r>=48. The retained uniform ratio theorem applies to every
lambda>=1 and Y>=1, including this constant 210:

    (X+1)^(2r)/X^r < psi_A(2r+1)/psi_P(r+1)
      < ((X+1)^(2r)/X^r)(1+1/[Y(X+1)])^(2r).

Together with Y<c/k<Y+1 it gives Y>X^r/3 and
H>3Y(X+1)>X^(r+1). The exact unit equation N=0 gives H|K. The universal
Pell projector therefore gives

    H | (X-2^R)(2^R X+1).

The entire product has magnitude below H. Indeed, writing u=2*4^r,

    |(X-u)(uX+1)| < 4*4^r X^2+8*16^r X < X^(r+1).

After division by X^(r+1), the two terms decrease for X>=32,r>=48;
at (32,48) they are 2^(-137) and 2^(-45). The divisible integer is zero,
so X=2^R. Hence q|X makes q a power of two, q=2^a with a>=5.

Since R>3q and 3*2^a>=7a for a>=5, q^7|X. Thus q^7|v0 and (2), (7)
give q^7|e*. Therefore rho is integral. Equation (6) then makes
Y/q^3-WB/h integral. Because gcd(q^3,h)=1 and W=1 modulo h, this gives

    q^3|Y, h|B, and B/h>=0.                            (8)

The uniform ratio theorem, fixed-minus parity, half-binomial rounding and
fresh native reconstruction are now exactly the retained source interfaces.
They reconstruct the unscaled source base Y(X+1)+2; they do not identify it
with the present A. At the whole supplied numerical tuple this produces a
finite syntactic ZFC refutation.

## 5. Constructive positive completeness

A finite refutation supplies canonical outer data q=2^a, X=2^R, R>3q,
R=3 modulo 4, q^3|Y, C>0 and B/h>=0, with the retained half-binomial
identity. Take w=X/q>0, and form the new constant-dilation A,P. Put

    c=psi_A(R), k=2psi_P((R+1)/2), tau=chi_P((R+1)/2),
    eta=c-kY, zeta=k-eta, kappa=K/H.

The uniform ratio theorem gives 0<eta<k, so eta,zeta are positive integers.
The universal projector gives integral kappa; the growth of k and c makes
K>0, so kappa>0. Identity (2) gives integral rho=e*/q^7. Also sigma=Y/q^3
is a positive integer.

Choose a positive period of the determinant-one Pell matrix at A modulo
c^2 tau. Positive multiples of that period give arbitrarily large solutions
(f0,I0) with c^2 tau|I0. Set i=I0/(c^2 tau)>0. Then a=f0^2-1, G=g^2
with g=tau f0, and f=2f0^2-1 is the doubled strong trace. The doubled
ordinate I=2f0 I0 has c^2|I and Q=(Delta I)^2. Choose the period multiple
large enough that g>kappa+sigma+|rho|. This cofinal choice is necessary;
the previous small-correction bound for an arbitrary period seed is not used.

Let S=Delta I, V=chi_S(R)/S and y=psi_S(R), positive integers since R is
odd. The odd quotient-polynomial identities, using R=3 modulo 4, give
V=-c modulo f and V=-R modulo c. Since f=1 modulo c and gcd(f,c)=1,

    T=(V+c+Rf)/(cf)

is a strictly positive integer. It gives V=f(cT-R)-c exactly. Define

    n=gy+(1+hL)(B/h)+rho-kappa-sigma.

Every term is integral, and the chosen lower bound on g makes n positive.
Its carrier is z=gy, so P0=0; the chosen kappa makes N=0. Therefore P=0.
All eleven inputs have been constructed in their actual positive domain.

The two directions establish the claimed zero-existence equivalence at the
retained native/refutation calibration, with no consistency assumption.

## 6. Exact degree and a fixed-coefficient witness

Let q0=beta J and k0=eta+zeta. The unique degree-170 part of P0 is

    -16 lambda^36 q0^46 w^24 Y^56 i^10 k0^32 (q0-F)^2.

Indeed deg(Q,M,G,V,Z)=(58,8,36,30,44); the term -QM^2GV^2 has degree
170, while QZ^2 has degree at most 146 and the remaining terms are lower.
The degree-four part of N is

    q0 w [3k0Y-2q0w-4lambda kappa Y].

Thus the complete degree-174 part of P is

    -48 lambda^36 q0^47 w^25 Y^56 i^10 k0^32 (q0-F)^2
       [3k0Y-2q0w-4lambda kappa Y].

In particular the literal coefficient of

    J^49 w^25 Y^57 i^10 eta^32 kappa

is +192 lambda^37 beta^49, nonzero at the actual retained positive beta.
The exponent sum is 174. This proves an attained degree, not only a DAG
upper bound or a generic-parameter estimate. The 104-operation count charges
every square, every small-constant multiplication, and every binary sum or
difference; reuse is free.

## 7. Rejected shortcut and remaining questions

Deleting kappa and reinserting K/H into the carrier would produce a tempting
ten-variable degree-176 formula. Its proof fails: with fixed lambda and free
Y, H need not be coprime to q, so the first-index congruence cannot be read
from the shared denominator. That formula is not an accepted construction.

Possible next work is to recover the projector quotient with no new coordinate
while proving the required denominator separation, or to find an inverse
Lucas polynomial of lower circuit cost with the same fourth-order identity.
The present proof does not claim historical priority for formal inverse
series or a global simplicity minimum. Its new application replaces the
variable dilation by a constant with denominators cleared in advance.
