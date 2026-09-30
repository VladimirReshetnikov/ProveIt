# Exact power-of-two geometry in 43 operations

The retained binary fixed-minus43 kernel, with scale equal to the supplied
positive parameter q and the free comparison of its existing `r+1` register with q, has
positive witnesses **exactly when q is a power of two greater than1**.
The complete relation costs **43=25M+18A**, with11 equations and17 positive
auxiliaries in addition to q. This is geometry only: stream bounds,
controller, ordinary input and acceptance are not included. The complete
universal bound remains76.

## 1. Literal source

Supply positive q and the retained positive coordinates

    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,ga,y_aux.

The source is the unchanged binary kernel, with `X=wq`, `Y=sq`,
`Delta=a^2+4a+3`, and `U=jc-(2r+1)`:

    r=q-1,
    ((XY)^2+X)(kY)^2=tau(tau+1),
    c=kY+eta, k=eta+zeta, k=r+1+hXY,
    a=Y(X+1), d=X+ac+ga(4a+3),
    d^2=1+Delta*c^2,
    (ic^2)^2=Delta*(f^2-1),
    Delta*(f^2-1)(U^2-y_aux^2)=1-y_aux^2,
    U=of-c.                                             (1)

The [literal source](pell_kernel_power_two43.py) replaces the existing
scale-register references by q; no square of q is computed or assumed.
The core already computes `r1=r+1`. Comparing that register with q
implements the first equation for free; no outer arithmetic instruction
is needed. All43 retained instructions remain, including the full
coefficient `ic^2`. This gives43 operations, eleven equations and eighteen
positive coordinates if q is also existentially supplied.

## 2. Soundness and the small boundaries

Positive r excludes q=1. Values q=2 and q=4 already have the required
geometry; no classification of their arbitrary kernel witnesses is
needed for this projection. If q=3, X,Y,a and `4a+3` are all0 modulo3.
The exponent equation forces d=0 modulo3, whereas the main norm has
`Delta=0` modulo3 and forces `d^2=1` modulo3. Thus q=3 is impossible.

It remains to consider q>=5. Put `A=a+2`, `E=XY`, `P=2XY^2+1` and
`J=2r+1=2q-1`. Before interpreting any power or index,

    r>=4, X,Y>=q,
    E>=q^2>r+1,
    a>=q(q+1)>J,
    P>A, (2P-1)-4A=4Y[X(Y-1)-1]-7>0.                  (2)

Both main and first discriminants are nonsquares: their parameters
A and P are integers greater than1, and each discriminant is the
parameter's square minus1. The first norm classifies k as `psi_P(n)`.
Its residue modulo E gives `n=r+1 mod E`, hence n>=r+1. The positive
interval `Y<c/k<Y+1` and the larger first parameter force the main index
`p>=n+1>=r+2>=6`. Therefore

    c=psi_A(p)>=(2A-1)^(p-1)>A^5>A*(A^2-1)^2.

Also c>J and `2p<=c`, by the same interval and elementary Pell growth.
These are the generic relaxed-rank and half-parameter hypotheses used
in the retained [binary proof](../../1980/BASE_TWO_PELL_89_PROOF.md).
The strong auxiliary coefficient and both minus congruences are
unchanged. They recover `p=J`, `c=psi_A(J)`, `d=chi_A(J)`.

If the first index exceeded r+1, it would be at least r+1+E. Since
E>r and `2P-1>4A`, Pell growth would give

    c/k <= (2A)^(2r)/(2P-1)^(r+E) < 1/2,

contrary to c/k>Y. Thus `k=psi_P(r+1)` exactly.

## 3. Lower ratio first, then the direct exponent recurrence

Let `T=XY^2` and `xi=(X+1)^(2r)/X^r`. The retained Pell estimates give

    c/k >= xi*(1+3/(2a))^(2r)*(1+1/(2T))^(-r) > xi,
    c/k < xi*(1+2/a)^(2r).                             (3)

The strict lower factor follows from `6T>a`, valid already for X,Y>=5.
Use that lower inequality first. The supplied interval gives `xi<Y+1`;
since `xi>X^r` and Y is integral,

    Y>=X^r, a>X^(r+1).

Now `4r/a<4r/5^(r+1)<1/2` for r>=4. The upper estimate in(3) consequently
becomes `c/k<xi*(1+8r/a)`. This order matters: the crude initial q=5
bound gives `4r/a<=8/15`, which is not less than1/2.

Use a direct recurrence to recover the exponent; no stronger
chi-congruence size criterion is required. The sequence

    H_j=chi_A(j)-a*psi_A(j)

has initial values1,2 and recurrence `H_(j+2)=2A*H_(j+1)-H_j`.
The sequence `2^j` satisfies that recurrence modulo `M=4a+3`, since
`4-4A+1=-M`. Hence `H_J=2^J mod M`. The supplied exponent equation
gives `X=H_J mod M`. Both representatives are strictly between0 and M:

    X<a,  2^J=2*4^r<X^(r+1)<a.

Thus `X=2^(2r+1)`. Since the positive integer q divides X, q is a
power of two. This proves the required projection for every possible
q, without assuming an unpaid field bound, a square scale, or parity.

For q>=5 the usual rounding conclusion is also available. From(3) and
`xi<Y+1<2Y`,

    0<c/k-xi<16r/(X+1)<1/2.

The binomial fractional tail is between0 and1/4. Integrality and the
positive ratio interval force `Y=floor(xi)`, and its residue modulo X
is `binom(2r,r)`. These facts support the converse below. The theorem
does not assert them for every possible q=2 or q=4 witness.

## 4. Every positive converse coordinate

Let q=2^t for t>=1, and put `r=q-1`, `J=2r+1`, `X=2^J` and
`Y=floor((X+1)^(2r)/X^r)`. The central-binomial valuation is

    v2 binom(2r,r)=popcount(r)=t.

Since the binomial integer part is congruent to that coefficient modulo
X, q divides Y. Also q divides X, so `w=X/q,s=Y/q` are positive integers.
For q>=4, the canonical ratio estimates and the binomial tail give both
strict ratio inequalities. Define

    a=Y(X+1), A=a+2, Delta=A^2-1, P=2XY^2+1,
    c=psi_A(J), d=chi_A(J), k=psi_P(r+1),
    eta=c-Yk, zeta=k-eta,
    tau=(chi_P(r+1)-1)/2,
    h=(k-r-1)/(XY), ga=(d-X-ac)/(4a+3).                 (4)

The first Pell congruence makes h integral; P is odd, so tau is integral.
The exponent recurrence makes ga integral. All are positive by growth;
for ga one can use `d-ac=2c-psi_A(J-1)>c>X`. The strict interval makes
eta,zeta positive.

The smallest endpoint q=2 is checked explicitly, without a small-error
estimate: `r=1,X=8,Y=10,a=90,A=92,c=33855,k=3202`,
`eta=1835,zeta=1367,h=40`. Equations(4) give positive integral tau,ga as
well. The checker materializes the full seventeen-coordinate extension
for this endpoint and checks every equality in(1).

For every q, use the retained generic auxiliary construction

    m=2cJ, f=chi_A(m), i=Delta*psi_A(m)/c^2,
    R=ic^2, y_aux=psi_R(J), u=chi_R(J)/R,
    o=(u+c)/f, j=(u+J)/c.                              (5)

The divisibility `c^2 | psi_A(2cJ)` is the usual Pell multiple-index
identity. For example, `psi_A(Jn)=c*psi_d(n)`, and `d^2=1 mod c`
implies `psi_d(n)=n*d^(n-1) mod c`; take n=2c. Thus i is a positive
integer. Odd J makes u integral. Since r is odd, `J=3 mod4`, and the
normalized odd-index polynomial identities give `u=-c mod f` and
`u=-J mod c`. Consequently o,j are positive integers. Their positivity
also follows directly from the plus numerators in(5).

The relaxed norm follows from `R=Delta*psi_A(m)`. The normalized Pell
equation at R gives the auxiliary norm, and(5) gives both minus
congruences. This constructs every coordinate of(1) positively. The
same construction applies at q=2; its auxiliary index is203130, small
enough for the checker to materialize even these large witnesses.

## 5. Evidence and scope

The [checker](pell_kernel_power_two43.py) independently expands all
eleven source polynomials and verifies the exact auxiliary norm
correction, the unchanged43-instruction core, and the complete43 ledger.
It checks the pre-index bounds through q=500, materializes canonical
main and first Pell coordinates at q=2,4,8,16,32, and materializes the
entire positive witness at q=2. The [receipt](pell_kernel_power_two43.json)
stores sizes rather than printing its enormous coordinates.

This module types q alone. It does not certify arbitrary binary strings,
FIFO transport, a finite controller, ordinary input, or accepting
computation. Independent full proof/source/default review passed, including
the small-q boundaries, lower-ratio-first argument, direct exponent
recurrence and full q=2 auxiliary witness. No Lean formalization or
complete universal bound below76 is claimed.
