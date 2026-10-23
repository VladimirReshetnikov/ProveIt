# Rational auxiliary Pell saturation

This independent lemma removes the need to force the normalized strong
index variable `i` to be divisible by H in the twelve-variable weighted
root construction. It also avoids any auxiliary-unit factorization claim.

## Lemma

Let S>1 and V be integers, and let y be rational. If

    S^2 V^2-(S^2-1)y^2=1,

then y is an integer.

### Proof

Write `S^2-1=D0 b^2`, where b is a positive integer and D0 is squarefree.
The integer S^2-1 is not a square: it lies strictly between (S-1)^2 and
S^2. Thus D0>1.

Put w=b y. The equation says `D0 w^2=S^2 V^2-1` is an integer. If w=p/q
in lowest terms, q^2 divides the squarefree integer D0, so q=1. Therefore
w is an integer. Neither V nor w is zero, as is immediate from the
original equation and S>1.

Let epsilon=x1+y1 sqrt(D0) be the least positive integral Pell unit with
x1>1, y1>0. Write

    epsilon^n=x_n+y_n sqrt(D0), n>=0.

The standard classification of positive integral Pell solutions gives

    S=x_m, b=y_m,
    |SV|=x_n, |w|=y_n

for positive indices m,n. In particular x_m divides x_n.

We prove the exact first-coordinate divisibility statement needed here:

    x_m | x_n  ==>  n=m (mod 2m).

Work in the finite ring `(Z/x_m Z)[xi]/(xi^2-D0)`. Epsilon is a unit,
since its norm is 1. The Pell identity gives

    epsilon^(2m)=(x_m+y_m xi)^2=-1 (mod x_m),

because the xi coefficient is divisible by x_m and
`D0 y_m^2=x_m^2-1`. Therefore, after reducing n modulo 2m, its first
coordinate is congruent up to sign to x_r for some `0<=r<=m`: use
`x_{-r}=x_r` to reflect a remainder larger than m. If r<m then

    1=x_0<=x_r<x_m,

so x_m cannot divide x_r. Thus r=m, proving `n=m (mod 2m)`.
Consequently n is an odd multiple of m.

Finally y_m divides y_{km} for every positive integer k. This follows
directly by expanding `(x_m+y_m sqrt(D0))^k`: every term in its lower
coefficient contains a factor y_m. Hence `b=y_m` divides `w=+/-y_n`.
It follows that y=w/b is an integer, as required.

The proof uses the fundamental unit of the integral equation
`x^2-D0 y^2=1`, not a possibly half-integral fundamental unit of the full
quadratic number-field ring. Thus no discriminant-modulo-four exception
has been omitted.

## Application to the weighted twelve-variable construction

Keep the original normalized `i` as a positive supplied variable; do not
replace it by Hj. Use the same A1,A2,D,Q,d,v,b,e,B as in the four-root
audit, so

    Q=(Delta i c^2)^2=S0^2, S0=Delta i c^2>1,
    d=Q-1, e=Q(Dv^2+b^2)-1, B=2Qvb.

Instead of amalgamating the auxiliary root y itself, amalgamate

    rho=d y.

For example put `Sgeom=Dv^2+b^2` and choose the integer bound

    W=2d(Sgeom+1).

For every real conjugate satisfying `rho^2=d(e-Bf)` and `f^2=D`, the
same estimate as before gives

    rho^2<2dQ Sgeom<4d^2 Sgeom,
    |rho|<2d sqrt(Sgeom)<W,

where `Q/(Q-1)<2`. One may use the original separation formulas

    K=1+H(2W+1), M=1+2K A2+2H W,
    Z=Ht+K(X+ac).

The following cheaper weights also suffice, including the choice `M=K`
rather than `M=K+1`:

    K=H W+1, M=K, Z=Ht+K(X+ac).

Indeed put Aparam=a+2. The positive source geometry gives
`Aparam<2E`, `c<2kY`, and c>1. Hence

    A2=1+(Aparam^2-1)c^2 < Aparam^2 c^2
      < 16(EkY)^2 < 16 A1.

Since H>=7, sqrt(A1)>1, and K>HW,

    HM sqrt(A1)-K sqrt(A2)
      > K(H-4)sqrt(A1) > K > HW.

Also `K sqrt(A2)>K>HW`. These are exactly the two strict separation
inequalities needed in the Galois argument. The bound Aparam<2E follows
from `E=XY`, `a=E+Y`, `X>=16`, `Y>=4096`; it invokes no unproved Pell
classification or decoded mask property.

Define the new polynomial as the product over the four formal sign pairs
`r^2=A1`, `sigma^2=A2` of

    [(Z-HM r-K sigma)^2-H^2 d e]^2-H^4 d^2 B^2 D.

A zero supplies r,sigma and

    rho=(Z-HM r-K sigma)/H,
    f=(d e-rho^2)/(d B), f^2=D,
    rho^2=d(e-Bf).

The multiquadratic separation argument in the companion audit, with rho
in place of y, gives integral r and sigma, and rational rho. Then f is
rational, hence integral because f^2=D is integral. The displayed
identity now makes rho^2 an integer. Therefore rho is an integer.

Set gamma=(sigma-X-ac)/H. The linear identity becomes

    t=Mr+K gamma+rho.

Since K=1 (mod H), the fact K gamma is integral forces gamma integral.
No coprimality condition on H and d has been used.

Now y=rho/d is rational. With `V=vf-b` integral, the identity for rho gives

    d y^2=e-Bf=Q V^2-1,
    S0^2 V^2-(S0^2-1)y^2=1.

The lemma proves y integral. Hence all normalized source equations are
restored with exactly the same signed-core domain as in the first audit.

Completeness is immediate from any old all-positive normalized solution:
keep its i and all other retained coordinates, and set

    t=K gamma+M tau+d y>0.

No enlarged auxiliary index, modular period, or new congruence is required.

## Optional single-product guard

The same unrestricted-i resultant also permits the literal single
polynomial

    P=Nk Nt (1+Res12)-1.

Here is the needed guard proof; it does not invoke a generic assertion
that unrelated unit factors must be positive. Write the formal factor as

    F=Cformal(r,sigma)^2-H^4 d^2 B^2 D.

Because B is even, F is a square modulo 4 in the free quadratic algebra.
Taking the product over the four formal sign changes gives

    Res12=Norm(Cformal)^2 (mod 4).

The expression Norm(Cformal) is itself an integer-coefficient polynomial,
so every integer specialization has Res12 congruent to 0 or 1 modulo 4.
At a zero of P all three integer factors are units. The factor 1+Res12
cannot be -1, since -1 is 3 modulo 4, so it equals 1 and Res12=0. Thus
Nk=Nt=epsilon for epsilon in {+1,-1}.

The weak transport bootstrap now yields Cword>=0 rather than Cword>0:
if Cword<0, the transport factor is at most -(K0+w)<=-2. In either case
q-F=Cword+alpha>0, hence R>0 and B remains nonzero. All root-recovery
arguments above are unchanged. The signed-domain theorem explicitly
allows common index/transport signs and proves they are both +1 after
Pell rank recovery. Therefore this product has the same positive zero
set as the three-equation system.

## Domain caveat

This application as stated retains positive i and T, ensuring d>0 and
B>0. It also works for nonzero signed i and nonzero signed T after using
absolute values in the cross-term bound, provided all other geometry
needed for v,b nonvanishing is established. It does not by itself license
allowing i=0 or T=0 in an unrestricted-integer lift. Any such extension
must separately exclude or handle those branches.
