# Bounded Pell search after the 91-operation product bound

This note records an unsuccessful reduction attempt and its exact
obstruction. It changes no published source system or fixed index. Fixed
numerals and equality tests are free throughout. The current reference
certificate is `round36_1980_product_bound_certificate.py`, with 49
multiplications and 42 additions. Nothing here establishes a smaller
universal certificate.

## 1. Replacing the auxiliary root by its square as an input

Write the retained quantities as

    A=a+4, D=A^2-1, c=psi_A(p), R=i*c^2, K=R^2,
    J=2r+1, u=J+j*c.

The current auxiliary equations are

    R^2=D*(f^2-1),
    K*(u^2-y^2)=1-y^2,
    u=c+o*f.

The candidate supplies a positive variable F instead of the root f and
uses

    R^2=D*(F-1),
    K*(u^2-y^2)=1-y^2,
    u=c+o*F.                                           (1)

There is a real arithmetic saving: the multiplication producing f^2
disappears, and its only consumer subtracts one directly from F. No other
primitive changes. The exploration script verifies all 22 full source
residuals for this altered system, including the same three acyclic
corrections. Its count is 48 multiplications and 42 additions.

This arithmetic observation does not establish universality. The old
positive-domain sufficiency proof used the first equation as a Pell norm
to recover an auxiliary index m with c dividing m. That conclusion is no
longer justified when F is not required to be a square.

Canonical necessity alone survives the change. If the old root is f_old,
set F=f_old^2. The half-parameter polynomial identity is valid modulo
f_old^2 because

    R^2=D*(f_old^2-1) = 1-A^2 mod f_old^2.

For the canonical J=1 mod 4, it gives u=c mod f_old^2. Hence the new
quotient o=(u-c)/F is a positive integer. The obstruction is specifically
the reverse direction.

## 2. An exact counterexample to the proposed replacement lemma

The following example satisfies the independent large-index and growth
hypotheses requested for this auxiliary audit:

    A=8, D=63, p=69, J=7,
    c=psi_8(69), d=chi_8(69),
    i=294*D=18522,
    R=294*D*c^2,
    F=1+294^2*D*c^4.                                  (2)

In particular,

    p>=66, A>J>1, J odd, p>=(J+3)/2,
    c>A*D^2, 0<2p<=c, R even, F odd,
    R=i*c^2, R^2=D*(F-1),

and F is not a square. The main coordinate has the exact value

    c=5832177165185523567265713248364040830524254217620985618097131991915982158283844865.

The script finds that 6367 divides F. Put

    Q=F/6367,
    N=1592*(Q+1).                                      (3)

Direct binary powering in the integer ring
`(Z/FZ)[sqrt(63)]` verifies the exact congruence

    chi_8(N)=1 mod F, psi_8(N)=0 mod F.                 (4)

It also verifies gcd(4N,c)=1. Let k be the representative in
{1,...,c} of

    (J-p)*(4N)^(-1) mod c,

and set

    s=p+4kN.                                          (5)

Thus s=1 mod 4, s>p, and s=J mod c. By (4),
psi_8(s)=psi_8(p)=c mod F. Define the positive Pell coordinates at the
integer base R by

    y=psi_R(s), u=chi_R(s)/R.                          (6)

The division in (6) is exact because s is odd. The polynomial identity
from the 92-operation proof gives

    u=Q_((s-1)/2)(R^2)
     =psi_8(s)=c mod F,

since R^2=1-A^2 mod F and (s-1)/2 is even. Independently, R=0 mod c
gives

    u=s=J mod c.

Both congruences are also checked directly by modular Pell powering at
base R; the implementation reduces chi_R(s) modulo R*F and R*c,
respectively, before dividing the integer remainder by R. It never
divides by a nonunit inside a residue ring.

Consequently

    o=(u-c)/F, j=(u-J)/c                               (7)

are integers. They are strictly positive: R>A, s>p, and the standard
growth bound gives

    u>(2R-1)^(s-1)>(2R-1)^(p-1)>c>J.

The first Pell identity in (6) is exactly

    (R*u)^2-(R^2-1)*y^2=1,

which rearranges to the middle equation of (1). Equations (2) and (7)
give the other equations in (1), together with u=J+jc. Nevertheless
p=69 is different from J=7.

This invalidates the proposed weakened auxiliary lemma even with
p>=66, c>AD^2, 0<2p<=c, A>J, and the index comparison
p>=(J+3)/2. It is deliberately not claimed to be a counterexample to
the full altered packed system: the remaining packing, first-index,
interval, and exponent equations have not been satisfied. A different
full-system argument might conceivably rescue (1), but the current
auxiliary proof cannot do so.

## 3. What the computation certifies

`../verification/explore_round36_auxiliary_square_input.py` produces
`../verification/explore_round36_auxiliary_square_input.json`. It records
all integers in (2)--(7), exact modular residues, the growth and parity
checks, and the complete altered-system arithmetic check.

Trial division and a probable-prime test propose the period N during the
bounded search. Primality is not a proof input: (4) is verified directly
by exact integer modular powering. Thus the period assertion remains
valid independently of whether a proposed factor is prime. The
astronomically large coordinates u and y are specified by exact Pell
sequences; the verifier does not attempt to materialize them.

The default bounded search uses A=8, p=69, J=7 and even multipliers
2,...,1000; the first accepted multiplier is 294. The receipt separately
labels the altered 90-operation arithmetic and the auxiliary
counterexample. It does not label the altered source as universal.

## 4. Two further local coordinate changes lose operations

The half-parameter norm already costs five operations once K and u are
available:

    U2=u*u, Y2=y*y, G=U2-Y2, L=K*G, P=1-Y2,
    L=P.

The positive coordinate z=y-u would instead give

    (K-1)*z*(2u+z)=u^2-1.

Its direct factored schedule needs seven operations: K-1, 2u, 2u+z,
the two products on the left, u^2, and u^2-1. The four existing
congruence operations for u are unchanged. This family loses two
operations.

For the first Pell norm, let U=w*n^2, Y=s*n^2, E=U*Y, and
Q=U*Y^2. Its current normalized form is

    tau*(tau+1)=(E^2+U)*(Y*k)^2.

It costs six operations after E and the shared interval product Y*k
are available. Restricting the first index to be odd allows the usual
half-index factorization

    k=z*v, tau=Q*z^2,
    (Q+1)*v^2-Q*z^2=1.

The factored norm Q*(z^2-v^2)=v^2-1 requires six operations including
the previously absent Q=E*Y. Constructing k=z*v adds a seventh. No
existing interval product is deleted, so this family loses one
operation. This count does not assume free division or free coordinate
reconstruction.

These are bounded, explicit obstacles, not an optimality argument for
the 91-operation certificate.
