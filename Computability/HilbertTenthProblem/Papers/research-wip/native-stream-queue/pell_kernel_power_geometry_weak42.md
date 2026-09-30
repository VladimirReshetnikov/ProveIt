# The single-product weakening does not certify powers of two

The new [43-operation binary power predicate](pell_kernel_power_two43.md)
cannot simply inherit the old single-product auxiliary saving. Replacing
`(i*c^2)^2` by `i*c^2` gives a literal **42=24M+18A** source with eleven
equations, but it has strictly positive witnesses at **q=5**. This remains
true with the free comparison `r+1=q`; the failure is not just a wrong
binomial valuation at an otherwise valid power of two.

This counterexample concerns only the specified geometry component. It
does not refute the complete75 candidate with its original packed fields,
compiler, transport and input bridge. The complete universal bound remains76.

## 1. The exact weakened source

Keep every equation of the43 power predicate, including `r+1=q`, except
for the relaxed auxiliary norm. With `X=wq`, `Y=sq`, `E=XY`,
`Delta=a^2+4a+3`, `J=2r+1` and `U=jc-J`, the changed equation is

    i*c^2=Delta*(f^2-1).

The last norm is evaluated as

    i*c^2*(U^2-y_aux^2)=1-y_aux^2,

and the minus congruence is still `U=of-c`. Removing the squaring
instruction saves exactly one multiplication. The adjacent checker
expands all eleven independent source polynomials and audits the residual
correction for the last norm. There are still seventeen positive auxiliary
coordinates apart from q.

## 2. Exact main and first Pell coordinates at q=5

Use the conventional sequences

    chi_A(n)+psi_A(n)*sqrt(A^2-1)=(A+sqrt(A^2-1))^n.

Fix

    q=X=Y=5, w=s=1, r=4, J=9,
    a=30, A=a+2=32, Delta=1023,
    P=2XY^2+1=251, E=25, M=4a+3=123,
    p=14587=7+20*729, n=9755=5+25*390.

Set `c=psi_A(p)`, `d=chi_A(p)`, `k=psi_P(n)`. Exact integer evaluation
gives

    55828*k < 10000*c < 55829*k,
    gcd(p,c)=1.

In particular `5k<c<6k`. Define

    eta=c-5k, zeta=6k-c,
    tau=(chi_P(n)-1)/2,
    h=(k-5)/25, ga=(d-5-30c)/123.

All these quantities are strictly positive integers. Integrality of h
follows from `P=1 mod25` and `n=5 mod25`; integrality of tau follows
from odd P. The direct exponent recurrence gives

    chi_(a+2)(p)-a*psi_(a+2)(p)=2^p mod(4a+3).

Here `2^7=5 mod123` and `2^20=1 mod123`, so the numerator defining ga
is divisible by123. It is positive because
`d-ac=2c-psi_A(p-1)>c>5`. The first Pell norm gives

    tau*(tau+1)=(E^2+X)*(Yk)^2.

The checker materializes every main coordinate and verifies all eight
literal equalities through the main norm, including `r+1=q`, as exact
integers. The main c has87,511 bits. Its receipt stores bit lengths and
hashes instead of a long decimal expansion. The stated ratio is an exact
rational interval, not a floating-point approximation.

## 3. Strictly positive weak auxiliary extension

The general extension in
[the single-product analysis](../../1980/EXPLORATION_SINGLE_PRODUCT_AUXILIARY_SCALE.md)
applies because p and J are odd, `J<c`, and `gcd(p,c)=1`. To make the
construction explicit, set

    m=2p, f=chi_A(m)=2d^2-1,
    R=Delta*psi_A(m)=2*Delta*c*d,
    i=4*Delta^2*d^2.

Then `R^2=i*c^2=Delta*(f^2-1)`. Write
`sigma=(-1)^((p-1)/2)=-1`. Choose the representative

    t0=(-sigma*J-p)*(4p)^(-1) mod c, 0<=t0<c,

and add c if needed so that `(-1)^t=-sigma`. The inverse exists, and
c is odd, so this parity adjustment is always possible. Put

    v=p+4pt,
    U=chi_R(v)/R, y_aux=psi_R(v),
    j=(U+J)/c, o=(U+c)/f.

For odd v, `chi_R(v)/R` is an integer polynomial in `R^2`. Its
normalized odd-index identities give

    U=sigma*v=-J mod c,
    U=sigma*psi_A(v)=sigma*(-1)^t*c=-c mod f.

The first uses `c|R` and the CRT choice; the second uses
`R^2=1-A^2 mod f` and the Pell step `psi_A(z+2m)=-psi_A(z) mod f`.
Thus j and o are integers. Here `R>f>2c>J` and `v>=3`, so
`U>=4R^2-3` makes both strictly positive. The Pell norm at base R gives

    R^2*(U^2-y_aux^2)=1-y_aux^2.

It also gives both required minus congruences by definition. This supplies
all five remaining positive coordinates and proves every weakened source
equation. The checker materializes f, R, i, the CRT representative and v,
and checks their exact identities and residues. It does not materialize
`chi_R(v)` or `psi_R(v)`; their existence and positivity are the parametric
Pell argument just given.

## 4. Consequence and evidence boundary

The retained comparison `r+1=q` is satisfied, yet q=5 is not a power of
two. Both the actual main index p and first index n differ from the
indices that the strong43 predicate recovers. The example also has even
r, showing that the strong kernel's signed-index parity cannot be
silently retained after this weakening.

Run [the checker](pell_kernel_power_geometry_weak42.py) without `--write`
to compare with [the saved receipt](pell_kernel_power_geometry_weak42.json).
The source audit and main coordinates are exact finite computations; the
final auxiliary extension is a proved formula. Independent full proof,
source, and default-replay review passed. No general lower bound for power predicates is asserted.
