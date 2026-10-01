# Infinite low-X outer families for the86 candidate

The later [all-input collapse](complete75_weakened86_all_input_collapse.md) and
[actual rejecting compiler](complete75_weakened86_rejecting_compiler.md) now refute
the specific86 weakening on actual program slices. The outer-only theorem below and
its independent scope remain unchanged.

The [complete negative-input successor](complete75_weakened86_full_negative_family.md)
pays the missing input/index congruences and all five auxiliary coordinates
for one fixed scalar compiler instance, giving infinitely many full positive
19-coordinate zeros at x=1. It does not instantiate an actual universal
program or establish false membership. The outer-only theorem and
certificate below remain unchanged.

There is no uniform bound on the first/main Pell indices or their odd
gap that follows from the **first norm, main norm, both strict ratios,
actual main-root congruence and outer transport equation alone**. For
every fixed compiler width d>=4, those equations have an infinite
family with fixed q,X,Y and unbounded odd `g=2n-p`.

This is a structural limitation of that proposed reduction, not a
counterexample to the [weakened86 candidate](complete75_weakened_bound86_candidate.md).
The family does not complete the input norm, the first-index equation
or the target congruence. In particular it supplies no passing full
class for the [negative-input extension criterion](complete75_weakened86_auxiliary_sign_lift.md).
This packet alone left soundness unresolved; the later all-input theorem
refutes the proposal. Its86=48M+38A operations,19 positive coordinates
and exact degree203 are unchanged.

The [checker](complete75_weakened86_infinite_outer_family.py) and
[receipt](complete75_weakened86_infinite_outer_family.json) also certify
one concrete tuple:

    d=4, q=16, X=8192, Y=4096,
    p=321629343237, n=214421015143,
    g=107212687049.

Its two strict ratio inequalities are verified by exact directed-integer
intervals. The actual main Pell coordinate c has8,362,419,590,553 bits
and is **not materialized**. A128-bit mantissa with an integer binary
exponent suffices to bound it rigorously and certify the strict
inequalities. The receipt contains the exact endpoints and a separate
96-bit-precision replay using the same interval algorithm. No floating-point
comparison is used in the certificate.

## 1. Fixed compiler data at every width

Fix any compiler constants satisfying the unchanged candidate contract
at width d>=4. Set

    B=q=2^d, Jrep=1, Y=q^3,
    e=the least odd integer at least3d,
    X=2^e, w=X/q^3 in{1,2}, s=1,
    a=Y(X+1), A=a+2, H=4a+3,
    E=XY, P=2XY^2+1.                                      (1)

Thus e>=13, and A and P are the actual first/main Pell parameters of
the source. They satisfy

    A<P<2A^2-1.                                           (2)

The first inequality follows from
`P-A=Y[X(2Y-1)-1]-1>0`. The second follows by expanding
`2A^2-1-P=2[Y^2(X^2+X+1)+4Y(X+1)+3]>0`.

Choose the remaining fixed outer data

    x=1, F=2, alpha=q-2-2d, zplus=1.                       (3)

Here alpha is positive for every d>=4. The computed width field is
`C=q-F-alpha-2d*x=0`, so the exact transport factor is

    (K0+X)C+(q-F)-zplus(q-1)=-1.                         (4)

This works independently of the positive fixed numeral K0 and of the
admissible masks and input offset. It therefore applies to any fixed
compiler constants satisfying the stated width contract. It makes no
claim about the represented input's membership in a program language.

## 2. An odd progression that pays the actual main-root condition

For the Pell sequences at A, put

    E_A(t)=chi_A(t)-(A-2)psi_A(t).

The recurrence, `E_A(0)=1`, `E_A(1)=2`, and `4A-1=H+4` prove

    E_A(t)=2^t modulo H.                                (5)

As H is odd, the powers of2 modulo H have a positive return period T.
One can find such a period by finite modular iteration; minimality is
irrelevant. Choose

    p=e+2Tj, j>=0.                                      (6)

Every p is odd, and `2^p=X modulo H`. With `c=psi_A(p)`, equation(5)
therefore gives the integer

    gamma=(chi_A(p)-a*c-X)/H.                            (7)

It is strictly greater than2. Indeed
`E_A(p)=2psi_A(p)-psi_A(p-1)>psi_A(p)` and p>=13, while

    psi_A(3)=4(a+2)^2-1>X+2H.

For the last inequality use X<=a: subtracting `X+8a+6` leaves a
strictly positive quantity. We may take `rho=1`, `sigma=gamma-1`,
so the actual main root `X+a*c+(rho+sigma)H` is `chi_A(p)` with both
supplied coordinates positive. This choice does not assert the input
norm involving rho; that remains a separate constraint.

For j>0 the family has **X<2^p**. It is therefore a low-X family,
despite X itself being a fixed power of2.

## 3. The two Pell units are multiplicatively independent

Write

    Delta_A=A^2-1, Delta_P=P^2-1,
    lambda_A=A+sqrt(Delta_A),
    lambda_P=P+sqrt(Delta_P),
    theta=log(lambda_A)/log(lambda_P).

The two quadratic fields are distinct. Since Y is even, A is even
and Delta_A is odd. On the other hand

    Delta_P=4XY^2(XY^2+1),
    v_2(Delta_P)=e+6d+2,

which is odd because e is odd. Their discriminants thus have different
square classes: the quotient has odd2-adic valuation and cannot be a
rational square. Both discriminants are nonsquares.

It follows that theta is irrational. If theta=r/s were rational with
positive integers r,s, then `lambda_A^s=lambda_P^r` would belong to
the intersection of the two distinct quadratic fields, hence to the
rationals. But its nonzero `psi_A(s)` coefficient of `sqrt(Delta_A)`
makes it irrational, a contradiction.

Equation(2) and monotonicity of `z+sqrt(z^2-1)` also give

    1/2<theta<1.                                        (8)

For the lower bound use
`lambda_A^2=chi_A(2)+sqrt(chi_A(2)^2-1)` and `chi_A(2)>P`.

## 4. Infinitely many exact strict ratios

Set

    beta=log(sqrt(Delta_P)/(2Y*sqrt(Delta_A)))/log(lambda_P),
    h=log((Y+1)/Y)/log(lambda_P),
    t_j=p*theta+beta, n=floor(t_j),

where p follows(6). Here `0<h<1`. The rotation step `2T*theta` is
irrational, so the fractional parts of t_j enter the open interval

    h/3 < fractional_part(t_j) < 2h/3                 (9)

infinitely often.

For completeness, the needed density fact has an elementary proof.
Given an irrational rotation step b and epsilon>0, the pigeonhole
principle applied to sufficiently many fractional parts gives a
positive multiple m with `0<distance(mb,Z)<epsilon`. Successive
nonnegative multiples of this small positive or negative displacement
form a mesh of the circle with gaps below epsilon. Applied after any
chosen starting index, that mesh meets any prescribed open interval
whose length exceeds2epsilon. Thus every tail of the original rotation
meets the interval, proving infinitely many visits. This argument
requires irrationality, not a numerical approximation to theta.

Let `r=(Y+1)/Y` and define the dominant positive ratio

    R0=sqrt(Delta_P)/(2sqrt(Delta_A))
       *lambda_A^p/lambda_P^n.

Condition(9) gives

    Y*r^(1/3)<R0<Y*r^(2/3).                            (10)

The exact Pell ratio is

    c/k=R0*(1-lambda_A^(-2p))/(1-lambda_P^(-2n)),
    c=psi_A(p), k=2psi_P(n).                           (11)

Here is an explicit uniform error margin. Put
`epsilon=1/[12(Y+1)]`, and choose an integer N with
`3^(2N)>12(Y+1)`. Once p,n>=N, both conjugate terms in(11) are less
than epsilon, and the correction factor lies strictly between
`1-epsilon` and `1/(1-epsilon)`.

Also `epsilon<1-r^(-1/3)`. To see this without a logarithmic estimate,
put z=1/(Y+1). The identity

    (1-z/3)^3=1-z+z^2/3-z^3/27>1-z

implies `1-(1-z)^(1/3)>z/3>epsilon`. Multiplying(10) by the bounds
for the correction factor now proves the actual strict inequalities

    Y<c/k<Y+1, hence kY<c<k(Y+1).                     (12)

There are infinitely many visits(9) with arbitrarily large j, so the
finite lower threshold on p,n loses only finitely many of them. Since
`n/p -> theta` and(8) holds, eventually `n<p<2n`, and the odd gap
`g=2n-p` tends to infinity along these visits.

Both ratio slacks are consequently positive:

    eta=c-kY, zeta=k(Y+1)-c.

The source's first-root slack is also positive:

    tau_gap=chi_P(n)-XY^2*k
           =2psi_P(n)-psi_P(n-1)>0.                    (13)

Equations(7),(12),(13) pay the actual first/main norms and positive
outer coordinates, not just formal real asymptotics. Together with(4),
they prove the infinite family claimed above.

## 5. One exact large-index certificate

At d=4 the constants are

    q=16, X=8192, Y=4096,
    A=33558530, P=274877906945, H=134234115.

The checker verifies the modular return `2^8758492=1 modulo H` directly;
it does not need a claim that this is the least period. With j=18361,

    p=13+2*8758492*18361=321629343237,
    n=214421015143,

the exact modular main-root test passes. The two ratio inequalities
are certified at96-bit and128-bit working precisions by directed
integer bounds, independently of how the candidate indices were found.

An endpoint is represented by two nonnegative integers `(m,e)`, meaning
the exact integer `m*2^e`. When a mantissa is shortened, lower endpoints
use integer floor and upper endpoints use integer ceiling. Addition
aligns exponents using the same outward directions; multiplication is
positive and uses endpoint products. Every resulting interval therefore
contains the exact integer result.

Binary Pell multiplication uses only positive operations:

    (x,y)*(u,v)=(xu+Delta*yv, xv+yu).

The checker raises `(A,1)` or `(P,1)` by binary exponentiation with
these intervals. No subtraction of nearly equal large approximations
is needed. Endpoint comparison uses total bit length, then compares
bounded mantissas if necessary; it never expands the huge exponent.

At128-bit precision all six ratio endpoints share exponent
`8362419590425`. Their mantissa intervals are

| Quantity | Lower mantissa | Upper mantissa |
| --- | ---: | ---: |
| kY | 185590106168053748214490852041120270487 | 185590106168053748214490852158065334551 |
| c | 185613373929143806435533469652823430608 | 185613373929143806435533469783409125902 |
| k(Y+1) | 185635416252567433211613530471794372115 | 185635416252567433211613530588767987221 |

The strict inequalities follow just by comparing the displayed
integers: the upper kY endpoint is below the lower c endpoint, and
the upper c endpoint is below the lower k(Y+1) endpoint. These are
rigorous enclosures, not floating-point or unproved error estimates.
The narrower128-bit intervals also lie inside their96-bit counterparts.

This concrete tuple validates only the stated outer equations. The
candidate's retained first-index congruence, input norm/discriminant and
full negative-input CRT class have not been completed. In particular
the target sign restriction from the auxiliary theorem is only noted:
this p is1 modulo4, so any full extension would require target residue-p.

## 6. Literal source connection and limits

The checker retains the frozen source hash and its full strong and input
rows. It symbolically evaluates the actual first, main and transport
sub-DAG after the substitutions above. It obtains exactly

    norm_first=chi_P(n)^2-(P^2-1)psi_P(n)^2=1,
    norm_main=chi_A(p)^2-(A^2-1)psi_A(p)^2=1,
    norm_transport=-1.

No equality of the complete polynomial to zero is asserted. The source
itself and its arithmetic count, degree and domain are unchanged.

Finite verification supplements the all-width proof with21 width cases,
75 exact main-residue/growth cases,2,560 directed integer operation
bounds,640 endpoint-order checks and250 fully materialized small Pell
pairs at five working precisions. These small tests validate the interval
implementation; they do not substitute for the outward-rounding proof.

```sh
python3 complete75_weakened86_infinite_outer_family.py
```

Author receipt generation and a fresh default replay pass. Root and
Native independently read the full proof/source and passed fresh default
replays, with no findings. Root additionally used a separately written,
outward-rounded radix10 2-by-2 matrix exponentiation at72 and96 decimal
digits to certify both strict ratios of the huge tuple, checked35 small
fully materialized Pell pairs, and verified the exact main modular
condition. Native used an independent256-bit integer/rational closed-form
Pell oracle with integer-square-root bounds to certify both huge-tuple
ratios, all six128-bit endpoint enclosures and the exact c bit length
8,362,419,590,553;128 small power fixtures and77 widths d=4 through80
also passed. Both independent oracles differ from the author's Pell-pair
interval recurrence. All four local links resolve.

The result rules out a uniform finite search based only on these outer
equations. It does not rule out a
uniform obstruction using the remaining input and index congruences,
and by itself did not settle soundness. The later all-input theorem
refutes the proposal; the established75/87 bounds remain unchanged.
