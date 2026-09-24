# A seventeen-operation positive raw-input exponent bridge

The complete [marked67 source](EXPLORATION_THREE_CELL_MARKED_67.md)
already supplies a very large indexed Pell solution. Reusing it adds
the exact relation

    W=P^(x+c0)

in **17 additional operations:7M+10A**, including construction of
`t=x+c0` and strengthening the existing low-field bound. Here `x` is
a positive raw input and `c0>=2` is any fixed numeral; the primary
specialization is `c0=3`. All five new Pell witnesses are strictly
positive. The combined counted schedule is **84=45M+39A**, with21
equations, but requires an external positive endpoint interface to
prove `W<q`. That interface and any uniqueness or initialization
conditions are not supplied or priced by this note. In particular84
is not a complete universal raw-input certificate.

The [checker](../verification/explore_raw_input_exponent_bridge.py)
and [receipt](../verification/explore_raw_input_exponent_bridge.json)
state all source equations and primitive operations. Fixed numerals
and equality comparisons have no cost.

## 1. Retained facts and the strengthened bound

Write the retained kernel's parameter and discriminant as

    A0=a+2, Delta=A0^2-1=a^2+4a+3.

The register named `A` in the executable source is `Delta`, not `A0`.
After the established marked67 soundness argument one has

    q=B^N, P=B^h, B>=16, 1<=h<=N,
    q^2<=r<q^4, J0=2r+1,
    U=2^J0, a=Yp(U+1),
    cmain=psi_A0(J0), dmain=chi_A0(J0),
    a>J0, Yp>0.                                       (1)

Here `psi,chi` are the second and first Pell sequences. They start
with `(chi(0),psi(0))=(1,0)` and `(chi(1),psi(1))=(A0,1)`.

Construct `t=x+c0`, and replace the previous equation `C+alpha=q` by

    C+t+alpha=q.                                      (2)

This preserves all previous pre-power bounds, because it implies
`0<C<q`; it additionally gives `0<t<q`. The unchanged retained kernel
therefore still establishes (1), before the new exponent argument.
The external endpoint interface must independently give

    0<W<q.                                           (3)

No power interpretation of W is used to obtain this preliminary bound.

## 2. Four equations and exact index recovery

Supply five new positive coordinates `kappa,mu,delta,phi,rho` and impose

    kappa=t+delta*(a+1),
    cmain=kappa+phi,
    mu^2=1+Delta*kappa^2,
    mu=W+kappa*(A0-P)+rho*(Delta-(A0-P)^2).             (4)

All positive solutions of the norm equation in (4) are indexed by a
positive integer u:

    kappa=psi_A0(u), mu=chi_A0(u).

For completeness, this usual Pell classification also follows by
descent: multiply `mu+kappa*sqrt(Delta)` by `A0-sqrt(Delta)`.
Its second coordinate becomes `A0*kappa-mu`, an integer in
`[0,kappa)`, and its first coordinate stays positive. Repetition ends
at `(1,0)`. Reversing the steps gives a power of the fundamental unit.
The gap equation and strict growth of psi give `0<u<J0`.

Reducing the Pell recurrence modulo `A0-1=a+1` gives

    psi_A0(u)=u mod(A0-1).

The first equation in (4) consequently gives `u=t mod(A0-1)`.
But (1)--(2) give

    0<u<J0<A0-1, 0<t<q<J0.

Hence this congruence is an equality: `u=t=x+c0`. There is no
unbounded-index ambiguity and no assumption that the raw input had
already been interpreted as a tableau length.

## 3. Recovering the power by a bounded congruence

Put

    v=A0-P, H=Delta-v^2=2*A0*P-P^2-1.                 (5)

The Pell polynomial identity

    chi_A0(t)-v*psi_A0(t)=P^t mod H                   (6)

is elementary. In the integer polynomial ring modulo H, substitute
`sqrt(Delta)=v`; then `A0-sqrt(Delta)` becomes P. Equivalently, apply
the recurrence for the two Pell coordinates and the identity
`2*A0*P=P^2+1 mod H`. This reasoning uses no division modulo H.

The last equation in (4) and (6) give `W=P^t mod H`. The necessary
strict bounds follow from the existing kernel, not from this
congruence. Since `P<=q`, `t<q`, and `q<=2^q`,

    P^t<q^q<=2^(q^2)<=2^r<U<A0.                      (7)

Also `A0>U>q^2+1>=P^2+1`, so `H>A0>0`. Thus both `P^t` and W lie
strictly between zero and H, by (3) and (7). Their congruence proves

    W=P^t=P^(x+c0).                                  (8)

The endpoint bound is essential to this argument. It is not omitted
from the interface merely because the modulus is extraordinarily large.

## 4. Positive completeness

Take a genuine marked cyclic solution of the retained predicate and
an endpoint satisfying `W=P^t<q`, where `t=x+c0` and `x>0`. The existing
typed cells are even and less than B, so

    C<=(B-2)J, J=(q-1)/(B-1), q-C>=J+1.

Writing `q=B^N,P=B^h`, strict `P^t<q` gives `N-1>=ht>=t`. Therefore
`J>=B^(N-1)>=B^t>t`, and

    alpha=q-C-t>0.                                  (9)

Thus strengthening the old bound needs no additional padding beyond
having an endpoint strictly inside the encoded word. The other old
positive coordinates and the actual packed index are unchanged.

Choose fresh

    kappa=psi_A0(t), mu=chi_A0(t),
    delta=(kappa-t)/(A0-1), phi=cmain-kappa,
    rho=(mu-(A0-P)*kappa-W)/H.                        (10)

The congruences above show that delta and rho are integral. Because
`t>=3`, the strict growth `psi_A0(t)>t` makes delta positive. Also
`t<q<J0` makes phi positive. The identity

    mu-(A0-P)*kappa=P*kappa-psi_A0(t-1)
                          >(P-1)*kappa

and `kappa>=psi_A0(2)=2*A0>W` show that rho is strictly positive.
All five new coordinates therefore satisfy (4) over positive integers.
In particular the smallest raw input `x=1` has no zero-quotient exception.

## 5. Exact seventeen-operation adapter

The retained source already computes `Pm1=P-1`, `bounded=C+alpha`,
and the discriminant register `A=Delta`. The identity

    A0-P=(a+1)-(P-1)

saves one addition compared with separately constructing `a+2`.
Append the following primitive instructions to the unchanged67 prefix:

| Register | Operation |
|---|---|
| t | x+c0 |
| raw_bound | bounded+t |
| ap1 | a+1 |
| index_product | delta*ap1 |
| index_rhs | t+index_product |
| pell_gap | kappa+phi |
| kappa2 | kappa*kappa |
| scaled_kappa2 | A*kappa2 |
| norm_rhs | scaled_kappa2+1 |
| mu2 | mu*mu |
| exponent_difference | ap1-Pm1 |
| difference2 | exponent_difference*exponent_difference |
| exponent_modulus | A-difference2 |
| modulus_multiple | rho*exponent_modulus |
| difference_multiple | kappa*exponent_difference |
| exponent_partial | W+difference_multiple |
| exponent_rhs | exponent_partial+modulus_multiple |

Replace the old bound comparison by `raw_bound=q`; retain all other
comparisons. Add `kappa=index_rhs`, `cmain=pell_gap`, `mu2=norm_rhs`,
and `mu=exponent_rhs`. These are four new equations, not five: the
strengthened bound replaces an existing equation.

The adapter is7M+10A. The combined source is84=45M+39A with21 equations.
It has the original27 positive unknowns, the five new positive Pell
unknowns, and the positive endpoint coordinate W:33 positive
existential coordinates in a later integration, besides raw input x.
Fixed c0 and all compiler constants are numerals. The endpoint's own
additional variables, equations and operations are outside this count.

## 6. Evidence and limits

The checker expands the complete84-operation schedule and verifies
every source residual, including the inherited auxiliary correction.
It also tests exact positive bridge witnesses over a finite grid of
bases, exponents and offsets, checks the Pell congruences separately,
and verifies the strengthened slack estimate on typed words.

These finite bridge witnesses use deliberately moderate Pell parameters
satisfying the explicit bridge inequalities. They are not materialized
full packed-kernel witnesses at astronomical indices. The proof above
derives the needed inequalities from the actual retained kernel.
No claim below17 operations, or complete raw-input improvement, is
made by this standalone adapter.
