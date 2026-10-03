# Positive input bridge and converse for the half-binomial kernel

This note audits the unchanged **14-operation ordinary-input bridge** and
the fresh strictly positive converse for the half-binomial kernel.
It does not prove the modified universal compiler. The literal complete
source has **75=41M+34A**, thirty positive witnesses, and nineteen equations;
its outer mask and compiler obligations are separate. The complete composition is now independently reviewed in
[the universal75 theorem](../../1980/FIXED_RAW_UNIVERSAL_75_PROOF.md).

The source aliases are `r=R`, `k=K`, `tau=T`. In particular, the new main
Pell index is the supplied packed `R`; it is not `2R+1`. Let

    A=a+2, Delta=A^2-1, H=4a+3,
    X=w*q^3, Y=s*q^3, E=XY, V=XY^2, P=2V+1.

The [literal source](complete75_half_binomial.py) changes the old first norm
to `(E^2+X)(KY)^2=T^2-1`, uses `K=R+1+hE`, and uses
`U=jc-R` in the strong auxiliary block. The first norm is exactly
`T^2-V(V+1)K^2=1`. Its positive fundamental solution is `(2V+1,2)`,
so its canonical coefficient is twice a Pell psi value. This factor two
does not change the input bridge.

## 1. Precise bridge hypotheses and soundness

Assume the outer equations have given

    q>=16, 0<W<C<q, C+alpha+2d*x=q,
    x,d,b positive, b odd, b<q,
    3q+1<=R<q^4.

Assume the independently proved new kernel conclusions

    X=2^R, a>X, a>q^6,
    c=psi_A(R), dmain=chi_A(R).

The fixed compiler has odd `b,d` and `b<q`; only odd `b` is needed here.
For `u=2d*x+b`, the four unchanged input equations are

    kappa=u+delta*Delta,       c=kappa+phi,
    mu^2=1+Delta*kappa^2,
    mu=W+a*kappa+rho*H.                                  (1)

All five supplied input witnesses `kappa,mu,delta,phi,rho` are strictly
positive. The raw bound gives

    3<=u<q+b<2q<R<A-1.                                   (2)

The positive norm and gap give an index `0<v<R` with
`kappa=psi_A(v)` and `mu=chi_A(v)`. Modulo `Delta`, the exact psi
representatives are `v` for odd `v`, and `vA` for even `v`. Both are
between zero and `Delta`: `v<R<A-1` implies `vA<A(A-1)<Delta`.
Thus `kappa=u mod Delta` is equality of representatives. Even `v` would
give `u=vA>=2A`, contrary to (2). Hence `v=u`, which is odd.

The standard integer-polynomial congruence is

    chi_A(u)-a*psi_A(u) = 2^u modulo H.                   (3)

It follows by evaluating `sqrt(Delta)` at `-a` modulo `H`, since
`Delta=a^2+H` and `A-a=2`. Equation (1) therefore gives `W=2^u mod H`.
Both representatives are smaller than `H`: `W<q<a`, and
`2^u<2^R=X<a`. Consequently

    W=2^(2d*x+b).

With the actual compiler numerals `B=2^d` and inner radix `2^b`, this
is exactly the original marker `W=2^b B^(2x)`, with ordinary input `x`.
There is no parity restriction on `x` and no radix conversion.

## 2. Every input witness in the converse is positive

Suppose the outer construction has supplied the displayed bounds and the
correct marker, and the new main kernel is constructed at the actual `R`.
Set

    kappa=psi_A(u), mu=chi_A(u),
    delta=(kappa-u)/Delta, phi=c-kappa,
    rho=(mu-a*kappa-2^u)/H.                              (4)

Odd `u` makes `delta` integral by the same discriminant congruence, and
`u>=3` makes it positive: `psi_A(3)=4A^2-1>3`, and strict recurrence
growth preserves `psi_A(u)>u`. Equation (2) makes `phi>0`.
Congruence (3) makes `rho` integral. Finally, for every positive index

    chi_A(u)-a*psi_A(u)
      =2*psi_A(u)-psi_A(u-1)>psi_A(u).

Since `u>=3` and `W<q<A`, this is greater than `W`, so `rho>0`.
Thus all four equations have a fresh positive solution. No witness is
borrowed from a different packed index or a previous compiler word.

## 3. Fresh positive half-binomial kernel extension

Here are the complete converse data, with their exact prerequisites.
Suppose

    q=2^t>=16, 3q+1<=R<q^4, R=3 modulo4,
    popcount((R-1)/2)>=3t+1.

Write `r0=(R-1)/2` (a mathematical abbreviation, not a paid register),
`n=r0+1`, and set

    X=2^R,
    Fbin=sum_(j=r0)^(2r0) binom(2r0,j) X^(j-r0),
    Y=Fbin/2, w=X/q^3, s=Y/q^3,
    a=Y(X+1), A=a+2, Delta=A^2-1, H=4a+3,
    E=XY, V=XY^2, P=2V+1,
    c=psi_A(R), dmain=chi_A(R),
    K=2*psi_P(n), T=chi_P(n),
    eta=c-KY, zeta=K-eta,
    h=(K-R-1)/E,
    gamma=(dmain-X-ac)/H.                               (5)

The exact binomial expansion gives an even positive `Fbin`, and

    v2(Y)=popcount(r0)-1.

Indeed `Fbin=binom(2r0,r0) mod X`, whose valuation is
`popcount(r0)<R`, and every other summand is divisible by `X`.
The assumptions therefore make `s` positive integral. They also make
`w` positive integral, since `R>=3q+1>3t`.

For clarity, the strict interval needed in (5) survives halving. Put
`xi=(X+1)^(2r0)/X^r0` and `k=K/2`. The same elementary Pell estimates
as in the [base-two ratio proof](../../1980/BASE_TWO_PELL_89_PROOF.md)
give, at these new values of `Y`,

    xi<c/k<xi(1+8r0/a).

Their hypotheses hold: `X,Y>=q^3`, `6V>a`, and
`4r0/a<2/q^2<1/2`. The binomial tail satisfies
`0<xi-Fbin<1/4`, so `xi/2=Y+epsilon` with `0<epsilon<1/8`.
Also `xi<2Y+1/4<4Y`; therefore

    0<c/K-xi/2<16r0/(X+1)<1/2.

It follows that `Y<c/K<Y+1`, proving `eta,zeta>0`.
The first norm is exact by `P^2-1=4V(V+1)`.
Since `P=1 mod E`, `psi_P(n)=n mod E`; hence `h` is integral.
As `n>=2`, `psi_P(n)>n`, making `h>0`. Congruence (3), now at
index `R`, makes `gamma` integral. Its numerator is positive because
`dmain-ac>c>X`.

For the strong auxiliary equations choose afresh

    m=2cR, f=chi_A(m), Aaux=Delta*psi_A(m), i=Aaux/c^2,
    yaux=psi_Aaux(R), U=chi_Aaux(R)/Aaux,
    j=(U+R)/c, o=(U+c)/f.                                (6)

All these quantities are positive integers. To see `c^2 | psi_A(m)`
directly, expand `(dmain+c*sqrt(Delta))^(2c)` and inspect the coefficient
of `sqrt(Delta)`: its linear term contains `2c*c`, and every higher odd
term contains `c^3`. This also proves the required divisibility for `i`.
Both auxiliary norms follow from the Pell identities.

Because `R` is odd, `chi_Z(R)/Z` is the integer polynomial
`Q_((R-1)/2)(Z^2)`. It has the exact identities

    Q_((R-1)/2)(0)=(-1)^((R-1)/2)*R,
    Q_((R-1)/2)(1-A^2)=(-1)^((R-1)/2)*psi_A(R).

Now `c | Aaux`, and `Aaux^2=Delta(f^2-1)=1-A^2 mod f`.
Since `R=3 mod4`, these give `U=-R mod c` and `U=-c mod f`.
Thus `j,o` are positive integral and `U=jc-R=of-c`, with exactly
the required fixed-minus signs. In particular no factor two is lost in
the auxiliary index, and the correct parity is `R=3 mod4`.

These formulas account for all sixteen internal kernel witnesses,
in addition to the supplied packed `R`. Together with (4), they supply
all five input witnesses. The remaining nine coordinates are the eight
other outer coordinates plus the shared `R`, for thirty in total.

## 4. Source and evidence scope

The adjacent checker independently matches all fourteen input instructions
to the old and new full sources, checks the four exact residuals, and
records the complete75 ledger without promoting its compiler theorem.
Its exact Pell prototypes test the main interval, first norm, input
quotients, signed auxiliary divisibilities and norms. The numerical
input-interface fixtures use the recovered main norm and bounds, without
claiming their `Y` has the compiler's scale divisibility. The small full
auxiliary fixtures are outside the full compiler domain. The universal
converse at the actual scale is the argument above, not finite testing.

Independent full proof/source/default review passes (receipt replay
`b5d2a8`), with no findings. This reviews the stated bridge and positive
converse scope; the complete compiler theorem is reviewed separately.
