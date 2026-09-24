# Ternary head geometry does not repair the unscaled Pell coordinate

The retained ternary geometry does not restore the power-of-three
conclusion after deleting U=wD0 from the 43-operation kernel. There are
complete positive solutions of the resulting isolated42 kernel with
a nonpower q divisible by3, scale D0=q^9, the exact scalar index-offset
and bound equations, and all the product/head geometry equations.

One example has q=21. A second uses C=2187 and R=6561, and even meets
an explicit choice of the fixed numerical thresholds in the
[91-operation tag interface](EXPLORATION_PRODUCT_COORDINATE_TAG.md).
The larger example is certified by only360 binomial-valuation checks,
not by summing an astronomical polynomial.

This does **not** give a tag-history counterexample. No values for its
eight/nine computation fields, actual packed polynomial, or its two
transport equations are asserted. It answers the narrower question of
whether the retained3-adic geometry and scalar index interface alone
repair this kernel deletion. The earlier
[isolated42 obstruction](EXPLORATION_UNSCALED_PELL_COORDINATE.md) is unchanged.

The [checker](../verification/explore_geometry_compatible_unscaled_pell.py)
and [receipt](../verification/explore_geometry_compatible_unscaled_pell.json)
contain all exact integers and valuation lists. They use integer
arithmetic and SymPy; the large native helper from the earlier artifact
is not run.

Author and two independent complete proof/source/dependency reviews and
fresh verification PASS, with no findings. An independent digit-carry
calculation also confirms all371 large coefficient valuations without
using the checker's factorial-valuation implementation.

## 1. A finite shifted-binomial certificate

For r>=1 define the canonical integer polynomial

    Y_r(U)=sum_{j=0}^r binom(2r,r+j) U^j.

It has the exact alternative form

    Y_r(U)=sum_{j=0}^r binom(2r-j-1,r-1)(U+1)^j.    (1)

To prove this, write

    Y_r(U)=[t^r](1+t)^(2r)/(1-Ut).

Put W=U+1. The denominator is 1+t-Wt, so its expansion as a formal
power series gives

    1/(1+t-Wt)=sum_{j>=0} W^j t^j/(1+t)^(j+1).

Taking the coefficient of t^r yields
binom(2r-j-1,r-j)=binom(2r-j-1,r-1), proving (1).
Only finitely many terms contribute; no analytic convergence or
p-adic limit is assumed.

Suppose a prime p divides U+1. To prove p^b|Y_r(U), it is sufficient
to check

    vp(binom(2r-j-1,r-1))+j>=b,
                       0<=j<min(b,r+1).            (2)

Every displayed low term then vanishes modulo p^b; every remaining
term has j>=b and vanishes because p|(U+1). The valuations in (2)
are exact consequences of Legendre's formula

    vp(n!)=sum_{i>=1} floor(n/p^i).

The number of divisions is logarithmic in n. In particular, (2) can
be checked for an enormous r without constructing its binomial
coefficients or the integer Y.

In our cases U=3^J, J=2r+1, and J=3 modulo6. Since3^3=-1 modulo7,
we have7|(U+1) and can apply (2) at p=7. Separately, if
v3(binom(2r,r))<J, every nonconstant term in the original Y_r(U)
is divisible by3^J, so

    v3(Y_r(U))=v3(binom(2r,r)).                     (3)

## 2. Full positive kernel completion

The omitted-coordinate source is the exact42-operation system in the
linked predecessor, with24 multiplications,18 additions/subtractions,
sixteen positive auxiliary coordinates and ten equations. The present
checker freshly verifies both fixed-sign schedules and all twenty source
comparisons, including their retained norm correction.

For each example below, r is even, U=3^(2r+1), and D0 divides Y_r(U).
All its retained preliminary inequalities hold:

    D0>=81, r>=27, r<2D0, D0<r^2,
    U>D0, U>48r.                                  (4)

Set Y=Y_r(U) and s=Y/D0. This is a positive integer. Sections2--4
of the earlier obstruction give the explicit remaining canonical
coordinates: main Pell indices2r+1 and r+1, the positive ratio gaps
eta,zeta, the positive integral quotients h,gamma, and the auxiliary
Pell index m=2c(2r+1). Its norm and congruence construction supplies
the final positive f,i,j,o,y coordinates. The sign is plus because r
is even. The proof there checks each of those positivity and integrality
dependencies; only the removed w=U/D0 needs divisibility of U by D0.

Here every D0 has a positive factor7, while U is a power of3. Thus
D0 does not divide U. Nevertheless all sixteen remaining auxiliary
coordinates exist and satisfy all ten fixed-plus42 equations. The
large U,Y and Pell coordinates are specified by exact formulas and
proved to exist, rather than materialized.

## 3. The exact geometry and scalar interface

Both examples satisfy all six equations

    kD=R,
    RH=H+q-1,
    RH=CZ,
    Rv=q,
    2r+1=q^9+2P,
    r+betaP=q^9,                                   (5)

with k=3 and strictly positive integer C,D,R,H,Z,v,q,r,P,betaP.
The fixed C and R are powers of3, C divides R, and

    A=R/C, Z=AH.

The checker also proves the six source identities symbolically under
the definitions

    R=CA, D=R/k, q=Rv, H=(q-1)/(R-1), Z=AH,
    P=r-(q^9-1)/2, betaP=q^9-r.

Those formal identities alone do not prove integrality. Every example
separately checks the required divisions and strict positivity.

### 3.1. A small radix q=21

Take

    C=R=k=3, D=A=1, v=7, q=21, H=Z=10,
    D0=21^9=794280046581,
    r=68891*7^8-1=397142905690,
    P=2882400, betaP=397137140891.

All equations (5) hold exactly, r is even, and (4) holds. Its odd
main index is3 modulo6. Formula (3) and the exact factorial valuations
give v3(Y)=11, which exceeds the required9. For the nine low shifted
coefficients in (1), the7-adic valuations are

    13,13,13,13,13,12,12,13,13.

They satisfy (2) with b=9. Hence both3^9 and7^9 divide Y, so
D0=21^9 divides Y. This supplies the full positive42 solution as well
as all of (5), even though q is not a power of3.

### 3.2. Geometry with C=2187

Take

    C=3^7=2187, R=3^8=6561, A=3, k=3, D=2187,
    v=7^40, q=3^8*7^40,
    H=(q-1)/6560, Z=3H,
    D0=q^9=3^72*7^360.

The exact congruence7^40=1 modulo6560 proves H is an integer and
all head geometry in (5) holds. Define

    cstar=78849398407287110441440517561704247,
    r=cstar*7^359-1,
    P=r-(D0-1)/2, betaP=D0-r.

The checker proves that r is even and strictly between(D0-1)/2 and
D0, so P,betaP are positive and the last two equations in (5) hold.
It also checks every inequality in (4) without materializing3^(2r+1).
The radix has125 binary bits and the index1124 binary bits.

The exact3-adic central-binomial valuation is385, exceeding the
required72 and smaller than J. The checker lists all360 valuations
in (2) for p=7,b=360. Their minimum is381, and the minimum of
valuation+j-360 is24. Thus (1) proves7^360|Y, and (3) proves3^72|Y.
These relatively prime factors give D0|Y and the complete positive
kernel extension.

This C also satisfies the fixed numerical thresholds of the91 source
at beta=2,a=2,Uappend=3,Li=9:

    C>max(K^3,3K*3^a,2K Uappend+3,K^2 Li), K=9.

This checks compatibility of the constants and the admitted initial
length bound only. It supplies no actual field or transport witness,
and is not asserted to be a normalized Neary instance.

## 4. Fresh evidence and scope

The checker uses24 symbolic polynomial cases to cross-check (1),2298
exact integer-binomial valuation comparisons, and1152 finite truncation
cases, including189 admitted divisibility certificates, to validate the
sufficient implication (2).
It does not claim that failure of (2) proves nondivisibility.

Both large certificates use only their exact factorial valuations,
modular powers, and integer geometry. The two kernel schedules and
six symbolic geometry/index equations are freshly checked. In particular
the earlier q=7 long modular computation is not repeated or assumed.
The general formal-series proof of (1) establishes the identity at the
large indices; finite examples supplement that proof.

The examples show that3|q, C|R, the head repunit equation, Rv=q,
the prescribed ninth-power scale and the exact positive scalar index
interface do not recover the omitted U divisibility or force q to be
a power of3. They do not assign the tag fields whose packing would
have to equal P, and they do not satisfy or refute the tag transports.
Thus they are a complete obstruction for this smaller interface,
not a false solution of the full91 tag system or of a proposed full90
source obtained by deleting its kernel multiplication.
