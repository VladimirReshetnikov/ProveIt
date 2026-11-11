# Independent check: compact44 signed-fold symbolic zero

**PASS, external symbolic mathematics.** This review independently checks the
frozen author construction in
`../../research/ordinary13-folded-root86-negated-compact44-seed/`. It
specifies a positive zero of the signed-fold 86/26 candidate at the four
P72/P115 compact44 byte integers, with `Bt<0`. The candidate JSON names the first-root input `r`; the
construction assigns its positive value `sigma`. The enormous binomial/Pell
witness is not expanded. This review does not prove a zero or nonzero of the
parent at a different q,R, unrestricted zero-existence nonequivalence, a new
Lean/iPRA theorem, a PDF interpretation, or closed source/object ancestry.

## Independent checks

The checker authenticates all raw little-endian and gzip payloads against
both independent bindings, pins the signed graph and author receipt, and
reconstructs the scalar CRT in a different order: it first combines the
mod-B and mod-4 residues and then imposes the beta residue. It obtains the
same specific alpha and R hashes, congruences and exact N popcount. In
particular alpha>beta and `R mod B=0`, hence `C=beta−alpha<0`, `X=2^R` has
`X≡1 (mod beta)`, and the indicated congruence makes b=beta divide negative
Bt. It checks `R>=2B` without constructing `2^R`.

The general floor calculation in the pinned reviewed Pell-floor packet
applies to the **prescribed** binomial Y without assuming a zero. For
`R=2N+1`, `N>=13`, `X=2^R`, and this Y, its leading two terms give
`Y>X^N/2`; the elementary recurrence estimates then give
`H<c/k<H+1/4`, where `H=(X+1)^(2N)/(2X^N)`. Its binomial expansion has
`Y<H<Y+1/4`. Consequently `Y<c/k<Y+1/2<Y+1` and
`eta=c−Yk`, `zeta=k−eta` are positive. The noncentral binomial terms are
multiples of `2^(R−1)`, while the half-central term has valuation
`popcount(N)−1<R−1`; hence v2(Y)=popcount(N)−1>=3B and q³ divides Y.

For the first Pell unit with `P=2XY²+1`, P≡1 modulo E=XY. The standard
recurrence gives `psi_P(N+1)≡N+1 (mod E)` and therefore
`k≡R+1 (mod E)`. Since R>=2B, `U=Yq²` divides E; the new gamma adjustment
is integral. Its first component `gamma0` is at least `2^(R−2)` by the
trace identity, while w=`2^(R−B)` and B>=3; hence gamma>0. The first Pell
norm gives `tau<ell+k`, so `sigma=ell+k+s−t−tau>0` when t<0. The exact
graph expressions then reduce to `Z=M*tau` and `Dstar=U*D0`.

For the ordinary auxiliary completion, the main index is **R in both**
`c=psi_(a+2)(R)` and the auxiliary exponent. Taking the c-th main-unit power
gives c²|L0 and `S0²=Delta*(f²−1)`. As R≡3 mod4, the reviewed Chebyshev
identity yields `V≡−psi_(a+2)(R)=−c (mod f²)`; since c|S0, its constant
coefficient yields `V≡−R (mod c)`, and `f²≡1 (mod c)`. Thus the stated T
is a positive integer; the main-unit and auxiliary Pell equations establish
both remaining residuals and y>V makes u positive. This is not the rejected
mismatched-index construction.

## Separate same-q,R parent obstruction

With J=1 the rank fixes `G=beta²+alpha`. Any positive parent scalar
representation at this same q,R has

```
alpha' = G−beta*(q−F'),
C' = q−F'−alpha' = q*(q−F')−G <= beta−alpha < 0,
```

because F'>=1. Positive X', K0 and F' then give `Bt'<0`, whereas every
positive parent zero forces Bt>0 from its first residual. Thus no positive
parent zero has the same q,R, even allowing all other coordinates to change.
This is not a claim about parent zeros at different q,R.

The checker also verifies the algebra and finite small Pell/Chebyshev
controls; these are checks of the derivation, not the unbounded proof itself.
