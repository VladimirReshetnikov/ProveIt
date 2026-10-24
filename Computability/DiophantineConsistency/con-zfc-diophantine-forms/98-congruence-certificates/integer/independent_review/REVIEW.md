# Independent review of the CRT and valuation family

## Verdict and assurance boundary

The new reductions in `PROOF.md` and `FAMILY.md` are sound and complete
relative to the retained, normalized source system Cal and its canonical
completeness witnesses. I found no gap in the use of the coprime carrier,
3-adic radical separation, the retained-root unit products, or the
restoration of the omitted integer witnesses. In particular, the
argument does not assume positivity or integrality before it has proved
them. The unrestricted integer domain is respected throughout.

This review covers the new algebra and number-theoretic composition. It
does not independently reprove the inherited source34/native/K215/ZFC
calibration, the inherited normalized-source completeness construction,
or the cited generalized-pentagonal representation theorem. The
consistency equivalence retains precisely those dependencies. This is
an ordinary mathematical review, not a newly compiled proof-assistant
certificate or a proof of consistency.

The final literal circuits independently pass topology, liveness and
binary-operation checks:

| Integer variables | Exact degree reviewed | Live operations |
|---:|---:|---:|
| 13 | 1072 | 195 |
| 14 | 414 | 148 |
| 15 | 218 | 130 |
| 16 | 124 | 118 |

The companion `check.py` also proves the rank-two, rank-three and
rank-four cleared-norm identities by exact sparse Laurent-polynomial
arithmetic. Its oracle recursively substitutes `x+sqrt(d)` and
`x-sqrt(d)` and multiplies the conjugates; it does not reuse the author's
norm identity. It matches all 6, 35 and 495 collected terms respectively,
checks polynomial denominator clearance, and verifies the precise
radicand-free monomial used in the modulo-four argument. All checks pass
both normally and with `python3 -O`. The finite checks are separate from
the unbounded semantic proof reviewed below.

## 1. The retained-root finalizer is valid before radical interpretation

For every assignment of unrestricted integers, the definitions force
q even, W divisible by four, X divisible by eight and a even. Consequently
Delta is three modulo four, Dtau is one modulo four, and S is one modulo
four. Thus

```
Ff = f^2 + I^2 (mod 4),
Fg = g^2       (mod 4),
Ft = tau^2     (mod 4).
```

The first factor belongs to residues 0, 1, 2 and the other two to
residues 0, 1. None can be minus one. This calculation does not presume
that f is a Pell root.

M=2q^2 and U=MH are divisible by eight. Every weighted integral radicand
and the numerator Cn of the rational radicand is divisible by 64.
In the cleared rank-r norm, every monomial other than
`delta^(2^(r-1))*p^(2^r)` contains one of these radicand numerators.
For r=2,3,4 the exponents on delta and p are even, so the norm is zero
or one modulo four, without any restriction on delta's parity.
Therefore `1+Nr` cannot equal minus one.

An integer product equal to one has each factor in {1,-1}. Excluding
minus one for every factor gives Nr=0 and exactly the intended retained
root equalities. This works before any division by delta and before
interpreting any square root. It also avoids treating a sign-unrestricted
factor as nonnegative.

## 2. The denominator never vanishes, even on unguarded assignments

The authentic coefficient is beta=2^1064921-1, which is odd and one
modulo three. Thus q is two modulo three. W is one modulo three, so X
is two modulo three and a=(X+1)Y is zero modulo three. Hence H and
Delta are multiples of three, while H=4a+3 is never zero.

Both definitions of Q, including the retained form
`Q=Delta*(f^2-1)`, give Q=0 modulo three unconditionally. Therefore
delta=Q-1 is minus one modulo three and cannot vanish; Cy=QV^2-1 is
also minus one. The raw Pell radicands and S are one modulo three.
No guard, retained-root equality or Archimedean sign is used here.

Let e=v_3(H)>=1. M is a 3-adic unit. The five-root construction has
the distinct even valuations

```
main: 0, auxiliary: 2e, strong: 2e+2,
first Pell: 2e+4, guard: 2e+6.
```

The retained constructions have

```
main: 0, auxiliary: 2e, first Pell: 2e+2, guard: 2e+4,
```

omitting the coordinates already retained. The change of weights is
consistent in the formulas and literal builder.

## 3. The valuation argument recovers signed roots without positivity

If a signed sum of square roots of the weighted nonzero rational
radicands is rational, group the summands by rational square class.
Distinct square classes are linearly independent over the rationals.
Within one class, write the roots as rational coefficients times one
fixed root. The coefficients' 3-adic valuations are half the distinct
radicand-valuation differences, up to a common shift. Hence the least
valuation is unique and their signed sum cannot vanish. Every
nontrivial square class is excluded.

This proves that each radicand is a rational square, including when
the original assignment would otherwise have produced negative raw
radicands or complex square roots. The positive weights are rational
squares, so the corresponding unweighted roots are rational too.
The roots of integral radicands are integers; only the auxiliary root
requires the later descent. A vanishing norm supplies the requisite
signed sum because delta has already been proved nonzero.

## 4. Guard recovery licenses the auxiliary descent

The equality S=g^2 (whether recovered or retained) gives

```
24N-21 = (6p2-1)^2 + (6p3-1)^2 + g^2 >= 0,
```

so N>0. From `N=GZ-(t^2-G-Z+1)^2>0`, the product GZ is positive.
G and Z cannot both be negative: writing G=-a, Z=-b with positive
integers a,b makes the subtracted square at least `(a+b+1)^2>ab`.
Thus G>0 and Z>0. Conversely the nearest-square construction works:
for positive integers G,Z, put s=G+Z-1>=1, choose the integer square
nearest to s, and its squared error is strictly less than s<=GZ.

If c=0, then eta=-Yk and zeta=(Y+1)k, so
`Z=-Y(Y+1)k^2<=0` for every integer Y. This contradicts Z>0.

Unconditionally Delta>=3: if v=0, a=0 and Delta=3; otherwise
|q|>=16, |W|>=4, |X|>=64, |Y|>=16, and |a|>=1008, which make
`Delta=(a+2)^2-1>1`. Since c and 2r+1 are nonzero, the recovered
strong equality gives `Q=Delta^2*I^2>=9`.

For completeness, the stated adjacent-coefficient descent is valid.
Write a rational solution y=b/d in lowest terms of
`QV^2-(Q-1)y^2=1`. Then d^2 divides Q-1. After signs are made
positive, V>1 implies

```
V < y < sqrt(Q/(Q-1))*V
  < (2Q-1)/(2(Q-1))*V.
```

Consequently `V'=(2Q-1)V-2(Q-1)y` is an integer strictly between
zero and V. The companion transformation of y preserves the norm
and its reduced denominator: `2Q-1` is coprime to d because
Q=1 modulo d. Descent ends at V=1, where y=1. Thus d=1.
This is applied only after Q>1 has been established.

## 5. The two carrier congruences restore the exact source witnesses

Since H=3 modulo q, q is prime to three, and H is odd,
`gcd(H,2q^2)=1`. Every signed-root relation has the main term Md
and all other terms divisible by U=MH. Reducing modulo M yields

```
v=q^2(2*v_old+1),
v_old=(v-q^2)/(2q^2) in Z.
```

This is the required odd q^3 scale for Y=qv, not merely a weaker
divisibility condition. It also excludes v=0 without a separate guard.
Reducing modulo H gives `gamma=(d-b0)/H` integral.

The strong-source restoration `I_old=Delta*I` has the required form
`(2*r_old+1)c^2`, because Delta is odd. The quotient
`j_aux=(V+R)/c` is integral: `f^2=1 modulo c` and
`V=f^2(cT-R)-c`. The other auxiliary quotient
`o=f(cT-R)` is visibly integral. These formulas restore exactly the
source strong and auxiliary equations, without an unlicensed positive
sign assumption.

In reverse, the chosen n is integral because the canonical source
witness already has both carrier congruences. For the retained family,

```
n=gamma+y-V-(v-q^2)/M
  +3*tau if the first root is not retained
  +9*g   if the guard root is not retained.
```

Substituting gives `p=Md+Uy` plus precisely the omitted weighted
roots. The signs and coefficients in this formula are correct. The
five-root version likewise uses `+9*tau+3*f+27*g`. Thus a norm
factor vanishes and the retained unit factors equal one.

## 6. Exact degrees and selected coefficients

I recomputed the leading-degree arguments and the displayed selected
coefficients. For thirteen variables, the carrier and auxiliary root
have degree 25. Sixteen branches cancel their degree-25 terms and
then have the uniquely dominant degree-20 guard term. The other
sixteen retain degree 25; denominator clearance contributes 352.
The total is 1072. The stated nonzero homogeneous part and selected
coefficient `2^1000*3^696*beta^480` follow.

For fourteen variables, the degree-20 guard root uniquely dominates
all other roots and the center, giving norm degree 400 and final
degree 414. Selecting h^32 in k0^32 gives the displayed coefficient
`-2^402*3^302*beta^196`.

For fifteen variables, the degree-17 first Pell root uniquely
dominates, giving norm degree 176 and final degree 218. Selecting
h^12 in k0^12 gives `-2^209*3^151*beta^104`.

For sixteen variables, write p=UV+s. The exact cancellation

```
delta*(p^2-A)-Cn
  = delta*(s^2+2UVs-A)-U^2*(V^2-1)
```

has degree at most 30. The degree-60 norm part is exactly

```
4*Q0^2*U0^2*V0^2*(s0^2-A0)
  = 2^13*q0^8*a0^8*f^8*R0^2*n*(2n+c).
```

It is nonzero. Multiplying the three retained factors gives degree
124. Selecting h^6, z^2 and n^2 uniquely gives the monomial and
coefficient `2^113*3^77*beta^58` stated in `FAMILY.md`.
All these coefficients remain nonzero after specializing to the
authentic positive beta. No assertion of exact degree relies only
on a generic-parameter computation or on one finite evaluation.

## Reproduction

From this component's directory:

```
python3 independent_review/check.py
python3 -O independent_review/check.py
```

The independent receipts pin the reviewed literal equation files and
builder. The author's separate `verify.py` supplies the full-tuple
coefficient regeneration, retained-source byte checks, rank-five
finite norm diagnostics, and exact univariate degree witnesses.
Those checks complement the mathematical review; neither finite
suite substitutes for the inherited semantic calibration.
