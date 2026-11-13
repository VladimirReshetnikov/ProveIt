# A symbolic-beta scalar obstruction with the full Pell interval

This is an ordinary-integer construction, not a Lean theorem or a full
trace74 graph zero. It shows that the strict Pell interval, the weighted
projection, first-index residue, signed rank congruence and signed
rank/main-index `SignMod` relation do not **by themselves** force the
reverse guard, even at the symbolic beta. The `SignMod` construction uses
an exact external gcd computation described below; it is not a Lean proof.
The note does not check all graph factors or the connection to an external
fixed payload.

## Parameters

Put

```text
B=590069, q=2^B, beta=q−1, J=1, h=q−1,
Y=q³, t=2Y=2^s, s=3B+1=1770208,
r=3056651345, n=3054883185, d=r−n=1768160,
X=2^r.
```

The constant `beta` is exactly the symbolic `betaNat=2^(67*8807)−1`.
The other three ports `K0,MC,MF` can be **any** naturals, including the
symbolic ones. The main index is odd, `n<r<2n`, `r≥B`, and

```text
r*d = s*(2n−r).                                           (1)
```

Hence `q|X` and `X^d=t^(2n−r)`. The numerical identities were obtained
from `s=32*55319`, `g=2048`, `d=s−g`, and `r=55319²−2s`.
The companion finite checker verifies these arithmetic identities and the
exponent comparisons without materializing the huge powers or Pell
ordinates.

Define the ordinary Pell ordinate by `y_0(z)=0`, `y_1(z)=1`, and
`y_(i+1)(z)=z*y_i(z)−y_(i−1)(z)`. Let

```text
u=Xt²,  k=2y_n(u+2),  c=y_r(t(X+1)+2).
```

Both **strict** inequalities hold:

```text
kY < c < k(Y+1).                                         (2)
```

Thus the natural values `eta=c−kY` and `zeta=k−eta` are positive and
satisfy both actual scalar identities `k=eta+zeta` and `c=kY+eta`. The
values `X` and `Y` have the displayed graph shapes: choose the relevant
positive witnesses `X/q` and `1`, respectively.

## Proof of the full interval

For `a≥1` and positive `j`, the recurrence yields
`a^(j−1)≤y_j(a+2)≤(a+2)^(j−1)`. Let `e=r−1` and `l=n−1`. By (1),

```text
(tX)^e = t*(Xt²)^l.                                      (3)
```

For the lower bound, `t²>2` and `e>l` give

```text
((X+1)/X)^e > ((Xt²+2)/(Xt²))^l.
```

These are positive rational comparisons, equivalently obtained by clearing
positive integer denominators. Multiplying by (3) yields
`[t(X+1)]^e > t*(Xt²+2)^l`. The Pell bounds then give
`c>t*y_n(Xt²+2)=kY`.

For the upper bound, the finite exponent comparison gives

```text
4eY < X.                                                  (4)
```

In particular `4e≤X`. The binomial estimate
`(1+2/X)^e≤1+4e/X` follows, for example, by bounding the binomial sum by a
geometric series with ratio `2e/X≤1/2`. Since `t>2`, the Pell upper bound
and (3) yield

```text
c < [t(X+2)]^e ≤ (tX)^e*(1+4e/X)
  < (tX)^e*(1+1/Y) ≤ k(Y+1).
```

All inequalities are strict where indicated; no asymptotic approximation
or evaluation of the enormous numbers is used.

## Projection and signed rank

The main index is odd and `X=2^r`, so the checked weighted projection's
product `hX(X−2^r)(2^rX+1)` is exactly zero and is divisible by
`H=4Y(X+1)−1`. Also `u=4XY²` is divisible by `q⁴`; the Pell recurrence
modulo `q⁴` has coefficient 2, so `y_n(u+2)≡n (mod q⁴)` and

```text
k ≡ 2n (mod q⁴).                                         (5)
```

An exact modular computation, reproduced by the independent algorithm
linked below, reports `gcd(c,q²−1)=1`. Also `c` is odd: the main Pell
coefficient is even and `r` is odd, so the recurrence modulo 2 gives
`c≡r≡1`. Hence `c`, `q²−1` and `q⁴` are pairwise coprime.

Let `RJ=MC+q*MF`, `a=2n−1`. By the Chinese remainder theorem, choose a
negative integer `R` satisfying

```text
R ≡ a (mod q⁴),   R ≡ RJ (mod q²−1),   R ≡ r (mod c).
```

Subtracting a sufficiently large multiple of the product of the three
moduli makes `R` as negative as desired. Set

```text
G=(R−RJ)/(q²−1)<0,   F=1,   C=q(q−1)−G>0.
```

Then `G=q(q−F)−C`, `R=(q²−1)G+RJ`, and (5) gives
`q⁴ | k−R−1`. Since `R<0` and `R≡r (mod c)`, its magnitude obeys
`(|R|+r) mod c=0`, the negative alternative of the repository's
`SignMod c |R| r` relation. Also `F+C≥q`, violating the reverse guard.
The carrier input is the same `w=X/q≥1` required by the graph's `X=wq`;
therefore `(K0+w)C−F≥0` for every natural `K0`. By taking `R` sufficiently
negative, the previously checked rank upper bound can also be met.

These are only selected scalar/register consequences. In particular no
other norm/carrier equations, all positive graph witnesses, or graph output
zero is asserted. Those unverified conditions may exclude this family.
The first `E`-square and main Pell norm are separately analyzed in
[`trace74-symbolic-pell-norms`](../trace74-symbolic-pell-norms/README.md).

The [`pell-gcd.c`](pell-gcd.c) program evaluates the main Pell ordinate
modulo `2^(2B)−1=q²−1` by a logarithmic-index doubling algorithm and
computes its gcd with that modulus using GMP. It does not construct the
enormous ordinate. Building with `gcc -O2 -Wall -Wextra -o
/tmp/trace74-pell-gcd-note pell-gcd.c -lgmp` and running
`timeout 60 /tmp/trace74-pell-gcd-note` produced `gcd=1` in actual tool
session 85249, exit 0. An independently implemented companion-matrix
algorithm and its evidence are recorded in
[`trace74-symbolic-pell-gcd-matrix`](../../reviews/trace74-symbolic-pell-gcd-matrix/README.md).
Both calculations are external computations, not formal Lean arithmetic or
an authenticated full-graph check.

Run `python3 -I -S -B research/trace74-symbolic-pell-projection-obstruction/check.py`
from `Computability/DiophantineConsistency`. The checker verifies the
fixed symbolic exponent bookkeeping and tests the Pell interval, positive
`eta,zeta`, both rank congruences and projection on a small analogous instance.
It does not enumerate or kernel-check the stated symbolic instance, nor
does it verify the universal proof or unmentioned graph equations.
