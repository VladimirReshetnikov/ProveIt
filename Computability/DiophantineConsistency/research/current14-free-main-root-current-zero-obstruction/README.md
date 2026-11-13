# A current-port zero after freeing the main root

The literal [61-operation probe](graph.json) is made from the displayed
65-operation graph by replacing the positive input `gamma` by a free positive
input `root`, deleting `ac`, `main_base`, `gammaH`, `main_root`, and using
`root` in the main square. All fourteen inputs and 61 rows are live. An old
positive zero maps forward by taking `root=X+a*c+gamma*H`.

The construction below gives a **symbolically specified positive zero of this
probe at the exact current 2011 ports**. Its original gamma cannot be recovered
while the other coordinates and root are held fixed. This is a proposed
external mathematical proof, using the cited reviewed Pell identities and
elementary bounds; it is not a Lean theorem. Its enormous witness is not
expanded or evaluated by the finite checker. No arbitrary-witness reverse
existence equivalence, old zero, or consistency conclusion follows.

## Finite scalar data

Use the complete current ports `beta,K,MC,MF`, with the `MF` shift already
included once. The checker authenticates their raw and compressed bytes.
Write

```
B=94517, beta=2^B−1, q=beta+1, lo=MC, hi=MF−beta,
J=1, F=q−hi, alpha=lo+hi−beta, C=beta−lo,
G=q*(hi−1)+lo+1, R=(G+1)*q²−1, N=(R−1)/2.
```

As in the [reviewed current-port construction](../current14-carrier64-current-full-zero/README.md),
these are positive old scalar coordinates, `q−F−alpha=C`, the literal gap
is G, and the literal rank is R. The checker confirms `R=3 (mod 4)`,
`popcount(N)=3B+1`, and `R>3B+2`. It also checks `gcd(C,beta)=1` and defines
the unique representative `t` with `0<t<beta` by

```
t = 2^(−R) * (F−K*C) * C^(−1)  (mod beta).
```

The inverses exist because beta is odd and C is coprime to beta. All the
modular work uses `R mod B`, because `2^B=1 (mod beta)`; it does not expand
`2^R`. Define symbolically

```
w=2^R*t,  X=q*w,
z=1+((K+w)*C−F)/beta.
```

The congruence makes z integral and its numerator is positive, since
`w>=2^R>F` and `C>=1`. Thus z is positive and the literal transport factor
is exactly 1. Here `X>=q*2^R>2^R` and `v2(X)>=B+R>3B+2`.

## Pell and auxiliary witnesses

Put

```
Y=(1/2)*sum_{j=0}^N binom(2N,j)*X^(N−j),
s=Y/q³, E=X*Y, m=E*Y, a=E+Y, H=4*a+3, Delta=a²+H.
```

The central binomial coefficient is even. Its half has 2-adic valuation
`popcount(N)−1=3B`, and every other summand is divisible by `X/2`;
therefore Y is integral and `v2(Y)=3B`, so s is positive integral.
The same elementary bounds proved in the
[Pell-floor packet](../current14-carrier64-pell-floor/README.md) apply here:
they use `X>=2^R`, `R=2N+1`, and the binomial-head definition of Y, not the
equality `X=2^R`. In particular `X>144N`, `X^N/2<Y<X^N`, and the tail and
ratio estimates give

```
Y < psi_(a+2)(R)/(2*psi_(2m+1)(N+1)) < Y+1.
```

Here `chi_p(j)+psi_p(j)*sqrt(p²−1)=(p+sqrt(p²−1))^j`. Take

```
k=2*psi_(2m+1)(N+1), tau=chi_(2m+1)(N+1),
c=psi_(a+2)(R), root=chi_(a+2)(R),
eta=c−Y*k, zeta=k−eta, n=(tau−k+R)/E.
```

The displayed ratio makes eta and zeta positive integers. The first Pell
recurrence gives `tau=1` and `k=R+1 (mod E)`, and `tau>k`, so n is a
positive integer. The graph's first and main norm factors are both 1.

For the strong factor write

```
f+L*sqrt(Delta)=(root+c*sqrt(Delta))^c,
i=L/c², S=Delta*L.
```

The binomial expansion gives `c²|L`, and the strong factor is Delta.
Let `(xaux,y)` be the R-th power of `S+sqrt(S²−1)` and put `V=xaux/S`.
Because `R=3 (mod 4)`, the odd Chebyshev congruences in the independently
reviewed [toy completion](../current14-carrier64-toy-full-zero/README.md) give
`V=−c (mod f²)` and `V=−R (mod c)`; also `f²=1 (mod c)`. Therefore

```
T=(R+(V+c)/f²)/c
```

is a positive integer and the auxiliary factor equals 1. Thus the actual
61-row output is `1*1*1*1*Delta−Delta=0` at this tuple. The completion uses
no original gamma equation and no relation `X=2^R`.

## The precise inverse obstruction

The main Pell recurrence gives `root−a*c=2^R (mod H)`. On the constructed
tuple `0<X−2^R<H`, since `X>2^R` and `H=4Y(X+1)+3>X`. Consequently H does
not divide `root−X−a*c`, so **no integer gamma** gives the original main-root
expression while keeping these other coordinates and root. This does not
exclude a different old witness. Since the free-root probe already has a
positive zero at these exact ports, however, the proposition that *every*
probe zero has *some* old zero is logically equivalent to existence of an
old zero: apply such a map to this witness, or conversely use a fixed old
zero as a constant map. The forward logical implication depends on the full
symbolic proof above, not merely the finite receipt.

The [checker](check.py) pins the literal original graph and reviewed proof
sources; reconstructs the exact graph cut; checks all row/input liveness,
whole port hashes, rank, population, modular inversion and transport
residue; and records the compact data in [result.json](result.json). It does
not evaluate Y, the Pell powers, the output on the enormous witness, prove
the inequalities, parse the PDF, or run Lean. Reproduce the finite checks:

```
python3 -I -S -B research/current14-free-main-root-current-zero-obstruction/check.py > /tmp/free-main-root-current.json
cmp /tmp/free-main-root-current.json research/current14-free-main-root-current-zero-obstruction/result.json
```
