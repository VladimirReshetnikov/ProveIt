# A deterministic internal strong Pell seed

Proposed next internal arithmetic pair: `ArithmeticPellSquaredSeed` and
Checks. This addresses a necessary part of the actual polynomial converse.
It does not assume a cofinal seed or an arbitrary-modulus divisibility
witness. All parameters and indices below belong to an arbitrary IΣ1 model.

Let d=xcoord R a, c=ycoord R a and δ=(a+1)(a+3), so d²=1+δc².
For the displayed fourteen-variable equation the strong norm needs
c² dividing a positive Pell ordinate at the same base. The external
construction invokes finite pigeonhole to find such an index. A direct
choice is available instead: **t=R*c**.

From the accepted double-coordinate and addition identities, genuine
Sigma1 induction on n gives natural internal witnesses r,s with

```
xcoord (2*n*R) a = 1+c*c*r
ycoord (2*n*R) a = 2*n*d*c+c*c*s.
```

The zero witnesses are 0,0. For a successor use

```
r' = r+2*δ+2*δ*c*c*r+4*n*δ*d*d+2*δ*s*d*c
s' = 2*d*c*r+s+4*n*δ*d*c+2*δ*c*c*s.
```

Every summand is nonnegative. The induction predicate has two existential
internal witnesses and fixed represented Pell coordinates; it is Sigma1,
without an induction over external naturals or arbitrary predicates.

Add one R-step to obtain, with the same r,s,

```
ycoord ((2*n+1)*R) a =
  (2*n+1)*c+c*c*(c*r+2*n*δ*c+s*d).
```

Now split c by the actual internal remainder modulo 2. If c=2*n,
the even identity is c² times d+s. If c=2*n+1, the odd identity is
c² times 1+c*r+2*n*δ*c+s*d. Therefore

```
∃ i, ycoord (R*c) a = i*c*c.
```

For positive R, the accepted time≤ordinate theorem gives c>0, R*c>0
and ycoord(R*c)>0. Thus i>0; put f=xcoord(R*c)>0. The accepted norm
then proves the actual additive strong norm

```
f*f = 1+δ*(i*c*c)*(i*c*c).
```

The public endpoint must expose t=R*c, f, i and the represented coordinate
bindings, positivity and norm. It must not merely assume the required
divisibility. Include R=0 as a structural divisibility client and require
R>0 precisely for the positive strong seed. The fixed multiplication t=R*c
also provides a concrete bound, without a search theorem or modulus oracle.

The proposed only import is accepted `ArithmeticPellPeriodicity`, which
already supplies all addition/doubling, norm and coordinate-growth laws.
The exact reachable current-source cache must be audited before compiling
the pair, using the accepted arithmetic inventory and package boundary.
No Foundation or prerequisite refresh is proposed. Standard caps, complete
source/Checks/driver reads, both input snapshots before the first command,
fresh regular outputs, all attempts and independent peer replay apply.

The simultaneous outer first/main Pell seed, exact interval/population
construction, auxiliary signed quotient congruences and final polynomial
converse remain separate obligations. This direct seed avoids the generic
internal pigeonhole step for the fourteen-variable strong norm; it does
not claim arbitrary moduli or the extra thirteen-variable carrier scale.
