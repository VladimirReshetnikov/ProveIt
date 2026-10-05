# Gamma83: radical periods and a fixed-cofactor target

This is a bounded continuation note for the **still unresolved
independent-gamma83** source. It proves an aggregate restriction on its
ordinary-input alias period: removing the multiplicities of the prime
factors of the native modulus changes that period by at most a factor of
nine, with an exact formula for the possible change. On the genuine
histories already constructed with `v3(H)=1`, there is no change at all.

A second consequence broadens the earlier conditional target `H=3p` to
`H=3p^f` for any positive exponent, and more generally to a fixed-cofactor
prime-power target. **Occurrence of these factorizations on an actual
history is unproved.** No false-input zero, unconditional small period,
new source, or operation saving is claimed. The order-lifting ingredients
are elementary; the novelty claimed here is only their explicit combined
consequence relative to the pinned gamma83 continuation notes.

## 1. Actual interface and existing limits

Fix a genuine canonical accepting history for an unchanged original
compiler, with its positive84 witnesses and forward independent-gamma83
witnesses. The pinned source and kernel give

```
6 | a,  H=4a+3,  Delta=(a+1)(a+3),  d=5^s with s>=1,
O=ord_H(2),  g=gcd(2Delta,O),  m=g/gcd(g,2d).
```

The native parameter is not free: `X=2^R`, `r=(R-1)/2`,
`2Y=sum_(j=0)^r binom(2r,r+j) X^j`, and `a=Y(X+1)`, with the actual
packing, population, masks, and computation restrictions on R.

At a parent input x0, keeping that outer/main history and the independent
gamma fixed permits exactly the positive inputs

```
x = x0 mod m,    alpha0+2d(x0-x)>0.
```

The two positive input witnesses are then refreshed by the established
Pell/CRT completion. They are not required to remain at their old values.
The new statements below apply to this exact source interface. They do
not substitute arbitrary arithmetic parameters for a native history.

Literal saved-source binding: row16 `R12=UM+sn2` is a; rows19–20 form
`a4m5=4*R12+3=H`; rows24–25 form `A=R12^2+a4m5=Delta`. Rows36–46 are
the retained input norm with `odd_index=2d*x+b`, `index_rhs=odd_index+delta*A`
and `exponent_rhs=W+a*index_rhs+rho*H`. The independent main quotient is
the supplied sigma in row21. The full83 array and all18 positive witness
names were read inertly. No row, numeral or domain is changed here.

The existing filters already bound individual prime-power carriers,
exclude finite prime sets on genuine histories, and show that their
extracted residue conditions alone cannot bound the residual period.
In particular the free CRT hosts in the residual-order note remain
nonnative. The following argument does not undo that limitation.

## 2. Exact reduction to the square-free modulus

Put `rad(H)=product_(ell|H, ell prime) ell` and define

```
O_rad=ord_rad(H)(2),
g_rad=gcd(2Delta,O_rad),
m_rad=g_rad/gcd(g_rad,2d).
```

Then, on every such canonical history,

```
m/m_rad = g/g_rad is one of 1,3,9.                 (1)
```

More exactly, let `e=v3(H)>=1` and

```
tau=max {v3(ord_ell(2)): ell|H prime, ell!=3},
```

where the empty maximum is0. The exact quotient is

| Condition | m/m_rad |
|---|---:|
| e=1 | 1 |
| e=2, tau=0 | 3 |
| e=2, tau>=1 | 1 |
| e>=3 | 3^(2-min(2,tau)) |

Proof. First,

```
16Delta=(H+1)(H+9),   gcd(H,Delta)=gcd(H,9).        (2)
```

Indeed16 is invertible modulo odd H, and the product on the right is9
modulo H. For each prime power `ell^f || H`, reduction gives
`ord_ell(2) | ord_(ell^f)(2)`, and

```
ord_(ell^f)(2) | ord_ell(2)*ell^(f-1).            (3)
```

The latter follows by raising `2^ord_ell(2)=1+ell*z` successively to
the ell-th power. Thus order lifting at ell can add only powers of ell.
The order modulo H is the least common multiple of these prime-power
orders. For every prime p other than3 dividing Delta, (2) gives `p∤H`;
hence its valuation in O is exactly its valuation in O_rad. Lifting at
odd primes also cannot change the2-part. All valuations in g and g_rad
therefore agree outside3.

At3, `ord_(3^e)(2)=2*3^(e-1)`: the binomial induction
`v3(4^n-1)=1+v3(n)` proves this exact order. Lifts at ell!=3 cannot
change their3-parts, so

```
v3(O)=max(e-1,tau),   v3(O_rad)=tau.
```

Because H+1 is a3-adic unit, (2) also gives

```
v3(Delta)=v3(H+9)
 = 1                         if e=1,
 = 2+v3(H/9+1) >=2          if e=2,
 = 2                         if e>=3.
```

Taking the minimum with the two order valuations proves the table and
`g/g_rad in {1,3,9}`. Finally d is a power of5. The quotient just found
is coprime to2d, so cancelling the factors shared with2d preserves this
quotient exactly, proving (1).

The existing finite-prime avoidance and reference-repunit constructions
give genuine accepting histories with `v3(H)=v3(Delta)=1`. For those
histories, `m=m_rad` exactly, even if other prime divisors of H occur
to very high powers. This is an aggregate equality, not a bound on m:
the orders modulo the distinct primes can still have arbitrarily large
shared factors in an arithmetic relaxation. Factoring rad(H) is not
being treated as a free operation in a Diophantine circuit.

## 3. A fixed-cofactor prime-power certificate

Suppose a particular genuine history has a factorization

```
H=C*ell^f,
ell>3 prime, f>=1, C odd, 3|C, gcd(C,ell)=1.       (4)
```

Let T be any certified positive period of2 modulo C, so `2^T=1 mod C`.
It need not be the least period. Set

```
D_C=oddpart(lcm(T,(C+1)(C+9))),
B_C=D_C/gcd(D_C,d).
```

Then the actual ordinary-input period satisfies

```
m | B_C.                                         (5)
```

Proof. CRT and (3) give
`O | lcm(T,ell^(f-1)*(ell-1))`. By (2), ell is coprime to Delta, so
the ell-power lifting factor cannot contribute to gcd(2Delta,O).
For an odd prime p, any shared contribution supplied by ell-1 is bounded
by `v_p(gcd(Delta,ell-1))`. Modulo ell-1, (4) gives H=C and hence

```
16Delta = (C+1)(C+9) mod (ell-1).
```

Since p is odd, this bounds that contribution by
`v_p((C+1)(C+9))`. Contributions supplied by T are bounded by v_p(T).
Thus the odd part of g divides D_C. Since Delta is odd and3|H, g has
exactly one factor2. Cancelling its common part with2d proves (5)
prime by prime. No division by a source coordinate, primality assumption
about C, or zero-set transformation is used.

For C=3, choose T=2. Then D_C=3, and

```
H=3*ell^f  ==>  m|3.                              (6)
```

This does not require f=1. Other simple choices illustrate the fixed
cofactor rather than the size of ell^f controlling the bound:

| C | Available T | D_C | Bound after cancelling d=5^s, s>=1 |
|---:|---:|---:|---:|
| 3 | 2 | 3 | m divides3 |
| 9 | 6 | 45 | m divides9 |
| 15 | 4 | 3 | m divides3 |

For the fixed compiler of the positive even inputs, any actual accepting
history at x0=4 with H=3*ell^f or H=15*ell^f would therefore transfer to
the rejected input1: the difference is3, while the slack increases by6d.
For H=9*ell^f, the analogous fixed downward target is x0=10 to x=1.
The inherited exact fiber theorem supplies the fresh positive delta and
rho and the other sixteen coordinates remain positive. These statements
are conditional on (4) at that actual history; no occurrence is proved.

## 4. Relation to the old power tests and next concrete question

The old sufficient tests use the order modulo the **full H**:
`2^[2^k(H-1)]=1 mod H` implies m=1, and
`2^[2^k(H-3)]=1 mod H` implies m|3. They include H=3p, but prime-power
lifting factors invisible to Delta can prevent both tests without
preventing a small m.

A strictly arithmetic illustration is a=18, H=75=3*5^2, Delta=399.
Here `ord_75(2)=20`, g=2 and m=1 for d=5. For every k>=0, the factor5
of the order divides neither `2^k*74` nor `2^k*72`, so neither old test
ever passes. This is not a native history: in particular its two-adic
valuation is far below the native q>=16 requirement. Its sole role is
to show that the new sufficient factorization class is not logically
subsumed by those two congruence tests on the arithmetic interface.

The useful next target is consequently a **certified small cofactor C
with prime-power complement**, or another method bounding the radical
order intersection on a real canonical history. Requiring H/3 itself
to be prime is unnecessarily restrictive for this route. Conversely,
merely enlarging repeated prime factors of H is not a way to force a
large alias modulus on the e=1 genuine-history subclass.

There is no present mechanism forcing (4) while preserving the actual
half-binomial value of a. Known dummy controls alter R and hence the
entire modulus, and do not establish a prime-power value of H/C. The
new factor criterion is therefore a precise next attack, not a completed
gamma83 language argument. The refuted shared-projection83 family with
W=0 remains excluded from this chart; no such transfer is assumed here.

## 5. Source pins, reading and bounded corroboration

All paths below are relative to
`Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/`.
Their bytes were read inertly; no source or predecessor helper ran.

| File | SHA256 |
|---|---|
| complete83_independent_gamma_scout.json | ed570bc9e96d59e88ec6b6c1302ac177eb6704cfcd85fe39a3346798e89f5e20 |
| complete83_independent_gamma_scout.md | bdbcc3be5396bced89373da5ffb30f0f3f113f7e8e7ebe65e4f7b730264f1b41 |
| complete83_gamma_power_tests.md | 4e8f358a2d651e4cc20946dd3632491d15ad3ee69eb32474a21289e052ec5e4b |
| complete83_gamma_native_finite_prime_avoidance.md | 93aa3b61dcd03f7ce65acca9619f90c29710235ec2438cb4dd14000d8bdb8a96 |
| complete83_gamma_native_repunit_filter.md | 2e6dc2b984cee9c48aab2cbf8b585d7084438b7bd83b1ebf9c0e97b0aa5c42e6 |
| gamma83_residual_order_obstruction.md | 7d2d15ccb608f295a344000f23d147b8f7ce2975e5732f2f6e2adc05363b2754 |
| complete75_gamma87_compiler_order_filters.md | 43d613204d6dc7192763e87e120f84ea0e3f18849a4fd23be26f56ca45b9fcc3 |

The current83 proof, both listed genuine-history filter notes, residual
obstruction and power-test note were read in full. The compiler-order
note's Section5 was read to compare its existing individual prime-power
carrier caps. The complete saved83 row array and its named interface were
read as data. This note uses the inherited native/fiber theorems with
their original proof scope; it does not redo their source audit.

A freshly written, unsaved standard-library arithmetic check tested
a=6,12,...,6006, factoring each small H and computing orders by modular
powers with prime-divisor reduction of the totient. Among these1001
arithmetic hosts, g/g_rad was1 in797 cases,3 in141, and9 in63. It checked
the m ratio for d=5,25,125 (3003 cases) and the cofactor bound using each
maximal non3 prime-power factor of H (4953 cases). The displayed H=75
order and period were also checked. These finite calculations only
corroborate the unrestricted proofs above. They are not native compiler
examples, are not full83 evaluations, and are not a frozen reproducible
evidence packet. No repository or Git object was modified.
