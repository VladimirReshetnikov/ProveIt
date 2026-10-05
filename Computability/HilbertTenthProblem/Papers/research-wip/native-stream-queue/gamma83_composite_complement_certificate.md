# Gamma83: a composite-complement certificate and a native obstruction

This bounded continuation gives a new **conditional sufficient criterion** for a small ordinary-input period, then rules out its simplest two-prime specialization on the existing filtered histories. It does not construct a modulus, factorization, rejected-input zero or new circuit. The independent-gamma83 source remains unresolved.

The criterion allows a composite base in `H=3u^f`: an appropriate radical order dividing `u²−1` implies `m|3`. In particular it covers certain two-prime complements with a certified relation between their factors. For the simplest such relation `u=p(2p−1)`, the filtered native residue at31 forbids the squarefree case `f=1`; only four residue classes of f survive. This is a narrowed failed route and a remaining conditional target, not a prime-value conjecture presented as a construction.

## 1. Fixed native interface and exact domain

Start with a genuine canonical accepting history of an unchanged original compiler, its positive84 witnesses, and the established forward independent-gamma83 chart. The inherited source/kernel and exact input-fiber theorem give

```
6|a,  H=4a+3,  Delta=(a+1)(a+3),  d=5^s, s>=1,
O=ord_H(2),  g=gcd(2Delta,O),  m=g/gcd(g,2d).
```

The native values remain

```
R=2r+1, X=2^R,
G_r(T)=sum_(j=0)^r binom(2r,r+j)T^j,
2Y=G_r(X), a=Y(X+1), H=H_r(X)=2(X+1)G_r(X)+3.
```

No independently chosen H is substituted for this value. The present sufficient theorem assumes that **this actual H** has a representation

```
H=3u^f,   u>1 odd, 3∤u, f>=1.                         (1)
```

Consequently `v3(H)=v3(Delta)=1`, the latter from
`16Delta=(H+1)(H+9)`. By the pinned radical-order theorem, `m=m_rad` for this history. These conclusions follow from (1) and do not require the finite-prime filtering construction. The further mod31 obstruction in Section3 applies only to that explicitly filtered subclass. In particular **f need not be assumed odd in the sufficient theorem**.

## 2. A quadratic radical-period certificate

Write `rad(u)` for the product of its distinct prime factors, put

```
L=ord_rad(u)(2), Lodd=oddpart(L).
```

**Theorem 1.** Under the native domain and (1), if

```
Lodd | u²−1,                                           (2)
```

then `m|3`.

Proof. Here `rad(H)=3 rad(u)`, so its order is `lcm(2,L)`. Consider an odd prime ell>3 dividing both Delta and this radical order. It divides Lodd and hence `u²−1`. In the field modulo ell, `u=1` or `u=−1`; therefore `H=3u^f` is 3 or −3 for **every** positive f. But

```
(H+1)(H+9) = 48 or −12 mod ell.
```

Neither value is zero at ell>3, contradicting ell|Delta. Thus the radical order/discriminant intersection has no odd prime divisor except3. Prime-power lifting from `rad(H)` to H cannot introduce any other common prime: the previous radical theorem gives equality of the input periods when `v3(H)=1`. Its3-part is at most3 because `v3(Delta)=1`. Finally m is odd: Delta is odd, O is even because3|H, and the denominator removes the single factor2 in g. Hence `m|3`.

This proof does not replace an order modulo the full H by an order modulo u without justification. Its two essential bridges are the **radical equality** at `v3(H)=1` and the actual source formula for Delta. It also does not infer (2) from polynomial irreducibility or from a finite list of successful residues.

Condition (2) allows powers of two in L that are absent from `u²−1`; they do not affect m. A stronger sufficient certificate is `L|u²−1`, which the next factorization provides. Primality and order verification are mathematical hypotheses or external finite tests here, not unpaid gates in a new Diophantine program.

**Corollary 2.** Let p and P be primes greater than3 satisfying, for an integer k>=2,

```
P=k(p−1)+1,     k|(p+1).                              (3)
```

If an actual native H is `3(pP)^f` for some f>=1, then `m|3`.

Indeed put `u=pP`. Modulo p−1, both p and P are1, so `p−1|u²−1`. Modulo P−1, `u=p`, and

```
P−1=k(p−1) | (p−1)(p+1)=p²−1.
```

Thus `P−1|u²−1` also. Fermat gives
`ord_rad(u)(2)=lcm(ord_p(2),ord_P(2)) | lcm(p−1,P−1) | u²−1`.
The primes are distinct because k>=2, and neither is3, so all hypotheses of Theorem1 hold. This admits a composite complement with two distinct primes, beyond merely renaming a prime-power complement. No occurrence of (3) inside the actual half-binomial value is proved.

As in the old exact fiber theorem, for the fixed compiler recognizing the positive even inputs, a genuine history at input4 satisfying Theorem1 would transfer to input1. The ordinary-input difference is3 and the refreshed width slack is `alpha_new=alpha_old+6d>0`; the established positive Pell/CRT completion refreshes delta and rho. This implication concerns the same full source and fixed compiler. It remains conditional on (1)–(2) at that genuine history; the finite-prime theorem does not supply them.

## 3. Native obstruction to the simplest two-prime shape

Now restrict to the actual accepting histories supplied by the pinned finite-prime avoidance theorem. The native-next note proves for these histories

```
H/3 = 22 mod31,        ord_31(22)=30.                  (4)
```

The origin of (4) is the actual canonical `E|R`, with5|E, hence `2^R=1 mod31`, together with a forced carry in `binom(2r,r)` at31. The exact tail symmetry gives `a=1/4` and `H=4 mod31`. It is not a congruence imposed on a free modulus, nor a condition asserted for every unfiltered canonical history.

For any representation (1) on this subclass, `u^f=22 mod31`. The power-order identity forces both `ord_31(u)=30` and `gcd(f,30)=1`. Consider k=2 in (3), so

```
u=p(2p−1),   1+8u=(4p−1)².                           (5)
```

At f=1, (4) makes `1+8u=22 mod31`. But22 is not a square modulo31. Hence **no filtered history has `H=3p(2p−1)`**, even with p allowed to be any integer. This excludes its prime-pair subcase without a prime-value assumption.

For arbitrary f the complete field calculation is:

| f modulo30 | Forced u modulo31 | Possible p modulo31 |
|---:|---:|---|
|1|22|none|
|7|13|none|
|11|17|none|
|13|21|19,28|
|17|3|17,30|
|19|11|none|
|23|12|23,24|
|29|24|21,26|

The forced u is `22^(f^{-1} mod30)`. For each row, (5) is a necessary and sufficient condition for a p residue, since4 is invertible modulo31. Other f classes cannot produce the order30 element22 at all. Thus the k=2 target on this subclass requires

```
f=13,17,23 or29 mod30; in particular f>=13.             (6)
```

The first native two-adic restriction adds a separate necessary condition. Write q=2^t. The native-next theorem gives, because f is now odd,
`v2(u−1)=3t+2`. By (5)'s factorization

```
u−1=(p−1)(2p+1),
```

and p is odd, so

```
v2(p−1)=3t+2,
p=1+4q³ mod8q³.                                      (7)
```

The surviving residues in the table and (7) are compatible by elementary CRT. Such residue compatibility is only local arithmetic: it neither makes p and2p−1 prime nor solves the exact native equation `H_r(2^R)=3[p(2p−1)]^f` with valid compiler words. No inference to a real history is drawn from it. The obstruction also does not rule out the squarefree pair on unfiltered histories, where (4) is unavailable, or all other k in (3).

## 4. Outcome and evidence boundary

The new finite sufficient certificate is (2), with the concrete composite class (3). The most immediate k=2,f=1 realization fails on the histories whose existing filter supplies the clean native residue (4). Its remaining exponent classes require at least a thirteenth power of the two-prime complement. The prior reciprocal-Eisenstein theorem forbids a formal polynomial-power identity for fixed r, but does not rule out these numerical perfect-power values. Neither an existence theorem nor an all-history obstruction follows.

This leaves an explicit arithmetic task: realize (2), or a factorization in (3), at one genuine accepting native H with the appropriate input. Requiring that realization is essential. No invocation of unproved prime-value conjectures, no arbitrary coprime choice of H, no shared-projection W=0 family and no generic scalar example fills this gap. There is no new universal83 claim or paid-operation saving.

The fresh standard-library helper checks three full integer-polynomial identities and the complete finite field table:900 power-map cases and930 `(f,p)` cases modulo31, with eight surviving pairs. It authenticates the following dependencies as inert bytes; it never runs or imports them. The actual83 JSON is hash-bound only, not reinterpreted as an arithmetic circuit in this packet. This helper evaluates no native half-binomial integer, Pell tuple or full83 output. These finite checks certify the table and identities; Theorem1 is the unrestricted proof above.

One earlier exploratory route was discarded rather than generalized from a constant term: `G_r(-1)=binom(2r,r)/2` does not imply `v_p(a)=v_p(X+1)+v_p(binom(2r,r))` at every prime dividing X+1. Fresh formula-only arithmetic at R=11 gives `v3(X+1)=1`, `v3(binom(10,5))=2`, but `a=37092131025501763710=18 mod81` has valuation2, not3. Higher Taylor terms can dominate or cancel. This small index is not a compiler history; that diagnostic is not part of the promoted receipt and supplies no source zero. No further prime-power claim is made from that route.

| Dependency (native-stream-queue/) | SHA-256 |
|---|---|
| gamma83_native_next.md | `6cf4719fab43ad8873e372a5be0108192cc0a90cadccd84fe58d1e7a76cdaf74` |
| gamma83_next_arithmetic.md | `4298f6f64d4c9e1037901df3e0d50095ee126b9e31a82106db60643365d64f93` |
| complete83_gamma_native_finite_prime_avoidance.md | `93aa3b61dcd03f7ce65acca9619f90c29710235ec2438cb4dd14000d8bdb8a96` |
| complete83_gamma_power_tests.md | `4e8f358a2d651e4cc20946dd3632491d15ad3ee69eb32474a21289e052ec5e4b` |
| complete83_independent_gamma_scout.json | `ed570bc9e96d59e88ec6b6c1302ac177eb6704cfcd85fe39a3346798e89f5e20` |

The native-next, radical-order and finite-prime notes were read in full; the power-test note's exact fiber and sufficient-test interfaces were read. Other current small-prime, repunit, scaling and ternary notes were consulted as comparison context. Their unread or previously reviewed proof portions are not certified anew. The exploratory calculations used only fresh arithmetic; no supplied, frozen, archived, committed or copied predecessor code ran. No repository or Git object was changed.

Fresh normal and `python -O` exact receipt replays from `/` both passed before freeze. Helper SHA-256: `25765478acf569fbed20b1fe7e1a963c3966c06422e6d439d7c45fd4ebbd4f6f`. Receipt SHA-256: `bdc4470099162ec32fd13e3e1e5205bcae9813a14ff2013efe8c21e70b9093c7`. The packet's helper/receipt supply bounded evidence only; none of the unresolved occurrence statements is promoted by a successful replay.
