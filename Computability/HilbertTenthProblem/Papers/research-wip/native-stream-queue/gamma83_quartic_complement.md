# Gamma83: a quartic period certificate and a native first-lift screen

This bounded continuation strengthens the complementary-order criterion for the unresolved independent-gamma83 source. It gives a factorization-free quartic power test, a strictly weaker complementary-order hypothesis than the previous quadratic one, and an exact first-lift restriction on a new two-prime target. It does **not** establish that any of these sufficient tests succeeds at a genuine compiler history. No new source, paid-operation bound, false-input zero or universality claim is made.

## 1. Fixed native domain

Keep an actual canonical accepting history and its existing positive84 and independent-gamma83 witnesses. The inherited native/input-fiber theorems give

```
6 | a, H=4a+3, Delta=(a+1)(a+3), d=5^s (s>=1),
O=ord_H(2), g=gcd(2Delta,O), m=g/gcd(g,2d).
```

In particular Delta and m are odd, 5 divides d, and

```
16Delta=(H+1)(H+9).
```

The existing finite-prime history construction supplies genuine histories at each accepted input with `v3(H)=v3(Delta)=1`. Unless stated otherwise, the new tests are restricted to this subclass. That construction does not supply the new tests themselves.

The exact native formula remains

```
R=2r+1, X=2^R, C=binom(2r,r),
G_r(T)=sum_(j=0)^r binom(2r,r+j)T^j,
2Y=G_r(X), a=Y(X+1), H=2(X+1)G_r(X)+3.
```

The previously proved reciprocal-Eisenstein argument makes `H_r(T^k)=2(T^k+1)G_r(T^k)+3` irreducible over the rationals for each fixed r and positive k. Accordingly, the numerical factor targets below are not supplied by a nonconstant polynomial factorization of this native expression. Dividing by the constant3 does not evade that limitation.

## 2. A new factorization-free sufficient test

**Lemma 1.** On the domain of Section1 with `v3(Delta)=1`,

```
oddpart(gcd(2Delta,H^4-81)) | 15.                 (1)
```

Proof. Let an odd prime power `ell^j` divide both Delta and `H^4-81`. For `ell!=3`, the two factors H+1 and H+9 cannot both be divisible by ell, since their difference is8. Thus all of `ell^j` divides one of them. Reducing the fourth power gives

```
ell^j | 80                  if H=-1 mod ell^j,
ell^j | 9^4-81=6480=81*80   if H=-9 mod ell^j.
```

Away from3 the only possible odd factor is therefore5, with exponent at most1. At3 the assumed valuation of Delta is1. This proves (1), including its prime-power strength.

**Theorem 2.** For any nonnegative e, a genuine history on this subclass satisfying

```
2^[2^e*(H^4-81)] = 1 mod H                       (2)
```

has `m|3`.

Indeed O divides the displayed exponent. Hence every odd valuation in g is bounded by (1). Its possible single factor5 is removed by the actual `5|d`; its single factor2 is removed by2d. Only one factor3 can remain. This is an external finite arithmetic certificate, not an unpaid modular exponentiation inside a Diophantine circuit.

The old `H-3` repeated-squaring test implies (2), because `H-3` divides `H^4-81`. The converse need not hold, even when both old `H-1` and `H-3` tests fail for every number of squarings. Section4 gives an exact arithmetic comparison. This proof does not assume a factorization of H or require the order O to be computed.

## 3. The weaker quartic complementary-order certificate

Suppose the **actual** H has a representation

```
H=3u^f, u>1 odd, 3 does not divide u, f>=1.
```

This alone gives `v3(H)=v3(Delta)=1`. Put

```
L=ord_rad(u)(2), Lodd=oddpart(L).
```

**Theorem 3.** If

```
Lodd | u^4-1,                                    (3)
```

then `m|3`.

The radical-order theorem says that replacing H by rad(H) leaves m exactly unchanged when `v3(H)=1`. The order modulo rad(H) is `lcm(2,L)`. By (3), its odd part divides `u^(4f)-1`, and hence divides `H^4-81=81(u^(4f)-1)`. Applying the prime-power argument of Lemma1 to the radical order gives m|3. No order-lifting factor is silently discarded: that is precisely the use of the inherited radical equality.

Condition (3) is weaker than the old condition `Lodd|u^2-1`; Section4 shows strictness. It need not imply the full-H test (2), because prime-power order lifts at primes dividing u can prevent (2) while being irrelevant to m.

A practical sufficient factor pattern is the following.

**Corollary 4.** Let p and P be primes greater than3 and

```
P=k(p-1)+1, k>=2, k | (p+1)(p^2+1).
```

If an actual H equals `3(pP)^f`, then m|3.

Write u=pP. Both factors are1 modulo p-1, so p-1 divides u^4-1. Modulo P-1, P is1 and u is p. The stated divisibility gives

```
P-1=k(p-1) | (p-1)(p+1)(p^2+1)=p^4-1.
```

Fermat's theorem therefore gives `L|lcm(p-1,P-1)|u^4-1`. This proves the claim. Primality and the numerical factorization are hypotheses, not newly free circuit operations or proved native occurrences.

## 4. Strictness and a different exponent-one target

There is an exact strictness example at the arithmetic interface:

```
p=13, P=61=5(p-1)+1, u=793,
H=2379, a=594, Delta=355215, d=5,
ord_13(2)=12, ord_61(2)=60, Lodd=15,
ord_H(2)=60, g=30, m=3.
```

The order claims have short exact certificates: at13, `2^6=-1` and `2^4=3`; at61, `2^30=-1`, `2^20=47` and `2^12=9`. Fermat's theorem and these prime-index tests give orders12 and60, and CRT gives order60 modulo `3*13*61`. Here 6 divides a, the3-adic hypotheses hold, and 15 divides `u^4-1` but not `u^2-1` (the latter is3 modulo15). Neither old full-H repeated-squaring test can pass:5 divides O but divides neither H-1 nor H-3. Yet60 divides `H^4-81`, so (2) already passes with e=0. These small values are **not native compiler coordinates**. They prove strict inclusion of the sufficient arithmetic criteria, not existence on any compiler slice.

The useful new exponent-one target is

```
u=p(10p-9), P=10p-9 prime,
p prime>3, p=2 or3 mod5.                          (4)
```

Since p is odd,2 divides p+1; and p^2=-1 modulo5, so10 divides `(p+1)(p^2+1)`. Corollary4 applies. In particular this pattern need not inherit the old quadratic divisibility at5: u is p modulo5, so5 does not divide u^2-1. Whether5 divides the actual radical order still depends on P; no generic exact-order assumption is made here.

On the existing filtered histories, the native-next note proves `H/3=22 mod31` and, if H=3u^f, `gcd(f,30)=1`. The older pattern `u=p(2p-1)` forced `f=13,17,23,29 mod30`. That exponent restriction belongs to that older pattern. It is not a restriction on every composite complement.

For (4) with f=1,

```
(20p-9)^2=81+40u.
```

At u=22 modulo31 the right side is `81+880=961=31^2`, so the condition is exactly

```
p=2 mod31.                                       (5)
```

There is no mod31 obstruction to f=1 for this new pattern. For the actual native q=2^t the population theorem gives `v2(u-1)=3t+2`. But

```
u-1=(p-1)(10p+1),
```

and the second factor is odd. Thus its exact dyadic requirement is

```
p=1+2^(3t+2) mod 2^(3t+3).                       (6)
```

For every t, (5), (6), either allowed residue modulo5 in (4), and for example p=1 modulo3 are consistent by CRT. This is only compatibility of these particular necessary residue conditions. It proves neither simultaneous primality of p,P nor compatibility with every other native restriction, and certainly not the equation `H_r(2^R)=3p(10p-9)` for a real accepting history.

**Retained preliminary correction.** An initial message proposed the k=4 pair `p(4p-3)` as a strict extension. Although it is covered by Corollary4, its odd predecessor-order bound already divides p-1, and hence u^2-1. It therefore does not witness strictness of the old odd-order criterion. The k=5 numerical example and the k=10 target above replace that comparison; no frozen predecessor statement has been altered.

## 5. An exact first-lift obstruction at the actual half-binomial

Compatibility modulo31 does not settle even the next modulus. The new target has a double discriminant root modulo31. This produces a check involving the **actual central binomial coefficient and actual index**, not an independently chosen modulus.

**Lemma 5.** If R=2r+1 is divisible by5 and `31|C=binom(2r,r)`, the native H obeys

```
H = 4 + (3/2)(2^R-1) + 2C mod31^2.              (7)
```

All denominators in this section are units modulo31^2. To prove (7), symmetry and a telescoping first moment give

```
G_r(1)=(2^(2r)+C)/2,
G'_r(1)=r*C/2.
```

For the second identity use

```
j*binom(2r,r+j)
 =r*[binom(2r-1,r+j-1)-binom(2r-1,r+j)]
```

and sum j=1,...,r; the result is `r*binom(2r-1,r)=r*C/2`. Put X=2^R and delta=X-1, which is divisible by31 because5 divides R. Integer-polynomial Taylor expansion gives

```
H=4G_r(1)+3+delta*[2G_r(1)+4G'_r(1)] mod31^2.
```

Substitute `G_r(1)=X/4+C/2`, and discard products of two multiples of31, to obtain (7). The use of 2^(2r)=X/2 is exact, with r fixed throughout that Taylor expansion.

**Corollary 6.** On these actual native indices, the exponent-one target `H=3p(10p-9)` necessarily satisfies

```
13 - 2*(R/5) + 18*(C/31) = 0 mod31.              (8)
```

Indeed (5) makes31 divide20p-9, so31^2 divides

```
3(20p-9)^2=243+40H.
```

Equation(7) reduces its right side to `403+60delta+80C`. Since `2^R=(1+31)^(R/5)`, delta/31 is R/5 modulo31. Dividing the congruence by31 gives (8). Conversely, for this native H, (8) is exactly the condition `31^2|243+40H`; it is not a converse to the square or prime-factor equation.

In particular, if31^2 divides C, then (8) forces `R/5=22 mod31`. Failure of that residue rules out the exponent-one k=10 shape. The existing filter forces only31|C, not this stronger carry depth or the new resonance. No simultaneous control of (8), its negation, primality or the whole factorization is claimed. This separates a concrete next native obstruction from a merely formal absence of the old f>=13 restriction.

## 6. Scope, dependencies and bounded corroboration

The new conclusions are (1)–(3), Corollary4, the exact f=1 necessary conditions (5)–(6), and the all-size native first-lift identity (7)–(8). They change the remaining arithmetic search but leave independent-gamma83 unresolved. On any actual even-input compiler history at ordinary input4 passing either sufficient test, the inherited exact input-fiber theorem would still produce an input1 alias with increased positive slack and fresh positive input witnesses. That conditional transfer is inherited, not a newly constructed zero.

Paths in this table are relative to `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/`.

| Dependency | SHA256 | Reading |
|---|---|---|
| gamma83_composite_complement_certificate.md | 70d5311c481545f0dc1655dff54040b7badc3802a6e621d284c39c5751a8c255 | Full |
| gamma83_native_next.md | 6cf4719fab43ad8873e372a5be0108192cc0a90cadccd84fe58d1e7a76cdaf74 | Full |
| gamma83_next_arithmetic.md | 4298f6f64d4c9e1037901df3e0d50095ee126b9e31a82106db60643365d64f93 | Full |
| complete83_gamma_native_finite_prime_avoidance.md | 93aa3b61dcd03f7ce65acca9619f90c29710235ec2438cb4dd14000d8bdb8a96 | Full |
| complete83_gamma_power_tests.md | 4e8f358a2d651e4cc20946dd3632491d15ad3ee69eb32474a21289e052ec5e4b | Theorems/input-fiber interface; prior full reading inherited |
| complete83_independent_gamma_scout.md | bdbcc3be5396bced89373da5ffb30f0f3f113f7e8e7ebe65e4f7b730264f1b41 | Full |
| complete83_independent_gamma_scout.json | ed570bc9e96d59e88ec6b6c1302ac177eb6704cfcd85fe39a3346798e89f5e20 | Hash only in this continuation |
| complete83_gamma_small_prime_digit_rules.md | b7248efe5f292bd5dcbf093ccd9f664d663b2eb23c022974b1a9f64b537a4f8e | Full |
| complete83_gamma_native_repunit_filter.md | 2e6dc2b984cee9c48aab2cbf8b585d7084438b7bd83b1ebf9c0e97b0aa5c42e6 | Full |

The small-prime digit-rule and reference-repunit filter notes were also reread in full as comparison context. Their explicit arbitrary-prefix and finite-filter limitations are respected; no full source-array audit is repeated here.

Fresh unsaved standard-library arithmetic independently verified the exact strictness example and its order60. It checked (7) and (8) at all72 formula indices `15<=R<2000`, `R=15 mod20`, having31 divide C. These are full finite modular-binomial calculations, not claimed native compiler histories. The formulas, theorems and arbitrary-index proofs above do not follow by extrapolating those checks. Additional small prime-pair searches were exploratory and are not promoted as evidence of native occurrence.

No supplied, archived, committed, frozen or copied predecessor code ran or was imported. No repository or Git object was changed. This is a proof-only continuation, without a new circuit, compiler, helper/receipt packet or changed operation claim.
