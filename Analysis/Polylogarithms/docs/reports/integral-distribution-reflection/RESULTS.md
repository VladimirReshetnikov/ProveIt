# Result and proof map

All labels refer to `article/integral_distribution.tex`. This report concerns the **complete raw prime-distribution presentation**, not the full algebra of polylogarithm identities.

| Result | Stable label | Evidence type |
|---|---|---|
| Fixed original-symbol basis over `Z[A_p]`, all-ring base change | `thm:unimodular` | Written unit-minor and integral-descent proof; exact certificates |
| Division-free recurrence, multidegree and coefficient bounds | `prop:bounds` | Induction on the explicit well-founded point order |
| Weighted Anderson resolution, arbitrary-ring exactness | `thm:resolution` | Finite filtration and split local complexes |
| Reflection Tate cohomology equals binary Koszul homology by parity | `thm:koszul` | Explicit acyclic subcomplex; no assumed spectral-sequence collapse |
| Complete integer-weight reflection Smith factors | `thm:scalar-torsion` | Koszul reduction and fixed-point trace |
| Universal cohomology before specialization | `cor:universal-tate` | Regular binary parameter sequence |
| Complete one-variable finite-jet torsion formula | `thm:jets` | Principal-ideal-ring Koszul reduction |
| All-complex-order polylogarithm normal forms | `thm:all-order` | Root filtering and meromorphic continuation |
| Pole-cancelled derivatives at order one | `thm:finitepart` | Laurent multiplication with explicit endpoint term |

## Scalar reflection formula

Let `q>2`, and put

```
r* = number of odd prime divisors of q + (1 if 4 divides q, else 0).
```

For either reflection coinvariant quotient, the underlying abelian group is

```
Z^(phi(q)/2) + (Z/2)^h,
```

where `h=0` if any odd-prime weight is even, and `h=2^(r*-1)` otherwise. A lone factor of two in the level does not increase `r*`. At `q=2`, the plus quotient is `Z` and the minus quotient is `Z/2`.

## Finite integral jets

Take `B_L=Z[u]/(u^L)`, arbitrary integer polynomial weights `a_p(u)`, and work modulo two. Form the parameters `1-a_p` at odd primes and, when `4|q`, `a_2(1-a_2)`. Let `v` be the smallest truncated `u`-valuation, with the zero polynomial assigned valuation `L`.

For `q>2`, either reflected quotient has underlying abelian group

```
Z^(L*phi(q)/2) + (Z/2)^(v*2^(r*-1)).
```

Its integer-torsion submodule over the jet ring is a direct sum of `2^(r*-1)` copies of `B_L/(2,u^v)`. The free abelian part need not be jet-free. This is illustrated explicitly at `q=3, L=2, a_3=1+u`.

## Analytic identities

The level-12 identity is

```
Li_s(exp(i*pi/6)) + Li_s(exp(5*i*pi/6))
 + (1+3^(1-s))*Li_s(-i)
 = (12^(1-s)-6^(1-s))*zeta(s).
```

It is a meromorphic identity, with the right side interpreted by its removable limit at `s=1`. At `s=1` that limit is `-log(2)`. Its first derivative has endpoint value

```
(log(12)^2-log(6)^2)/2 - EulerGamma*log(2).
```

The article includes every higher derivative and an analogous level-30 identity. The short polynomial row combinations are in `data/short_identity_certificates.json`; they use three and five raw distribution rows, respectively.

## Checks actually completed

| Check | Count |
|---|---:|
| Polynomial levels, 2 through 120 | 119 |
| Raw polynomial rows | 3,317 |
| Point normal forms | 7,259 |
| Independent certificate files | 7 |
| Point identities in independent replay | 414 |
| Raw rows in independent replay | 366 |
| Scalar parity assignments | 2,348 |
| Binary raw rows in scalar sweep | 488,954 |
| Finite binary-jet cases | 1,635 |
| Reflected raw integer Smith matrices | 136 |
| Unreflected raw integer Smith matrices | 68 |
| Resolution cases over F2, F3, F5 | 498 |
| Short displayed-identity raw-row certificates | 2 |
| Exact cyclotomic product polynomial divisions | 2 |
| Mutated certificates rejected | 3 |
| Floating-point diagnostics, not certified enclosures | 20 |

There is no inference from the finite ranges to the general theorems: the article supplies the uniform proofs separately. The verifier certifies polynomial identities relative to the stated distribution laws. No proof-assistant verification, period independence, or proof of `S_6` is claimed.
