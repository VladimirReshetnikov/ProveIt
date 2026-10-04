# Independent review of the gamma83 power and width tests

**PASS, with no requested correction.** This review concerns the conditional criteria in [complete83_gamma_power_tests.md](complete83_gamma_power_tests.md). It does not prove that either congruence occurs on a genuine compiler history, resolve independent-gamma83, or establish a new universal arithmetic bound.

The complete frozen helper and companion note were read. The exact immediate source/domain assumptions were cross-read in `complete83_independent_gamma_scout.md`, the historical exact-period proof, the modified half-binomial compiler, and the cited positive-width estimate. The author's normal and optimized exact receipt replays were run freshly from `/`; both pass. No predecessor Python or archived program was executed.

## Frozen evidence

| Author file | SHA-256 |
|---|---|
| complete83_gamma_power_tests.py | `f3f73ad7c0ecf1c37097e9eab68c56dd5b0586408c56d05d458c6df49b514562` |
| complete83_gamma_power_tests.json | `07210a53139f13cb76ef3f05198cdf2ad2b391ed23aa29426babfe211cea2371` |
| complete83_gamma_power_tests.md | `4e8f358a2d651e4cc20946dd3632491d15ad3ee69eb32474a21289e052ec5e4b` |

All eight dependency pins in the authenticated receipt were verified by the fresh replays. In particular the source remains the independent-gamma chart with 83=47M+36A, eighteen strictly positive witnesses and degree 187. This packet emits no new source and makes no additional gate-saving claim.

## Independent mathematical checks

For a fixed genuine parent history, the inherited exact alias theorem says precisely that the stipulated alpha shift and fresh input Pell coordinates give a full positive child zero when

```
x>0, x≡x0 (mod m), alpha0+2d(x0−x)>0,
m=g/gcd(g,2d), g=gcd(2Delta,ord_H(2)).
```

With `A_width=floor((alpha0−1)/(2d))`, the admissible interval is `1<=x<=x0+A_width`. Downward and upward multiples of m give exactly `1+floor((x0−1)/m)+floor(A_width/m)` inputs. A distinct one exists precisely when `m<=max(x0−1,A_width)`. This characterizes the stated history-preserving family, not all possible outer histories above x. Increasing only the input Pell index cannot change its width or modulus.

The genuine kernel gives even a divisible by 3, `Delta=(a+1)(a+3)` odd and `H=4a+3` divisible by 3. Thus ord_H(2) is even, `v2(g)=1`, and m is odd. Direct Euclidean identities give

```
gcd(2Delta,H−1)=2*gcd(a+3,5)∈{2,10},
gcd(2Delta,H−3)=2*gcd(Delta,a)=6.
```

For the first line, `gcd(a+1,2a+1)=1` and `gcd(a+3,2a+1)=gcd(a+3,5)`; equivalently the displayed coefficient resultant is 5. For the second, Delta≡3 modulo a. These arguments control prime powers as well as prime divisors. The actual compiler's power-of-five b and `2^b>=16` imply b>=5 and hence 5|d; no diagnostic numerical choice is substituted for this recipe.

If `2^[k(H−c)]=1 mod H`, the true order divides k(H−c). At each prime, the valuation of g is at most that of k plus that of `gcd(2Delta,H−c)`. Removing gcd(g,2d) therefore yields m|k for c=1 and m|3k for c=3. Since m is odd, only the odd part of k matters. In particular k=2^e gives m=1 or m|3. Equivalently, multiplying H−1 or H−3 by a power of two cannot change its gcd with 2Delta, because 2Delta has exactly one factor of 2 and both offsets are already even. No primality assumption on H is used.

For the fixed compiler of positive even ordinary inputs, a genuine accepted x0=4 satisfying the first test therefore extends to x=3; satisfying the second extends to x=1. The changes to alpha are +2d and +6d, so positivity is automatic. The inherited CRT construction refreshes positive delta,rho while retaining the intended noninput factors. These would be complete false-input zeros on that same valid fixed compiler slice. The unresolved premise is the occurrence of the modular test at the H of an actual accepted native history. Merely prescribing H, appealing to padding, or supplying a small input Pell component does not meet it.

The exact native valuation also checks. Put r=(R−1)/2. The central binomial coefficient has 2-adic valuation popcount(r); every j>=1 term in the half-binomial sum has valuation at least R, strictly larger. Dividing the sum by 2 and multiplying by odd X+1 gives `v2(a)=popcount(R)−2`. The actual mask population then gives v2(a)=3t and H≡3 modulo 4q³. These restrictions do not establish either period test.

## Fresh bounded cross-check and limits

In addition to reading and replaying the author helper, a separate standard-library calculation recomputed all 256 small component orders by factoring Euler's phi and repeatedly removing prime factors whenever modular exponentiation permitted it. This differs from the author's direct residue iteration. Every saved order, g and m matched.

For each offset c=1,3, the independent calculation formed `D_order=O/gcd(O,H−c)`. A power test exists precisely when D_order is a power of two, with least e equal to its binary logarithm. Intersecting those e with 0,...,5 reproduced every saved test list. This is an independent finite check, not an assertion that these small parameters are native histories.

The receipt's 24,576 general tests, 4,653 passing cases and 17,280 width enumerations agree with the helper. The materialized a=12,H=51 and a=48,H=195 examples are positive **input components** only; a=1092,H=4371 is modular/CRT evidence only. Its order 230 verifies the H−1 congruence without any prime-modulus assumption. The eight half-binomial samples verify an exact formula at their stated indices; their failures do not exclude successful tests elsewhere. No giant complete compiler zero is materialized or inferred.

The author uses explicit exceptions and recursively type-exact receipt comparison; normal and `-O` replays preserve the checks. The finite checks supplement the proofs above and the inherited full-source alias theorem. They do not replace the outstanding genuine-history existence argument or recertify the entire universal 84 construction.
