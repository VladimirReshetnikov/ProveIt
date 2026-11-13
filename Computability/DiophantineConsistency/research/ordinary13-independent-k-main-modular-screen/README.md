# Bounded small-prime screen for the fixed-slice main condition

The [conditional fixed-port construction](../ordinary13-independent-k-fixed-slice-conditional/) needs `H | 2^R-q`, where

```
N=67*8807, q=2^N, H=4*q³*(q+1)+3,
```

and the constructed R is odd. The deterministic sieve tests every prime `p≤2,000,000` by computing q modulo p, without materializing q, H, R or any Pell ordinate. The only prime in that range dividing H is 3. It does not obstruct the condition: N and R are odd, so `q≡2^R≡2 (mod 3)`. In addition `H≡6 (mod 9)`, so the 3-adic factor of H is exactly 3.

This is a finite screen, not a proof that H has no larger prime factors, that the full divisibility condition holds, that any candidate valuation is a graph zero, or that the 84-operation candidate is equivalent to its parent. Other prime or composite divisors can still obstruct it.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-independent-k-main-modular-screen/check.py | cmp - research/ordinary13-independent-k-main-modular-screen/receipt.json
```

No Lean or provider build was run.
