# Independent review: bounded main-condition modular screen

The [screen](../../research/ordinary13-independent-k-main-modular-screen/README.md) correctly checks all 148,933 primes through 2,000,000 inclusive. An independently implemented segmented sieve and alternate evaluation of `H=4(q⁴+q³)+3` reproduce the sole reported divisor, 3. No q, H, R or Pell ordinate was materialized.

The fixed symbolic beta is `2^(67*8807)−1`; with J=1 the actual child rows give `q=beta+1=2^590069`. The selected w=s=1 gives X=q, Y=q³ and `a=Y(X+1)`, so the graph's H is exactly `3+4q³(q+1)`. For this particular slice the cited conditional construction has `G=q*t−1`; q is even, the fixed low mask MC is even, and the remaining q*MF term is even. Hence R is odd. This review checks the relevant graph and low-mask source interfaces but does not establish the full conditional construction in Lean.

Since N=590069 is odd, q≡2 modulo 3; odd R gives 2^R≡2 modulo 3, so the factor 3 does not obstruct the main condition. More precisely N≡5 modulo 6, giving q≡5 modulo 9 and H≡6 modulo 9. Thus the 3-adic valuation of H is exactly one, and no higher power of 3 needs checking for divisibility by H.

The result is a finite sieve only: factors above two million may obstruct the main divisibility, and the screen does not establish that condition, the auxiliary condition, any graph zero, a zero map or an iPRA theorem. It also does not authenticate compiled providers or a physical PDF. The receipt reproduces both the author screen and its cited fixed-slice checker, performs the independent segmented sieve and checks the source wiring and residue calculations. From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B reviews/ordinary13-independent-k-main-modular-screen-independent/check.py | cmp - reviews/ordinary13-independent-k-main-modular-screen-independent/receipt.json
```
