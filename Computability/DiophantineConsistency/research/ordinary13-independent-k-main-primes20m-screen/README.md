# Fixed-slice main condition: primes through 20 million

For the [independent-k fixed slice](../ordinary13-independent-k-fixed-slice-auxiliary-discharge/), the remaining standard-integer condition is `H | 2^R-q`, with

```
N=67*8807, q=2^N, H=4q³(q+1)+3,
```

and odd R. This screen extends the separately retained two-million check. A deterministic Eratosthenes sieve enumerates all 1,270,607 primes at most 20,000,000 and computes `q mod p` with modular exponentiation. The only prime found to divide H is 3. For that prime, q and `2^R` are both 2 modulo 3 because N and R are odd, so it cannot obstruct the condition. Independently, the checker obtains `H≡6 (mod 9)`, so 3 occurs to exactly the first power.

No q, H, R, Pell ordinate or huge fixed coefficient is materialized: the sieve uses roughly 20 MB of transient memory and writes only the small receipt. This is a finite search, not a factorization of H. Prime factors above the limit can still obstruct the main condition. The screen does not prove the condition true, a full graph zero, a zero map, a Lean theorem or an iPRA endpoint.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-independent-k-main-primes20m-screen/check.py | cmp - research/ordinary13-independent-k-main-primes20m-screen/receipt.json
```
