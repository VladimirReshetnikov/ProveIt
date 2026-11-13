# Independent source review: direct 85 growth bound

Positive J and beta≥46 imply `q=1+J*beta≥47`. The same 85 own-zero
projection gives `q | 3X`, and positive X gives `q≤3X`; discreteness then
forces X≥16. The exact-index witnesses yield `r=n−1`, `r+1=n`, `r≥2` and
`R=2r+1`. The main and first Pell coordinates are rewritten into the exact
argument order required by `power_bound`, including the positive zeta slot.
No `q | X` or `X=2^R` premise is used.

The checker pins the source interfaces, replays author and independent
projection receipts, and tests finite threshold and index arithmetic. The
case q=48, X=16 reaches the threshold without q dividing X; a q=45, X=15
boundary shows why a sufficient lower bound is needed. These are not graph
zeros. This is source and finite review only: Lean elaboration, compact beta
instantiation, power equality, providers, external-file binding and iPRA
remain open.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary14-85-growth-draft-independent/check.py > /tmp/growth85-independent.json
cmp /tmp/growth85-independent.json reviews/ordinary14-85-growth-draft-independent/result.json
```
