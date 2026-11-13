# Independent source review: 84 first Pell index

Positive q, w and s imply the explicitly defined `Q=X*Y²` is positive.
The source first norm rewrites using `ell=Q*k` to
`tau²=1+Q(Q+1)k²`. The cited positive-parameter classification has exactly
the asserted `n≤k`, x-coordinate and doubled y-coordinate conclusions; it
handles `Q−1` only after establishing Q positive. This draft does not equate
the resulting index with the rank.

The checker pins both source interfaces, replays the author and independent
first-norm receipts, and checks actual finite Pell recurrence coordinates,
including the zero-index boundary. This is source and finite review only;
Lean elaboration, rank windows, exact index, provider compatibility, external
binding and the iPRA endpoint remain open.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary14-84-first-index-draft-independent/check.py > /tmp/first-index84-independent.json
cmp /tmp/first-index84-independent.json reviews/ordinary14-84-first-index-draft-independent/result.json
```
