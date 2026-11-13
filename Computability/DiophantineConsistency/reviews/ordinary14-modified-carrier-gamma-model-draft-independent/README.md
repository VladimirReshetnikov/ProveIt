# Independent source review: modified carrier gamma bound

The two proposed statements and their proofs are mathematically consistent on
source inspection. The cited Pell power, ordinate monotonicity and `x_gt`
interfaces match the calls. The factorization has the strictly positive
remainder `8a+9`; together with `X,w ≤ a` it gives `X+H*w<c`. Assuming
`gamma ≤ w` then makes the subtraction-free natural balance contradict
`d>(a+1)c`. The graph-shaped corollary derives the two size bounds from its
explicit `Y>0`, `q≥1`, `X=q*w`, and `a=XY+Y` assumptions; positive `U`
permits cancellation. The rank hypothesis `R≥3` is used and a concrete
`R=2` counterexample demonstrates it cannot simply be dropped.

The checker pins the source and cited source interfaces, replays the author
receipt, and independently enumerates actual natural Pell/carrier balances and
the rank-two boundary. This is **source review and finite testing only**.
Lean has not elaborated or kernel-checked the draft; tactic rewrites, model
instances, providers, graph extraction, constant association and the iPRA
endpoint remain unverified.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary14-modified-carrier-gamma-model-draft-independent/check.py > /tmp/modified-carrier-gamma-independent.json
cmp /tmp/modified-carrier-gamma-independent.json reviews/ordinary14-modified-carrier-gamma-model-draft-independent/result.json
```
