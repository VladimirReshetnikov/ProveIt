# Independent source review: 85 own-zero guard and rank

The reviewed 85 graph uses slot 6 directly as X in the guard factor `X+K`.
The own-zero guard residual yields `F+alpha<q` under the stated positive F/X
and beta/K port casts. The rank source expression does not involve X; its
graph-independent natural-rank representation requires only the proved F and
q² bounds and the explicit MC/MF casts. The proposed proof never takes an 84
or FreeJ graph zero and does not assume `q | X`.

The checker pins revised source and dependencies, replays the author and
independent graph/rank receipts, and checks finite literal 85 guard/rank
evaluations including X values not divisible by q. These inputs are not
claimed full graph zeros. This is source and finite review only; Lean
elaboration, power recovery, q-divisibility, provider compatibility,
external-file binding and iPRA remain open.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary14-85-guard-rank-draft-independent/check.py > /tmp/guard-rank85-independent.json
cmp /tmp/guard-rank85-independent.json reviews/ordinary14-85-guard-rank-draft-independent/result.json
```
