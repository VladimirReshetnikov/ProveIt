# Independent source review: compact symbolic 84/85 specialization

The symbolic port constructor is `[beta,K,low,beta+high]`; the fourth entry
is not merely the high payload. The cited `port_bounds` conjunction provides,
in order, positive beta, low<beta, beta+high<2*beta and beta≥46. The wrapper
selects those entries correctly, uses `t=67*8807=590069` and beta's stated
model identity to derive the Mersenne form, and supplies all four natural-port
casts to the generic equivalence with the correct argument order. K remains an
arbitrary natural parameter.

The checker pins all source interfaces, replays the author and independently
reviewed generic wrapper, and tests small symbolic port layouts and bounds.
This is source review, not Lean elaboration. All transitive drafts and
providers, connection to the iPRA endpoint, and the association with external
equation, TeX or PDF bytes remain open.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary14-84-85-compact-model-equivalence-draft-independent/check.py > /tmp/compact-equiv8485-independent.json
cmp /tmp/compact-equiv8485-independent.json reviews/ordinary14-84-85-compact-model-equivalence-draft-independent/result.json
```
