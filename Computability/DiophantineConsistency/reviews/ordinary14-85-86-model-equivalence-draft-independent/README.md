# Independent source review: positive 85/86 equivalence wrapper

The forward implication gives an 85 positive zero to the reviewed 85-to-86
map; the reverse implication gives an 86 positive zero to the fresh-root map.
Both receive the same integer ports and beta cast, while the positive-beta
premise required by the reverse direction remains explicit. The natural-port
specialization uses the existing `cast_port p 0` interface. Other integer
ports are unconstrained in the generic statement.

The checker pins both source directions and replays the author and independent
map receipts. This is source-interface review only; all drafts remain
unelaborated, with provider compatibility, external-file binding and the iPRA
endpoint open.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary14-85-86-model-equivalence-draft-independent/check.py > /tmp/equiv8586-independent.json
cmp /tmp/equiv8586-independent.json reviews/ordinary14-85-86-model-equivalence-draft-independent/result.json
```
