# Independent source review: positive 84/85 equivalence wrapper

The source wrapper's forward direction passes the 84 positive zero to the
84-to-85 map, and its reverse direction passes the 85 positive zero to the
85-to-84 map. Both receive the same integer ports, natural beta/K/MC/MF
representatives and mask bounds. The theorem also retains the size and
Mersenne hypotheses required by the reverse map; it does not assume either
target zero or `q | X`.

The checker pins the wrapper and both map sources and replays the author and
independent map receipts. This is source-interface review only. The imported
maps and their transitive dependencies have not been elaborated in Lean;
concrete compact-port binding, provider compatibility, connection to the iPRA
endpoint and external equation/PDF semantics remain open.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary14-84-85-model-equivalence-draft-independent/check.py > /tmp/equiv8485-independent.json
cmp /tmp/equiv8485-independent.json reviews/ordinary14-84-85-model-equivalence-draft-independent/result.json
```
