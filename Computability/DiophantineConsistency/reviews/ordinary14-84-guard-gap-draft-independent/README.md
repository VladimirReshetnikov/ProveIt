# Independent source review: 84 guard gap

The guard formula matches the 84 graph and uses explicit difference-ring
representations for both beta and K. Its own-zero field extraction selects the
guard residual. Natural `q=1+J*beta` and positive w give `X>0`, so `X+K>0`;
positive F and nonnegative `J*beta*h` make the guard product positive. The
signed factor `q−F−alpha` must then be positive, and `ι_lt_ι` transfers the
strict gap to the natural model. No natural subtraction is used in this step.

The checker pins the source interfaces, replays the author and independent
field-extraction receipts, tests bounded actual guard zeros, and records
counterexamples when key stated assumptions are omitted. This remains source
and finite review: Lean elaboration, rank representation, model provider
compatibility, external file association and the iPRA endpoint are open.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary14-84-guard-gap-draft-independent/check.py > /tmp/guard-gap84-independent.json
cmp /tmp/guard-gap84-independent.json reviews/ordinary14-84-guard-gap-draft-independent/result.json
```
