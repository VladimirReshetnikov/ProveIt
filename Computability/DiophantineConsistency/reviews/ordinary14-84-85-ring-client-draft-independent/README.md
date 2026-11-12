# Independent source review: 84 to 85 ring evaluation

The proposed slot updates implement `X=q*w` and
`gamma_old=gamma_prime-w` in a commutative ring. The 85 carrier's extra
`E*q` equals `U*w` from `Y=q³s`, so the update makes the main fields agree;
all remaining exposed field dependencies agree under the same update. The
output shape is the same sum of five squares. The checker pins both literal
sources and candidates, replays the author's receipt, and independently tests
all fields and output over the integers and composite residue rings.

This is a source review, with finite tests as controls, not a proof for all
rings. The Lean imports name draft overlay modules; no common provider,
elaboration or kernel check has been established. A positive-natural witness
map requires extra derivations, including gamma positivity in one direction
and q-divisibility in the other. Graph zero extraction, fixed port binding,
parent bridges and the iPRA endpoint remain open.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary14-84-85-ring-client-draft-independent/check.py > /tmp/ring84-85-independent.json
cmp /tmp/ring84-85-independent.json reviews/ordinary14-84-85-ring-client-draft-independent/result.json
```
