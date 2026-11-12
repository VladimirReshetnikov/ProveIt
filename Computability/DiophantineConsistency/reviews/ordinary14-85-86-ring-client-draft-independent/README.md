# Independent source review: 85-to-86 ring fields

The proposed ring update sends 85 slot 7 s to 86 Y=q³s and slot 8 r to
r+s, using the original s in both expressions. The first signed cut
`M(P−r−s)+Yb=M(P−r)` follows from `M=q³b`; all four other residuals and the
output compare under the same update. This is an algebraic ring-field source
proposal, not a positive-model map or a reverse quotient proof.

The checker pins the graph sources and candidates, replays their independent
reviews and the author receipt, and checks signed integer and composite-ring
field evaluations. This is source and finite review only: Lean elaboration,
provider compatibility, external-file binding and iPRA remain open.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary14-85-86-ring-client-draft-independent/check.py > /tmp/ring8586-independent.json
cmp /tmp/ring8586-independent.json reviews/ordinary14-85-86-ring-client-draft-independent/result.json
```
