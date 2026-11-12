# Independent source review: literal 86 graph

The literal source matches the pinned 86-row candidate, with slot 6 as X,
slot 7 as Y and slot 8 as the old first-root coordinate. Its first signed
term retains `M*(ell+k−r)+Y*b`; the six exposed fields and five-square output
shape agree with the candidate. All literal rows are topologically ordered
and live in the output.

The checker independently parses the source rows, checks slot and port
bindings and dependency/liveness, and replays the generator receipt. This is
source review only: Lean elaboration, the 85/86 coordinate bridge, provider
compatibility, external-file binding and iPRA remain open.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary14-residue-guard86-lean-draft-independent/check.py > /tmp/literal86-independent.json
cmp /tmp/literal86-independent.json reviews/ordinary14-residue-guard86-lean-draft-independent/result.json
```
