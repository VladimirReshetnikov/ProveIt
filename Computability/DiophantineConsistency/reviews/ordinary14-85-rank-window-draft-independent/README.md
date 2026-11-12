# Independent source review: direct 85 rank window

The source uses the 85 graph's own guard gap and the scalar-window and
lower-40 facts with matching parameter order. Positive beta and valuation,
four port casts and the two mask bounds remain explicit. The stated natural
rank rewrite and upper window yield `40≤R` and `R+1<q⁴`. No 84/FreeJ graph
zero or q-divisibility of X is used.

The checker pins the sources, replays the author and independent dependency
receipts, and checks a finite scalar grid. Its sharp R=40 guard example has
q not dividing X and is not asserted to be a full graph zero. This is source
and finite review only; Lean elaboration, exact-index calibration, provider
compatibility, external-file binding and iPRA remain open.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary14-85-rank-window-draft-independent/check.py > /tmp/rank-window85-independent.json
cmp /tmp/rank-window85-independent.json reviews/ordinary14-85-rank-window-draft-independent/result.json
```
