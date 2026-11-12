# Independent source review: direct 85 first-index residues

The first norm uses direct `X=slot6`, so its stated positivity, together with
positive q and slot 7, gives positive `Q=X*Y²` without `q | X`. The predecessor
identity and discriminant rewrite match `solution_residues`; the same returned
index and two natural quotient witnesses give the displayed x/y coordinate,
`tau=1+2Qr` and `k=2n+4Qs` equations. No rank equality is asserted.

The checker pins the sources, replays the author and independent direct-norm
receipts, and tests finite direct-X Pell recurrences including q not dividing X.
These controls are not graph-zero witnesses. This is source review only;
Lean elaboration, exact calibration, provider compatibility, external-file
binding and iPRA remain open.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary14-85-first-index-residues-draft-independent/check.py > /tmp/first-residues85-independent.json
cmp /tmp/first-residues85-independent.json reviews/ordinary14-85-first-index-residues-draft-independent/result.json
```
