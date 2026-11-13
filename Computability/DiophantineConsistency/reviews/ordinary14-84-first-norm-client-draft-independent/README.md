# Independent source review: 84 first norm

The client extracts A0 from the 84 graph's own zero, rewrites the existing
slot-8 update by `putRoot_self`, and uses the graph-specific scaled residual
under the explicit beta cast. Positive beta and J make the scale positive;
the radicand is positive as one plus a natural product. The generic scaled
root interface returns the magnitude of the signed difference and does not
assume its orientation.

The checker pins the reviewed interfaces, replays the author and independent
zero-field receipts, and independently checks literal first-field evaluations
with both signs of the difference and a zero-scale boundary. This is source
and finite review only: Lean elaboration, Pell classification, provider
compatibility, external file/PDF binding and the iPRA endpoint remain open.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary14-84-first-norm-client-draft-independent/check.py > /tmp/first-norm84-independent.json
cmp /tmp/first-norm84-independent.json reviews/ordinary14-84-first-norm-client-draft-independent/result.json
```
