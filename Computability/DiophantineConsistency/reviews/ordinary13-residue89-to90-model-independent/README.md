# Independent source review: 89 to 90 root-coordinate transport

The 90 literal and residual sources are exactly the 89 sources with `shift_r=n_r+1` inserted and used by the first-root graph. All other rows and residual order are unchanged. Thus `90(v)=89(raiseR(v))`, where raiseR adds one only at coordinate 8, and the four proposed residual comparisons have the correct direction. For an 89 valuation with positive r, lowering that coordinate and then raising it recovers the valuation.

The stronger client explicitly assumes `ForcedR`: every 89 zero has positive original r. The weaker client assumes `PositiveReplacement`: every 89 zero has some 89 zero with positive r. ForcedR implies the replacement by retaining the same valuation. The replacement client correctly lowers the r coordinate of the supplied *new* zero; it does not claim that the original r was positive or that the root-switch graph client has already been proved. Each conditional no-zero map has the correct directions.

Both bridge paths explicitly assume `PolynomialBridge` for the positive-shifted 82 parent and inherit the proposed 90-to-82 forcing chain. The source supplies neither that parent bridge nor graph extraction of either root hypothesis, fixed compact bytes, provider ancestry or an end-to-end iPRA theorem. The K argument remains an arbitrary standard natural. Regenerated source and author receipt were pinned and reproduced; no Lean tactics or axiom reports were executed.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-residue89-to90-model-independent/check.py | cmp - reviews/ordinary13-residue89-to90-model-independent/result.json
python3 -I -S -B research/ordinary13-residue89-to90-model-draft/check.py | cmp - research/ordinary13-residue89-to90-model-draft/receipt.json
```
