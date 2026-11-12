# Residue-89 ↔ residue-90 model transport drafts

This source-only packet proposes two model no-zero interfaces for the 89-row
natural graph and its 90-row parent. **No Lean source here has been
elaborated**, and no parent endpoint, compiled provider, fixed-kernel bytes
or physical PDF binding is authenticated.

The graphs differ by one addition at coordinate 8: the 90 graph uses `r+1`,
and the 89 graph uses `r`. The `raiseR` valuation adds one there. Four
proposed all-ring residual comparisons give the exact 90-value at a tuple
and the 89-value at `raiseR` of that tuple, at arbitrary signed ports.

The first client assumes `ForcedR`: every 89 zero has its original `r>0`.
That would allow a predecessor and a same-model zero map. The separate
[fact-level forced-r draft](../ordinary13-residue89-r-model-draft/) proposes
part of this proof under the explicit model kernel bound `K0+1≤q²`; graph
binding and the compact kernel bound are not supplied here.

The second client uses the strictly weaker `PositiveReplacement`: for every
89 zero, there exists another 89 zero with positive r. It does **not** assert
that the original r is positive. A proposed root-switch arithmetic lemma
can construct the replacement under further signed-quotient premises without
the K0 upper bound, but graph extraction and preservation of the other three
residuals have not been discharged. Both clients compose conditionally with
the source-only direct 90→positive-82 bridge, whose positive-82 parent
`PolynomialBridge` remains an explicit external Lean-level hypothesis.
All gamma, model compact-port, fixed K, parent and provider obligations are
inherited. The two 88/87 fold families are handled separately.

Run from `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-residue89-to90-model-draft/check.py | cmp - research/ordinary13-residue89-to90-model-draft/receipt.json
```

The read-only check pins the exact graphs/drafts, reconstructs the four
residual source proposals, verifies the r-shift row edit, rechecks external
source receipts and tests bounded signed inputs. It does not run Lean or stage.
