# AQ17/105 evaluation and forcing-cut extraction draft

This separate packet proposes source proofs for the two explicit missing
hypotheses in [the AQ17/105 transfer](../adaptive-aq17-forced105-model-draft/).
**It has not been elaborated by Lean.** None of its identities, arithmetic
tactics, imports, axiom reports or endpoint has been kernel-checked.

`AQ17Forced105Evaluation.lean.src` compares all eight natural residuals with
the positive parent's residuals under the mixed valuation, composes their
squares, and proposes the graph zero equivalence for arbitrary signed ports
in every relevant IΣ₁ model. `AQ17Forced105CutExtraction.lean.src` names the
shifted positive expressions `c`, `delta`, `ell`, `I`, and the model natural
`q = I²`; proves proposed bounds `c ≥ 2`, `I ≥ 2`, `q ≥ 4`; and proposes
extracting both quotient norms, the signed strong equality, the additive
auxiliary equation and the shifted-rank time equation from residual indices
0, 1, 2, 3 and 7. The exact `linear_combination` steps in the source are
proof attempts requiring verification, not assumed results.

The endpoint source composes these with the earlier arithmetic-forcing and
model-transfer drafts. It **still has explicit AQ17/94, AQ20/104 and AQ22/110
graph obligations**, and inherits the fixed-port beta condition and historical
provider provenance. The optional seventh J-forcing lemma, its root-residual
extraction, the model representation of the second port, and any AQ17/104
endpoint are outside this packet. The prior draft corrected its time cut to
use the shifted rank `v 13 + 1`; this source uses that same coordinate.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/adaptive-aq17-forced105-extraction-draft/check.py | cmp - research/adaptive-aq17-forced105-extraction-draft/receipt.json
```

The check pins sources, verifies finite case coverage and reruns the existing
external graph checker. It does not run Lean, authenticate providers, or prove
any model theorem or internal endpoint.
