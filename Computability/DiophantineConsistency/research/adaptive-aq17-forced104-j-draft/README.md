# AQ17/104 seventh-coordinate source draft

This packet proposes an unelaborated Lean bridge from the 17-natural-input,
104-operation literal to the 105-operation literal. **No theorem, tactic,
provider import or endpoint here has been Lean checked.**

At a zero of the 104-row graph, the source proposes extracting from residual
5 the exact `J=0` branch

```
0 = (1-F-alpha)*(X+K0)-F
```

in the model difference ring. The displayed `F`, `alpha`, and `X` are the
shifted positive coordinates. The J-forcing argument requires the **exact
representation** `((p 1 : ℤ) : DiffRing V) = ι k` for a model natural `k`;
its natural nonnegativity then makes the branch impossible. The proposed fixed
client uses `ModelThirteenCarrier.port1` to represent the current `K0`. Its
application and provider ancestry have not been checked here. No arbitrary
negative second-port claim is made.

The transport draft gives the 104 graph the 105 valuation with one added to J,
proposes eight pointwise residual identities for that substitution, and uses
J positivity to take the reverse predecessor. It composes the resulting
no-zero transfer with the 105 draft and the earlier parent bridges. The
endpoint still explicitly assumes the three AQ17/94, AQ20/104 and AQ22/110
graph obligations and inherits the separate strict-positive first-port
requirement. The AQ105 forcing extraction, the 104 root branch, the current
port lemma and all graph identities remain unelaborated proposals, not an
iPRA endpoint or a checked equivalence to an untranslated sentence.

From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B research/adaptive-aq17-forced104-j-draft/check.py | cmp - research/adaptive-aq17-forced104-j-draft/receipt.json
```

This read-only checker pins source and graph bytes, checks vector and finite
case coverage, and reruns the relevant external graph checks. It does not
execute Lean, validate proof tactics, or authenticate compiled providers.
