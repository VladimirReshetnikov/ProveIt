# Conditional amplified height at arbitrary model indices

The Lean theorem `Trace74NearDiagonalLargeHeightModel.amplified_height` proves `8hK²Y² < X` over any model of `IΣ₁`, from the explicit hypotheses `Y≥1`, `power Y (k+4)<8X²`, and `512h²K⁴<power Y k`. Here `power` is the represented model exponentiation. The proof expands `power Y (k+4)`, multiplies the lower bound by positive `Y⁴`, cancels eight, and compares squares.

This result does not prove either height hypothesis, link them to a graph zero, or establish the reverse guard or an iPRA endpoint. The first hypothesis is of the form established by the preceding [Pell height theorem](../trace74-near-diagonal-height-model/README.md); the lower power bound remains a separate obligation.

A captured-provider author check exited 0 and reported `[propext, Classical.choice, Quot.sound]`:

```text
LEAN_PATH=/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  timeout 120 /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -M3000 -j1 -DElab.async=false --root=Computability/DiophantineConsistency/research/trace74-near-diagonal-large-height-model \
  Computability/DiophantineConsistency/research/trace74-near-diagonal-large-height-model/Trace74NearDiagonalLargeHeightModel.lean \
  -o /tmp/Trace74NearDiagonalLargeHeightModel.olean
```

SHA-256: source `a38328d2b796db94dd5ffca4139e93ba20fc2f0448427990f72f950ca79d1bd1`, imported `Trace74NearDiagonalHeightModel.olean` `d98ee6ac00adc72d8b2e95aa40b3653f125a6e2644f2fd7ba8eaec2e4ceac797`, output object `01b02431bd9afe6f85c07190976b120c27519310807e2936a0282ba5a7b96252`. The temporary provider paths and their transitive dependencies and search-path resolution have not been independently audited. This is not a clean current-source rebuild or independent replay.
