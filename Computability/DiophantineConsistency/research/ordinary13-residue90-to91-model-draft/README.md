# Residue-90 ↔ residue-91 model transport draft

This packet proposes an unelaborated Lean no-zero transfer between the natural
90-row graph with unshifted gamma and its 91-row predecessor with gamma
shifted by one. **No declaration, import, provider or endpoint has been Lean
checked.**

The generated 91-row literal has the same 13 variable coordinates and four
ordered residuals as the 90-row graph. `raiseGamma` adds one at coordinate
12; four proposed all-ring residual identities give
`literal91(v) = literal90(raiseGamma v)` at arbitrary signed ports. The
reverse zero map uses a predecessor of gamma, obtained from the separate
source-only compact-symbolic gamma-forcing chain. This proof does not require
f/y positivity: those are separately drafted for the broader positive-parent
zero map.

The compact no-zero client uses a symbolic tuple with K an **arbitrary
standard natural**. It inherits all unelaborated graph, norm, rank, Pell,
quotient and provider dependencies of gamma forcing. Its native client takes
`PolynomialBridge` for the 91-row parent as an explicit external Lean-level
hypothesis; this packet does not construct that bridge, identify fixed K or
port bytes with a displayed PDF, or establish an iPRA endpoint.

Run from `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-residue90-to91-model-draft/check.py | cmp - research/ordinary13-residue90-to91-model-draft/receipt.json
```

The read-only checker reconstructs source and residual DAGs, verifies the exact
gamma-only row edit, reruns external graph and inherited draft checks, and
checks bounded pointwise controls. It does not run Lean, stage artifacts or
authenticate provider ancestry.
