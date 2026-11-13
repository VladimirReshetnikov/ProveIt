# Exact unit-target presentation of the eta/zeta parent

The pinned 85-row eta/zeta parent computes its last two rows as

```text
P0123 = P012 * Fs
out = P0123 − 1.
```

`presentation.json` removes only the last subtraction and writes the equation as `P0123 = 1`. The left-hand arithmetic circuit then has 84 binary operations. Every port tuple and witness has the same truth value for this equation as for the parent's `out=0`, over any ring with one; no witness transport or compact-port assumption is needed.

This is a **presentation saving only**. Its associated zero polynomial remains `P0123−1`, and computing that normalized polynomial from zero still takes the same displayed 85 operations. It is not evidence of a smaller normalized polynomial circuit, a minimality result, a Lean proof, or an iPRA endpoint. The exact parent and its existing proof obligations are unchanged.

The checker pins the graph and presentation, checks that the 84 rows are the exact parent prefix and that the target is one, and evaluates bounded integer controls. The universal equality follows immediately from the last row, not from those controls.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary13-eta85-unit-target-presentation/check.py | cmp - research/ordinary13-eta85-unit-target-presentation/receipt.json
```
