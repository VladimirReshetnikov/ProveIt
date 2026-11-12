# Actual residue-graph q∣3X adapter draft

This packet proposes composing the actual 90-row residue graph's oriented
main root and the separate conditional exact-index source with the
[fact-level q∣3X projection draft](../ordinary13-residue-three-projection-model-draft/).
**No source or provider in this composition has been elaborated by Lean.**

`actual_main_balance` proposes using the actual signed main-norm pair and
`DirectMainNorm.direct_main_orientation` to obtain the positive main root and
its balance, with the essential `X*Y*q` term in the positive part.
`q_dvd_threeX_of_graph` proposes combining that balance with the actual-graph
exact-index source and the fact-level divisibility lemma. Its explicit
premises are the graph zero, positive J, beta and X, `F+alpha<q`, and the
rank window for a represented natural port tuple. All imported norm,
Pell/index, auxiliary, rank, signed-divisibility and provider facts remain
source-only proof obligations.

The proposed conclusion is only `q∣3X`. This packet does not use an implicit
Bézout condition, assert `q∣X`, recover a q-power, prove an eta-zero
extension, identify compact fixed-K bytes or the displayed PDF, or establish
an iPRA endpoint.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-residue-three-projection-graph-draft/check.py | cmp - research/ordinary13-residue-three-projection-graph-draft/receipt.json
```

The bounded read-only checker pins source dependencies, reruns the fact-level
certificates and controls the pair-to-oriented-balance sign on finite inputs.
It does not execute Lean, stage artifacts or authenticate providers.
