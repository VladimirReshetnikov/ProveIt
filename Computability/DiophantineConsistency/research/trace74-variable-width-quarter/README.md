# A fractional-width exclusion below the symbolic exponent

`Trace74VariableWidthQuarter.quarter_threshold` proves in every `IΣ₁`
model that any internal `n,w,B` satisfying `1≤w`, `4w≤n`, and `8n≤B`
automatically satisfy the arithmetic threshold and subtraction bounds of
the [direct-index client](../trace74-variable-width-index-client/README.md).
The proof transfers inequalities into the model's discretely ordered
difference ring and then back to the natural model.

`fixed_graph_quarter_impossible` uses this with `B=67*8807=590069`: for
one positive trace74 zero whose first port is symbolic `betaNat`, and
supplied same-tuple first/main Pell ordinates at `n,r`, the conditions
`1≤w`, `4w≤n`, `8n≤590069` and `r≤n+w` are inconsistent. The other ports
remain arbitrary. This is a model-level theorem and the index upper bound
is an explicit premise; no ceiling or conclusion about indices above it
is assumed or proved.

The theorem does not yet choose `w=floor(n/4)`, exclude larger values of
`n` or wider index gaps, bind symbolic ports to an external payload, prove
the reverse guard, or establish an iPRA endpoint.

The Lean 4.32.0 author check used `/tmp:` prepended to the captured
`lean_path` field from
[`trace74-fixed-main-index-eleven-draft/observations/attempt01/terminal.json`](../trace74-fixed-main-index-eleven-draft/observations/attempt01/terminal.json),
`timeout 120`, `-M3000 -j1 -DElab.async=false`, this directory as
`--root`, and output `/tmp/Trace74VariableWidthQuarter.olean`. Actual
tool session 98673 exited 0 without warnings; both named axiom reports
list only `propext`, `Classical.choice` and `Quot.sound`. An earlier run
failed to elaborate two nonnegative casts and was rejected.

```text
Trace74VariableWidthQuarter.lean        58588cca492945259d8c30c16e65e18a73597312ae38388b4f2966022c0776b5
Trace74VariableWidthQuarter.olean       fc598f048546cb857e263d22bf003464ac39f0f784c91060f1dc47122d808d49
Trace74VariableWidthIndexClient.olean  7d1ded34fcfffa1753f3d21032627ce290bc67fcaa0aef8cb9531977cfdd812a
Lean executable                        e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550
```

This is a captured-provider author check, not an independent replay or
coherent current-source rebuild. Full transitive/package/dynamic ancestry
and search-path selection were not independently authenticated.
