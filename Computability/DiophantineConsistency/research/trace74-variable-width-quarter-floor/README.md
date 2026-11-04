# Same-zero floor-quarter index separation

`Trace74VariableWidthQuarterFloor.fixed_graph_floor_separation` proves
in any model of `IΣ₁` that one positive trace74 graph zero with symbolic
first port and supplied same-tuple Pell ordinates at `n,r` must satisfy

```text
n + n/4 < r
```

provided `4≤n` and `8n≤67*8807=590069`. Division is the arithmetic
model's integer division. The proof chooses `w=n/4` in the previously
checked [quarter-width theorem](../trace74-variable-width-quarter/README.md),
deriving `4w≤n` by model division and `w≥1` using its quotient/remainder
identity. The other three ports remain arbitrary natural numbers.

The upper bound on `n` and both ordinate identities remain explicit;
this does not prove a bound on every index, bind symbolic and external
ports, prove the reverse guard, or establish an iPRA endpoint.

The Lean 4.32.0 author check used `/tmp:` prepended to the captured
`lean_path` field from
[`trace74-fixed-main-index-eleven-draft/observations/attempt01/terminal.json`](../trace74-fixed-main-index-eleven-draft/observations/attempt01/terminal.json),
`timeout 120`, `-M3000 -j1 -DElab.async=false`, this directory as
`--root`, and output `/tmp/Trace74VariableWidthQuarterFloor.olean`.
Actual session 81220 exited 0 without warnings; the named axiom report
lists only `propext`, `Classical.choice`, and `Quot.sound`.

```text
Trace74VariableWidthQuarterFloor.lean   3d04a75a690c881328ddff5bec3dfd3362ed1cc1e08fb38add1791be7c85c898
Trace74VariableWidthQuarterFloor.olean  16e860545e7f0bb98a2a0befb5786efceb9abf7bf9d00fae28a154391d7fdf5f
Trace74VariableWidthQuarter.olean       fc598f048546cb857e263d22bf003464ac39f0f784c91060f1dc47122d808d49
Lean executable                         e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550
```

This is a captured-provider author check, not an independent replay or
coherent current-source rebuild. Full transitive/package/dynamic ancestry
and search-path selection were not independently authenticated.
