# A conditional fractional separation for linked Pell indices

`Trace74VariableWidthFractionalClient.fixed_graph_fractional` proves in
any model of `IΣ₁` that a positive trace74 zero with symbolic first port
and supplied same-tuple Pell ordinates at `n,r` satisfies

```text
5n < 4r,
```

provided `4≤n` and the **explicit** index bound `8n≤67*8807=590069`.
The proof converts the [floor-quarter bound](../trace74-variable-width-quarter-floor/README.md)
using model division, the remainder bound and discrete order. The remaining
three ports are arbitrary natural numbers.

`fixed_exists_fractional_indices` retains one linked same-zero pair with
`n≥7`, `r≥11`, `n+3<r<2n`, odd `r`, both ordinate identities and the
first-index residue modulo `q⁴`. For **that same pair** it concludes the
implication `8n≤590069 → 5n<4r`. It does not establish the antecedent.
Thus this is not an unconditional fractional separation for every zero,
a bound on all indices, an external payload binding, a reverse guard, or
an iPRA endpoint.

The Lean 4.32.0 author check used `/tmp:` prepended to the captured
`lean_path` field from
[`trace74-fixed-main-index-eleven-draft/observations/attempt01/terminal.json`](../trace74-fixed-main-index-eleven-draft/observations/attempt01/terminal.json),
`timeout 120`, `-M3000 -j1 -DElab.async=false`, this directory as
`--root`, and output `/tmp/Trace74VariableWidthFractionalClient.olean`.
Actual session 99952 exited 0 without warnings; all three named axiom
reports list only `propext`, `Classical.choice`, and `Quot.sound`.

```text
Trace74VariableWidthFractionalClient.lean   a91d587c418b9423c6d535052eafc1703c2152905d5094d467b7fc527a65874c
Trace74VariableWidthFractionalClient.olean  b5d78040ec6dbbc00e41aa9d0392e60514dcf85b209f24ca9e55ab257d7e4b6c
Trace74VariableWidthQuarterFloor.olean      16e860545e7f0bb98a2a0befb5786efceb9abf7bf9d00fae28a154391d7fdf5f
Trace74Width3FixedGlobal.olean              67534a0145c69b65b35727987bd91fdf85b515e9ea24215aa602216d29a83e96
Lean executable                             e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550
```

This is a captured-provider author check, not an independent replay or
coherent current-source rebuild. Full transitive/package/dynamic ancestry
and search-path selection were not independently authenticated.
