# Direct-index variable-width graph obstruction

`Trace74VariableWidthIndexClient.graph_index_impossible` packages the
variable-width obstruction using supplied first/main indices `n,r` and
width `w` directly, over arbitrary models of `IΣ₁`. It excludes one
positive trace74 zero and its supplied same-tuple ordinate identities
under the explicit conditions

```text
power 2 B ≤ q,
3w+1 ≤ n,      10w ≤ 3n,      r ≤ n+w,
2w(n+w)+5w ≤ B(3n−10w).
```

Both subtractions are natural-model truncated subtractions, and the
theorem proves their cancellation using the displayed bounds. The proof
instantiates the preceding
[`m,e` graph client](../trace74-variable-width-graph-join/README.md)
with `m=n−(3w+1)` and `e=3n−10w`; no parity assumption is required.

`fixed_graph_index_impossible` specializes `B` to `67*8807` under the
symbolic fixed first-port identity, using its represented exponential
lower bound on `q`. Other ports remain arbitrary natural numbers. This
does not establish the explicit index/threshold assumptions, rule out
all zeros, prove a reverse guard or an iPRA endpoint, or bind the
symbolic port to an external payload. The case `n≤3w` is outside the
statement.

The Lean 4.32.0 author check used `/tmp:` prepended to the captured
`lean_path` field from
[`trace74-fixed-main-index-eleven-draft/observations/attempt01/terminal.json`](../trace74-fixed-main-index-eleven-draft/observations/attempt01/terminal.json),
`timeout 120`, `-M3000 -j1 -DElab.async=false`, this directory as
`--root`, and output `/tmp/Trace74VariableWidthIndexClient.olean`. Actual
tool session 71173 exited 0 without warnings; both named axiom reports
list only `propext`, `Classical.choice` and `Quot.sound`.

```text
Trace74VariableWidthIndexClient.lean   bbf53a49ce325445431b27fcc087ef6268b14fa13e7dc29ea0e45a2075ed26b9
Trace74VariableWidthIndexClient.olean  7d1ded34fcfffa1753f3d21032627ce290bc67fcaa0aef8cb9531977cfdd812a
Trace74VariableWidthGraphJoin.olean    57b72440c2dc905ce2a3ef1026a942c440a1709e2915955341e494a34e8c47e4
Lean executable                        e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550
```

This is a captured-provider author check, not an independent replay or
coherent current-source rebuild. Full transitive/package/dynamic ancestry
and search-path selection were not independently authenticated.
