# Unbounded-index minimum separation at the fixed symbolic port

`Trace74VariableWidthMinimum.fixed_graph_minimum_separation` proves in
every model of `IΣ₁` that a positive trace74 graph zero with symbolic first
port and the supplied same-tuple first/main Pell ordinates at `n,r` has

```text
n + min(n/4, 73758) < r,
```

provided `n≥4`. Division is model integer division. There is **no upper
bound on `n`** in the statement; the minimum saturates at `73758`. This
uses the symbolic exponent `67*8807=590069` and the exact comparison
`8*73758=590064≤590069`. The remaining three ports are arbitrary naturals.

The proof first establishes a general arithmetic threshold: when `1≤w`,
`4w≤n`, and `8w≤B`, the quantitative hypotheses of the
[direct-index variable-width client](../trace74-variable-width-index-client/README.md)
follow. In the difference ring, setting `D=3n−10w` gives `n≤2D`; the
threshold's left side is at most `4wn`, which is at most `8wD≤BD`. It then
chooses `w=min(n/4,73758)` using model quotient/remainder facts.

`fixed_exists_minimum_indices` retains **one same-zero linked pair** with
`n≥7`, `r≥11`, `n+3<r`, `r<2n`, odd `r`, both ordinate identities and
the first-index residue modulo `q⁴`, along with the minimum separation.
No upper bound on either index is asserted. The saturated additive gap does
not rule out larger gaps, prove the reverse guard or 74/75 equivalence,
bind symbolic and external ports, or establish an iPRA endpoint.

The Lean 4.32.0 author check used `/tmp:` prepended to the captured
`lean_path` field from
[`trace74-fixed-main-index-eleven-draft/observations/attempt01/terminal.json`](../trace74-fixed-main-index-eleven-draft/observations/attempt01/terminal.json),
`timeout 120`, `-M3000 -j1 -DElab.async=false`, this directory as
`--root`, and output `/tmp/Trace74VariableWidthMinimum.olean`. Actual
session 13357 exited 0 without warnings; all five named axiom reports
list only `propext`, `Classical.choice`, and `Quot.sound`.

```text
Trace74VariableWidthMinimum.lean      df79949ff57353353e020247ffb806a423bdb61f2badd8b8621bb19c4ced5906
Trace74VariableWidthMinimum.olean     ae20cd61f8a825ea4c9118637c634de931c4999894e4457f56bd98fa753ebaa2
Trace74VariableWidthIndexClient.olean 7d1ded34fcfffa1753f3d21032627ce290bc67fcaa0aef8cb9531977cfdd812a
Trace74Width3FixedGlobal.olean         67534a0145c69b65b35727987bd91fdf85b515e9ea24215aa602216d29a83e96
Lean executable                        e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550
```

This is a captured-provider author check, not an independent replay or
coherent current-source rebuild. Full transitive/package/dynamic ancestry
and search-path selection were not independently authenticated.
