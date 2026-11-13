# Complementary two-sevenths index separation

`Trace74VariableWidthTwoSevenths.fixed_graph_two_sevenths_separation`
proves in every model of `IΣ₁` that a positive trace74 graph zero with
symbolic first port and supplied same-tuple Pell ordinates at `n,r` has

```text
n + min((2n)/7, 32781) < r,
```

provided `n≥7`. Division is model integer division; there is **no upper
bound on `n`**. The width saturates at `32781`, since
`18*32781+10=590068≤67*8807=590069`. Other ports are arbitrary naturals.

The generic threshold assumes `2≤w`, `7w≤2n` and `18w+10≤B`. Its
arithmetic identity is

```text
(36w+20)(3n−10w) − 2[2w(n+w)+5w] = (2n−7w)(52w+30) ≥ 0.
```

It applies the [direct-index variable-width obstruction](../trace74-variable-width-index-client/README.md).
The fixed client chooses `w=min((2n)/7,32781)`, with quotient/remainder
facts proving the quotient at least two. This slope gives a stronger
separation at some indices than the earlier quarter-width result, while
its saturation constant is smaller: neither bound is claimed to dominate
the other for all `n`.

`fixed_exists_both_indices` retains **one same-zero linked pair** with
`n≥7`, `r≥11`, `n+3<r`, `r<2n`, odd `r`, both ordinate identities, the
first-index residue modulo `q⁴`, this bound and the prior
`n+min(n/4,118013)<r` bound. It does not prove the reverse guard or 74/75
equivalence, bind symbolic and external ports, or establish an iPRA
endpoint.

The Lean 4.32.0 author check used `/tmp:` prepended to the captured
`lean_path` field from
[`trace74-fixed-main-index-eleven-draft/observations/attempt01/terminal.json`](../trace74-fixed-main-index-eleven-draft/observations/attempt01/terminal.json),
`timeout 120`, `-M3000 -j1 -DElab.async=false`, this directory as
`--root`, and output `/tmp/Trace74VariableWidthTwoSevenths.olean`.
Actual session 75379 exited 0 without warnings; all five named axiom
reports list only `propext`, `Classical.choice`, and `Quot.sound`.

```text
Trace74VariableWidthTwoSevenths.lean   3ecd08615e90b699f91c23ec2bf9085a05bb14599731fc8f68646bd1505b6ef4
Trace74VariableWidthTwoSevenths.olean  552a1f732dc11377b6a65a45bc19ddd24640fa1c2143581c64e892e96f89402b
Trace74VariableWidthMinimumSharp.olean b0698ab7ff085e4d4ea18f3c55a8e398092239e7daa9800ee7f53384df8ceb60
Lean executable                        e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550
```

This is a captured-provider author check, not an independent replay or
coherent current-source rebuild. Full transitive/package/dynamic ancestry
and search-path selection were not independently authenticated.
