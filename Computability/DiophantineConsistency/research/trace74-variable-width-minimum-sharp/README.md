# Sharper unbounded-index minimum separation

`Trace74VariableWidthMinimumSharp.fixed_graph_minimum_separation` proves
in every model of `IΣ₁` that a positive trace74 graph zero with symbolic
first port and supplied same-tuple first/main Pell ordinates at `n,r` has

```text
n + min(n/4, 118013) < r,
```

provided `n≥4`. Division is model integer division, and there is **no
upper bound on `n`**. The minimum saturates at `118013`, using
`5*118013+3=590068≤67*8807=590069`. The other three ports are arbitrary
naturals.

The general `minimum_threshold` theorem assumes `1≤w`, `4w≤n`, and
`5w+3≤B` and derives the hypotheses of the
[direct-index obstruction](../trace74-variable-width-index-client/README.md).
Its central identity in the difference ring is

```text
(10w+5)(3n−10w) − 2[2w(n+w)+5w] = (n−4w)(26w+15) ≥ 0.
```

Since `3n−10w≥0` and `10w+5≤2B`, the desired threshold follows.
The fixed client chooses `w=min(n/4,118013)` using model quotient and
remainder. This sharpens the earlier sufficient coefficient `8w≤B`.

`fixed_exists_minimum_indices` retains one same-zero linked pair with
`n≥7`, `r≥11`, `n+3<r`, `r<2n`, odd `r`, both ordinate identities and the
first-index residue modulo `q⁴`, along with the minimum separation. This
does not rule out larger index gaps, prove the reverse guard or 74/75
equivalence, bind symbolic and external ports, or establish an iPRA
endpoint.

The Lean 4.32.0 author check used `/tmp:` prepended to the captured
`lean_path` field from
[`trace74-fixed-main-index-eleven-draft/observations/attempt01/terminal.json`](../trace74-fixed-main-index-eleven-draft/observations/attempt01/terminal.json),
`timeout 120`, `-M3000 -j1 -DElab.async=false`, this directory as
`--root`, and output `/tmp/Trace74VariableWidthMinimumSharp.olean`.
Actual session 88639 exited 0 without warnings; all five named axiom
reports list only `propext`, `Classical.choice`, and `Quot.sound`. An
earlier attempt failed on a fixed-cap numeral inference and was rejected.

```text
Trace74VariableWidthMinimumSharp.lean   8c74879e5b76c45e668742114b8395b99699f6163eb0a76a01003d6c8ae2b10e
Trace74VariableWidthMinimumSharp.olean  b0698ab7ff085e4d4ea18f3c55a8e398092239e7daa9800ee7f53384df8ceb60
Trace74VariableWidthIndexClient.olean   7d1ded34fcfffa1753f3d21032627ce290bc67fcaa0aef8cb9531977cfdd812a
Trace74Width3FixedGlobal.olean          67534a0145c69b65b35727987bd91fdf85b515e9ea24215aa602216d29a83e96
Lean executable                         e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550
```

This is a captured-provider author check, not an independent replay or
coherent current-source rebuild. Full transitive/package/dynamic ancestry
and search-path selection were not independently authenticated.
