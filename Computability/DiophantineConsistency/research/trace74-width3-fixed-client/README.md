# Width-three linked-index separation at symbolic beta

`Trace74Width3FixedClient.fixed_exists_width3_indices` proves in every
model of `IΣ₁` that one positive trace74 graph zero with the fixed symbolic
first port supplies linked first and main indices `n,r` satisfying the
existing bounds `n≥7`, odd `r≥11`, `n+2<r<2n`, both ordinate identities,
and the first-ordinate residue modulo `q⁴`. It also proves, for the same
indices, `n≥12 → n+3<r` using the width-three graph theorem. The other
three ports are arbitrary.

The stronger separation is conditional on `n≥12`; the result does not
exclude the intervening small-index cases or establish the reverse guard,
general absence of zeros, 74/75 equivalence, or an iPRA endpoint. The
external fixed payload's connection to symbolic ports is not addressed.

The bounded Lean 4.32.0 author check used `/tmp:` prepended to the
`lean_path` field in
[`trace74-fixed-main-index-eleven-draft/observations/attempt01/terminal.json`](../trace74-fixed-main-index-eleven-draft/observations/attempt01/terminal.json),
with `timeout 120`, `-M3000 -j1 -DElab.async=false`, this directory as
`--root`, and output `/tmp/Trace74Width3FixedClient.olean`. Actual tool
session 29154 exited 0 without warnings; the report lists only `propext`,
`Classical.choice`, and `Quot.sound`.

```text
Trace74Width3FixedClient.lean       45b21695fa93fd5b367bc8bedd8dc3e39b02ee44481ec6381584b483033b2345
Trace74Width3FixedClient.olean      d2950932241da27e1271aba8f1f59e490241fff400cb6a7500709ee71afaec70
Trace74Width3GraphJoin.olean        39cc9dfd8470348527a0354cb4ec5c6f741347e4914e5753506a3d135618e1a0
Trace74NearDiagonalFixedClient.olean 9307af5c52d317b5e4079072cc1c9182789d8fe796403a445a6caf4662e39557
```

This is an author check against captured temporary providers, not an
independent replay or clean current-source build. Full transitive/package
ancestry and search-path selection have not been authenticated.
