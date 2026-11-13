# Exclusion of main index 11 when the first index is at least 8

`Trace74AtLeastEightR11GraphExclusion.graph_r11_impossible` proves that
the following cannot hold for the **same** tuple in any model of `IΣ₁`:
the first port and all ten witnesses are positive; the actual 74-operation
graph has a zero; `q≥2³⁰`; the supplied first Pell index is `n≥8`; and the
main Pell index is 11 with both displayed ordinate identities satisfied.

When `n=8`, the proof uses the separately checked [same-zero fixed-index
exclusion](../trace74-n8-r11-graph-exclusion/README.md). When `n>8`,
discreteness gives `n≥9`, hence `11≤n+2`, and the existing [large-q
near-diagonal theorem](../trace74-near-diagonal-graph-join/README.md)
excludes the pair. In particular, the case `n=7` is not excluded by this
theorem. The result does not prove the reverse guard, 74/75 equivalence,
or an iPRA endpoint.

Lean 4.32.0 author check session 1037 exited zero without warnings, with
the axiom report `[propext, Classical.choice, Quot.sound]`. The command
used `timeout 120`, `-M3000 -j1 -DElab.async=false`, this directory as
`--root`, and `/tmp/Trace74AtLeastEightR11GraphExclusion.olean` as
output. `LEAN_PATH` was `/tmp` followed by the provider sequence in the
[uniform reduction record](../trace74-uniform-projection-reduction-draft/README.md).
The preceding attempt failed on two addition-order elaboration mismatches.

```text
source        bfa4855168a203edb5b16c4e00d52527d32d2de0cfc9a3f44691151b3f761c60
output        022aafacecd9158d650b08562ffa893aa457bc9f430cbc102eb4c174e2b7a9e1
n8/r11 zero   08f862eec2ff5728c26d70e1e4fa3b6fdb341195e8578a0506d8c1537fe2bd8b
near diagonal 64856c47d738c01ef643eff2c90f48efb52f2372d1e8fbbeef688764c9a3a177
```

This is a captured-provider author check, not an independent replay or a
coherent current-source rebuild. Full transitive provider, package and
search-path ancestry remain outside the check.
