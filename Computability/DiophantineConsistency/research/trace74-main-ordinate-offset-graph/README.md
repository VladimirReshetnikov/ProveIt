# Positive offset residue on a fixed-symbolic graph tuple

`Trace74MainOrdinateOffsetGraph.graph_offset_residue` binds the main
Pell-ordinate residue to a supplied positive tuple: for positive first
port and witnesses and a supplied main ordinate at `r`, it proves
`0<v₈<k` and `v₈ mod Y = r mod Y`. The graph-zero equation is not needed
once those tuple hypotheses are supplied.

`fixed_exists_offset_indices` applies this to the same linked pair
already obtained for a positive 74 graph zero with fixed symbolic first
port. It retains both first/main ordinate identities, the first-index
residue, oddness and the two previously checked unbounded-index minimum
separations. The other ports are arbitrary. This new congruence is a
necessary condition, not a demonstration that the index or offset is
smaller than `Y`; it does not yield the reverse guard, fixed external
payload binding, or an iPRA endpoint.

The Lean 4.32.0 author check used `/tmp:` prepended to the `lean_path`
field of [`trace74-fixed-main-index-eleven-draft/observations/attempt01/terminal.json`](../trace74-fixed-main-index-eleven-draft/observations/attempt01/terminal.json),
with `-M3000 -j1 -DElab.async=false`, a 120-second subprocess timeout,
this directory as `--root`, and output `/tmp/Trace74MainOrdinateOffsetGraph.olean`.
Tool session 5477 exited 0; both reports list only `propext`,
`Classical.choice` and `Quot.sound`. A first attempt used a provider
path without `Trace74FixedQLarge` and exited 1 before elaboration.

Source SHA-256:
`60c5d0b36ea445660ab2ce46459fc347d15352cd381a2f8aec19301048265a88`.
Output object SHA-256:
`fea131b7f0e2bbeb679c26ac9da213e4c4e3c69c61da502a34952d5ffe23c036`.
Imported `Trace74MainOrdinateOffsetResidue.olean` SHA-256:
`42d992613f5927202e032b8a5f5a24a200b0b028cb74c4fb6e2e6cb7571e3cb2`.
Imported `Trace74VariableWidthTwoSevenths.olean` SHA-256:
`552a1f732dc11377b6a65a45bc19ddd24640fa1c2143581c64e892e96f89402b`.
The captured-provider check does not authenticate full transitive,
package or dynamic ancestry or first search-path selection; it is not
a clean current-source build or an independent replay.
