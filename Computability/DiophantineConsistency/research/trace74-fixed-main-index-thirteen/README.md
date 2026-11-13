# Main index at least 13 when the first index is at least 8

`Trace74FixedMainIndexThirteen.fixed_main_index_ge_thirteen` proves in
every model of `IΣ₁` that, for a positive actual trace74 zero with the
symbolic fixed first port and a **supplied** first Pell ordinate at index
`n≥8`, there is a linked main index `r` for that same tuple satisfying
`r≥13`, `n+2<r<2n`, oddness, and the main ordinate equation. The other
three ports remain arbitrary.

The proof combines the earlier linked index `r≥11` with the checked
same-zero exclusion of `r=11` at `n≥8`; parity rules out `r=12`. It
does **not** establish `n≥8` for all zeros: the first-index-7 case remains
open. The external fixed payload binding, reverse guard, and iPRA endpoint
are not established here.

Lean 4.32.0 author check session 50879 exited zero without warnings, with
axiom report `[propext, Classical.choice, Quot.sound]`. It invoked Lean
with `-M3000 -j1 -DElab.async=false`, a 120-second subprocess timeout,
this directory as `--root`, and output
`/tmp/Trace74FixedMainIndexThirteen.olean`. `LEAN_PATH` was `/tmp:`
prepended to the `lean_path` field in the captured [fixed-main-index-11
receipt](../trace74-fixed-main-index-eleven-draft/observations/attempt01/terminal.json).
A preceding invocation failed immediately because its shorter search path
omitted `Trace74FixedMainIndexEleven`.

```text
source         5a7463520d7897681af80e6d7343854ed0215b6ed88a0d17fee88b4472127d65
output         8cfa49a72d12626cc8ddb365a4b88a43982e7a288c3e4506716b9dce1a6f51fe
general r11    022aafacecd9158d650b08562ffa893aa457bc9f430cbc102eb4c174e2b7a9e1
fixed indices  9307af5c52d317b5e4079072cc1c9182789d8fe796403a445a6caf4662e39557
```

This is a captured-provider author check. Complete transitive provider,
package and search-path ancestry were not authenticated; no independent
replay or coherent current-source rebuild is claimed.
