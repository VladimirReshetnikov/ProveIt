# Upper Pell interval for a positive tuple

`Trace74UpperPellGapModel.tuple_upper_pell_gap` proves the upper half of
the same-tuple Pell interval in every `IΣ₁` model. Given the first and main
ordinate identities and `v 9>0`, it derives

```text
y_r(Y(X+1)−1) < 2(Y+1) y_n(2(XY²−1)+1).
```

This follows from the actual definitions `c=kY+v 8` and `k=v 8+v 9`.
The companion theorem `tuple_upper_power_gap` applies the represented Pell
sandwich at positive internal indices, giving an explicit reverse power
inequality. It assumes `X≥1` and `Y≥1`; neither theorem assumes a graph
zero or proves the reverse guard. The index shifts are `n−1` and `r−1`.

The author ran Lean 4.32.0 with `timeout 120`, `-M3000 -j1`,
`-DElab.async=false`, this directory as `--root`, and output
`/tmp/Trace74UpperPellGapModel.olean`. `LEAN_PATH` was `/tmp:` followed by
the captured `lean_path` in
[`trace74-main-index-eleven-draft/observations/attempt01/terminal.json`](../trace74-main-index-eleven-draft/observations/attempt01/terminal.json).
Actual session 43392 exited 0; both axiom reports listed only `propext`,
`Classical.choice`, and `Quot.sound`. An initial invocation lacked an
import provider, and a second failed on an addition-order elaboration
error; neither was accepted.

Source SHA-256:
`617a491d15f611a64792f5beed50152ac4987a434d408740a487a356c18c05b3`.
Output object SHA-256:
`8805aa2c2f7fe902a90c890a376439f9dd4be873e95967c8d365fb8bfa64df7b`.
Direct imported `Trace74PellGapBinding.olean` SHA-256:
`8ffc0282fa2dc540cbba08255c19ca780234da569fd2ad2b1163418c0966445a`.
Temporary captured providers, complete transitive/package/dynamic ancestry
and search-path selection were not independently authenticated; this is not
a clean current-source build or independent replay.
