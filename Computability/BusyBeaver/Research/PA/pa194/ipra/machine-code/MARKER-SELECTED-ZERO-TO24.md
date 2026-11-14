# Selected-register-zero marker path to dense 24

`PA194MarkerZeroSelectedTo24.markerZeroTo24` continues the genuine selected-
register-zero marker path from dense 15 through an all-model zero-run scan,
a marker-return cell, dense 17 and the header controller to dense 24. It
preserves the exact hypotheses of the preceding marker-to-15 theorem: the
non-first marker position and delimiter layout, the k=1 controller header,
selected value zero, and first physical value `m+6`. All eight non-first
marker positions and arbitrary model-valued residual lengths `m` are covered;
no blank suffix or `idx+n=7` hypothesis is imposed. The exact model clock is
stated in Lean.

For the returned even file code `file = rr+rr`, the endpoint has left half
`2*zeros(2, zeros(6, u))+1`. Its right half is

```
t = 1 + 2*file
b = zeros(5, zeros(m, t))
right = ones(1, 1 + 4*b).
```

The theorem holds in every candidate PRA model, including for nonstandard
values and clocks. It starts from the stated intermediate marker
configuration and does not establish blank-tape reachability or a source
instruction simulation.

A manual comparison for standard natural values suggests that when `u=0` and
`m≥30`, the endpoint tape has the concrete `rootFrame` shape with path `11`,
padding `m-30`, and the preserved file: the right-hand bits are `11`, then
`m+6` zeros, then the separator one and file. The pinned PA194 source-site
list resolves that prefix to its leftmost leaf `110` (`inc 6`, index 3671).
This comparison, the source-site identification, and the dense/native
control relation are not established by the present theorem, and neither
`u=0` nor the padding bound is shown reachable. No iPRA consistency direction
is claimed.

The five new modules passed an author suffix rebuild against previously
checked prerequisite overlays, with `propext`, `Classical.choice`, and
`Quot.sound` as their reported axioms and no `sorryAx`. The full nested
checker `check-marker-selected-zero-to24.sh` is supplied but has not been run.
