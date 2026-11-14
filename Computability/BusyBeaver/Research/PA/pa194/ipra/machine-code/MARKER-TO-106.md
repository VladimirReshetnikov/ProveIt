# PA194 marker path through the odd state-61 branch

`PA194MarkerTo106.markerTo106` extends the genuine marker-entry path in
`MARKER-THIRD-17.md` to dense state 106. The initial `k=1` header and exact
delimiter/file shape, positive selected value, and first physical value
`k+7` remain assumptions. It covers all non-first marker positions in every
candidate PRA model, including nonstandard values and scan lengths. The
first-value-six, selected-zero, state-42 zero-residual, and other header
cases remain separate.

The third returned header selects the odd state-61 branch, which begins
61 → 86 → 73 → 85. State 85 then scans a model-valued run of ones and exits
to 106. `PA194State61OddRoute.oddTo106` checks that reusable segment, and
`PA194OddHeaderTo106.oddHeaderTo106` connects it to the returned header.
The complete marker theorem gives an explicit clock and both tape halves;
the final right half is exactly `r`, where `2*r` is the updated remaining
file after the first physical block. The generic state-106 theorem permits arbitrary r. For the actual composed
file layout, `MARKER-TO-71.md` proves r has a nonempty one-run and the next
branch is forced.

The result does not establish blank-tape reachability, identify the dense-106
configuration as a source frame or source instruction, or prove either PA
consistency direction.

Replay from the repository root with pinned overlays:

```sh
TMPDIR=/dev/shm IPRA_LEAN_OVERLAY=/path/to/ipra/lib \
  IPRA_FOUNDATION_OVERLAY=/path/to/foundation/lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-marker-to-106.sh
```

An independent suffix replay rebuilt the new module(s) against separately
checked controller objects and preserved prerequisite/scratch overlays. The
reported theorem axioms did not include `sorryAx`. The shared comprehensive
prerequisite replay is running separately.
