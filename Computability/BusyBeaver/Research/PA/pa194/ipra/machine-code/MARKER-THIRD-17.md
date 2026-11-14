# PA194 next header return after the dense-84 scan

`PA194MarkerThird17.markerToThird17` extends the genuine marker path in
`MARKER-SECOND-17.md` through the second dense-17 configuration. Its exact
left layout has four ones followed by an even tail, so the pinned machine
returns to dense 17 after six more steps, now with the `k=1` padded header
shape. All earlier restrictions remain: the selected register is positive,
the initial first physical value is `k+7`, and the stated intermediate
header, delimiter, and file layout must hold. The theorem works in every
candidate PRA model, including nonstandard values.

Let `2*r` be the updated file after its first block and let
`w = ones(k+1,3+8*r)`. The final right half is exactly
`1+4*ones(4,1+4*w)`; the left half is the prior padded k=1 header. The full
clock is explicit. `PA194Second17Return.secondToHeader` proves the final
six-step segment separately. This returned file differs from the prior
header-return file: w is odd, so the subsequent state-61 path must be
analyzed separately from the earlier even branch.

These results concern intermediate physical configurations. They do not
prove blank-tape reachability, a source-frame or source-instruction
correspondence, or either PA consistency direction.

Replay from the repository root with pinned overlays:

```sh
TMPDIR=/dev/shm IPRA_LEAN_OVERLAY=/path/to/ipra/lib \
  IPRA_FOUNDATION_OVERLAY=/path/to/foundation/lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-marker-third-17.sh
```

The author completed a fresh suffix replay of the relevant modules with no
`sorryAx`. A separate independent suffix replay has stalled on filesystem I/O;
the full nested replay is also still running.
