# PA194 return to the same physical header shape

`PA194MarkerHeaderRecurrence.markerHeaderRecurrence` composes the genuine
non-first marker run, the physical decrement and return, and the subsequent
controller scans through state 16 back to dense state 17. It works at every
non-first marker position in every candidate PRA model, including
nonstandard register contents and clock lengths. The assumed starting tape
has the exact `k=1` header and delimiter shapes stated in the theorem; the
selected register must be nonzero, and the initial first physical register
must be `k+7`. After the decrement path that first block has value `k+1`.
The first-value-six case, selected-zero case, state-42 zero-residual case,
and other header layouts are separate and are not covered.

For the exact updated file `p` after the first physical block, the theorem
proves there is an `r` with `p = 2*r`. Set

```
z = zeros(2, zeros(k, 1 + 4*r))
w = ones(4, 1 + 4*z)
```

The returned state-17 tape has left half `h = 1 + 2*zeros(2,zeros(6,u))`
and right half `1 + 4*w`. Thus its **left half has the same k=1 padded
header shape** as the starting controller path, and the exact transformed
right half is stated above. The theorem also gives the full model-valued
physical clock. `PA194SixteenHeaderReturn.backToHeader` proves the last
five-step state-16-to-17 segment independently.

The same header shape does not imply the next branch repeats: the exact
returned right half selects the four-one route to dense state 61. The
checked continuation from there to dense state 84 is described in
`MARKER-TO-84.md`.

This closes a physical header-shape recurrence, not yet a source-machine
simulation: it has not identified the transformed right tape with a source
instruction or source frame, and has not proved the starting shape reachable
from the blank tape. Neither PA consistency direction follows yet.

Replay from the repository root with pinned overlays:

```sh
TMPDIR=/dev/shm IPRA_LEAN_OVERLAY=/path/to/ipra/lib \
  IPRA_FOUNDATION_OVERLAY=/path/to/foundation/lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-marker-header-recurrence.sh
```

An independent ordered suffix replay rebuilt eight controller and recurrence
modules in a fresh tmpfs overlay against separately checked machine objects and
preserved prerequisite/scratch overlays. The reported theorem axioms did not
include `sorryAx`. The full nested replay is running separately.
