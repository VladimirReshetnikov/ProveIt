# PA194 positive return through state 16

`PA194MarkerPositiveSixteen.markerPositiveSixteen` extends the genuine
non-first marker path and positive selected-register decrement through state
16. It works for every non-first marker position and in every candidate PRA
model, with arbitrary, possibly nonstandard, values and run lengths. It
retains the exact `k=1` header and delimiter assumptions, requires a
positive selected value, and requires the initial first physical register
value to be `k+7`. Its reconstructed value is `k+1`, so this extension covers
the positive reconstructed-first-value branch. The first-value-six and
zero-selected-value branches are not covered.

The theorem starts at the actual marking entry and gives an explicit clock and
both tape halves at state 16. It does not assume that the returned remaining
file is even: `PA194ReturnedUpdatedEven.updatedEven` proves this for all
physical indices. `PA194SevenToSixteen.positiveFirstToSixteen` supplies the
reusable continuation from state 7, via states 9, 12, 13, 14, and 15. It
uses the existing all-model, nonstandard-length controller scan.

These are physical-machine facts about a specified intermediate tape shape.
The proof has not established that the starting shape is reached from the
blank tape, nor identified the state-16 tape with a source frame or source
instruction. It proves neither PA consistency direction.

Replay from the repository root with pinned overlays:

```sh
TMPDIR=/dev/shm IPRA_LEAN_OVERLAY=/path/to/ipra/lib \
  IPRA_FOUNDATION_OVERLAY=/path/to/foundation/lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-marker-positive-sixteen.sh
```

An independent ordered suffix replay rebuilt the fourteen listed controller
and state-16 modules in a fresh tmpfs output directory, using separately checked
marker/decrement objects and preserved scratch and prerequisite overlays. The
reported theorem axioms did not include `sorryAx`. The full nested replay is
running separately.
