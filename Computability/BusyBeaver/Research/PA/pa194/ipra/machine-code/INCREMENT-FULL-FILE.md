# Complete physical file after the slot-8 increment

`PA194IncrementFullFile.completeFile` rewrites the exact output code from
`MARKER-TO-INCREMENT.md` as one ordinary eleven-block physical file. Its
blocks are: the returned first physical value `k`; the seven retained
prefix values; the incremented physical slot-8 value; the pre-existing
spare; and a newly appended one-valued spare, followed by the zero suffix.
The original selected-register decrement is already reflected in the
retained prefix or in the slot-8 input value. This equality holds in every
candidate PRA model, including nonstandard values.

This is a physical-file equality. The dense-7 endpoint has an even left
half and is not itself the canonical root frame, as shown in
`MARKER-TO-INCREMENT.md`. No source control, source instruction, blank-tape
reachability, or PA consistency direction is established here.

Replay from the repository root with pinned overlays:

```sh
TMPDIR=/dev/shm IPRA_LEAN_OVERLAY=/path/to/ipra/lib \
  IPRA_FOUNDATION_OVERLAY=/path/to/foundation/lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-increment-full-file.sh
```

An independent fresh suffix replay rebuilt this theorem together with all
eleven increment and endpoint boundary modules against separately checked
slot-eight and rewind overlays, without `sorryAx` in reported dependencies.
