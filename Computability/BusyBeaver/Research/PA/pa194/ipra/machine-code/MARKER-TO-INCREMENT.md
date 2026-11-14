# PA194 marker path through the forced slot-8 increment

`PA194MarkerToIncrement.markerToIncrement` composes the genuine non-first
marker-entry path through the positive decrement, seven-block return,
physical-slot-8 mark, dense-2 dispatch, the slot-8 increment box, and the
first-block return to dense state 7. It works for all eight non-first marker
positions in every candidate PRA model, including nonstandard register
values and clock lengths.

The theorem assumes the exact initial `k=1` header and delimiter/file shape,
positive selected register, first physical value `k+7`, and `idx+n=7` for
the nine-block remaining file. **It additionally assumes that the final
suffix is zero.** This blank-suffix premise is required by the existing
increment box and is not inferred from the earlier arbitrary-suffix theorem.
The first-value-six, selected-zero, state-42 zero-residual and other header
cases remain separate.

The initial selected physical block is decremented. After the seven-block
rewind, the block at physical slot 8 is marked and the box increments it;
if these are the same block, the increment acts on the already-decremented
value. The first physical block is returned with value `k`. The exact
remaining-file result is given by `PA194IncrementOutputExact.outputExact`:
the seven prefix values are retained, slot 8 is incremented, the existing
spare is retained, and a fresh one-valued spare is appended. The final dense-7
halves and the complete primitive-recursive model clock are stated in the
composed theorem. `PA194MarkedExitIncrement.markedExitIncrement` separately
proves the marked-exit-to-increment and head-return segment.

This is an exact intermediate physical transformation. The dense-7 left
half is even and `PA194IncrementBoundary.evenLeftNotOne` proves it cannot
equal 1 in any candidate PRA model. The canonical standard-natural source
root has singleton left tape `[true]`, numeric code 1. The pinned external
label map additionally identifies dense 7 as native 40, whereas the source
root control is native 84 (dense 24). Thus this endpoint itself is not the
canonical root. Reaching and identifying a later root frame, blank-tape
reachability, and matching these compound changes to a source instruction
remain open. Neither PA consistency direction is proved here.

Replay from the repository root with pinned overlays:

```sh
TMPDIR=/dev/shm IPRA_LEAN_OVERLAY=/path/to/ipra/lib \
  IPRA_FOUNDATION_OVERLAY=/path/to/foundation/lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-marker-to-increment.sh
```

An independent fresh suffix replay rebuilt all eleven increment and endpoint
boundary modules against separately checked slot-eight and rewind overlays.
It passed without `sorryAx` in the reported theorem dependencies. The
comprehensive `check-marker-to-increment.sh` nested replay also subsequently
passed, including the final marker-to-increment theorem.
