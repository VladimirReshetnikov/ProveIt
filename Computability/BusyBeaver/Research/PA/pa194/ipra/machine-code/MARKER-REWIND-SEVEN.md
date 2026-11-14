# PA194 seven-block rewind and next marked block

`PA194MarkerRewindSeven.markerRewindSeven` extends the genuine marker-entry
path in `MARKER-TO-14.md` through the complete rewind of the seven traversed
physical blocks. It applies to all eight non-first marker positions, in
every candidate PRA model, including nonstandard register contents and
clock values. It assumes the exact initial `k=1` header and delimiter/file
layout, a positive selected register, initial first physical value `k+7`,
and `idx+n=7` for the complete nine-block remaining file. The
first-value-six, selected-zero, state-42 zero-residual and other header
cases remain separate.

The theorem returns to dense state 17 with the seven traversed blocks back
on the right in their original order. The following block's delimiter code
changes from `4*s+2` to `4*s`: its first one is erased, giving the marked
physical shape. The full model-valued clock and exact left and right halves
are stated explicitly. `PA194UpdatedSevenOdd.matchSevenOdd` proves that the
remaining-file half needed for the state-14 exit is necessarily odd for
all eight marker positions. `PA194SevenRewind.sevenTo17` gives the reusable
seven-block physical segment.

`PA194RewindFile.rewindFile` proves a more general finite-block invariant:
starting at dense 17 with its specified double-halved left file, odd right
half, and a final left tail that is twice an odd value, it rewinds any fixed
finite number of blocks with an exact primitive-recursive clock and folded
right file. Values and clocks may be nonstandard model elements.

This endpoint is still a physical controller state, not a proved canonical
source frame or source instruction. Blank-tape reachability and both PA
consistency directions remain open.

Replay from the repository root with pinned overlays:

```sh
TMPDIR=/dev/shm IPRA_LEAN_OVERLAY=/path/to/ipra/lib \
  IPRA_FOUNDATION_OVERLAY=/path/to/foundation/lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-marker-rewind-seven.sh
```

An independent ordered suffix replay rebuilt the four rewind modules against
separately checked traversal objects and preserved prerequisite/scratch
overlays. Their reported theorem axioms did not include `sorryAx`; the full
nested replay remains separate.
