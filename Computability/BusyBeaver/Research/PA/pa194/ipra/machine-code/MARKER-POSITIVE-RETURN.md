# Returning the first block after the PA194 decrement

`PA194MarkerPositiveReturn.markerPositiveReturn` continues the genuine
non-first marker path described in `MARKED-CYCLE-DECREMENT.md` through the
positive selected-register decrement and the subsequent first-block return.
It applies at each non-first marker position in every candidate PRA model,
including nonstandard register values and loop lengths. It assumes the exact
`k=1` starting header, the initial first physical value `m+6`, the specified
selected delimiter and following file, and a nonzero selected value. The
physical zero-selected-register case and the state-42 zero-residual branch
are separate and are not covered here.

The endpoint is dense state 7 with left half `a3` as defined in the theorem
and right half `2*block(m, updatedFile)`. Thus the first physical block has
changed from `m+6` to `m`; the selected block contains the predecessor of its
positive old value; and the intervening and following blocks are unchanged.
The additional low zero in the right half is part of the stated physical tape
layout. `continuePositive` factors the final return as a reusable all-model
composition, and `returnResidual` proves that return in exactly `m+2` steps.

This does not prove that the starting layout is reached from the blank tape,
that the endpoint is a source frame, or that these physical changes implement
a particular source instruction. It does not prove either PA consistency
direction.

Replay from the repository root with the pinned overlays:

```sh
TMPDIR=/dev/shm IPRA_LEAN_OVERLAY=/path/to/ipra/lib \
  IPRA_FOUNDATION_OVERLAY=/path/to/foundation/lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-marker-positive-return.sh
```

The checker rebuilds the two prerequisite chains and both return modules in
private temporary directories and rejects `sorryAx` in the reported theorem
dependencies.

An independent suffix replay rebuilt both new modules against separately
checked marker-cycle and decrement objects and preserved prerequisites, with no
`sorryAx` in the reported dependencies. The full nested replay is running
separately.
