# PA194 rewind restores the prefix and marks physical slot 8

`PA194MarkerMarkedSlot8.markerMarkedSlot8` strengthens the complete genuine
marker-entry run in `MARKER-REWIND-SEVEN.md`. At its dense-17 endpoint, the
seven traversed physical blocks appear on the right in their original order,
followed by the existing `PA194MarkedFile.markedBlock` code for the next
physical block. `PA194UpdatedSevenMark.matchSevenMark` supplies the exact
all-model witness that makes the earlier `4*s` delimiter a marked block.

The full nine-register file's first physical block is still represented on
the left/controller side, so the seven right-prefix blocks are physical
slots 1 through 7 and the next marked block is slot 8.
`PA194SlotEight.logicalSixAtPhysicalEight` checks the existing finite
`M6.Source.physicalRegister` permutation: logical register 6 maps to physical
slot 8. This identifies the physical position and its logical register; it
does not prove which source instruction is active or that the machine is at
a source frame.

All original assumptions remain explicit: an intermediate genuine marker
entry at any of the eight non-first positions, the exact `k=1` header and
file layout, a positive selected value, first physical value `k+7`, and
`idx+n=7`. Values and clocks may be nonstandard model elements. The
first-value-six, selected-zero, state-42 zero-residual, and other header
cases remain separate. Blank-tape reachability, source-instruction
correspondence, and both PA consistency directions remain open.

Replay from the repository root with pinned overlays:

```sh
TMPDIR=/dev/shm IPRA_LEAN_OVERLAY=/path/to/ipra/lib \
  IPRA_FOUNDATION_OVERLAY=/path/to/foundation/lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-marker-slot-eight.sh
```

An independent suffix replay rebuilt the three new modules against separately
checked rewind/traversal objects and preserved prerequisite/scratch overlays.
The displayed theorem axioms did not include `sorryAx`; the full nested replay
is separate.
