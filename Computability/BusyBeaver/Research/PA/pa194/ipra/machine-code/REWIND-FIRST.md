# PA194 state-14 first-block rewind

`PA194RewindFirst.firstTo17` proves a reusable all-model physical segment
beyond dense state 14. If the left half is `block(v,2*l)` and the right half
is `2*t+1`, it first follows the pinned state-14 and state-15 transitions,
then runs the marker-return scan for v steps plus its boundary steps. It
reaches dense 17 after exactly `2+(v+2)` steps. The final halves are
`half(l)` and `parity(l)+4*ones(v,1+8*t)`. The value v and all tape halves
may be nonstandard elements of a candidate PRA model.

This is the first physical block of a potential reverse traversal, not a
proof that the complete seven-block left fold is restored, that a canonical
source root is reached, or that either PA consistency direction holds. The
odd-right-half and even remaining-left-tail shapes must still be linked to
the full marker-to-state-14 endpoint before claiming a composed run.

Replay from the repository root with pinned overlays:

```sh
TMPDIR=/dev/shm IPRA_LEAN_OVERLAY=/path/to/ipra/lib \
  IPRA_FOUNDATION_OVERLAY=/path/to/foundation/lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-rewind-first.sh
```

An independent suffix replay recompiled this module against separately checked
traversal objects and preserved prerequisite/scratch overlays. Its reported
theorem axioms did not include `sorryAx`; the full nested replay is separate.
