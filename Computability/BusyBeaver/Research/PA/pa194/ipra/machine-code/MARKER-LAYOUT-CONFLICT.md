# Non-first marker output is not the conditional increment-route input

`PA194MarkerLayoutConflict.positiveMarkOutputNotRoute` proves an all-model
incompatibility between the exact output right half of the existing
`PA194MarkAll.modelMarkAllPositive` theorem and the right-half assumption in
`PA194IncrementDispatch.markerToIncrement`.

For any non-first position, `modelMarkAllPositive` returns
`parity(l) + 2*a`, where `a` is `returnCode` applied to a nonempty regular
prefix followed by the marked tail. `regularPrefixBit` proves that `a` has
second-lowest binary bit 1, in every candidate PRA model. The particular
nine-bit route in `markerToIncrement` instead requires the right half to have
the form `2*(4*v)+1`. `positiveMarkOutputNotRoute` proves that these two
forms can never be equal, for arbitrary parameters and nonstandard model
values. Its statement is stronger than required: it does not need the finite
position bound or the selected-delimiter condition of `modelMarkAllPositive`.

Consequently the conditional marker-exit-to-increment theorem remains a valid
physical equation for its stated tape shape, but it **cannot** be composed
immediately with the existing non-first marking-output theorem. This result
says nothing about other controller paths, the first physical marker, or either
PA consistency direction. The actual source/file layout invariant remains open.

Replay from the repository root using the pinned overlays:

```sh
TMPDIR=/dev/shm IPRA_LEAN_OVERLAY=/path/to/ipra/lib \
  IPRA_FOUNDATION_OVERLAY=/path/to/foundation/lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-marker-layout-conflict.sh
```

The script rebuilds the marking prerequisites and this module in a private
temporary directory and rejects `sorryAx` in the reported dependencies.

An independent suffix replay recompiled this module against the preserved
marker prerequisites in a fresh tmpfs output directory, with no `sorryAx` in
the reported axioms. The full standalone replay is still in progress.
