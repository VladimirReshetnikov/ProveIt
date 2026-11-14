# PA194 positive-decrement return and next scan

`PA194MarkerPositiveScan.markerPositiveScan` composes the genuine non-first
marker path and positive selected-register decrement from
`MARKER-POSITIVE-RETURN.md` with the next physical controller and register
scan. Under the same `k=1` header, initial first value `m+6`, exact delimiter
and file shape, and positive selected value, the state-7 endpoint executes
states 7 → 9 → 12 → 12, then state 12 scans the reconstructed first block
of value `m`. The theorem gives an exact clock and both tape halves at state
13 for arbitrary candidate PRA models, including nonstandard model values.

The right half is the updated file after its first block: intervening blocks
and the following suffix are unchanged, and the selected positive register
is replaced by its predecessor. The scanned first block is represented by
`m` zero cells on the left, in the explicit shape of the theorem. The source
first value was `m+6`. Neither the starting layout's reachability nor a
source-frame or source-instruction correspondence is established.

`PA194SevenReturnController.sevenThroughFirst` gives the reusable state-7 to
state-13 physical segment, and `continueThroughFirst` composes it with any
matching state-7 run. The zero selected-value and zero residual branches are
outside this theorem; see the earlier packages for their partial results.

Replay from the repository root with pinned overlays:

```sh
TMPDIR=/dev/shm IPRA_LEAN_OVERLAY=/path/to/ipra/lib \
  IPRA_FOUNDATION_OVERLAY=/path/to/foundation/lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-marker-positive-scan.sh
```

An independent suffix replay rebuilt the two new modules against separately
checked marker and decrement objects, reusing preserved prerequisites. The
reported theorem axioms did not include `sorryAx`; the full author nested
replay also passed using the audited overlays.
