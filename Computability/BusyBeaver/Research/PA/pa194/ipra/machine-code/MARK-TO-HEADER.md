# PA194 marking-entry to controller state 24

`PA194MarkToHeader.firstMarkTo24` and `positiveMarkTo24` compose the
physical marking runs with the checked marker-exit-to-state-24 controller
segment. Together they cover all nine physical register positions in every
candidate PRA model; tape and register values may be nonstandard. The clocks
and both resulting tape halves are explicit in the Lean statements.

For the first position, the start control is dense 113. The left half is
`2*ones(k,256*u)+1` and the right half is `2*(2*t+1)`. The resulting control
is 24, with left half `512*u+1` and right half `ones(k,4*t)`.

For the remaining positions, the start control is the corresponding checked
`markerControl`. The left half has the same padded one-run form; the right
half is the explicit regular-file code with the selected delimiter constraint
`e (Fin.last (n+1)) = 2*(2*t+1)`. The resulting control is 24 with the same
left half and a right half consisting of `k` ones prepended to the exact
returned marked-file code. The arithmetic description is shorthand for the
explicit model terms in the statements.

These theorems require the displayed starting tape shapes. They do not show
that source dispatch establishes those shapes, that state 24 is an increment or
decrement entry, or either consistency implication.

To replay from the repository root:

```sh
TMPDIR=/dev/shm IPRA_LEAN_OVERLAY=/path/to/ipra/lib \
  IPRA_FOUNDATION_OVERLAY=/path/to/foundation/lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-mark-to-header.sh
```

The script freshly rebuilds the marker and header prerequisites and checks
the new theorem in a private temporary directory, rejecting `sorryAx` in the
reported dependencies.

An independent suffix replay rebuilt the new controller modules in order in a
fresh temporary overlay, reusing the preserved marker prerequisites. The
printed dependencies had no `sorryAx`. The nested replay command above also rebuilds the
prerequisite chain; its full run is in progress.
