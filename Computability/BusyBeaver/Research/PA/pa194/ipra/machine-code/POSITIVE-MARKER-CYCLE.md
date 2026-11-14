# A non-first marking cycle to dense state 42

`PA194ThresholdCycle.thresholdCycleTo42` proves a physical controller
invariant in every candidate PRA model: from state 35 with left half
`4096*u+13` and right half five one bits followed by an arbitrary model value
`r`, it returns through states 15 and 17, runs the checked `k=1` header path,
and reaches state 42 after 36 steps. Its output halves are `65536*u+222` and
`2*r`. The exact clock and tape values are stated using the repository's
primitive-recursive model functions.

`PA194PositiveMarkCycle.positiveMarkFiveTo42` connects this invariant to the
**actual** `modelMarkAllPositive` marking output. It covers each of the eight
non-first physical positions, assuming the existing selected-delimiter input
condition, the displayed `k=1` padded header, and that the first unmarked
prefix register has value `n+5`. The values `n`, the other register values,
and the remaining file tail may be nonstandard. It ends at state 42 with left
half `65536*u+222` and right half `2*ones(n,w)`, where `w` is the exact encoded
remainder of the prefix file. The Lean statement gives the precise `w`, full
input layout, and a clock equal to the physical marking clock plus 57 steps.

This is an actual marking-output/controller composition, with explicit
hypotheses. It does not yet show a closed recurrence on source configurations,
identify state 42 with a source operation, prove the `k=1` layout reachable
from source dispatch, or prove either PA consistency direction. Shorter
first-register values are covered only through the earlier state-35 branch
classification and remain to be continued.

To replay from the repository root:

```sh
TMPDIR=/dev/shm IPRA_LEAN_OVERLAY=/path/to/ipra/lib \
  IPRA_FOUNDATION_OVERLAY=/path/to/foundation/lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-positive-mark-cycle.sh
```

The script rebuilds the marking, header, dispatch and threshold prerequisites
and these modules in a private temporary directory, rejecting `sorryAx` in
reported theorem dependencies.

An independent suffix replay rebuilt both cycle modules in a fresh tmpfs
overlay against separately checked marker and threshold objects. The reported
theorem axioms did not include `sorryAx`; the full author nested replay also passed with the audited
overlays.
