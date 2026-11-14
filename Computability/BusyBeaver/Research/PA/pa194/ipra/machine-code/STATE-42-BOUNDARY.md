# PA194 state-42 returned-file split

`PA194State42Boundary.runDichotomy` proves the complete two-step behavior for
state 42 when its right half is `2*ones(n,2*t)`. If `n=0`, the states are
42 → 59 → 84 and both tape halves return unchanged. If `n=m+1`, the states
are 42 → 59 → 1, the left half is multiplied by four, and the right half is
`ones(m,2*t)`. The disjunction is exhaustive in every candidate PRA model,
including nonstandard model elements and run lengths.

`returnedTailEven` proves that the exact `returnCode` remainder `w` occurring
in the non-first marking cycle is even, for every finite prefix length and
all model values. `returnedRunDichotomy` consequently applies the split to
state 42 with right half `2*ones(n,w)` without any separate evenness premise.
This is the right-half shape reached by the `n+5` branch of
`PA194PositiveMarkCycle.positiveMarkFiveTo42` under its stated assumptions.

The theorem does not identify the state-1 residual with the marked decrement
file, prove that state 84 is a source frame, establish a closed source-level
recurrence, or prove either PA consistency direction. Those layout and
reachability obligations remain open.

To replay from the repository root:

```sh
TMPDIR=/dev/shm IPRA_LEAN_OVERLAY=/path/to/ipra/lib \
  IPRA_FOUNDATION_OVERLAY=/path/to/foundation/lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-state42-boundary.sh
```

The script rebuilds the header-controller prerequisites and three row/split
modules in a private temporary directory, rejecting `sorryAx` in reported
theorem dependencies.

An independent suffix replay rebuilt the table row and state-42 modules in a
fresh tmpfs overlay against the preserved marker prerequisites, with no
`sorryAx` in the reported theorem dependencies. A full nested replay is running
separately.
