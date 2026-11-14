# PA195 quotient control totality

`PA195ControlData.lean` kernel-checks the unfolded parent's complete native
transition table: every transition target is either the native halt label 254
or a control with table rows, and both read-bit transitions are present at
every working control. It also checks that native start 74 is valid, the
folded table has no halt-control transitions, and the state projection fixes
halt.

`PA195Control.lean` lifts these finite facts to any full tape and head
position. A defined parent step always ends at a valid control, every valid
nonhalting parent configuration has a next step, and every halted folded
configuration is stuck. These are standard-Lean statements, not PRA or iPRA
proofs.

Check from the repository root, with a private temporary build directory:

```sh
task_dir=$(mktemp -d /dev/shm/pa195-control-check.XXXXXXXX)
lake env lean -M6000 -j1 -o "$task_dir/PA195LocalQuotient.olean" \
  Computability/BusyBeaver/Research/PA/pa195-quotient/PA195LocalQuotient.lean
LEAN_PATH="$task_dir:$(lake env printenv LEAN_PATH)" lean -M6000 -j1 \
  -o "$task_dir/PA195AllTape.olean" \
  Computability/BusyBeaver/Research/PA/pa195-all-tape/PA195AllTape.lean
LEAN_PATH="$task_dir:$(lake env printenv LEAN_PATH)" lean -M6000 -j1 \
  -o "$task_dir/PA195ControlData.olean" \
  Computability/BusyBeaver/Research/PA/pa195-control/PA195ControlData.lean
LEAN_PATH="$task_dir:$(lake env printenv LEAN_PATH)" lean -M6000 -j1 \
  Computability/BusyBeaver/Research/PA/pa195-control/PA195Control.lean
rm -rf "$task_dir"
```

The finite certificate reports no axioms. The checked semantic results use
`propext` and, for totality and closure, `Quot.sound`.
