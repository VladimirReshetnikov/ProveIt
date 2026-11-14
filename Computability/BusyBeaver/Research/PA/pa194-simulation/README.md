# PA194 one-step quotient simulation

`PA194Simulation.lean` proves the incoming-history invariant for the exact
parent transition table: it holds at start control 74 and after every
successful parent step. Using the ordinary and 28 exceptional table cases,
`simulation_step` proves that every parent step from a configuration with
that invariant is simulated by a strictly positive number of folded steps.
Both machines may have any integer head position and any full binary tape;
their endpoints have the same tape and the projected control.

To check the module from the repository root:

```sh
task_dir=$(mktemp -d /dev/shm/pa194-simulation-check.XXXXXXXX)
lake env lean -M6000 -j1 -o "$task_dir/PA194LocalQuotient.olean" \
  Computability/BusyBeaver/Research/PA/pa194-quotient/PA194LocalQuotient.lean
for task_module in PA194AllTape PA194Translate PA194Ordinary; do
  case "$task_module" in
    PA194AllTape) task_source=pa194-all-tape ;;
    PA194Translate) task_source=pa194-translate ;;
    PA194Ordinary) task_source=pa194-ordinary ;;
  esac
  LEAN_PATH="$task_dir:$(lake env printenv LEAN_PATH)" lean -M6000 -j1 \
    -o "$task_dir/$task_module.olean" \
    "Computability/BusyBeaver/Research/PA/$task_source/$task_module.lean"
done
LEAN_PATH="$task_dir:$(lake env printenv LEAN_PATH)" lean -M6000 -j1 \
  Computability/BusyBeaver/Research/PA/pa194-simulation/PA194Simulation.lean
rm -rf "$task_dir"
```

This is a standard-Lean one-step result. It does not itself prove a global
halting equivalence or an internal PRA or iPRA theorem.
