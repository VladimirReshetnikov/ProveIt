# PA195 one-step quotient simulation

`PA195Simulation.lean` proves the incoming-history invariant for the exact
parent transition table: it holds at start control 74 and after every
successful parent step. Using the ordinary and 28 exceptional table cases,
`simulation_step` proves that every parent step from a configuration with
that invariant is simulated by a strictly positive number of folded steps.
Both machines may have any integer head position and any full binary tape;
their endpoints have the same tape and the projected control.

To check the module from the repository root:

```sh
task_dir=$(mktemp -d /dev/shm/pa195-simulation-check.XXXXXXXX)
lake env lean -M6000 -j1 -o "$task_dir/PA195LocalQuotient.olean" \
  Computability/BusyBeaver/Research/PA/pa195-quotient/PA195LocalQuotient.lean
for task_module in PA195AllTape PA195Translate PA195Ordinary; do
  case "$task_module" in
    PA195AllTape) task_source=pa195-all-tape ;;
    PA195Translate) task_source=pa195-translate ;;
    PA195Ordinary) task_source=pa195-ordinary ;;
  esac
  LEAN_PATH="$task_dir:$(lake env printenv LEAN_PATH)" lean -M6000 -j1 \
    -o "$task_dir/$task_module.olean" \
    "Computability/BusyBeaver/Research/PA/$task_source/$task_module.lean"
done
LEAN_PATH="$task_dir:$(lake env printenv LEAN_PATH)" lean -M6000 -j1 \
  Computability/BusyBeaver/Research/PA/pa195-simulation/PA195Simulation.lean
rm -rf "$task_dir"
```

This is a standard-Lean one-step result. It does not itself prove a global
halting equivalence or an internal PRA or iPRA theorem.
