# PA195 local quotient at any head position

`PA195Translate.lean` shows that the full-tape transition and finite-run
semantics commute with integer translation. `checked_case_any_head` applies
the 28 verified exceptional reader simulations at any integer head position
on any full tape, assuming only the recorded history and current bits.

To check from the repository root, use a private temporary build directory:

```sh
task_dir=$(mktemp -d /dev/shm/pa195-translate-check.XXXXXXXX)
lake env lean -M6000 -j1 -o "$task_dir/PA195LocalQuotient.olean" \
  Computability/BusyBeaver/Research/PA/pa195-quotient/PA195LocalQuotient.lean
LEAN_PATH="$task_dir:$(lake env printenv LEAN_PATH)" lean -M6000 -j1 \
  -o "$task_dir/PA195AllTape.olean" \
  Computability/BusyBeaver/Research/PA/pa195-all-tape/PA195AllTape.lean
LEAN_PATH="$task_dir:$(lake env printenv LEAN_PATH)" lean -M6000 -j1 \
  Computability/BusyBeaver/Research/PA/pa195-translate/PA195Translate.lean
rm -rf "$task_dir"
```

The result is a standard-Lean finite-run statement. It does not yet give a
model-internal trace iteration or a PRA or iPRA consistency theorem.
