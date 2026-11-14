# PA194 local quotient at any head position

`PA194Translate.lean` shows that the full-tape transition and finite-run
semantics commute with integer translation. `checked_case_any_head` applies
the 28 verified exceptional reader simulations at any integer head position
on any full tape, assuming only the recorded history and current bits.

To check from the repository root, use a private temporary build directory:

```sh
task_dir=$(mktemp -d /dev/shm/pa194-translate-check.XXXXXXXX)
lake env lean -M6000 -j1 -o "$task_dir/PA194LocalQuotient.olean" \
  Computability/BusyBeaver/Research/PA/pa194-quotient/PA194LocalQuotient.lean
LEAN_PATH="$task_dir:$(lake env printenv LEAN_PATH)" lean -M6000 -j1 \
  -o "$task_dir/PA194AllTape.olean" \
  Computability/BusyBeaver/Research/PA/pa194-all-tape/PA194AllTape.lean
LEAN_PATH="$task_dir:$(lake env printenv LEAN_PATH)" lean -M6000 -j1 \
  Computability/BusyBeaver/Research/PA/pa194-translate/PA194Translate.lean
rm -rf "$task_dir"
```

The result is a standard-Lean finite-run statement. It does not yet give a
model-internal trace iteration or a PRA or iPRA consistency theorem.
