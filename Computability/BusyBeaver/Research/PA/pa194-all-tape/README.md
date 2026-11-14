# PA194 local quotient on complete tapes

`PA194AllTape.lean` lifts the finite certificate from `../pa194-quotient` to
complete two-way tapes `Int → Bool`. For each of the 28 recorded cases,
`checked_case_all_tapes` proves that, when the tape has the recorded history
and current bits at positions -1 and 0, the folded run reaches exactly the
projected parent one-step configuration, including equality of the entire
tape. Positions are relative to the initial head. Other tape cells are
arbitrary.

To check from the repository root, compile the finite certificate into a
private temporary directory and then check the lifting module:

```sh
task_dir=$(mktemp -d /dev/shm/pa194-tape-check.XXXXXXXX)
lake env lean -M6000 -j1 -o "$task_dir/PA194LocalQuotient.olean" \
  Computability/BusyBeaver/Research/PA/pa194-quotient/PA194LocalQuotient.lean
LEAN_PATH="$task_dir:$(lake env printenv LEAN_PATH)" \
  lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194-all-tape/PA194AllTape.lean
rm -rf "$task_dir"
```

The theorem concerns standard natural-number finite runs. It does not yet
iterate the quotient for arbitrary model-length traces or prove halting
or consistency equivalence in PRA or iPRA.
