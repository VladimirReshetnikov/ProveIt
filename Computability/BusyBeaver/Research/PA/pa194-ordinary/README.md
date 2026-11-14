# PA194 ordinary transitions on complete tapes

`PA194Ordinary.lean` uses the checked quotient tables to prove that every
parent transition outside the seven pairs of folded reader controls agrees
with one folded transition after state projection. The proof allows any head
position and any complete tape. It imports `PA194AllTape` and therefore also
depends on the finite certificate in `../pa194-quotient`.

To check from the repository root, build the two prerequisites in a private
temporary directory and check the theorem:

```sh
task_dir=$(mktemp -d /dev/shm/pa194-ordinary-check.XXXXXXXX)
lake env lean -M6000 -j1 -o "$task_dir/PA194LocalQuotient.olean" \
  Computability/BusyBeaver/Research/PA/pa194-quotient/PA194LocalQuotient.lean
LEAN_PATH="$task_dir:$(lake env printenv LEAN_PATH)" lean -M6000 -j1 \
  -o "$task_dir/PA194AllTape.olean" \
  Computability/BusyBeaver/Research/PA/pa194-all-tape/PA194AllTape.lean
LEAN_PATH="$task_dir:$(lake env printenv LEAN_PATH)" lean -M6000 -j1 \
  Computability/BusyBeaver/Research/PA/pa194-ordinary/PA194Ordinary.lean
rm -rf "$task_dir"
```

This one-step standard-Lean theorem does not itself establish a trace-level
halting equivalence or a theorem in PRA or iPRA.
