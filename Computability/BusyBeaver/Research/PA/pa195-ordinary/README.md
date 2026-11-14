# PA195 ordinary transitions on complete tapes

`PA195Ordinary.lean` uses the checked quotient tables to prove that every
parent transition outside the seven pairs of folded reader controls agrees
with one folded transition after state projection. The proof allows any head
position and any complete tape. It imports `PA195AllTape` and therefore also
depends on the finite certificate in `../pa195-quotient`.

To check from the repository root, build the two prerequisites in a private
temporary directory and check the theorem:

```sh
task_dir=$(mktemp -d /dev/shm/pa195-ordinary-check.XXXXXXXX)
lake env lean -M6000 -j1 -o "$task_dir/PA195LocalQuotient.olean" \
  Computability/BusyBeaver/Research/PA/pa195-quotient/PA195LocalQuotient.lean
LEAN_PATH="$task_dir:$(lake env printenv LEAN_PATH)" lean -M6000 -j1 \
  -o "$task_dir/PA195AllTape.olean" \
  Computability/BusyBeaver/Research/PA/pa195-all-tape/PA195AllTape.lean
LEAN_PATH="$task_dir:$(lake env printenv LEAN_PATH)" lean -M6000 -j1 \
  Computability/BusyBeaver/Research/PA/pa195-ordinary/PA195Ordinary.lean
rm -rf "$task_dir"
```

This one-step standard-Lean theorem does not itself establish a trace-level
halting equivalence or a theorem in PRA or iPRA.
