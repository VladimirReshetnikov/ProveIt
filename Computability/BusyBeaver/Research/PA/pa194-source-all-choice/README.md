# Total choice for an internal Foundation universal-rule premise

`choiceCode : Code 3` is a fixed finite candidate-PRA code taking a conclusion
set `s`, a distinguished formula `special`, and a premise member `q`. It
returns `0` if `special = q`; otherwise it returns one plus the result of the
fixed source preimage search. Thus zero is the distinguished-formula marker,
and a successor `u+1` carries the selected source formula code `u`.

`all_premise_choice` proves the selector correct for every member of the exact
Foundation universal-introduction premise `insert (free L p) (setShift L s)`
when that premise has an internal `DerivationOf` under a Foundation Δ₁ theory.
The result holds in every candidate-PRA model with an IΣ₁ arithmetic reduct,
including nonstandard derivations, sets and formulas. If the distinguished
formula is also in `setShift L s`, equality takes priority and the code returns
the zero marker; this is permitted by the theorem.

This discharges both branches of this selection problem. It does not yet
produce a complete coded proof traversal, compiler correctness, PA/source
calculus calibration, or a machine halting reduction.

The final module passed a fresh Lean 4.32 suffix rebuild against the freshly
rebuilt universal-preimage, binary set-search, source-shift suffixes and the
audited project and Foundation objects. `#print axioms` reports `[propext,
Classical.choice, Quot.sound]`, without `sorryAx`. The full nested replay below
is pending; the source-shift dependency has passed its own full replay.

From the repository root, with matching audited project and Foundation objects:

```sh
IPRA_LEAN_OVERLAY=/path/to/project/lib \
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
  Computability/BusyBeaver/Research/PA/pa194-source-all-choice/check.sh
```

The script rebuilds the prerequisite chain under `/dev/shm` by default; set
`TMPDIR` for another suitable temporary directory.
