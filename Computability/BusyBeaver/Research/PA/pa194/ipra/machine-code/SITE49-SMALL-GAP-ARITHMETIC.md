# Site-49 small-gap header arithmetic

`PA194Site49SmallGapArithmetic.gapTwo`, `gapThree` and `gapFour` are Lean-checked natural-number arithmetic lemmas. They compare the explicit ten-bit output prefix from `PA194Site49PositiveFinish.returnWord`, followed respectively by one, two or three zero cells and an odd marker, against the actual fourteen-bit site-50 path followed by an arbitrary natural number. Each proves the words unequal. These zero-cell counts correspond arithmetically to site-49 frame gaps 2, 3 and 4 in the positive branch.

The small standalone module does not yet formally connect its `word` function to the model-valued literal stepper or prove a theorem about the machine's subsequent behavior. The separately checked return theorem supplies the physical output prefix; the combined machine-level non-match remains future work. No impossibility of the full computation or consistency implication is claimed.

A fresh replay passed exit 0 and no sorryAx. From the repository root, with a nonexistent output directory:

```sh
bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-site49-small-gap-arithmetic.sh "$PWD" Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code /dev/shm/pa194-site49-small-gap-arithmetic-repo
```

The checker uses the repository's Lean toolchain, copies and rechecks the source, audits the three axioms, and records the source hash. Its only import is `Lean.Elab.Tactic.Omega`.
